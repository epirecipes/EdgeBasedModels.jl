# Legacy tests: dynamic (the DynamicConfigurationModel of EdgeBasedModels 0.1).
#
# Owner: WP21 (DESIGN_NetworkEpiCore.md §G.2), which replaced the legacy Volz–Meyers-style builder
# by the Miller–Slim–Volz dynamic fixed-degree lift `edge_based(model, DynamicNetwork(base,
# NeighbourExchange(η)))` (src/lift/dynamic.jl; its tests are in test/suites/dynamic.jl). The 0.1
# tests of this file checked only the keys of the defective builder (LEGACY[E05, E06] and
# LEGACY-WEAK[E07, E30]: SEIR was silently an SIR model with recovery rate σ); they are replaced by
#
# - the migration error of the legacy entry point (design §A.7: functionality that returned wrong
#   numbers errors immediately), whose routing belongs to the owner of src/factories.jl;
# - the migration path, run on the legacy inputs of the E05/E07 regression tests
#   (VERIFIED_ISSUES.md), with the verified reference values;
# - the goldens of test/golden/dynamic/, regenerated from the new lift (their notes say how they
#   were validated).

using EdgeBasedModels
using ModelingToolkit
using Symbolics
using OrdinaryDiffEq: Vern9
using Test

isdefined(Main, :GoldenTools) || Base.include(Main, joinpath(@__DIR__, "..", "golden", "GoldenTools.jl"))
using Main.GoldenTools

const EBM = EdgeBasedModels
const TOL = (solver = Vern9(), reltol = 1e-11, abstol = 1e-13)

@testset "legacy dynamic" begin
    @testset "DynamicConfigurationModel: the migration error (E05, E06, E07)" begin
        @parameters β γ κ η₁ η₂
        prog = DiseaseProgression([DiseaseStage(:I; transmission_rate = β), DiseaseStage(:R; transmission_rate = 0)],
                                  [DiseaseTransition(:I, :R, γ)]; entry = :I)
        model = DynamicConfigurationModel(poisson_pgf(κ), prog, η₁, η₂)
        err = EBM._dynamic_configuration_error(model)
        @test err isa ArgumentError
        msg = sprint(showerror, err)
        for s in ("E05", "E06", "E07", "M_S = qθψ'(θ)/ψ'(1)", "q = 1 − ρ", "η₁ was never used",
                  "DynamicNetwork(ConfigurationNetwork(pgf), NeighbourExchange(η₂))", "DormantContacts")
            @test occursin(s, msg)
        end
        # The legacy entry point build_edge_system(::DynamicConfigurationModel) (src/factories.jl)
        # throws this error since WP29 (the defective 0.1 builder is deleted).
        r = try
            build_edge_system(model)
        catch e
            e
        end
        @test r isa ArgumentError && sprint(showerror, r) == msg
        # the legacy model's progression still converts (the migration starts here)
        @test contact_model(model) isa ContactModel
    end

    @testset "the migration path on the legacy inputs gives the verified numbers" begin
        # E05 regression inputs: symbolic β, γ, κ, a legacy poisson_pgf(κ) and progression. With
        # β = 0.6, γ = 1, κ = 3, η = 1 and 0.1% seeded, the Miller–Slim–Volz DFD value is R∞ = 0.473831
        # (neighbour-exchange SSA, N = 2×10⁵: 0.47380 ± 0.00054; N = 4×10⁵: 0.47385 ± 0.00041); the
        # legacy builder gave 0.501817 with S(0) + I(0) = 1.001.
        @parameters β γ κ η
        prog = DiseaseProgression([DiseaseStage(:I; transmission_rate = β), DiseaseStage(:R; transmission_rate = 0)],
                                  [DiseaseTransition(:I, :R, γ)]; entry = :I)
        net = DynamicNetwork(ConfigurationNetwork(poisson_pgf(κ)), NeighbourExchange(η))
        sys = edge_based(contact_model(prog), net)
        p = Dict(:β => 0.6, :γ => 1.0, :κ => 3.0, :η => 1.0)
        sol = solve_epidemic(sys; p, initial = SeedFraction(:I => 1e-3), tspan = (0.0, 400.0), TOL...)
        S, I, R = (compartment(sys, sol, X) for X in (:S, :pop_I, :pop_R))
        @test S[1] + I[1] + R[1] ≈ 1 atol = 1e-12
        @test maximum(abs.(S .+ I .+ R .- 1)) < 1e-9
        @test R[end] ≈ 0.473831 atol = 2e-6
        # η = 0 is the static model (0.220249 for the static expanded EBCM; the legacy builder: 0.220468)
        sol0 = solve_epidemic(sys; p = merge(p, Dict(:η => 0.0)), initial = SeedFraction(:I => 1e-3),
                              tspan = (0.0, 400.0), TOL...)
        @test compartment(sys, sol0, :pop_R)[end] ≈ 0.220249 atol = 2e-6

        # E07 regression inputs: a legacy SEIR progression (E listed first, so transitions[1] is E → I).
        # The lift keeps E, σ and γ; attack rates at η = 0.3 for γ = 0.1 and 0.5 are 0.9786 and 0.6088
        # (independent DFD-SEIR ODEs; SSA 0.9784 ± 0.0002 at γ = 0.1), where the legacy builder gave
        # 0.6165 for both.
        @parameters σ
        seir = DiseaseProgression([DiseaseStage(:E; transmission_rate = 0), DiseaseStage(:I; transmission_rate = β),
                                   DiseaseStage(:R; transmission_rate = 0)],
                                  [DiseaseTransition(:E, :I, σ), DiseaseTransition(:I, :R, γ)]; entry = :E)
        sys = edge_based(contact_model(seir), net)
        @test haskey(sys.variables, :pop_E)
        pnames = Set(string.(ModelingToolkit.parameters(sys.system)))
        @test issubset(Set(["β", "σ", "γ", "κ", "η"]), pnames)
        attack(γv) = begin
            s = solve_epidemic(sys; p = Dict(:β => 0.2, :σ => 0.5, :γ => γv, :κ => 5.0, :η => 0.3),
                               initial = SeedFraction(:E => 1e-3), tspan = (0.0, 400.0), TOL...)
            1 - compartment(sys, s, :S)[end]
        end
        @test attack(0.1) ≈ 0.9786 atol = 1e-4
        @test attack(0.5) ≈ 0.6088 atol = 1e-4
    end

    check_area("dynamic")
end
