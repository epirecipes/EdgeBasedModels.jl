# Legacy tests: multitype.
#
# Split verbatim from the pre-refactor test/runtests.jl of EdgeBasedModels 0.1 (working tree of
# 2026-09-26) by WP1 of DESIGN_NetworkEpiCore.md; only comments were added.
# Owner after Phase 0: WP29 (legacy removal); WP17 replaces the builder through the assembler.
# Annotation tags (grep for them):
#   LEGACY-WRONG[<id>]  the assertion pins a value that VERIFIED_ISSUES.md <id> shows to be wrong;
#   LEGACY-WEAK[<id>]   the test cannot detect the defect <id> (structure only, or a loose reference);
#   LEGACY[<id>]        the code under test has the verified defect <id>; the test itself is neutral.
# They stay until the owning bug-fix work package replaces them (design section G.1).
#
# WP29: build_edge_system(::MultiTypeConfigurationModel) is a deprecation shim that forwards to the
# multitype lift of the stratified model (src/factories.jl). The within-type equations are the 0.1
# ones, and so are the names θ_<partner>_<node> and φ_<X>_<partner>_<node>. What changed, and is
# asserted below in place of the 0.1 expectation: every system has the cumulative accumulator of
# design §J.8 (one more equation and variable); populations are pop_<X>_<type>, fractions of ALL
# nodes (design §J.6), so the 0.1 within-type value is pop_<X>_<type>/n_<type> (there are no
# R_<type> and I_<type> aliases); every species has a seed parameter seed_<X>_<type>. The type sizes
# are inferred from edge reciprocity (equal here). test/suites/00_legacy_multitype.jl's goldens
# (test/golden/multitype/) were regenerated for these names, and the testset "0.2 reproduces the 0.1
# within-type trajectories" checks the new numbers against the 0.1 CSVs kept in
# test/golden/multitype/v01/.

using EdgeBasedModels
using ModelingToolkit
using Symbolics
using Test

import Catalyst

isdefined(Main, :GoldenTools) || Base.include(Main, joinpath(@__DIR__, "..", "golden", "GoldenTools.jl"))
using Main.GoldenTools

@testset "legacy multitype" begin
    @testset "Multivariate PGFs" begin
        @parameters κ_A κ_B

        # Multivariate Poisson
        pgf = multivariate_poisson_pgf([:A, :B], Dict(:A => κ_A, :B => κ_B))
        @test length(pgf.types) == 2
        @test pgf.types == [:A, :B]

        # Partial derivative contains κ_A
        d_A = partial_derivative(pgf, :A)
        @test occursin("κ_A", string(d_A))

        # Mixed partial contains both parameters
        d_AB = mixed_partial(pgf, :A, :B)
        @test occursin("κ_A", string(d_AB)) && occursin("κ_B", string(d_AB))

        # Mean degree: ⟨k_A⟩ = κ_A (after exp(0) cleanup)
        m_A = mean_degree(pgf, :A)
        @test isequal(m_A, κ_A)

        # Evaluation at symbolic point
        @variables θ_A θ_B
        val = eval_multivariate_pgf(pgf, Dict(:A => θ_A, :B => θ_B))
        @test occursin("θ_A", string(val))

        # Independent PGF from univariate Poissons
        pgf_a = poisson_pgf(κ_A; varname = :za)
        pgf_b = poisson_pgf(κ_B; varname = :zb)
        indep = independent_pgf(:A => pgf_a, :B => pgf_b)
        @test length(indep.types) == 2
        @test isequal(mean_degree(indep, :A), κ_A)
    end

    @testset "Multi-type SIR (2 types)" begin
        @parameters β γ κ_AA κ_AB κ_BA κ_BB

        pgf_A = multivariate_poisson_pgf([:A, :B], Dict(:A => κ_AA, :B => κ_AB))
        pgf_B = multivariate_poisson_pgf([:A, :B], Dict(:A => κ_BA, :B => κ_BB))

        progression = DiseaseProgression(
            [DiseaseStage(:I; transmission_rate = β), DiseaseStage(:R; transmission_rate = 0)],
            [DiseaseTransition(:I, :R, γ)];
            entry = :I,
        )

        model = MultiTypeConfigurationModel(
            types = [:A, :B],
            pgfs = Dict(:A => pgf_A, :B => pgf_B),
            progression = progression,
        )
        result = @test_deprecated build_edge_system(model)
        eqs = ModelingToolkit.equations(result.system)

        # Multi-type systems now retain stage-population dynamics explicitly (16 in 0.1, + the
        # §J.8 accumulator).
        @test length(eqs) == 17

        # Check θ variables for all type pairs
        for j in [:A, :B], l in [:A, :B]
            @test haskey(result.variables, Symbol("θ_", j, "_", l))
        end

        # Check φ variables for each stage and type pair
        for stage in [:I, :R], j in [:A, :B], l in [:A, :B]
            @test haskey(result.variables, Symbol("φ_", stage, "_", j, "_", l))
        end

        # Population-level variables per type (fractions of all nodes; no R_<type>/I_<type> aliases)
        @test haskey(result.variables, :pop_R_A) && haskey(result.variables, :pop_R_B)
        @test haskey(result.observables, :S_A) && haskey(result.observables, :S_B)
        @test haskey(result.variables, :pop_I_A) && haskey(result.variables, :pop_I_B)

        # Check cross-type edge hazards and excess hazards
        for j in [:A, :B], l in [:A, :B]
            @test haskey(result.observables, Symbol("edge_hazard_", j, "_", l))
            @test haskey(result.observables, Symbol("excess_hazard_", j, "_", l))
            @test haskey(result.observables, Symbol("φ_S_", j, "_", l))
        end

        # Default initial conditions should set all θ to 1 (17 states and the four seed parameters
        # seed_I_A, seed_I_B, seed_R_A, seed_R_B; 0.1 had 16 states and ρ_A, ρ_B)
        ic = default_initial_conditions(result)
        @test length(ic) == 21
        theta_vars = [v for (k, v) in result.variables if startswith(string(k), "θ")]
        @test all(ic[v] ≈ 1.0 for v in theta_vars)
        # the 0.1 seeding, ε = 10⁻³ of every type (a symbolic mean degree gives equal sizes 1/2)
        @test result.metadata[:network].sizes == [0.5, 0.5]
        @test ic[result.variables[:pop_I_A]] ≈ 0.5e-3
        @test ic[result.variables[:pop_I_B]] ≈ 0.5e-3
    end

    @testset "Multi-type SIR runs (φ-seeding regression)" begin
        # Regression: like the single-type expanded form, the multi-type
        # builder must seed φ_entry from the algebraic relation
        # φ_S = ∂ψ/∂x_l(θ) / ∂ψ/∂x_l(1). Without the seed, all φ_I(0) = 0,
        # all edge hazards vanish, and the epidemic never starts.
        using OrdinaryDiffEqDefault
        pgf_A = multivariate_poisson_pgf([:A, :B], Dict(:A => 4.0, :B => 1.0))
        pgf_B = multivariate_poisson_pgf([:A, :B], Dict(:A => 1.0, :B => 4.0))
        progression = DiseaseProgression(
            [DiseaseStage(:I; transmission_rate = 0.2), DiseaseStage(:R; transmission_rate = 0)],
            [DiseaseTransition(:I, :R, 0.1)]; entry = :I,
        )
        model = MultiTypeConfigurationModel(
            types = [:A, :B], pgfs = Dict(:A => pgf_A, :B => pgf_B),
            progression = progression,
        )
        result = @test_deprecated build_edge_system(model)
        ic = default_initial_conditions(result)
        sol = solve(ODEProblem(result.system, ic, (0.0, 200.0));
                    abstol = 1e-9, reltol = 1e-9)
        @test sol.retcode == ReturnCode.Success
        # With β/γ=2 on degree-5 networks, the epidemic should infect a
        # substantial fraction of each type (within-type fractions: pop/n, n = 1/2 by reciprocity).
        n = Dict(zip(result.metadata[:network].types, result.metadata[:network].sizes))
        @test n[:A] ≈ 0.5 && n[:B] ≈ 0.5
        R_A = sol[result.variables[:pop_R_A]][end] / n[:A]
        R_B = sol[result.variables[:pop_R_B]][end] / n[:B]
        @test R_A > 0.4
        @test R_B > 0.4
    end

    @testset "Multi-type SEIR (3 types)" begin
        @parameters σ β γ
        types = [:Y, :M, :O]

        pgf_Y = multivariate_poisson_pgf(types, Dict(:Y => 5, :M => 2, :O => 1))
        pgf_M = multivariate_poisson_pgf(types, Dict(:Y => 2, :M => 4, :O => 2))
        pgf_O = multivariate_poisson_pgf(types, Dict(:Y => 1, :M => 2, :O => 3))

        progression = DiseaseProgression(
            [DiseaseStage(:E; transmission_rate = 0), DiseaseStage(:I; transmission_rate = β), DiseaseStage(:R; transmission_rate = 0)],
            [DiseaseTransition(:E, :I, σ), DiseaseTransition(:I, :R, γ)];
            entry = :E,
        )

        model = MultiTypeConfigurationModel(
            types = types,
            pgfs = Dict(:Y => pgf_Y, :M => pgf_M, :O => pgf_O),
            progression = progression,
        )
        result = @test_deprecated build_edge_system(model)
        eqs = ModelingToolkit.equations(result.system)

        # 9 θ, 27 φ, 9 pop and the accumulator (0.1: 45 equations; 48 variables with R_Y, R_M, R_O)
        @test length(eqs) == 46
        @test length(result.variables) == 46
    end

    @testset "Multi-type with contact matrix" begin
        @parameters β γ κ

        # Two types, assortative mixing (prefer same type)
        pgf_A = multivariate_poisson_pgf([:A, :B], Dict(:A => κ, :B => κ))
        pgf_B = multivariate_poisson_pgf([:A, :B], Dict(:A => κ, :B => κ))

        progression = DiseaseProgression(
            [DiseaseStage(:I; transmission_rate = β), DiseaseStage(:R; transmission_rate = 0)],
            [DiseaseTransition(:I, :R, γ)];
            entry = :I,
        )

        # Cross-type transmission at half rate
        model = MultiTypeConfigurationModel(
            types = [:A, :B],
            pgfs = Dict(:A => pgf_A, :B => pgf_B),
            progression = progression,
            contact_matrix = Dict((:A, :A) => 1, (:B, :B) => 1, (:A, :B) => Symbolics.Num(1) // 2, (:B, :A) => Symbolics.Num(1) // 2),
        )
        result = @test_deprecated build_edge_system(model)
        eqs = ModelingToolkit.equations(result.system)
        @test length(eqs) == 17                          # 16 in 0.1, + the §J.8 accumulator

        # LEGACY-WEAK[E30, E32]: the halved rate in θ_A_B is implemented correctly but never asserted;
        # contact_matrix is a per-edge rate multiplier indexed (infector, infectee), not a mixing matrix.
        # θ equations for cross-type should have halved β
        eq_strs = [string(eq) for eq in eqs]
        # Verify the system built without error and has the expected structure
        @test haskey(result.variables, :θ_A_B)
        @test haskey(result.variables, :θ_B_A)
    end

    check_area("multitype")

    # WP29 regenerated these goldens: the shim forwards to the multitype lift, whose node-level columns
    # are fractions of all nodes. Rescaled by the type sizes (1/2, from edge reciprocity) every 0.1
    # column is reproduced to the golden tolerance.
    @testset "0.2 reproduces the 0.1 within-type trajectories (WP29)" begin
        half = Dict(:a => 0.5, :b => 0.5)
        for case in load_cases("multitype")
            check_v01(case; columns = within_type_columns(half, occursin("seir", case.name) ? (:E, :I, :R) : (:I, :R)))
        end
    end
end
