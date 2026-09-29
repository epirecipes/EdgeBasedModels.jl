# Deprecations and migration errors of EdgeBasedModels 0.2 (WP14, DESIGN_NetworkEpiCore.md §A.7).
#
# Owner: WP14 (WP29 extends it when it retires the legacy layer). Every shim has a
# `@test_deprecated` and every removed function a `@test_throws` with its migration message. The
# errors that replace wrong numbers carry a check of the claim their message makes: Rempała's
# exact Poisson reduction for to_mass_action (E08), the SIS admissibility report for build_sis
# (E01).

using EdgeBasedModels
using NetworkEpiCore
using ModelingToolkit
using Symbolics
using Test
using OrdinaryDiffEq: ODEProblem, solve, Vern9
import Catalyst

const EBM = EdgeBasedModels
const TOL = (reltol = 1e-10, abstol = 1e-12)

errmsg(f) = try
    f()
    ""
catch e
    sprint(showerror, e)
end

@testset "deprecations and migration errors" begin
    @testset "build_sis / generate_sis / SIS via build_edge_system (E01)" begin
        pgf = poisson_pgf(5.0)
        @test generate_sis === build_sis
        @test_throws ErrorException build_sis(pgf, 0.4, 1.0)
        @test_throws ErrorException generate_sis(pgf, 0.4, 1.0)
        msg = errmsg(() -> build_sis(pgf, 0.4, 1.0))
        @test occursin("SIR dynamics relabelled", msg) && occursin("ebm-core #1", msg)
        @test occursin("NodeBasedModels.node_based(sis_model(), net)", msg)
        @test occursin("NetworkOutbreaks.simulate", msg)
        # the legacy entry point keeps its ArgumentError, with the same text
        @test_throws ArgumentError build_edge_system(StaticConfigurationModel(pgf, sis_model(τ = 0.4, γ = 1.0)))
        @test errmsg(() -> build_edge_system(StaticConfigurationModel(pgf, sis_model(τ = 0.4, γ = 1.0)))) ==
              errmsg(() -> throw(ArgumentError(EBM._SIS_MESSAGE)))
        @parameters κ
        @test_throws ArgumentError build_edge_system(StaticConfigurationModel(poisson_pgf(κ), sis_model()))
        @test_throws ArgumentError build_edge_system(StaticConfigurationModel(pgf, sis_model()); form = :bogus)
        # the low-level verb refuses SIS and SIRS with the admissibility report (§B.7)
        err = try
            edge_based(sis_model(), ConfigurationNetwork(RegularDegree(3)))
        catch e
            e
        end
        @test err isa AdmissibilityError
        report = sprint(showerror, err)
        @test occursin("`γ, I --> S` (type resus: node → sus) produces the susceptible species S", report)
        @test occursin("node_based", report) && occursin("simulate", report)
        @test_throws ArgumentError build_edge_system(StaticConfigurationModel(pgf, sirs_model(τ = 0.4, γ = 1.0, ε = 0.1)))
    end

    @testset "build_sis_reinfection: removed, a migration error (a pairwise model; NodeBasedModels)" begin
        # WP14 kept a depwarn shim while the legacy suites still called it; WP29 deleted
        # src/reinfection_counting.jl, and the function is the error design §A.7 asks for.
        pgf = poisson_pgf(5.0)
        for L in (0, 1, 2)
            @test_throws ErrorException build_sis_reinfection(pgf, 1 / 6, 1 / 4, L)
        end
        msg = errmsg(() -> build_sis_reinfection(pgf, 1 / 6, 1 / 4, 1))
        @test occursin("pairwise model", msg) && occursin("E01", msg)
        @test occursin("NodeBasedModels.node_based(with_reinfection_counting(sis_model(; τ, γ), L)", msg)
        @test occursin("SeedFraction(:I_1 => ρ)", msg) && occursin("SeedFraction(:I_0 => ρ)", msg)
        @test occursin("NetworkOutbreaks.simulate", msg)
        # The replacement the message names reproduces the removed model: NodeBasedModels'
        # node_based(with_reinfection_counting(sis_model(τ = 1/6, γ = 1/4), L), Poisson(5)) seeded with
        # SeedFraction(:I_1 => 0.01) (:I_0 for L = 0) gives I(30), I(120) equal to the 0.1 values
        # 0.654740646584, 0.654792120088 (L = 0), 0.651163545213, 0.652776967610 (L = 1) and
        # 0.648061133351, 0.651812907502 (L = 2), which WP14 checked against the 0.1 implementation
        # to 1e-10 before the 0.1 code was deleted. NodeBasedModels is deliberately not a test
        # dependency of EdgeBasedModels (00_legacy_core.jl checks that EdgeBasedModels never loads it),
        # so these values are pinned for NodeBasedModels' own suite to reproduce.
        # the 0.1 structural lift of legacy types is gone too (NetworkEpiCore's lift is on ContactModels)
        @test_throws ErrorException with_reinfection_counting(DiseaseProgression(sir_model()), 2)
        @test_throws ErrorException with_reinfection_counting(StaticConfigurationModel(pgf, sir_model()), 2)
        @test occursin("contact_model(prog)",
                       errmsg(() -> with_reinfection_counting(DiseaseProgression(sir_model()), 2)))
        @test with_reinfection_counting(sis_model(), 2) isa ContactModel
    end

    @testset "to_mass_action / compare_models (E08)" begin
        pgf = poisson_pgf(5.0)
        model = StaticConfigurationModel(pgf, sir_model(τ = 1 / 6, γ = 1 / 4))
        @test_throws ErrorException to_mass_action(model)
        @test_throws ErrorException compare_models(model; tspan = (0.0, 40.0))
        msg = errmsg(() -> to_mass_action(model))
        @test occursin("γ + τ", msg) && occursin("Rempała", msg) && occursin("φ_I", msg)
        for form in (":exact", ":edge", ":general", ":limit", ":calibrated")
            @test occursin(form, msg)
        end
        # The claim of the message, checked independently: on Poisson(5), MA(β = 5τ, γ + τ) started at
        # (S, I) = (1 − ρ, ρ) reproduces the edge-based S(t) (Rempała 2023, Thm 1), while the old map
        # MA(5τ, γ) does not (max|ΔS| = 0.28 in verified issue E08).
        τ, γ, ρ = 1 / 6, 1 / 4, 1e-3
        sys = build_sir(pgf, τ, γ)
        sol = solve_epidemic(sys; init = default_initial_conditions(sys; seed_fraction = ρ),
                             tspan = (0.0, 40.0), saveat = 0.5, TOL...)
        S_eb = compartment(sys, sol, :S)
        ma(β, g) = solve(ODEProblem((u, _, _) -> [-β * u[1] * u[2], β * u[1] * u[2] - g * u[2]],
                                    [1 - ρ, ρ], (0.0, 40.0)), Vern9(); saveat = 0.5, TOL...)
        exact = ma(5τ, γ + τ)
        old = ma(5τ, γ)
        @test maximum(abs.(S_eb .- first.(exact.u))) < 1e-8
        @test maximum(abs.(S_eb .- first.(old.u))) > 0.2
        # … and its I is the edge variable φ_I, not the prevalence
        @test maximum(abs.(compartment(sys, sol, :φ_I) .- last.(exact.u))) < 1e-8
        @test maximum(abs.(compartment(sys, sol, :I) .- last.(exact.u))) > 0.05
    end

    @testset "compose / verify_functoriality / EBCMFunctor (E22)" begin
        @test !(:compose in names(EdgeBasedModels))
        city = @test_deprecated open_sir(poisson_pgf(5.0), 0.3, 0.1; name = :city)
        rural = @test_deprecated open_sir(poisson_pgf(3.0), 0.2, 0.1; name = :rural)
        @test_throws ErrorException EdgeBasedModels.compose(city, rural, [:I => :S])
        @test_throws ErrorException EdgeBasedModels.compose(city, rural, Pair{Symbol,Symbol}[])
        @test occursin("glue", errmsg(() -> EdgeBasedModels.compose(city, rural, [:I => :S])))
        @test occursin("E22", errmsg(() -> EdgeBasedModels.compose(city, rural, [:I => :S])))
        # a wired composite used to be reported functorial vacuously (is_functorial = true, max_diff = 0)
        @test_throws ErrorException verify_functoriality(city, rural, [:I => :S])
        @test_throws ErrorException verify_functoriality(city, rural, Pair{Symbol,Symbol}[])
        @test_throws ErrorException EBCMFunctor(:F)
        @test occursin("check_naturality", errmsg(() -> verify_functoriality(city, rural, [:I => :S])))
    end

    @testset "stratify(::OpenEBCM) (E24)" begin
        reg5 = polynomial_pgf([0, 0, 0, 0, 0, 1.0])
        base = @test_deprecated open_sir(reg5, 0.3, 0.2; name = :base)
        # K = 1 used to replace the 5-regular base by Poisson(5): final size 0.9406 instead of 0.9872
        @test_throws ErrorException stratify(base, [:a], fill(1.0, 1, 1))
        @test_throws ErrorException stratify(base, [:young, :old], [0.7 0.3; 0.3 0.7])
        msg = errmsg(() -> stratify(base, [:a], fill(1.0, 1, 1)))
        @test occursin("E24", msg) && occursin("sbm_network", msg) && occursin("unstructured", msg)
        # the replacement is the multitype lift of the stratified model; with one stratum it is the
        # untyped lift (M10), so it keeps the 5-regular final size the legacy map lost
        st = strata([:a, :b]; sizes = [0.5, 0.5])
        @test is_admissible(stratify(sir_model(), st), :edge_based;
                            network = unstructured(ConfigurationNetwork(RegularDegree(5)), st))
        s1 = edge_based(stratify(sir_model(τ = 0.3, γ = 0.2), strata([:a])),
                        unstructured(ConfigurationNetwork(RegularDegree(5)), strata([:a])))
        s0 = build_sir(reg5, 0.3, 0.2)
        R(sys) = compartment(sys, solve_epidemic(sys; tspan = (0.0, 400.0), TOL...), :cumulative)[end]
        @test R(s1) ≈ R(s0) rtol = 1e-8
        @test R(s0) > 0.98                                   # not the Poisson(5) value 0.9406
    end

    @testset "open_sir / open_seir / tensor / OpenEBCM (depwarn shims forwarding to NetworkEpiCore)" begin
        m1 = @test_deprecated open_sir(poisson_pgf(5.0), 1 / 6, 1 / 4; name = :a)
        m2 = @test_deprecated open_sir(poisson_pgf(3.0), 0.3, 1 / 4; name = :b)
        # the replacement objects: an open ContactModel and its network
        @test m1 isa OpenEBCM && m1.model isa OpenContactModel && m1.network isa ConfigurationNetwork
        @test isequivalent(contact_model(m1.model), sir_model(τ = 1 / 6, γ = 1 / 4))
        @test [p.name for p in m1.ports] == [:S, :I, :R] && all(p -> p isa Port, m1.ports)
        @test [p.type for p in m1.ports] == [:susceptible, :infectious, :recovered]
        # lowering an open model is edge_based of the forwarded objects
        s1 = edge_based(m1)
        ref = build_sir(poisson_pgf(5.0), 1 / 6, 1 / 4)
        sol1 = solve_epidemic(s1; tspan = (0.0, 60.0), saveat = 1.0, TOL...)
        solr = solve_epidemic(ref; tspan = (0.0, 60.0), saveat = 1.0, TOL...)
        @test compartment(s1, sol1, :S) ≈ compartment(ref, solr, :S) rtol = 1e-12
        @test build_edge_system(m1) isa EdgeModelSystem
        # tensor: disjoint_union on the block-diagonal MultitypeNetwork (law H8)
        tp = @test_deprecated tensor(m1, m2)
        @test tp isa OpenEBCM && length(tp.ports) == 6
        @test tp.network isa MultitypeNetwork && tp.network.types == [:a, :b] && tp.network.sizes == [0.5, 0.5]
        @test isequivalent(contact_model(tp.model),
                           contact_model(disjoint_union(:a => sir_model(τ = 1 / 6, γ = 1 / 4),
                                                        :b => sir_model(τ = 0.3, γ = 1 / 4))))
        sys = build_edge_system(tp)
        @test haskey(sys.variables, :pop_I_a) && haskey(sys.variables, :pop_I_b)
        # the 0.1 seeding (ρ in each component) and, per component, the component's own model:
        # the within-component fractions are those of the single-network lifts
        ic = default_initial_conditions(sys; seed_fraction = 0.01)
        sol = solve_epidemic(sys; init = ic, tspan = (0.0, 60.0), saveat = 1.0, TOL...)
        refb = build_sir(poisson_pgf(3.0), 0.3, 1 / 4)
        solb = solve_epidemic(refb; init = default_initial_conditions(refb; seed_fraction = 0.01),
                              tspan = (0.0, 60.0), saveat = 1.0, TOL...)
        refa = solve_epidemic(ref; init = default_initial_conditions(ref; seed_fraction = 0.01), tspan = (0.0, 60.0),
                              saveat = 1.0, TOL...)
        @test compartment(sys, sol, :S_a) ./ 0.5 ≈ compartment(ref, refa, :S) rtol = 1e-9
        @test compartment(sys, sol, :pop_I_b) ./ 0.5 ≈ compartment(refb, solb, :pop_I) rtol = 1e-8
        # the component names must differ (they used to collide inside ModelingToolkit)
        @test_throws ArgumentError tensor(m1, m1)
        # a tensor product of a tensor product: compose ContactModels directly
        @test_throws ArgumentError tensor(tp, m1)
        # SEIR components are allowed now: the 0.1 observable that counted latent stages as
        # infectious (E23) is gone with the 0.1 implementation
        e = @test_deprecated open_seir(poisson_pgf(5.0), 0.5, 0.3, 0.2; name = :e)
        @test isequivalent(contact_model(e.model), seir_model(τ = 0.3, σ = 0.5, γ = 0.2))
        @test [p.type for p in e.ports] == [:susceptible, :latent, :infectious, :recovered]
        te = @test_deprecated tensor(e, m2)
        syse = build_edge_system(te)
        sole = solve_epidemic(syse; tspan = (0.0, 10.0), saveat = 1.0, TOL...)
        @test all(compartment(syse, sole, :pop_E_e) .>= 0)
        @test compartment(syse, sole, :pop_E_e)[1] ≈ 0.5e-3 atol = 1e-15   # ρ = 10⁻³ of component e
    end

    @testset "edge_*_model return the legacy type" begin
        p = @test_deprecated edge_sir_model(β = 0.3, γ = 0.1)
        @test p isa DiseaseProgression && p.entry === :I && p.stages[1].transmission_rate == 0.3
        @test (@test_deprecated edge_sir_model()).stages[1].transmission_rate === :β
        s = @test_deprecated edge_seir_model(σ = 0.5)
        @test s isa DiseaseProgression && s.entry === :E && s.transitions[1].rate == 0.5
        q = @test_deprecated edge_sis_model()
        @test q.transitions[1].target === :S
        r = @test_deprecated edge_sirs_model(ε = 0.2)
        @test r.transitions[2].rate == 0.2
        # the canned models are NetworkEpiCore's; β is its deprecated alias of τ
        cm = @test_deprecated sir_model(β = 0.3, γ = 0.1)
        @test isequivalent(cm, sir_model(τ = 0.3, γ = 0.1))
        @test isequivalent(contact_model(p), cm)
    end

    @testset "progression_from_catalyst → contact_model" begin
        rn = Catalyst.@reaction_network begin
            β, S + I --> 2I
            γ, I --> R
        end
        prog = @test_deprecated progression_from_catalyst(rn; susceptible = :S, entry = :I)
        @test prog isa DiseaseProgression && prog.entry === :I
        rate = prog.stages[findfirst(s -> s.name === :I, prog.stages)].transmission_rate
        @test !(rate isa Number) && :β in nameof.(Symbolics.get_variables(rate))
        @test isequivalent(contact_model(prog), contact_model(rn))
        # Regression (WP14 review): the network's parameter defaults stay attached to the rates,
        # so the legacy model solves without p, as 0.1's did (its rates were Catalyst's own
        # parameters), and an explicit p still overrides them
        rnd0 = Catalyst.@reaction_network begin
            @parameters τ = 0.3 γ = 0.1
            τ, S + I --> 2I
            γ, I --> R
        end
        pdef = @test_deprecated progression_from_catalyst(rnd0)
        sdef = build_edge_system(StaticConfigurationModel(poisson_pgf(5.0), pdef))
        R30(sys; kw...) = compartment(sys, solve_epidemic(sys; tspan = (0.0, 30.0), saveat = 1.0, TOL..., kw...), :R)[end]
        @test parameter_defaults(sdef) == Dict(:τ => 0.3, :γ => 0.1)
        @test R30(sdef) ≈ R30(build_sir(poisson_pgf(5.0), 0.3, 0.1)) rtol = 1e-9          # 0.88057919
        @test R30(sdef; p = Dict(:τ => 1 / 6, :γ => 1 / 4)) ≈ R30(build_sir(poisson_pgf(5.0), 1 / 6, 1 / 4)) rtol = 1e-9
        sol0 = solve(ODEProblem(sdef.system, default_initial_conditions(sdef), (0.0, 30.0)), Vern9(); saveat = 1.0, TOL...)
        @test compartment(sdef, sol0, :R)[end] ≈ R30(sdef) rtol = 1e-9
        # transmission_rates: a non-zero entry overrides the rate the reactions give (as in 0.1)
        pov = @test_deprecated progression_from_catalyst(rnd0; transmission_rates = Dict(:I => 0.5))
        @test pov.stages[findfirst(s -> s.name === :I, pov.stages)].transmission_rate == 0.5
        rn1 = Catalyst.@reaction_network begin
            γ, I --> R
        end
        prog1 = @test_deprecated progression_from_catalyst(rn1; transmission_rates = Dict(:I => 1, :R => 0))
        @test prog1.entry === :I && [s.name for s in prog1.stages] == [:I, :R]
        @test prog1.stages[1].transmission_rate == 1
        # branching at infection was dropped silently; now it is an error
        rnb = Catalyst.@reaction_network begin
            τ1, S + I --> E1 + I
            τ2, S + I --> E2 + I
            σ, E1 --> I
            σ, E2 --> R
            γ, I --> R
        end
        @test_throws ArgumentError progression_from_catalyst(rnb)
        rn_bad = Catalyst.@reaction_network begin
            β, I + R --> 2I
        end
        @test_throws ArgumentError progression_from_catalyst(rn_bad; susceptible = :S, entry = :I)
        # an entry keyword that disagrees with the network is overridden, with a warning
        rne = Catalyst.@reaction_network begin
            β, S + I --> E + I
            σ, E --> I
            γ, I --> R
        end
        pe = @test_logs (:warn, r"disagrees with the reaction network") match_mode = :any begin
            progression_from_catalyst(rne; entry = :I)
        end
        @test pe.entry === :E
        # duplicate reactions: 0.1 added their rates, and so does the shim (NetworkEpiCore's
        # contact_model refuses them unless merge_duplicates = true)
        rnd = Catalyst.@reaction_network begin
            β1, S + I --> 2I
            β2, S + I --> 2I
            γ1, I --> R
            γ2, I --> R
        end
        pd = @test_deprecated progression_from_catalyst(rnd)
        τd = pd.stages[findfirst(s -> s.name === :I, pd.stages)].transmission_rate
        @test Set(nameof.(Symbolics.get_variables(τd))) == Set([:β1, :β2])
        @test length(pd.transitions) == 1
        @test Set(nameof.(Symbolics.get_variables(pd.transitions[1].rate))) == Set([:γ1, :γ2])
        # the same epidemic as the model with the summed rates (τ = 0.1 + 0.2, γ = 0.05 + 0.07)
        vals = Dict(:β1 => 0.1, :β2 => 0.2, :γ1 => 0.05, :γ2 => 0.07)
        sd = build_edge_system(StaticConfigurationModel(poisson_pgf(5.0), pd))
        sold = solve_epidemic(sd; p = vals, tspan = (0.0, 40.0), saveat = 1.0, TOL...)
        s1 = build_sir(poisson_pgf(5.0), 0.3, 0.12)
        sol1 = solve_epidemic(s1; tspan = (0.0, 40.0), saveat = 1.0, TOL...)
        @test maximum(abs.(compartment(sd, sold, :S) .- compartment(s1, sol1, :S))) < 1e-10
        @test_throws ArgumentError progression_from_catalyst(rnd; merge_duplicates = false)
    end

    @testset "compartment(sol, sys, X): the legacy argument order" begin
        sys = build_sir(poisson_pgf(5.0), 0.3, 0.1)
        sol = solve_epidemic(sys; tspan = (0.0, 10.0), saveat = 1.0)
        @test (@test_deprecated compartment(sol, sys, :S)) == compartment(sys, sol, :S)
        @test (@test_deprecated compartments(sol, sys, [:S, :I])) == compartments(sys, sol, [:S, :I])
        @test (@test_deprecated population_fraction(sol, sys, :R)) == population_fraction(sys, sol, :R)
        @test_throws ArgumentError compartment(sys, sol, :nonexistent)
    end

    @testset "NaturalTransformation is NetworkEpiCore's" begin
        @test EdgeBasedModels.NaturalTransformation === NetworkEpiCore.NaturalTransformation
        # the legacy metadata-only constructor NaturalTransformation(name, source::Type, target::Type,
        # description) is an error with a migration message (its replacement is Semiconjugacy/verify)
        for src in (StaticConfigurationModel, ClusteredConfigurationModel, DynamicConfigurationModel,
                    MultiTypeConfigurationModel)
            @test_throws ErrorException NaturalTransformation(:ebcm_to_mass_action, src, Nothing, "legacy")
        end
        msg = errmsg(() -> NaturalTransformation(:ebcm_to_mass_action, StaticConfigurationModel, Nothing,
                                                 "EBCM → mass-action; valid when network is Poisson"))
        @test occursin("E08", msg) && occursin("Semiconjugacy", msg) && occursin("verify", msg) &&
              occursin("mass_action(sys; form)", msg)
        # NetworkEpiCore's constructors are untouched
        η = NaturalTransformation(:probe; source = :edge_based, target = :mass_action,
                                  applies = (cm, net) -> true, component = (cm, net) -> nothing)
        @test η isa NetworkEpiCore.NaturalTransformation && η.source === :edge_based
    end
end
