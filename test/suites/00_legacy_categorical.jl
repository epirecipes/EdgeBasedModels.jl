# Legacy tests: categorical.
#
# Split from the pre-refactor test/runtests.jl of EdgeBasedModels 0.1 (working tree of 2026-09-26) by
# WP1 of DESIGN_NetworkEpiCore.md. Owner after Phase 0: WP29 (legacy removal); WP18 for mass_action.
#
# WP29 deleted the 0.1 categorical layer (src/categorical.jl). Each 0.1 testset below is kept under its
# name and now checks what design §A.7 makes of its function:
#   - OpenEBCM, open_sir, open_seir, tensor: deprecation shims forwarding to NetworkEpiCore's open models
#     (open_model, disjoint_union) and edge_based; the 0.1 assertions are kept where they still hold, and
#     the numbers are checked against the 0.1 goldens (test/golden/categorical/v01/);
#   - compose, stratify(::OpenEBCM), to_mass_action, EBCMFunctor, verify_functoriality, compare_models and
#     the metadata-only NaturalTransformation: errors whose message names the replacement (verified
#     issues E08, E22, E24), and each testset checks that the named replacement does the 0.1 job. The
#     full tests of the replacements are in deprecations.jl, lift_composition.jl, lift_multitype.jl and
#     reverse.jl.
# The 0.1 annotations LEGACY-WRONG[E08, E30] (to_mass_action, compare_models), LEGACY[E22] (compose) and
# LEGACY[E24] (stratify) are resolved: the wrong values are no longer produced by anything.

using EdgeBasedModels
using NetworkEpiCore
using ModelingToolkit
using Symbolics
using Test

import Catalyst

isdefined(Main, :GoldenTools) || Base.include(Main, joinpath(@__DIR__, "..", "golden", "GoldenTools.jl"))
using Main.GoldenTools

errmsg(f) = try
    f()
    ""
catch e
    sprint(showerror, e)
end

@testset "legacy categorical" begin
    @testset "Categorical composition" begin
        using OrdinaryDiffEqDefault
        TOL = (abstol = 1e-10, reltol = 1e-10)

        # ---- §1 OpenEBCM construction ----
        @testset "OpenEBCM auto-ports SIR" begin
            pgf = poisson_pgf(5.0)
            m = @test_deprecated open_sir(pgf, 0.3, 0.1)

            @test m isa OpenEBCM
            @test m.name == :sir
            # 0.2: the model is NetworkEpiCore's open model (0.1: a StaticConfigurationModel)
            @test m.model isa OpenContactModel && m.network == ConfigurationNetwork(pgf)
            @test isequivalent(contact_model(m.model), sir_model(τ = 0.3, γ = 0.1))

            # SIR → 3 ports: S (susceptible), I (infectious), R (recovered)
            @test length(m.ports) == 3
            types = [p.type for p in m.ports]
            @test :susceptible in types
            @test :infectious in types
            @test :recovered  in types

            names = [p.name for p in m.ports]
            @test :S in names
            @test :I in names
            @test :R in names
        end

        @testset "OpenEBCM auto-ports SEIR" begin
            pgf = poisson_pgf(5.0)
            m = @test_deprecated open_seir(pgf, 0.2, 0.3, 0.1)

            @test m.name == :seir
            @test length(m.ports) == 4
            types = [p.type for p in m.ports]
            @test count(==(:susceptible), types) == 1
            @test count(==(:latent),      types) == 1
            @test count(==(:infectious),  types) == 1
            @test count(==(:recovered),   types) == 1
        end

        # ---- §2 tensor() — independent systems ----
        @testset "tensor product" begin
            pgf_a = poisson_pgf(5.0)
            pgf_b = poisson_pgf(3.0)
            m1 = @test_deprecated open_sir(pgf_a, 0.3, 0.1; name = :pop_a)
            m2 = @test_deprecated open_sir(pgf_b, 0.2, 0.1; name = :pop_b)

            tp = @test_deprecated tensor(m1, m2)
            @test tp isa OpenEBCM
            # All ports from both systems preserved (3 + 3)
            @test length(tp.ports) == 6

            # Build the tensor system (0.1: build_edge_system(tp.model); tp.model is an open model now)
            sys = build_edge_system(tp)
            @test sys isa EdgeModelSystem

            # Should have variables from both subsystems (0.2 names: the partner → node edge
            # variable θ_<b>_<a> of the multitype lift, and the populations pop_<X>_<a>)
            @test haskey(sys.variables, :θ_pop_a_pop_a)
            @test haskey(sys.variables, :θ_pop_b_pop_b)
            @test haskey(sys.variables, :pop_R_pop_a)
            @test haskey(sys.variables, :pop_R_pop_b)
            @test !haskey(sys.variables, :θ_pop_a_pop_b)       # no cross-type edges (block diagonal)

            # Solve and verify independence:
            # each θ should settle to a value determined only by its own network
            ic = default_initial_conditions(sys)
            prob = ODEProblem(sys.system, ic, (0.0, 100.0))
            sol = solve(prob; TOL...)
            @test sol.retcode == ReturnCode.Success

            # Solve standalone models for comparison
            sys_a = build_edge_system(m1)
            ic_a  = default_initial_conditions(sys_a)
            sol_a = solve(ODEProblem(sys_a.system, ic_a, (0.0, 100.0)); TOL...)

            sys_b = build_edge_system(m2)
            ic_b  = default_initial_conditions(sys_b)
            sol_b = solve(ODEProblem(sys_b.system, ic_b, (0.0, 100.0)); TOL...)

            # θ final values must match standalone systems (0.1: atol 1e-6 at tolerance 1e-8)
            θ_a_tensor = sol[sys.variables[:θ_pop_a_pop_a]][end]
            θ_a_solo   = sol_a[sys_a.variables[:θ]][end]
            @test θ_a_tensor ≈ θ_a_solo atol = 1e-8

            θ_b_tensor = sol[sys.variables[:θ_pop_b_pop_b]][end]
            θ_b_solo   = sol_b[sys_b.variables[:θ]][end]
            @test θ_b_tensor ≈ θ_b_solo atol = 1e-8
        end

        # ---- §3 compose() — coupled systems ----
        # 0.1 (verified issue E22): compose built nothing; build_edge_system(::ComposedModel) threw for any
        # wiring. 0.2: an error naming NetworkEpiCore's glue, which does build the coupled model.
        @testset "compose with coupling" begin
            pgf_a = poisson_pgf(5.0)
            pgf_b = poisson_pgf(3.0)
            m1 = @test_deprecated open_sir(pgf_a, 0.3, 0.1; name = :city)
            m2 = @test_deprecated open_sir(pgf_b, 0.2, 0.1; name = :rural)

            @test_throws ErrorException EdgeBasedModels.compose(m1, m2, [:I => :S])
            msg = errmsg(() -> EdgeBasedModels.compose(m1, m2, [:I => :S]))
            @test occursin("glue", msg) && occursin("E22", msg)
            # the replacement composes the syntax and lifts it: SIR with vaccination S → V glued on S
            vax = ContactModel(:vax; transitions = [NodeTransition(:S, :V, 0.05)])
            sirv = glue(sir_model(τ = 0.3, γ = 0.1), vax; on = [:S])
            sys = edge_based(sirv, ConfigurationNetwork(PoissonDegree(5.0)))
            @test haskey(sys.variables, :pop_V)
            sol = solve_epidemic(sys; tspan = (0.0, 100.0), TOL...)
            @test sol.retcode == ReturnCode.Success
            @test compartment(sys, sol, :pop_V)[end] > 0.01
        end

        # ---- §4 stratify() ----
        # 0.1 (verified issue E24): stratify(::OpenEBCM, strata, mixing) replaced the degree law of every
        # stratum by a multivariate Poisson with the base mean. 0.2: an error; the replacement is
        # NetworkEpiCore's stratify on a typed network (golden categorical/stratify_sir_*).
        @testset "stratify" begin
            pgf = poisson_pgf(5.0)
            base = @test_deprecated open_sir(pgf, 0.3, 0.1; name = :base)
            mixing = [0.7 0.3;
                      0.3 0.7]
            @test_throws ErrorException stratify(base, [:young, :old], mixing)
            msg = errmsg(() -> stratify(base, [:young, :old], mixing))
            @test occursin("E24", msg) && occursin("stratify(model, strata(names; sizes))", msg)
            # the replacement: 16 equations as in 0.1, + the §J.8 accumulator
            st = strata([:young, :old])
            net = MultitypeNetwork(st.names, st.sizes,
                                   MultivariateDegree[SplitDegrees(PoissonDegree(5.0), [:young => 0.7, :old => 0.3]),
                                                      SplitDegrees(PoissonDegree(5.0), [:young => 0.3, :old => 0.7])])
            sys = edge_based(stratify(sir_model(τ = 0.3, γ = 0.1), st), net)
            @test length(ModelingToolkit.equations(sys.system)) == 17
            sol = solve_epidemic(sys; initial = SeedFraction(:I_young => 5e-4, :I_old => 5e-4), tspan = (0.0, 100.0), TOL...)
            @test sol.retcode == ReturnCode.Success
        end

        # ---- §5 to_mass_action ----
        # 0.1 (verified issue E08): MA(τ·ψ''(1)/ψ'(1), γ), which is not a reduction of the edge-based model.
        # 0.2: an error naming mass_action(sys; form); Rempała's exact Poisson map has γ_eff = γ + τ.
        @testset "to_mass_action" begin
            prog_num = DiseaseProgression(
                [DiseaseStage(:I; transmission_rate = 0.3),
                 DiseaseStage(:R; transmission_rate = 0)],
                [DiseaseTransition(:I, :R, 0.1)]; entry = :I)
            model = StaticConfigurationModel(poisson_pgf(5.0), prog_num)
            @test_throws ErrorException to_mass_action(model)
            msg = errmsg(() -> to_mass_action(model))
            @test occursin("E08", msg) && occursin("γ + τ", msg) && occursin("mass_action(sys; form)", msg)
            # the replacement: the reaction rates of the Rempała image are β = μτ = 1.5 and γ + τ = 0.4
            img = mass_action(build_edge_system(model); form = :edge)
            @test img isa MassActionImage
            sol = solve_epidemic(build_edge_system(model); tspan = (0.0, 40.0), saveat = 1.0, TOL...)
            @test sol.retcode == ReturnCode.Success
        end

        # ---- §6 EBCMFunctor ----
        # 0.1 (verified issue E22): a wrapper of build_edge_system with a vacuous functoriality check.
        # 0.2: an error; the lift is edge_based(model, net).
        @testset "EBCMFunctor" begin
            @test_throws ErrorException EBCMFunctor(:F)
            @test occursin("edge_based(model, net)", errmsg(() -> EBCMFunctor(:F)))
            m = @test_deprecated open_sir(poisson_pgf(5.0), 0.3, 0.1)
            sys = edge_based(m)                                    # what F(m) returned
            @test haskey(sys.variables, :θ) && haskey(sys.observables, :S)
            sol = solve_epidemic(sys; tspan = (0.0, 100.0), TOL...)
            @test sol.retcode == ReturnCode.Success
            @test 0.0 < compartment(sys, sol, :S)[end] < 1.0
        end

        # ---- §7 verify_functoriality ----
        # 0.1 (LEGACY-WEAK[E30]): compared θ only, and only where functoriality holds by construction.
        # 0.2: an error; the laws are checked with vector_fields_equal on symbolic_ode (H1, H8).
        @testset "verify_functoriality" begin
            m1 = @test_deprecated open_sir(poisson_pgf(5.0), 0.3, 0.1; name = :fa)
            m2 = @test_deprecated open_sir(poisson_pgf(3.0), 0.2, 0.1; name = :fb)
            @test_throws ErrorException verify_functoriality(m1, m2, Pair{Symbol,Symbol}[])
            @test occursin("vector_fields_equal", errmsg(() -> verify_functoriality(m1, m2, Pair{Symbol,Symbol}[])))
            # the tensor case the 0.1 check covered, as the replacement states it: the lift of the tensor
            # product solves each component exactly (law H8)
            tp = @test_deprecated tensor(m1, m2)
            sys = build_edge_system(tp)
            sol = solve_epidemic(sys; tspan = (0.0, 100.0), TOL...)
            sa = build_edge_system(m1)
            sola = solve_epidemic(sa; tspan = (0.0, 100.0), TOL...)
            @test sol[sys.variables[:θ_fa_fa]][end] ≈ sola[sa.variables[:θ]][end] atol = 1e-8
        end

        # ---- §8 compare_models ----
        @testset "compare_models" begin
            model = StaticConfigurationModel(poisson_pgf(5.0), DiseaseProgression(
                [DiseaseStage(:I; transmission_rate = 0.3), DiseaseStage(:R; transmission_rate = 0)],
                [DiseaseTransition(:I, :R, 0.1)]; entry = :I))
            @test_throws ErrorException compare_models(model; tspan = (0.0, 80.0))
            @test occursin("E08", errmsg(() -> compare_models(model; tspan = (0.0, 80.0))))
        end

        # ---- §9 NaturalTransformation metadata ----
        @testset "NaturalTransformation" begin
            @test_throws ErrorException NaturalTransformation(
                :ebcm_to_mass_action,
                StaticConfigurationModel,
                Nothing,
                "EBCM → mass-action; valid when network is Poisson")
            @test NaturalTransformation === NetworkEpiCore.NaturalTransformation
        end
    end

    check_area("categorical")

    # WP29 regenerated these goldens (see test/golden/categorical/cases.jl): the tensor product and the
    # Poisson stratification reproduce every 0.1 column (node-level columns rescaled by the type size 1/2);
    # the bimodal stratification does not (E24), and its replacement is checked against the unstratified
    # bimodal golden instead, which it must equal by symmetry (the strata stay identical).
    @testset "0.2 against the 0.1 numbers (WP29)" begin
        cases = Dict(c.name => c for c in load_cases("categorical"))
        # the 0.1 tensor named its edge variables per component (θ_a, φ_I_a); the multitype lift names them
        # by partner and node type (θ_a_a, φ_I_a_a), the only edges of the block-diagonal network
        tcols = within_type_columns(Dict(:a => 0.5, :b => 0.5), (:I, :R))
        for c in (:a, :b), v in ("θ", "φ_I", "φ_R", "φ_S")
            tcols["$(v)_$c"] = f -> f["$(v)_$(c)_$c"]
        end
        check_v01(cases["tensor_sir_pois5_pois3"]; columns = tcols)
        check_v01(cases["stratify_sir_pois5"]; columns = within_type_columns(Dict(:young => 0.5, :old => 0.5), (:I, :R)))
        new = run_case(cases["stratify_sir_bim"])
        col(r, name) = r.data[:, findfirst(==(name), r.columns)]
        header, legacy = read_golden_csv(joinpath(GOLDEN_DIR, "categorical", V01_DIR, "stratify_sir_bim.csv"))
        bim = run_case(only(c for c in load_cases("core") if c.name == "sir_bim_expanded"))
        for (X, Y) in (("S", "S"), ("pop_I", "pop_I"), ("pop_R", "pop_R"))
            total = X == "S" ? col(new, "S_young") .+ col(new, "S_old") : col(new, "$(X)_young") .+ col(new, "$(X)_old")
            @test compare_columns(total, col(bim, Y)).ok
        end
        # … while the 0.1 numbers (E24) are far from it
        S01 = (legacy[:, findfirst(==("S_young"), header)] .+ legacy[:, findfirst(==("S_old"), header)]) ./ 2
        @test maximum(abs.(S01 .- col(bim, "S"))) > 0.01
    end
end
