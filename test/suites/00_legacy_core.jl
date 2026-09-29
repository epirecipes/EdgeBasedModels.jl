# Legacy tests: core.
#
# Split verbatim from the pre-refactor test/runtests.jl of EdgeBasedModels 0.1 (working tree of
# 2026-09-26) by WP1 of DESIGN_NetworkEpiCore.md; only comments were added.
# Owner after Phase 0: WP29 (legacy removal); WP14 moves the NetworkOutbreaks adapter check to adapters_no.jl.
# Annotation tags (grep for them):
#   LEGACY-WRONG[<id>]  the assertion pins a value that VERIFIED_ISSUES.md <id> shows to be wrong;
#   LEGACY-WEAK[<id>]   the test cannot detect the defect <id> (structure only, or a loose reference);
#   LEGACY[<id>]        the code under test has the verified defect <id>; the test itself is neutral.
# They stay until the owning bug-fix work package replaces them (design section G.1).

using EdgeBasedModels
using ModelingToolkit
using Symbolics
using Test

import Catalyst

import TOML

isdefined(Main, :GoldenTools) || Base.include(Main, joinpath(@__DIR__, "..", "golden", "GoldenTools.jl"))
using Main.GoldenTools

@testset "legacy core" begin
    @testset "PGFs" begin
        pgf = polynomial_pgf([0.2, 0.3, 0.5])
        @test isequal(Symbolics.value(mean_degree(pgf)), 1.3)

        @parameters κ
        poisson = poisson_pgf(κ)
        d1 = pgf_derivative(poisson, 1)
        @test string(d1) == string(κ * exp(κ * (poisson.variable - 1)))

        # Second derivative
        d2 = pgf_derivative(poisson, 2)
        @test occursin("κ", string(d2))
    end

    @testset "Disease model factories" begin
        @parameters β σ γ κ

        # WP29: sir_model & co. are NetworkEpiCore's and return a ContactModel (design §A.7); the
        # legacy DiseaseProgression is its converted form, which this testset keeps checking.
        @test sir_model(; τ = β, γ = γ) isa ContactModel
        sir = DiseaseProgression(sir_model(; τ = β, γ = γ))
        @test sir.susceptible == :S
        @test sir.entry == :I
        @test [stage.name for stage in sir.stages] == [:I, :R]
        @test length(sir.transitions) == 1
        @test sir.transitions[1].source == :I
        @test sir.transitions[1].target == :R

        seir = DiseaseProgression(seir_model(; σ = σ, τ = β, γ = γ))
        @test seir.susceptible == :S
        @test seir.entry == :E
        @test [stage.name for stage in seir.stages] == [:E, :I, :R]
        @test length(seir.transitions) == 2
        @test seir.transitions[1].source == :E
        @test seir.transitions[1].target == :I
        @test seir.transitions[2].source == :I
        @test seir.transitions[2].target == :R

        pgf = poisson_pgf(κ)
        built_sir = build_sir(pgf, β, γ; form = :expanded)
        factory_sir = build_edge_system(StaticConfigurationModel(pgf, sir); form = :expanded)
        @test keys(built_sir.variables) == keys(factory_sir.variables)
        @test keys(built_sir.observables) == keys(factory_sir.observables)
        @test length(ModelingToolkit.equations(built_sir.system)) == length(ModelingToolkit.equations(factory_sir.system))

        built_seir = build_seir(pgf, σ, β, γ; form = :expanded)
        factory_seir = build_edge_system(StaticConfigurationModel(pgf, seir); form = :expanded)
        @test keys(built_seir.variables) == keys(factory_seir.variables)
        @test keys(built_seir.observables) == keys(factory_seir.observables)
        @test length(ModelingToolkit.equations(built_seir.system)) == length(ModelingToolkit.equations(factory_seir.system))
    end

    @testset "Expanded SIR builder" begin
        @parameters β γ κ
        model = build_sir(poisson_pgf(κ), β, γ; form = :expanded)
        eqs = ModelingToolkit.equations(model.system)

        @test length(eqs) >= 3
        @test haskey(model.observables, :S)
        @test haskey(model.observables, :I)
        @test haskey(model.observables, :edge_hazard)
        @test haskey(model.observables, :excess_hazard)
        @test haskey(model.variables, :θ)
        @test haskey(model.variables, :R)
    end

    @testset "Expanded SIR runs and matches compact" begin
        # Regression: prior to seeding φ_I from θ via the algebraic relation
        # φ_S = ψ'(θ)/ψ'(1), the expanded-form ICs left φ_I(0) = 0 and the
        # epidemic never started (θ stayed at 1 - ε). Now both forms must
        # agree on the final attack rate within numerical tolerance.
        using OrdinaryDiffEqDefault
        β_v, γ_v, κ_v = 0.10, 0.10, 5.0
        m_exp = build_sir(poisson_pgf(κ_v), β_v, γ_v; form = :expanded)
        m_cmp = build_sir(poisson_pgf(κ_v), β_v, γ_v; form = :compact)
        sol_exp = solve(ODEProblem(m_exp.system,
                                   default_initial_conditions(m_exp),
                                   (0.0, 200.0));
                        abstol = 1e-9, reltol = 1e-9)
        sol_cmp = solve(ODEProblem(m_cmp.system,
                                   default_initial_conditions(m_cmp),
                                   (0.0, 200.0));
                        abstol = 1e-9, reltol = 1e-9)
        R_exp = compartment(m_exp, sol_exp, :R)[end]
        R_cmp = compartment(m_cmp, sol_cmp, :R)[end]
        @test R_exp > 0.5                 # epidemic actually took off
        @test isapprox(R_exp, R_cmp; atol = 5e-3)
    end

    @testset "Expanded SIR seed conservation" begin
        using OrdinaryDiffEqDefault
        # E31: guards the uncommitted S = (1-ρ)ψ(θ) change in _build_expanded (verified correct).
        seed_fraction = 0.02
        model = build_sir(poisson_pgf(5.0), 0.1, 0.1; form = :expanded)
        sol = solve_epidemic(model;
                             tspan = (0.0, 60.0),
                             init = default_initial_conditions(model; seed_fraction),
                             saveat = 1.0,
                             abstol = 1e-9,
                             reltol = 1e-9)
        @test sol.retcode == ReturnCode.Success

        S = compartment(sol, model, :S)
        I = compartment(sol, model, :I)
        R = compartment(sol, model, :R)
        @test S[1] ≈ 1 - seed_fraction atol = 1e-12
        @test I[1] ≈ seed_fraction atol = 1e-12
        @test R[1] ≈ 0.0 atol = 1e-12
        @test all(isapprox.(S .+ I .+ R, 1.0; atol = 1e-8))
    end

    @testset "Compact SIR builder" begin
        @parameters β γ κ
        model = build_sir(poisson_pgf(κ), β, γ; form = :compact)
        eqs = ModelingToolkit.equations(model.system)

        @test length(eqs) == 2
        @test haskey(model.variables, :θ)
        @test haskey(model.variables, :R)
        @test haskey(model.observables, :S)
        @test haskey(model.observables, :I)
    end

    @testset "Convenience wrappers" begin
        model = build_sir(poisson_pgf(5.0), 0.3, 0.1; form = :compact)
        ic = default_initial_conditions(model)
        manual = solve(ODEProblem(model.system, ic, (0.0, 20.0)); abstol = 1e-8, reltol = 1e-8)
        wrapped = solve_epidemic(model; tspan = (0.0, 20.0), init = ic, abstol = 1e-8, reltol = 1e-8)

        S = compartment(wrapped, model, :S)
        I = compartment(wrapped, model, :I)
        bundle = compartments(wrapped, model, [:S, :I, :R])

        @test length(S) == length(wrapped.t)
        @test length(I) == length(wrapped.t)
        @test haskey(bundle, :S)
        @test haskey(bundle, :I)
        @test haskey(bundle, :R)
        @test population_fraction(wrapped, model, :I) == I
        @test_throws ArgumentError compartment(wrapped, model, :X)
        @test isapprox(S[end], manual[model.observables[:S]][end]; atol = 1e-8)
        @test isapprox(I[end], manual[model.observables[:I]][end]; atol = 1e-8)

        ic_seed = default_initial_conditions(model; seed_fraction = 0.02)
        ic_eps = default_initial_conditions(model; ε = 0.02)
        @test ic_seed[model.variables[:θ]] ≈ 1.0
        @test ic_seed[model.variables[:R]] ≈ 0.0
        @test ic_seed == ic_eps
    end

    @testset "generate_* / build_* parity aliases" begin
        # Functional aliases
        @test generate_sir === build_sir
        @test generate_sis === build_sis
        @test generate_seir === build_seir
        # generate_edge_system actually builds (use @parameters to avoid Symbol-arith)
        @parameters β γ
        m1 = build_edge_system(StaticConfigurationModel(poisson_pgf(5.0), sir_model(β = β, γ = γ)))
        m2 = generate_edge_system(StaticConfigurationModel(poisson_pgf(5.0), sir_model(β = β, γ = γ)))
        @test typeof(m1) === typeof(m2)
    end

    @testset "edge_*_model disambiguating aliases" begin
        # 0.2 (design §A.7): the canned models are NetworkEpiCore's (a ContactModel); edge_*_model
        # are depwarn shims that return the legacy DiseaseProgression of the same model.
        for (legacy, canned) in ((edge_sir_model, sir_model), (edge_sis_model, sis_model),
                                 (edge_seir_model, seir_model), (edge_sirs_model, sirs_model))
            prog = @test_deprecated legacy(; β = :τ)
            @test prog isa DiseaseProgression
            @test isequivalent(contact_model(prog), canned())
        end
    end

    if Base.find_package("NetworkOutbreaks") === nothing
        @info "Skipping NetworkOutbreaks integration tests; NetworkOutbreaks is not available"
    else
        @testset "NetworkOutbreaks integration" begin
            import NetworkOutbreaks
            using Graphs
            using StableRNGs
            using Statistics: mean

            # The adapter lives in NetworkOutbreaks' EdgeBasedModels extension until WP16 deletes it;
            # WP14 moves this check to test/suites/adapters_no.jl.
            # Adapter dispatch is provided by the package extension that loads
            # when both NetworkOutbreaks and EdgeBasedModels are present.
            prog = sir_model()                   # a ContactModel since 0.2 (rates τ, γ)
            params = Dict(:τ => 1.5, :γ => 1.0)
            model = NetworkOutbreaks.OutbreakModel(prog, params)
            @test :S in model.compartments
            @test :I in model.compartments
            @test :R in model.compartments
            @test any(t -> t.from == :S && t.to == :I && t.type == :infection,
                      model.transitions)

            # Run a small ensemble on a regular graph and check final size sanity.
            g = random_regular_graph(400, 6; rng = StableRNG(7))
            spec = NetworkOutbreaks.OutbreakSpec(
                model = model,
                network = g,
                initial = NetworkOutbreaks.SeedFraction(:I => 0.05),
                tspan = (0.0, 60.0),
            )
            ens = NetworkOutbreaks.simulate_ensemble(spec; nsims = 8, seed = 123)
            fs = mean(NetworkOutbreaks.final_size(t; recovered = :R) for t in ens.trajectories)
            # LEGACY-WEAK[E31]: only a sanity range; the quantitative SSA baseline is the
            # "E31 static SIR/SEIR EBCM baseline" testset of this file.
            @test 0.10 < fs <= 1.0
        end
    end

    # ---- Added by WP1 (not part of the pre-refactor suite) ------------------------------------

    @testset "Package hygiene (WP1 dependency trim)" begin
        # NodeBasedModels was never imported by src/; Graphs, JSON3 and OrdinaryDiffEq are test-only.
        project = TOML.parsefile(joinpath(pkgdir(EdgeBasedModels), "Project.toml"))
        for name in ("NodeBasedModels", "Graphs", "JSON3", "OrdinaryDiffEq")
            @test !haskey(project["deps"], name)
        end
        for name in ("Graphs", "JSON3", "OrdinaryDiffEq")
            @test haskey(project["extras"], name)
            @test name in project["targets"]["test"]
        end
        @test !haskey(get(project, "sources", Dict{String, Any}()), "NodeBasedModels")
        # Loading EdgeBasedModels (done above) must not load NodeBasedModels.
        @test !any(m -> nameof(m) == :NodeBasedModels, values(Base.loaded_modules))
    end

    @testset "E31 static SIR/SEIR EBCM baseline" begin
        # Verified issue E31 (regression test of the skeptic's corrected fix): the static builders are
        # correct with S = (1-ρ)ψ(θ) in _build_expanded. 6-regular network, τ = 2/3, γ = σ = 1, ρ = 0.01.
        import OrdinaryDiffEq
        ρ = 0.01; β = 2 / 3; γ = 1.0; σ = 1.0
        pgf = polynomial_pgf([0, 0, 0, 0, 0, 0, 1.0])
        e31_solve(m, tmax) = solve_epidemic(m; tspan = (0.0, tmax), solver = OrdinaryDiffEq.Tsit5(),
            init = default_initial_conditions(m; seed_fraction = ρ), saveat = 0.1, abstol = 1e-10, reltol = 1e-10)

        # (1) SEIR expanded: seed mass conservation, seeds in E
        ms = build_seir(pgf, σ, β, γ; form = :expanded)
        ss = e31_solve(ms, 60.0)
        S = compartment(ss, ms, :S); E = compartment(ss, ms, :pop_E)
        I = compartment(ss, ms, :I); R = compartment(ss, ms, :R)
        @test S[1] ≈ 1 - ρ atol = 1e-12
        @test E[1] ≈ ρ atol = 1e-12
        @test all(isapprox.(S .+ E .+ I .+ R, 1.0; atol = 1e-8))
        @test_throws ArgumentError build_seir(pgf, σ, β, γ; form = :compact)

        # (2) SIR compact == expanded for S, I and R
        mc = build_sir(pgf, β, γ; form = :compact)
        me = build_sir(pgf, β, γ; form = :expanded)
        sc = e31_solve(mc, 20.0); se = e31_solve(me, 20.0)
        for X in (:S, :I, :R)
            @test maximum(abs.(compartment(sc, mc, X) .- compartment(se, me, X))) < 1e-8
        end

        # (3) Miller (2014) eqs (3)-(4): θ∞ = 1 - T + T(1-ρ)ψ'(θ∞)/ψ'(1), R∞ = 1 - (1-ρ)ψ(θ∞)
        T = β / (β + γ); θ = 0.5
        for _ in 1:10_000
            θ = 1 - T + T * (1 - ρ) * θ^5
        end
        Rinf = 1 - (1 - ρ) * θ^6
        @test e31_solve(me, 200.0)[me.variables[:R]][end] ≈ Rinf atol = 1e-6
        @test R[end] ≈ Rinf atol = 1e-5                     # SEIR, same T

        # (4) SSA baseline on a 6-regular configuration graph (N = 2e4, 200 seeds)
        if Base.find_package("NetworkOutbreaks") === nothing
            @info "Skipping the E31 SSA baseline; NetworkOutbreaks is not available"
        else
            import NetworkOutbreaks
            import Graphs
            import StableRNGs
            N = 20_000
            tg = collect(0.0:0.1:20.0)
            g = Graphs.random_regular_graph(N, 6; rng = StableRNGs.StableRNG(2026))
            model = NetworkOutbreaks.OutbreakModel([:S, :I, :R], [false, true, false],
                [NetworkOutbreaks.OutbreakTransition(:S, :I, β, :infection),
                 NetworkOutbreaks.OutbreakTransition(:I, :R, γ, :spontaneous)])
            spec = NetworkOutbreaks.OutbreakSpec(model = model, network = g,
                initial = NetworkOutbreaks.SeedFraction(:I => ρ), tspan = (0.0, 20.0))
            ens = NetworkOutbreaks.simulate_ensemble(spec; nsims = 20, seed = 31,
                algorithm = NetworkOutbreaks.NextReaction())
            _, Isim = NetworkOutbreaks.mean_curve(ens, :I; tgrid = tg)
            _, Ssim = NetworkOutbreaks.mean_curve(ens, :S; tgrid = tg)
            Iebm = compartment(se, me, :I); Sebm = compartment(se, me, :S)
            @test maximum(abs.(Isim ./ N .- Iebm)) < 0.01
            @test maximum(abs.(Ssim ./ N .- Sebm)) < 0.015
            @test abs((1 - Ssim[end] / N) - (1 - Sebm[end])) < 0.005
        end
    end

    @testset "golden harness" begin
        # The comparison must detect a 1e-6 relative perturbation and accept a round trip exactly.
        x = [1.0, 0.5, 1e-3, 0.0]
        @test compare_columns(x, copy(x)).ok
        @test !compare_columns(x .* (1 + 1e-6), x).ok
        @test !compare_columns([1.0, NaN], [1.0, 1.0]).ok
        @test compare_columns([1.0, NaN], [1.0, NaN]).ok
        @test compare_columns([1e-13], [0.0]).ok              # below the absolute floor
        @test !compare_columns([1e-11], [0.0]).ok
        # Infinities match only the same infinity (Inf/Inf would otherwise be a NaN scaled error
        # that no comparison flags, so a finite golden turning into Inf would pass).
        @test !compare_columns([Inf], [1.0]).ok
        @test !compare_columns([1.0], [-Inf]).ok
        @test !compare_columns([-Inf, 0.5], [0.3, 0.5]).ok
        @test !compare_columns([Inf], [-Inf]).ok
        @test compare_columns([Inf], [Inf]).ok
        @test compare_columns([-Inf, 0.5], [-Inf, 0.5]).ok
        let c = compare_columns([0.5, Inf], [0.5, 1.0])
            @test !c.ok && c.worst == 2 && c.maxabs == Inf
        end
        @test compare_columns([0.0], [0.0]; atol = 0.0).ok      # exact zero with no absolute floor
        @test !compare_columns([1e-300], [0.0]; atol = 0.0).ok
        # Later work packages may add areas (design G.1), so only require the Phase 0 ones.
        @test issubset(["analysis", "categorical", "clustered", "core", "dynamic", "multiplex",
                        "multitype", "seir_multistage"], golden_areas())
        @test join_notes("a", "", "b") == "a b"
        @test join_notes("", "") == ""
        mktempdir() do dir
            case = GoldenCase("scratch", "roundtrip"; description = "round trip",
                run = () -> GoldenResult(Dict{String, Any}("a" => 1 / 3), [0.0, 1.0], ["x", "θ"],
                                         [0.1+0.2 1/3; 2/3 π], Dict{String, Any}("names" => ["b", "a"]),
                                         Dict("s" => exp(1.0))))
            write_golden(case, run_case(case); dir = dir)
            header, data = read_golden_csv(golden_paths(case; dir = dir)[2])
            @test header == ["t", "x", "θ"]
            @test data == [0.0 0.1+0.2 1/3; 1.0 2/3 π]    # bit-for-bit
            meta = TOML.parsefile(golden_paths(case; dir = dir)[1])
            @test meta["scalars"]["s"] === exp(1.0)
            @test meta["setup"]["a"] === 1 / 3
            @test meta["check"]["rtol"] == CHECK_RTOL
            # A metadata-only update rewrites description/issues/notes and nothing else; the case
            # must not run (it would throw here).
            toml_path, csv_path = golden_paths(case; dir = dir)
            csv_before = read(csv_path, String)
            annotated = GoldenCase("scratch", "roundtrip"; description = "round trip, annotated",
                                   issues = ["E99"], notes = "a note", run = () -> error("must not run"))
            @test update_golden_metadata(annotated; dir = dir)
            @test !update_golden_metadata(annotated; dir = dir)            # already up to date
            meta2 = TOML.parsefile(toml_path)
            @test meta2["issues"] == ["E99"] && meta2["notes"] == "a note"
            @test meta2["description"] == "round trip, annotated"
            for k in setdiff(union(keys(meta), keys(meta2)), GOLDEN_METADATA_KEYS)
                @test get(meta2, k, missing) == get(meta, k, missing)
            end
            @test read(csv_path, String) == csv_before
            @test_throws ArgumentError update_golden_metadata(
                GoldenCase("scratch", "absent"; description = "", run = () -> nothing); dir = dir)
            @test_throws ArgumentError update_golden_metadata(
                GoldenCase("scratch", "roundtrip"; kind = :scalars, description = "", run = () -> nothing); dir = dir)
        end
    end

    # The harness helpers live in test/runtests.jl, so they exist only when run through it.
    if isdefined(Main, :suite_matches) && isdefined(Main, :selected_suites)
        @testset "suite selection" begin
            @test Main.suite_matches("sis", "00_legacy_sis.jl")
            @test !Main.suite_matches("sis", "00_legacy_analysis.jl")       # whole words only
            @test Main.suite_matches("legacy_core", "00_legacy_core.jl")
            @test !Main.suite_matches("legacy_core", "00_legacy_catalyst.jl")
            @test Main.suite_matches("00_legacy_eon.jl", "00_legacy_eon.jl")
            @test Main.suite_matches("seir_multistage", "00_legacy_seir_multistage.jl")
            @test !Main.suite_matches("multistage_seir", "00_legacy_seir_multistage.jl")
            @test !Main.suite_matches("", "00_legacy_core.jl")
            legacy = Main.selected_suites(["legacy"])
            @test all(f -> startswith(f, "00_legacy_"), legacy) && "00_legacy_core.jl" in legacy
            sis = Main.selected_suites(["sis"])
            @test "00_legacy_sis.jl" in sis && !("00_legacy_analysis.jl" in sis)
            @test_throws ErrorException Main.selected_suites(["sis", "no_such_suite_name"])
        end
    end

    check_area("core")

    # WP29 regenerated the core goldens for new names only (E26_FIXED_NOTE in GoldenTools): every 0.1
    # column of every case is reproduced to the golden tolerance by the per-reaction assembler.
    @testset "0.2 reproduces the 0.1 numbers (WP29)" begin
        for case in load_cases("core")
            case.kind === :trajectory && check_v01(case)
        end
    end
end
