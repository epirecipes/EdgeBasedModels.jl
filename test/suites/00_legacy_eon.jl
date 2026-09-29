# Legacy tests: eon (cross-validation against EoN, Kiss-Miller-Simon's Python package).
#
# The first two testsets are the pre-refactor test/test_eon_crossval.jl and test/test_eon_patterns.jl
# of EdgeBasedModels 0.1, moved here by WP1 of DESIGN_NetworkEpiCore.md. Changes: the misplaced `end`
# of test_eon_crossval.jl (which left the SEIR testset outside its parent) is fixed, a wrong comment is
# corrected, and annotations are added. The assertions are unchanged. Owner after Phase 0: WP19
# ("the EoN cross-validation tests are kept"). Annotation tags as in the other 00_legacy files:
#   LEGACY-WEAK[<id>]  the test cannot detect a mismatch of the size of verified issue <id>.
#
# The last testset (added by WP1) is the like-for-like comparison of verified issue E29, against
# references in test/golden/eon/ written by test/golden/eon/generate_eon.py (EoN 1.2rc1).

using EdgeBasedModels
using ModelingToolkit
using OrdinaryDiffEq
using Test

import JSON3
import TOML

const EON_REF = JSON3.read(read(joinpath(@__DIR__, "..", "eon_reference.json"), String))
const EON_GOLDEN_DIR = joinpath(@__DIR__, "..", "golden", "eon")

@testset "legacy eon" begin
    @testset "EoN cross-validation" begin
        # All scenarios use canonical R₀ = 2, γ = 0.25 on Poisson(5) networks.
        # LEGACY-WEAK[E29]: eon_reference.json's ebcm_poisson5 and attack_rate_poisson5 come from ONE
        # Erdős-Rényi graph ER(N = 1000, p = 5/999, seed 42) with excess degree 5.034, not from Poisson(5).
        # The model agrees with EoN to < 1e-6 like for like (last testset); these legacy comparisons pass
        # only because of atol = 5e-3 / rtol = 1e-2.
        ref = EON_REF

        @testset "EBCM SIR on Poisson(5)" begin
            @parameters β γ κ
            pgf = poisson_pgf(κ)
            model = build_sir(pgf, β, γ; form = :compact)
            ic = default_initial_conditions(model; seed_fraction = 0.01)
            prob = ODEProblem(model.system,
                merge(ic, Dict(β => 1/6, γ => 0.25, κ => 5.0)), (0.0, 40.0))
            sol = solve(prob, Tsit5(); saveat = 0.2)
            I_curve = compartment(sol, model, :I)
            R_curve = compartment(sol, model, :R)

            @test isapprox(maximum(I_curve), ref.ebcm_poisson5.peak_I; atol=0.005)
            @test isapprox(R_curve[end], ref.ebcm_poisson5.final_size; atol=0.005)
        end

        @testset "Attack rate (final size) on Poisson(5)" begin
            # LEGACY-WEAK[E29]: compares final_size (ρ → 0, exact Poisson: 0.7968121) with EoN's
            # Attack_rate_cts_time on the ER graph at ρ = 0.01 (0.7987353).
            pgf_num = poisson_pgf(5.0)
            prog = DiseaseProgression(
                [DiseaseStage(:I; transmission_rate=1/6), DiseaseStage(:R)],
                [DiseaseTransition(:I, :R, 0.25)]; entry=:I)
            fs_model = StaticConfigurationModel(pgf_num, prog)
            fs = final_size(fs_model)
            @test isapprox(fs.R_infinity, ref.attack_rate_poisson5.attack_rate; atol=0.005)
        end

        @testset "EBCM SIS with reinfection counting on Poisson(5)" begin
            # WP29: build_sis_reinfection (a pairwise model; SIS has no exact edge-based model, verified
            # issue E01) is removed from EdgeBasedModels. The comparison of its L = 1 endemic prevalence
            # with EoN's compact pairwise model (the reference ref.ebcm_sis_poisson5) belongs to its
            # replacement, NodeBasedModels.node_based(with_reinfection_counting(sis_model(), 1), net).
            @test_throws ErrorException build_sis_reinfection(poisson_pgf(5.0), 1 / 6, 0.25, 1)
            @test occursin("NodeBasedModels.node_based",
                           try build_sis_reinfection(poisson_pgf(5.0), 1 / 6, 0.25, 1); "" catch e; sprint(showerror, e) end)
            @test haskey(ref, :ebcm_sis_poisson5)          # the reference data are kept for the replacement
        end

        # Moved inside "EoN cross-validation": in test_eon_crossval.jl a misplaced `end` left it at top
        # level (verified issue E30). Its seed (0.05) differs from seir_ssa_poisson5's (0.01), so it is
        # compared with the SIR peak only.
        @testset "EBCM SEIR on Poisson(5)" begin
            pgf_num = poisson_pgf(5.0)
            @parameters β_seir γ_seir σ_seir
            prog = DiseaseProgression(
                [DiseaseStage(:E; transmission_rate=0),
                 DiseaseStage(:I; transmission_rate=β_seir),
                 DiseaseStage(:R)],
                [DiseaseTransition(:E, :I, σ_seir),
                 DiseaseTransition(:I, :R, γ_seir)]; entry=:E)
            model = StaticConfigurationModel(pgf_num, prog)
            sys = build_edge_system(model; form=:expanded)
            ic = default_initial_conditions(sys; seed_fraction=0.05)
            sol = solve(ODEProblem(sys.system,
                merge(ic, Dict(β_seir=>1/6, γ_seir=>0.25, σ_seir=>0.5)),
                (0.0, 40.0)), Tsit5())
            I_seir = compartment(sol, sys, :I)
            # SEIR peak should be ~0.15 (lower than SIR ~0.23 due to latent period)
            # and match the EoN Gillespie_simple_contagion SSA
            @test 0.10 < maximum(I_seir) < 0.25
            @test maximum(I_seir) < ref.ebcm_poisson5.peak_I  # SEIR peak < SIR peak
        end
    end

    # Mirrors the test patterns from EoN/tests/test_from_joel.py with actual numeric assertions
    # (EoN's tests are visual-only).
    @testset "EoN-equivalent tests" begin

        @testset "EBCM on Poisson (test_SIR_EBCM)" begin
            # EoN: N=1, gamma=1, tau=1.5, kave=3, rho=0.01
            pgf = poisson_pgf(3.0)
            prog = DiseaseProgression(
                [DiseaseStage(:I; transmission_rate=1.5), DiseaseStage(:R)],
                [DiseaseTransition(:I, :R, 0.25)]; entry=:I)
            model = StaticConfigurationModel(pgf, prog)
            sys = build_edge_system(model; form=:expanded)
            ic = default_initial_conditions(sys; seed_fraction=0.01)
            sol = solve(ODEProblem(sys.system, ic, (0.0, 10.0)), Tsit5())
            I_curve = compartment(sol, sys, :I)
            R_curve = compartment(sol, sys, :R)
            S_curve = compartment(sol, sys, :S)

            # R₀ = T·κ = (1.5/1.75)·3 ≈ 2.571 with γ = 0.25 here (EoN's test uses γ = 1, giving 1.8;
            # the old comment "(1.5/2.5)·3 = 1.8" was wrong for this code, verified issue E30) → epidemic occurs
            @test maximum(I_curve) > 0.05
            # Final size should be > 0 (epidemic)
            @test R_curve[end] > 0.3
            # S + I + R conservation (within ρ tolerance)
            @test all(abs.(S_curve .+ I_curve .+ R_curve .- 1.0) .< 0.02)
        end

        @testset "SIR final size consistency (test_SIR_final_sizes)" begin
            # EoN: configuration model with degrees [3,6,3,6,20], tau=0.2, gamma=1
            pgf = poisson_pgf(5.0)
            prog = DiseaseProgression(
                [DiseaseStage(:I; transmission_rate=0.5), DiseaseStage(:R)],
                [DiseaseTransition(:I, :R, 0.25)]; entry=:I)
            model = StaticConfigurationModel(pgf, prog)

            # Analytic final size
            fs = final_size(model)
            # ODE final size
            sys = build_edge_system(model; form=:expanded)
            ic = default_initial_conditions(sys; seed_fraction=0.01)
            sol = solve(ODEProblem(sys.system, ic, (0.0, 50.0)), Tsit5())
            R_ode = compartment(sol, sys, :R)

            # Analytic and ODE should agree closely
            @test isapprox(fs.R_infinity, R_ode[end]; atol=0.02)
        end

        @testset "SIR compact vs expanded form agreement" begin
            @parameters β γ κ
            pgf = poisson_pgf(κ)

            compact = build_sir(pgf, β, γ; form=:compact)
            expanded = build_sir(pgf, β, γ; form=:expanded)

            ic_c = default_initial_conditions(compact; seed_fraction=0.01)
            ic_e = default_initial_conditions(expanded; seed_fraction=0.01)

            params = Dict(β => 1/6, γ => 0.25, κ => 5.0)
            sol_c = solve(ODEProblem(compact.system, merge(ic_c, params), (0.0, 40.0)), Tsit5())
            sol_e = solve(ODEProblem(expanded.system, merge(ic_e, params), (0.0, 40.0)), Tsit5())

            I_c = compartment(sol_c, compact, :I)
            I_e = compartment(sol_e, expanded, :I)

            # Both forms should give same peak
            @test isapprox(maximum(I_c), maximum(I_e); rtol=0.02)
        end

        @testset "SIS reinfection counting convergence" begin
            # WP29: the convergence in L of the reinfection-counted pairwise SIS model is a property of
            # NodeBasedModels' replacement; build_sis_reinfection is an error for every L.
            for L in 0:2
                @test_throws ErrorException build_sis_reinfection(poisson_pgf(5.0), 1 / 6, 0.25, L)
            end
        end

        @testset "R₀ scaling (test_estimate_SIR_prob_size)" begin
            pgf = poisson_pgf(5.0)
            for (τ, should_epidemic) in [(0.01, false), (0.1, true), (0.5, true)]
                prog = DiseaseProgression(
                    [DiseaseStage(:I; transmission_rate=τ), DiseaseStage(:R)],
                    [DiseaseTransition(:I, :R, 0.25)]; entry=:I)
                model = StaticConfigurationModel(pgf, prog)
                T = τ / (τ + 0.25)
                R0 = T * 5
                fs = final_size(model)
                if should_epidemic
                    @test fs.R_infinity > 0.1
                else
                    @test fs.R_infinity < 0.05
                end
            end
        end

        @testset "SEIR peak lower than SIR (test_SIR_dynamics)" begin
            pgf = poisson_pgf(5.0)
            # SIR
            sys_sir = build_edge_system(StaticConfigurationModel(pgf,
                DiseaseProgression([DiseaseStage(:I; transmission_rate=1/6), DiseaseStage(:R)],
                    [DiseaseTransition(:I, :R, 0.25)]; entry=:I)); form=:expanded)
            ic_sir = default_initial_conditions(sys_sir; seed_fraction=0.05)
            sol_sir = solve(ODEProblem(sys_sir.system, ic_sir, (0.0, 40.0)), Tsit5())
            # SEIR
            sys_seir = build_edge_system(StaticConfigurationModel(pgf,
                DiseaseProgression(
                    [DiseaseStage(:E; transmission_rate=0), DiseaseStage(:I; transmission_rate=1/6), DiseaseStage(:R)],
                    [DiseaseTransition(:E, :I, 0.5), DiseaseTransition(:I, :R, 0.25)]; entry=:E)); form=:expanded)
            ic_seir = default_initial_conditions(sys_seir; seed_fraction=0.05)
            sol_seir = solve(ODEProblem(sys_seir.system, ic_seir, (0.0, 40.0)), Tsit5())

            I_sir = compartment(sol_sir, sys_sir, :I)
            I_seir = compartment(sol_seir, sys_seir, :I)

            # SEIR peak must be lower than SIR (latent period spreads out epidemic)
            @test maximum(I_seir) < maximum(I_sir)
            # But SEIR should still have an epidemic
            @test maximum(I_seir) > 0.05
        end
    end

    # ---- Added by WP1 (not part of the pre-refactor suite) ------------------------------------

    @testset "E29 like-for-like EoN references (same network, same seeding)" begin
        # EoN's EBCM uses ψ̂ = (1-ρ)ψ, φ_S(0) = 1-ρ, θ(0) = 1, R(0) = 0: the same convention as EBM's
        # builders, so on the same degree distribution the two agree to the ODE tolerance. References:
        # test/golden/eon/eon_like_for_like.toml (+ *_curves.csv), from generate_eon.py (EoN 1.2rc1).
        ref = TOML.parsefile(joinpath(EON_GOLDEN_DIR, "eon_like_for_like.toml"))
        setup = ref["setup"]
        τ, γ, ρ = setup["tau"], setup["gamma"], setup["rho"]
        @test τ ≈ 1 / 6 && γ == 0.25 && ρ == 0.01
        prog = DiseaseProgression([DiseaseStage(:I; transmission_rate = τ), DiseaseStage(:R)],
                                  [DiseaseTransition(:I, :R, γ)]; entry = :I)
        networks = (("sir_poisson5", () -> poisson_pgf(5.0)),
                    ("sir_er1000_seed42", () -> polynomial_pgf(Float64.(ref["sir_er1000_seed42"]["pk"]))))
        for (key, pgf_fn) in networks, form in (:compact, :expanded)
            @testset "$key, form = :$form" begin
                m = build_edge_system(StaticConfigurationModel(pgf_fn(), prog); form = form)
                ic = default_initial_conditions(m; seed_fraction = ρ)
                sol = solve(ODEProblem(m.system, ic, (0.0, setup["tmax"])), Tsit5();
                            saveat = 0.2, reltol = 1e-10, abstol = 1e-12)
                S = compartment(sol, m, :S); I = compartment(sol, m, :I); R = compartment(sol, m, :R)
                @test length(sol.t) == setup["tcount"]
                @test maximum(I) ≈ ref[key]["peak_I"] atol = 1e-5
                @test sol.t[argmax(I)] ≈ ref[key]["peak_t"] atol = 1e-9
                @test R[end] ≈ ref[key]["R40"] atol = 1e-5
                @test S[1] ≈ 1 - ρ atol = 1e-12
                @test maximum(abs.(S .+ I .+ R .- 1)) < 1e-8
                lines = readlines(joinpath(EON_GOLDEN_DIR, ref[key]["curves"]))
                @test first(lines) == "t,S,I,R"
                eon = reduce(vcat, [permutedims(parse.(Float64, split(l, ','))) for l in lines[2:end]])
                @test eon[:, 1] ≈ sol.t atol = 1e-12
                @test maximum(abs.(eon[:, 2] .- S)) < 1e-5
                @test maximum(abs.(eon[:, 3] .- I)) < 1e-5
                @test maximum(abs.(eon[:, 4] .- R)) < 1e-5
            end
        end
        # The legacy JSON value is the ER-graph one, and it is NOT the Poisson(5) value (difference 4.8e-4):
        @test ref["sir_er1000_seed42"]["peak_I"] ≈ EON_REF.ebcm_poisson5.peak_I atol = 1e-12
        @test abs(ref["sir_poisson5"]["peak_I"] - ref["sir_er1000_seed42"]["peak_I"]) > 1e-4

        # final_size is the ρ → 0 relation: equal to EoN's Attack_rate_cts_time(exact Poisson, rho = None).
        fs = final_size(StaticConfigurationModel(poisson_pgf(5.0), prog))
        @test fs.R_infinity ≈ ref["attack_rate"]["poisson5_rho_to_0"] atol = 1e-8
        @test ref["attack_rate"]["er1000_seed42_rho_001"] ≈ EON_REF.attack_rate_poisson5.attack_rate atol = 1e-12

        # SIS: the reinfection-counting model (L = 1) and EoN's compact pairwise model are different
        # closures that differ by about 0.07% on the same exact Poisson(5) network (E29). WP29 removed
        # the reinfection-counting model from EdgeBasedModels (build_sis_reinfection is an error; its
        # replacement is NodeBasedModels'), so this comparison belongs to NodeBasedModels' suite; the
        # reference stays in test/golden/eon/eon_like_for_like.toml.
        @test_throws ErrorException build_sis_reinfection(poisson_pgf(5.0), τ, γ, 1)
        @test haskey(ref["sis"], "poisson5_compact_pairwise_I_end")
    end
end
