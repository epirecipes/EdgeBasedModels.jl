"""
EoN-equivalent test suite for EdgeBasedModels.jl

Mirrors the test patterns from EoN/tests/test_from_joel.py with
actual numeric assertions (EoN's tests are visual-only).
"""

using Test
using EdgeBasedModels
using ModelingToolkit
using OrdinaryDiffEq

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

        # R₀ = T·κ = (1.5/2.5)·3 = 1.8 → epidemic occurs
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
        # L=0,1,2 should converge; L=0 should match compact pairwise
        pgf = poisson_pgf(5.0)
        @parameters β γ
        results = Float64[]
        for L in 0:2
            sys = build_sis_reinfection(pgf, β, γ, L)
            ic = default_initial_conditions(sys; seed_fraction=0.01)
            sol = solve(ODEProblem(sys.system, merge(ic, Dict(β=>1/6, γ=>0.25)),
                (0.0, 120.0)), Tsit5(); maxiters=100000)
            totals = reinfection_totals(sys, sol)
            push!(results, totals[:I][end])
        end
        # Monotonic convergence
        @test results[1] >= results[2] >= results[3]
        # All within 1% of each other
        @test (results[1] - results[3]) / results[1] < 0.01
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
