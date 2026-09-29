# Legacy tests: multiplex.
#
# Split verbatim from the pre-refactor test/runtests.jl of EdgeBasedModels 0.1 (working tree of
# 2026-09-26) by WP1 of DESIGN_NetworkEpiCore.md; only comments were added.
# Owner after Phase 0: WP22 (multiplex through the assembler).
#
# WP22 update (verified issues E12, E13): `build_multiplex_sir(layers)` now returns an
# `EdgeModelSystem` of the per-reaction multiplex lift instead of a `(system, u0, tspan, p)` tuple,
# so the 0.1 destructuring `sys, u0, tspan, p = build_multiplex_sir(layers)` is replaced by the
# EdgeModelSystem API below; each testset keeps its 0.1 intent. `form = :compact` has the 0.1 shape
# (one θ per layer and R, `length(layers) + 1` equations). multiplex_R0 is now ρ(K) (E12): the 0.1
# expectations below are for Poisson layers and a single layer, where ρ(K) equals the 0.1 sum, so
# they are unchanged. The goldens of this area were replaced by WP22 (see
# test/golden/multiplex/cases.jl); the new behaviour is tested in test/suites/multiplex.jl.
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

isdefined(Main, :GoldenTools) || Base.include(Main, joinpath(@__DIR__, "..", "golden", "GoldenTools.jl"))
using Main.GoldenTools

@testset "legacy multiplex" begin
    @testset "Multiplex Networks" begin
        using OrdinaryDiffEqDefault
        using LinearAlgebra: eigvals

        @testset "build_multiplex_sir" begin
            pgf1 = poisson_pgf(3.0)
            pgf2 = poisson_pgf(2.0)
            layers = [
                (:home, pgf1, 0.3, 0.1),
                (:work, pgf2, 0.2, 0.1),
            ]
            # 0.2 (E13): an EdgeModelSystem, not a (sys, u0, tspan, p) tuple
            m = @test_nowarn build_multiplex_sir(layers)
            @test m isa EdgeModelSystem
            @test m.system isa ModelingToolkit.System
            # the 0.1 shape (θ_home, θ_work, R) is the compact form
            mc = build_multiplex_sir(layers; form = :compact)
            @test length(ModelingToolkit.equations(mc.system)) == length(layers) + 1
            @test haskey(mc.variables, :θ_home) && haskey(mc.variables, :θ_work) && haskey(mc.variables, :R)
        end

        @testset "Solves correctly" begin
            pgf1 = poisson_pgf(3.0)
            pgf2 = poisson_pgf(2.0)
            layers = [
                (:home, pgf1, 0.3, 0.1),
                (:work, pgf2, 0.2, 0.1),
            ]
            m = build_multiplex_sir(layers)
            sol = solve_epidemic(m; initial = SeedFraction(:I => 1e-3), tspan = (0.0, 100.0),
                                 abstol = 1e-8, reltol = 1e-8)
            @test sol.retcode == ReturnCode.Success
            # All solution values should be finite
            @test all(isfinite, sol.u[end])
        end

        @testset "multiplex_R0" begin
            pgf1 = poisson_pgf(3.0)
            pgf2 = poisson_pgf(2.0)
            layers = [
                (:home, pgf1, 0.3, 0.1),
                (:work, pgf2, 0.2, 0.1),
            ]
            R0 = multiplex_R0(layers)
            # E12 (fixed in 0.2): R₀ is the spectral radius ρ(K) of the layer NGM; for independent
            # Poisson layers det K = 0, so it equals the 0.1 sum T₁·excess₁ + T₂·excess₂.
            # Poisson(κ): excess = κ, T = β/(β+γ)
            T1 = 0.3 / (0.3 + 0.1)  # 0.75
            T2 = 0.2 / (0.2 + 0.1)  # 2/3
            expected = T1 * 3.0 + T2 * 2.0
            @test R0 ≈ expected atol = 1e-8
        end

        @testset "Single layer = standard" begin
            pgf = polynomial_pgf([0.0, 0.2, 0.5, 0.3])
            β, γ = 0.4, 0.1
            layers = [(:only, pgf, β, γ)]
            R0_mpx = multiplex_R0(layers)

            # Standard formula: T·(⟨k²⟩-⟨k⟩)/⟨k⟩
            pk = [0.0, 0.2, 0.5, 0.3]
            mean_k = sum((k - 1) * pk[k] for k in 1:length(pk))
            mean_k2 = sum((k - 1)^2 * pk[k] for k in 1:length(pk))
            T = β / (β + γ)
            R0_std = T * (mean_k2 - mean_k) / mean_k
            @test R0_mpx ≈ R0_std atol = 1e-8
        end

        @testset "Three layers" begin
            pgf1 = poisson_pgf(2.0)
            pgf2 = poisson_pgf(1.5)
            pgf3 = poisson_pgf(1.0)
            layers = [
                (:home, pgf1, 0.3, 0.1),
                (:work, pgf2, 0.2, 0.1),
                (:community, pgf3, 0.1, 0.1),
            ]
            m = @test_nowarn build_multiplex_sir(layers; form = :compact)
            @test length(ModelingToolkit.equations(m.system)) == length(layers) + 1
            sol = solve_epidemic(m; initial = SeedFraction(:I => 1e-3), tspan = (0.0, 100.0),
                                 abstol = 1e-8, reltol = 1e-8)
            @test sol.retcode == ReturnCode.Success
            R0 = multiplex_R0(layers)
            @test R0 > 0
            @test isfinite(R0)
        end

        @testset "susceptible_fraction" begin
            pgf1 = poisson_pgf(3.0)
            pgf2 = poisson_pgf(2.0)
            # At θ=1 (no infection), S should be 1
            S_init = susceptible_fraction([pgf1, pgf2], [1.0, 1.0])
            @test S_init ≈ 1.0 atol = 1e-8
            # At intermediate θ, S should be in (0,1)
            S_mid = susceptible_fraction([pgf1, pgf2], [0.8, 0.9])
            @test 0.0 < S_mid < 1.0
        end
    end

    check_area("multiplex")
end
