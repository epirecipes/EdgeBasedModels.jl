# Legacy tests: analysis.
#
# Split verbatim from the pre-refactor test/runtests.jl of EdgeBasedModels 0.1 (working tree of
# 2026-09-26) by WP1 of DESIGN_NetworkEpiCore.md; only comments were added.
# Owner after Phase 0: WP19 (analysis).
# Annotation tags (grep for them):
#   LEGACY-WRONG[<id>]  the assertion pins a value that VERIFIED_ISSUES.md <id> shows to be wrong;
#   LEGACY-WEAK[<id>]   the test cannot detect the defect <id> (structure only, or a loose reference);
#   LEGACY[<id>]        the code under test has the verified defect <id>; the test itself is neutral.
# They stay until the owning bug-fix work package replaces them (design section G.1).
#
# WP19 (the owner) fixed E14, E15, E16, E17, E18 and E31(i) in src/analysis.jl; the assertions
# below are unchanged (they hold before and after the fixes), their tags now say FIXED[<id>], and
# the regression tests with reference values are in test/suites/analysis.jl. The E31(i) test at the
# end, `@test_broken` before, is now a `@test`.

using EdgeBasedModels
using ModelingToolkit
using Symbolics
using Test

import Catalyst

isdefined(Main, :GoldenTools) || Base.include(Main, joinpath(@__DIR__, "..", "golden", "GoldenTools.jl"))
using Main.GoldenTools

@testset "legacy analysis" begin
    @testset "R₀ computation" begin
        @parameters β γ κ
        pgf = poisson_pgf(κ)

        # SIR R₀ = βκ/(β+γ)
        prog = DiseaseProgression(
            [DiseaseStage(:I; transmission_rate = β), DiseaseStage(:R; transmission_rate = 0)],
            [DiseaseTransition(:I, :R, γ)];
            entry = :I,
        )
        scm = StaticConfigurationModel(pgf, prog)
        R0 = basic_reproduction_number(scm)
        R0_str = string(Symbolics.simplify(R0))
        @test occursin("β", R0_str)
        @test occursin("κ", R0_str)
        @test occursin("γ", R0_str)

        R0_numeric = Symbolics.value(Symbolics.substitute(R0, Dict(β => 0.1, γ => 0.05, κ => 5.0)))
        @test R0_numeric ≈ 10.0 / 3.0 atol = 1e-10

        # SEIR R₀ should equal SIR R₀ (E stage is non-infectious)
        @parameters σ
        seir_prog = DiseaseProgression(
            [DiseaseStage(:E; transmission_rate = 0), DiseaseStage(:I; transmission_rate = β), DiseaseStage(:R)],
            [DiseaseTransition(:E, :I, σ), DiseaseTransition(:I, :R, γ)];
            entry = :E,
        )
        R0_seir = basic_reproduction_number(StaticConfigurationModel(pgf, seir_prog))
        R0_seir_val = Symbolics.value(Symbolics.substitute(R0_seir, Dict(β => 0.1, γ => 0.05, σ => 0.2, κ => 5.0)))
        @test R0_seir_val ≈ 10.0 / 3.0 atol = 1e-10

        # Two-stage infectious: T = 1 - [γ₁/(β₁+γ₁)]·[γ₂/(β₂+γ₂)]
        @parameters β₁ β₂ γ₁ γ₂
        twostage = DiseaseProgression(
            [DiseaseStage(:I1; transmission_rate = β₁), DiseaseStage(:I2; transmission_rate = β₂), DiseaseStage(:R)],
            [DiseaseTransition(:I1, :I2, γ₁), DiseaseTransition(:I2, :R, γ₂)];
            entry = :I1,
        )
        R0_2 = basic_reproduction_number(StaticConfigurationModel(pgf, twostage))
        R0_2_val = Symbolics.value(Symbolics.substitute(R0_2, Dict(β₁ => 0.1, γ₁ => 0.5, β₂ => 0.2, γ₂ => 0.3, κ => 5.0)))
        expected_T = 1 - (0.5 / 0.6) * (0.3 / 0.5)
        @test R0_2_val ≈ expected_T * 5.0 atol = 1e-10
    end

    @testset "Degree Correlation" begin
        @testset "neutral_correlated_pgf" begin
            pk = [0.0, 0.2, 0.5, 0.3]  # degrees 0,1,2,3
            cpgf = neutral_correlated_pgf(pk)
            @test cpgf isa CorrelatedPGF
            @test cpgf.max_degree == 3
            # Every row of the mixing matrix must sum to 1
            for k in 1:size(cpgf.mixing_matrix, 1)
                @test sum(cpgf.mixing_matrix[k, :]) ≈ 1.0 atol = 1e-8
            end
        end

        # LEGACY[E20]: r·δ_kk is added to rows with p_k = 0 (spurious eigenvalues for zero-padded classes).
        @testset "assortative_correlated_pgf" begin
            pk = [0.0, 0.2, 0.5, 0.3]
            neutral = neutral_correlated_pgf(pk)
            r0_pgf = assortative_correlated_pgf(pk, 0.0)
            # r=0 should match neutral mixing matrix
            @test r0_pgf.mixing_matrix ≈ neutral.mixing_matrix atol = 1e-10

            # r=1 should be identity-like (diagonal dominant)
            r1_pgf = assortative_correlated_pgf(pk, 1.0)
            for k in 1:size(r1_pgf.mixing_matrix, 1)
                @test r1_pgf.mixing_matrix[k, k] ≈ 1.0 atol = 1e-8
            end
        end

        @testset "correlated_R0 neutral = standard" begin
            pk = [0.0, 0.2, 0.5, 0.3]
            T = 0.4
            cpgf = neutral_correlated_pgf(pk)
            R0_corr = correlated_R0(cpgf, T)

            # Standard R₀ = T·(⟨k²⟩-⟨k⟩)/⟨k⟩
            mean_k = sum((k - 1) * pk[k] for k in 1:length(pk))
            mean_k2 = sum((k - 1)^2 * pk[k] for k in 1:length(pk))
            R0_std = T * (mean_k2 - mean_k) / mean_k

            @test R0_corr ≈ R0_std atol = 1e-6
        end

        @testset "Assortativity range" begin
            pk = [0.0, 0.3, 0.4, 0.3]
            T = 0.5
            R0_neutral = correlated_R0(assortative_correlated_pgf(pk, 0.0), T)
            R0_assort = correlated_R0(assortative_correlated_pgf(pk, 1.0), T)
            @test isfinite(R0_neutral)
            @test isfinite(R0_assort)
            @test R0_neutral > 0
            @test R0_assort > 0
        end

        @testset "Poisson neutral" begin
            # For Poisson(κ), ⟨k²⟩-⟨k⟩ = κ², so R₀ = T·κ
            κ = 4.0
            T = 0.3
            # Approximate Poisson with truncated distribution
            max_k = 20
            pk = [exp(-κ) * κ^k / factorial(k) for k in 0:max_k]
            pk ./= sum(pk)  # renormalize after truncation
            cpgf = neutral_correlated_pgf(pk)
            R0_corr = correlated_R0(cpgf, T)
            @test R0_corr ≈ T * κ atol = 0.05
        end

        @testset "Row normalization" begin
            pk = [0.1, 0.3, 0.4, 0.2]
            for r in [0.0, 0.25, 0.5, 0.75, 1.0]
                cpgf = assortative_correlated_pgf(pk, r)
                for k in 1:size(cpgf.mixing_matrix, 1)
                    @test sum(cpgf.mixing_matrix[k, :]) ≈ 1.0 atol = 1e-8
                end
            end
        end
    end

    @testset "Analytics on configuration model" begin
        pgf  = poisson_pgf(5.0)
        prog = sir_model(β = 0.3, γ = 0.1)        # R₀ = 0.3/0.4 · 5 = 3.75
        model = StaticConfigurationModel(pgf, prog)

        # FIXED[E18]: final_size is a bracketed (Brent) solve with an exact threshold test; ρ → 0 by default,
        # `seed_fraction = ρ` for a finite seed (E31(i)).
        # final_size
        fs = final_size(model)
        @test 0.7 < fs.R_infinity < 1.0
        @test 0.0 < fs.θ_infinity < 1.0

        # sub-threshold case
        prog_sub = sir_model(β = 0.01, γ = 1.0)   # R₀ ≪ 1
        sub_fs = final_size(StaticConfigurationModel(pgf, prog_sub))
        @test sub_fs.R_infinity == 0.0
        @test sub_fs.θ_infinity == 1.0

        # FIXED[E15]: epidemic_probability is the infector-side (mixed-binomial) formula, 0.905224 here (the
        # bond-percolation value was 0.974082); the range assertion below holds for both.
        # epidemic_probability
        pep = epidemic_probability(model)
        @test 0.5 < pep < 1.0
        # sub-threshold returns 0
        @test epidemic_probability(StaticConfigurationModel(pgf, prog_sub)) == 0.0

        # FIXED[E16]: the confidence_bands variance is Ball (2021) Theorem 2.2; these are ordering checks only.
        # confidence_bands: lower < mean < upper, std_error positive
        cb = confidence_bands(model, 1_000)
        @test cb.lower <= cb.mean <= cb.upper
        @test cb.std_error > 0.0
        @test 0.0 <= cb.lower && cb.upper <= 1.0
        # near-zero epidemic returns all-zero bands
        cb0 = confidence_bands(StaticConfigurationModel(pgf, prog_sub), 1_000)
        @test cb0.mean == 0.0 && cb0.std_error == 0.0

        # Empty infectious stages now throws (regression)
        empty_prog = DiseaseProgression(
            [DiseaseStage(:R; transmission_rate = 0)],
            DiseaseTransition[]; entry = :R)
        @test_throws ArgumentError final_size(StaticConfigurationModel(pgf, empty_prog))
    end

    @testset "disease_free_equilibrium" begin
        @parameters β γ
        pgf = poisson_pgf(5.0)
        model = StaticConfigurationModel(pgf, sir_model(β = β, γ = γ))
        # LEGACY-WEAK[E21]: the DFE keys (stage names, φ_X) do not match the builders' keys (pop_X).
        dfe = disease_free_equilibrium(model)
        @test dfe[:S] == 1.0 && dfe[:θ] == 1.0
        @test dfe[:I] == 0.0 && dfe[:R] == 0.0
        @test dfe[Symbol("φ_I")] == 0.0
    end

    @testset "basic_reproduction_number compatibility overloads" begin
        # CorrelatedPGF overload
        cpgf = neutral_correlated_pgf([0.0, 0.5, 0.5])
        @test basic_reproduction_number(cpgf, 0.5) == correlated_R0(cpgf, 0.5)

        # E12: consistency with multiplex_R0 only (ρ(K) is tested in test/suites/analysis.jl).
        # Multiplex tuple overload
        layers = [
            (:home, poisson_pgf(3.0), 0.2, 0.1),
            (:work, poisson_pgf(8.0), 0.1, 0.1),
        ]
        @test basic_reproduction_number(layers) ≈ multiplex_R0(layers)
    end

    @testset "epidemic_threshold (analytic, no Nemo)" begin
        # SIR on Poisson(5): κ = 5, threshold β_c = γ/(κ-1) = 0.1/4 = 0.025
        pgf = poisson_pgf(5.0)
        model = StaticConfigurationModel(pgf, sir_model(β = 0.1, γ = 0.1))
        β_c = epidemic_threshold(model)
        @test β_c ≈ 0.1 / 4 atol = 1e-12

        # Sub-critical network (κ ≤ 1) raises
        sparse = StaticConfigurationModel(poisson_pgf(0.5), sir_model(β = 0.1, γ = 0.1))
        @test_throws ArgumentError epidemic_threshold(sparse)

        # Symbolic single-stage SEIR returns a symbolic expression that satisfies
        # R₀ = 1 when β is substituted with β_c.
        @parameters β σ γ
        seir = StaticConfigurationModel(pgf, seir_model(β = β, σ = σ, γ = γ))
        β_c_sym = epidemic_threshold(seir)
        R0_sym = basic_reproduction_number(seir)
        R0_at_threshold = Symbolics.substitute(R0_sym, Dict(β => β_c_sym))
        @test isequal(Symbolics.simplify(R0_at_threshold - 1), 0)
    end

    # ---- Added by WP1 (not part of the pre-refactor suite) ------------------------------------

    @testset "E31(i): final_size with a finite seed (WP19 enhancement)" begin
        # final_size uses the ρ → 0 relation by default. With ρ = 0.01 on Poisson(5) (τ = 1/6, γ = 1/4) the
        # ODE and Miller (2014) eqs (3)-(4) with φ_S(0) = 1-ρ give R∞ = 0.800204 (EoN Attack_rate_cts_time
        # agrees), final_size gives the ρ → 0 value 0.796812. WP19 added the `seed_fraction` keyword (this
        # was a @test_broken, a MethodError, before).
        ρ = 0.01; T = (1 / 6) / (1 / 6 + 1 / 4); θ = 0.5
        for _ in 1:10_000
            θ = 1 - T + T * (1 - ρ) * exp(5 * (θ - 1))
        end
        Rinf = 1 - (1 - ρ) * exp(5 * (θ - 1))
        @test Rinf ≈ 0.8002039676767994 atol = 1e-9          # EoN, test/golden/eon/eon_like_for_like.toml
        model = StaticConfigurationModel(poisson_pgf(5.0),
            DiseaseProgression([DiseaseStage(:I; transmission_rate = 1 / 6), DiseaseStage(:R; transmission_rate = 0)],
                               [DiseaseTransition(:I, :R, 1 / 4)]; entry = :I))
        @test final_size(model).R_infinity ≈ 0.7968121300200202 atol = 1e-9   # ρ → 0 (EoN rho=None)
        @test final_size(model; seed_fraction = ρ).R_infinity ≈ Rinf atol = 1e-12
    end

    check_area("analysis")
end
