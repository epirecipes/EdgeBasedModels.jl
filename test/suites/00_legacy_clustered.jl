# Legacy tests: clustered.
#
# Split verbatim from the pre-refactor test/runtests.jl of EdgeBasedModels 0.1 (working tree of
# 2026-09-26) by WP1 of DESIGN_NetworkEpiCore.md; only comments were added.
# Owner after Phase 0: WP20 (Volz 2011 clustered lift).
#
# WP20 replaced the clustered builder by the Volz et al. (2011) lift with triangle pair states
# (src/lift/clustered.jl; verified issue E02), so the variable-name checks now name the pair
# states (φ3_X_Y, χ_X) instead of the legacy per-edge φ3_X, and the goldens of this area were
# deliberately regenerated (validated in test/suites/clustered.jl against Volz's equations and
# exact stochastic simulation). The LEGACY-WRONG assertions on E03/E04 are replaced by the correct
# values: through NetworkEpiCore/WP20 code where that exists, and (FIXED by WP29) for the legacy
# functions of src/pgf.jl and src/builders.jl, which WP20 does not own (fixes requested).
# Annotation tags (grep for them):
#   LEGACY-WRONG[<id>]  the assertion pins a value that VERIFIED_ISSUES.md <id> shows to be wrong;
#   LEGACY-WEAK[<id>]   the test cannot detect the defect <id> (structure only, or a loose reference);
#   LEGACY[<id>]        the code under test has the verified defect <id>; the test itself is neutral.
# They stay until the owning bug-fix work package replaces them (design section G.1).

using EdgeBasedModels
using NetworkEpiCore
using ModelingToolkit
using Symbolics
using Test

const EBM = EdgeBasedModels

import Catalyst

isdefined(Main, :GoldenTools) || Base.include(Main, joinpath(@__DIR__, "..", "golden", "GoldenTools.jl"))
using Main.GoldenTools

@testset "legacy clustered" begin
    @testset "Clustering" begin
        using OrdinaryDiffEqDefault

        _numval(x) = Float64(Symbolics.value(
            Symbolics.substitute(x, Dict(exp(Symbolics.Num(0.0)) => 1, exp(Symbolics.Num(0)) => 1))))

        @testset "ClusteredPGF construction" begin
            cpgf = clustered_poisson_pgf(3.0, 1.0)
            @test cpgf isa ClusteredPGF
            @test _numval(mean_single_degree(cpgf)) ≈ 3.0
            @test _numval(mean_triangle_degree(cpgf)) ≈ 1.0
        end

        @testset "Clustering coefficient" begin
            cpgf = clustered_poisson_pgf(3.0, 1.0)
            cc = _numval(clustering_coefficient(cpgf))
            @test 0.0 ≤ cc ≤ 1.0
            # E03: the transitivity of clustered_poisson_pgf(3, 1) is 2⟨t⟩/⟨k(k−1)⟩ = 2/27 ≈ 0.0741
            # (Graphs on N = 1e5: 0.0740); 2⟨t⟩/(2⟨t⟩+⟨s⟩) = 0.4 is the fraction of edges in triangles.
            @test clustering_coefficient(ClusteredNetwork(cpgf)) ≈ 2 / 27 atol = 1e-12
            @test _numval(triangle_edge_fraction(cpgf)) ≈ 0.4 atol = 1e-10
            # FIXED[E03] (WP29): the legacy method of src/pgf.jl returned the triangle-edge fraction 0.4
            @test cc ≈ 2 / 27 atol = 1e-10
        end

        @testset "Zero clustering = standard model" begin
            @parameters β γ
            # No triangle edges → should behave like standard model
            cpgf_zero = clustered_poisson_pgf(5.0, 0.0)
            @test _numval(clustering_coefficient(cpgf_zero)) ≈ 0.0 atol = 1e-10

            clustered_model = ClusteredConfigurationModel(
                cpgf_zero,
                DiseaseProgression(
                    [DiseaseStage(:I; transmission_rate = β), DiseaseStage(:R; transmission_rate = 0)],
                    [DiseaseTransition(:I, :R, γ)]; entry = :I),
            )
            R0_clustered = basic_reproduction_number(clustered_model)
            R0_val = _numval(Symbolics.substitute(R0_clustered, Dict(β => 0.1, γ => 0.05)))

            # Standard Poisson SIR: R₀ = β·κ/(β+γ) = 0.1·5/(0.15) = 10/3
            std_pgf = poisson_pgf(5.0)
            std_model = StaticConfigurationModel(
                std_pgf,
                DiseaseProgression(
                    [DiseaseStage(:I; transmission_rate = β), DiseaseStage(:R; transmission_rate = 0)],
                    [DiseaseTransition(:I, :R, γ)]; entry = :I),
            )
            R0_std = basic_reproduction_number(std_model)
            R0_std_val = _numval(Symbolics.substitute(R0_std, Dict(β => 0.1, γ => 0.05)))

            @test R0_val ≈ R0_std_val atol = 1e-8
            # the tree-of-triangles R₀ of the Volz lift (E04) agrees without triangles
            @test EBM._clustered_reproduction_number(sir_model(; τ = 0.1, γ = 0.05),
                                                     ClusteredNetwork(cpgf_zero)) ≈ R0_std_val atol = 1e-10
        end

        @testset "Clustered SIR builds" begin
            @parameters β γ
            cpgf = clustered_poisson_pgf(3.0, 1.0)
            result = @test_nowarn build_clustered_sir(cpgf, β, γ)
            @test result isa EdgeModelSystem

            # Variables: θ₂, θ₃, φ2_I, φ2_R, R and (E02, Volz et al. 2011) the triangle pair states
            # φ3_X_Y and the conditional partner states χ_X, which replace the legacy per-edge φ3_X
            @test haskey(result.variables, :θ₂)
            @test haskey(result.variables, :θ₃)
            @test haskey(result.variables, :φ2_I)
            @test haskey(result.variables, :φ2_R)
            for name in (:χ_I, :χ_R, :φ3_I_I, :φ3_I_R, :φ3_R_R)
                @test haskey(result.variables, name)
            end
            @test !haskey(result.variables, :φ3_I) && !haskey(result.variables, :φ3_R)
            @test haskey(result.variables, :R)

            # Observables (the pair states with a susceptible partner are observables)
            @test haskey(result.observables, :S)
            @test haskey(result.observables, :I)
            @test haskey(result.observables, :φ2_S)
            for name in (:χ_S, :φ3_S_S, :φ3_S_I, :φ3_S_R)
                @test haskey(result.observables, name)
            end
        end

        # E02 (fixed by WP20): the model is now Volz et al. 2011 (the legacy θ₃² treated triangle
        # partners as independent edges); these structural checks are unchanged.
        @testset "Clustered SIR solves" begin
            cpgf = clustered_poisson_pgf(3.0, 1.0)
            model = build_clustered_sir(cpgf, 0.5, 0.1)
            ic = default_initial_conditions(model)
            prob = ODEProblem(model.system, ic, (0.0, 100.0))
            sol = solve(prob; abstol = 1e-8, reltol = 1e-8)

            @test sol.retcode == ReturnCode.Success

            # Extract final values — epidemic should complete
            S_final = sol[model.observables[:S]][end]
            I_final = sol[model.observables[:I]][end]
            R_final = sol[model.variables[:R]][end]

            @test 0.0 < S_final < 1.0
            @test I_final ≈ 0.0 atol = 1e-4     # epidemic should die out
            @test R_final > 0.0                   # some recovered
            @test isapprox(S_final + I_final + R_final, 1.0; atol = 1e-4)
            # Regression: φ-seeding must drive a real epidemic on both
            # single and triangle edges. Without seeding both φ2_I(0)
            # and φ3_I(0) from θ - φ_S, epidemic stalls and R_final ≈ ε.
            @test R_final > 0.1
        end

        # E04 (corrected fix): the legacy R₀ T·g_xx/g_x + T·(2g_y/g_x)(1+T) is heuristic, and the property
        # this testset asserted, R₀(4.5, 0.25) > R₀(3, 1) at τ = 0.1, γ = 0.05, is false: the
        # tree-of-triangles NGM gives 3.3466 < 3.3858, and SSA growth rates agree (0.3534 vs 0.3717).
        # Clustering lowers R₀ against the unclustered network with the same degree sequence.
        @testset "Clustering reduces R₀ (against the same degree sequence)" begin
            @parameters β γ
            # Same total mean degree = 5, but different clustering
            cpgf_low = clustered_poisson_pgf(4.5, 0.25)   # low clustering
            cpgf_high = clustered_poisson_pgf(3.0, 1.0)   # high clustering
            R0v(pgf) = EBM._clustered_reproduction_number(sir_model(; τ = 0.1, γ = 0.05), ClusteredNetwork(pgf))
            @test R0v(cpgf_low) ≈ 3.3466 atol = 1e-4
            @test R0v(cpgf_high) ≈ 3.3858 atol = 1e-4
            T = 0.1 / 0.15
            @test R0v(cpgf_high) < T * 27 / 5          # k = s + 2t: E[k(k−1)]/E[k] = 27/5, no clustering
            @test R0v(cpgf_low) < T * (4.5^2 + 4 * 4.5 * 0.25 + 4 * 0.25^2 + 2 * 0.25) / 5

            prog = DiseaseProgression(
                [DiseaseStage(:I; transmission_rate = β), DiseaseStage(:R; transmission_rate = 0)],
                [DiseaseTransition(:I, :R, γ)]; entry = :I)
            # FIXED[E04]: basic_reproduction_number(::ClusteredConfigurationModel) of src/builders.jl is
            # the tree-of-triangles R₀ (it was a heuristic): at the true threshold of (3, 1),
            # T_c = 0.190158 (Volz final size, NGM and N = 10⁶ simulation), it is 1 (the heuristic gave
            # 0.7214), symbolically and numerically.
            Tc = 0.190158
            legacy = basic_reproduction_number(ClusteredConfigurationModel(cpgf_high, prog))
            @test Float64(Symbolics.value(Symbolics.substitute(legacy, Dict(β => Tc / (1 - Tc), γ => 1.0);
                                                               fold = Val(true)))) ≈ 1.0 atol = 1e-5
            @test basic_reproduction_number(ClusteredConfigurationModel(cpgf_high,
                DiseaseProgression([DiseaseStage(:I; transmission_rate = Tc / (1 - Tc)), DiseaseStage(:R)],
                                   [DiseaseTransition(:I, :R, 1.0)]; entry = :I))) ≈ 1.0 atol = 1e-5
        end

        @testset "Clustered SEIR builds and solves" begin
            cpgf = clustered_poisson_pgf(3.0, 1.0)
            model = @test_nowarn build_clustered_seir(cpgf, 0.2, 0.5, 0.1)
            @test model isa EdgeModelSystem

            # SEIR has 3 stages (E, I, R) so more φ variables (E02: triangle pair states)
            @test haskey(model.variables, :θ₂)
            @test haskey(model.variables, :θ₃)
            @test haskey(model.variables, :φ2_E)
            @test haskey(model.variables, :φ2_I)
            @test haskey(model.variables, :φ2_R)
            for name in (:χ_E, :χ_I, :χ_R, :φ3_E_E, :φ3_E_I, :φ3_E_R, :φ3_I_I, :φ3_I_R, :φ3_R_R)
                @test haskey(model.variables, name)
            end

            ic = default_initial_conditions(model)
            prob = ODEProblem(model.system, ic, (0.0, 100.0))
            sol = solve(prob; abstol = 1e-8, reltol = 1e-8)
            @test sol.retcode == ReturnCode.Success

            S_final = sol[model.observables[:S]][end]
            @test 0.0 < S_final < 1.0
        end

        @testset "Custom ClusteredPGF from coefficient matrix" begin
            # Simple bivariate distribution: p(0,0)=0.1, p(1,0)=0.3, p(0,1)=0.2, p(1,1)=0.4
            joint = [0.1 0.2; 0.3 0.4]
            cpgf = @test_nowarn clustered_pgf(joint)
            @test cpgf isa ClusteredPGF

            # mean single degree = 0·(0.1+0.2) + 1·(0.3+0.4) = 0.7
            @test _numval(mean_single_degree(cpgf)) ≈ 0.7 atol = 1e-10
            # mean triangle degree = 0·(0.1+0.3) + 1·(0.2+0.4) = 0.6
            @test _numval(mean_triangle_degree(cpgf)) ≈ 0.6 atol = 1e-10

            cc = _numval(clustering_coefficient(cpgf))
            @test 0.0 ≤ cc ≤ 1.0
            # E03: the transitivity of this joint PGF is 2⟨t⟩/⟨k(k−1)⟩ = 1.2/2.8 = 3/7 (empirical
            # 0.4281); 1.2/1.9 is the fraction of edges in triangles
            @test clustering_coefficient(ClusteredNetwork(cpgf)) ≈ 3 / 7 atol = 1e-12
            @test _numval(triangle_edge_fraction(cpgf)) ≈ 1.2 / 1.9 atol = 1e-10
            # FIXED[E03] (WP29): the legacy method of src/pgf.jl returned 1.2/1.9
            @test cc ≈ 3 / 7 atol = 1e-10

            # Should also build and solve an SIR model
            model = build_clustered_sir(cpgf, 0.5, 0.1)
            ic = default_initial_conditions(model)
            prob = ODEProblem(model.system, ic, (0.0, 100.0))
            sol = solve(prob; abstol = 1e-8, reltol = 1e-8)
            @test sol.retcode == ReturnCode.Success
        end
    end

    check_area("clustered")
end
