# Legacy tests: seir_multistage.
#
# Split verbatim from the pre-refactor test/runtests.jl of EdgeBasedModels 0.1 (working tree of
# 2026-09-26) by WP1 of DESIGN_NetworkEpiCore.md; only comments were added.
# Owner after Phase 0: WP29 (legacy removal); WP19 for the Erlang transmissibility.
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

@testset "legacy seir_multistage" begin
    @testset "SEIR builder" begin
        @parameters σ β γ κ
        model = build_seir(poisson_pgf(κ), σ, β, γ)
        eqs = ModelingToolkit.equations(model.system)

        # Expanded SEIR now keeps stage-population variables in the compiled system. 0.2 (WP29):
        # the assembler adds one equation, the cumulative-incidence accumulator of design §J.8
        # (θ, φ_E, φ_I, φ_R, pop_E, pop_I, pop_R, cumulative).
        @test length(eqs) == 8
        @test haskey(model.variables, :cumulative)
        @test haskey(model.variables, :θ)
        @test haskey(model.variables, :φ_E)
        @test haskey(model.variables, :φ_I)
        @test haskey(model.variables, :φ_R)
        @test haskey(model.variables, :R)
        @test haskey(model.observables, :S)
        @test haskey(model.observables, :I)
    end

    @testset "Method of Stages" begin
        @testset "ErlangStage construction" begin
            es = ErlangStage(:I, 5, 0.1; transmission_rate = 0.5)
            @test es.name == :I
            @test es.n_substages == 5
            @test es.total_rate == 0.1
            @test es.transmission_rate == 0.5
        end

        @testset "GammaApproxStage" begin
            gs = GammaApproxStage(:I, 10.0, 0.3; transmission_rate = 0.5)
            # n = round(1/0.3²) = round(11.11) = 11
            @test gs isa ErlangStage
            @test gs.n_substages == 11
            @test gs.total_rate ≈ 1 / 10.0
            @test gs.transmission_rate == 0.5
        end

        # LEGACY-WEAK[E09]: these tests pass the stage-level rate γ as the exit rate. The documented convention
        # is the sub-stage rate n·γ (Erlang(n, nγ), mean 1/γ); with γ the last sub-stage leaves at γ and the mean
        # sojourn is (2n-1)/(nγ). The assertions check structure only, so they cannot see this (E30).
        @testset "expand_erlang_stages basics" begin
            @parameters γ_mos β_mos
            erlang_I = ErlangStage(:I, 3, γ_mos; transmission_rate = β_mos)
            prog = expand_erlang_stages(
                [erlang_I, DiseaseStage(:R)],
                [DiseaseTransition(:I, :R, γ_mos)];
                entry = :I,
            )
            # 3 sub-stages of I + R = 4 stages total
            @test length(prog.stages) == 4
            @test prog.stages[1].name == :I_1
            @test prog.stages[2].name == :I_2
            @test prog.stages[3].name == :I_3
            @test prog.stages[4].name == :R
            @test prog.entry == :I_1
        end

        @testset "Sub-stage rate" begin
            n = 3
            γ_val = 0.3
            erlang_I = ErlangStage(:I, n, γ_val; transmission_rate = 0.5)
            prog = expand_erlang_stages(
                [erlang_I, DiseaseStage(:R)],
                [DiseaseTransition(:I, :R, γ_val)];
                entry = :I,
            )
            # Internal chain transitions: I_1→I_2 and I_2→I_3 should have rate = n * γ
            chain_transitions = [tr for tr in prog.transitions if tr.source in (:I_1, :I_2) && tr.target in (:I_2, :I_3)]
            @test length(chain_transitions) == 2
            for tr in chain_transitions
                @test tr.rate ≈ n * γ_val  # 3 * 0.3 = 0.9
            end
        end

        @testset "Transmission inherited" begin
            @parameters β_inh
            erlang_I = ErlangStage(:I, 3, 0.5; transmission_rate = β_inh)
            prog = expand_erlang_stages(
                [erlang_I, DiseaseStage(:R)],
                [DiseaseTransition(:I, :R, 0.5)];
                entry = :I,
            )
            # All I sub-stages should have the transmission rate
            for i in 1:3
                stage = prog.stages[i]
                @test stage.name == Symbol(:I, "_", i)
                @test isequal(stage.transmission_rate, β_inh)
            end
            # R should have zero transmission
            @test prog.stages[4].transmission_rate == 0
        end

        @testset "Erlang(1) = exponential" begin
            @parameters γ_e1 β_e1
            # Erlang with 1 sub-stage
            erlang1 = ErlangStage(:I, 1, γ_e1; transmission_rate = β_e1)
            prog_erlang = expand_erlang_stages(
                [erlang1, DiseaseStage(:R)],
                [DiseaseTransition(:I, :R, γ_e1)];
                entry = :I,
            )
            # Should produce 2 stages: I_1 and R
            @test length(prog_erlang.stages) == 2
            @test prog_erlang.stages[1].name == :I_1
            # The transition from I_1 → R should have rate γ_e1 (1 * γ_e1)
            exit_tr = [tr for tr in prog_erlang.transitions if tr.source == :I_1 && tr.target == :R]
            @test length(exit_tr) == 1
            @test isequal(exit_tr[1].rate, γ_e1)
        end

        @testset "Model builds and solves" begin
            @parameters β_ms γ_ms κ_ms
            pgf = poisson_pgf(κ_ms)
            erlang_I = ErlangStage(:I, 3, γ_ms; transmission_rate = β_ms)
            prog = expand_erlang_stages(
                [erlang_I, DiseaseStage(:R)],
                [DiseaseTransition(:I, :R, γ_ms)];
                entry = :I,
            )
            scm = StaticConfigurationModel(pgf, prog)
            result = build_edge_system(scm)
            eqs = ModelingToolkit.equations(result.system)
            @test length(eqs) == 10                    # 9 in 0.1, + the §J.8 accumulator
            @test haskey(result.variables, :θ)
            @test haskey(result.variables, :R)
            @test haskey(result.observables, :S)
        end

        # LEGACY-WEAK[E09]: ErlangStage(:I, 5, 5γ) with exit 5γ has mean 9/(25γ) = 3.6, not 1/γ = 10, so the
        # name is false; a same-mean Erlang(5) is ErlangStage(:I, 5, γ) with exit 5γ.
        @testset "Same mean, different dynamics" begin
            @parameters κ_sd
            γ_val = 0.1
            β_val = 0.05
            κ_val = 10.0

            # Erlang(1, γ) — exponential
            erlang1 = ErlangStage(:I, 1, γ_val; transmission_rate = β_val)
            prog1 = expand_erlang_stages(
                [erlang1, DiseaseStage(:R)],
                [DiseaseTransition(:I, :R, γ_val)];
                entry = :I,
            )
            scm1 = StaticConfigurationModel(poisson_pgf(κ_sd), prog1)
            r1 = build_edge_system(scm1; name = :erlang1)
            eqs1 = ModelingToolkit.equations(r1.system)

            # Erlang(5, 5γ) — sharper distribution, same mean
            erlang5 = ErlangStage(:I, 5, 5 * γ_val; transmission_rate = β_val)
            prog5 = expand_erlang_stages(
                [erlang5, DiseaseStage(:R)],
                [DiseaseTransition(:I, :R, 5 * γ_val)];
                entry = :I,
            )
            scm5 = StaticConfigurationModel(poisson_pgf(κ_sd), prog5)
            r5 = build_edge_system(scm5; name = :erlang5)
            eqs5 = ModelingToolkit.equations(r5.system)

            @test length(eqs1) == 6                    # 5 and 13 in 0.1, + the §J.8 accumulator
            @test length(eqs5) == 14

            # Both models should build without error (sizes differ)
            @test length(eqs5) > length(eqs1)
        end

        @testset "SEIR with Erlang stages" begin
            @parameters σ_se β_se γ_se κ_se
            erlang_E = ErlangStage(:E, 2, σ_se; transmission_rate = 0)
            erlang_I = ErlangStage(:I, 3, γ_se; transmission_rate = β_se)
            prog = expand_erlang_stages(
                [erlang_E, erlang_I, DiseaseStage(:R)],
                [DiseaseTransition(:E, :I, σ_se), DiseaseTransition(:I, :R, γ_se)];
                entry = :E,
            )
            # E_1, E_2, I_1, I_2, I_3, R = 6 stages
            @test length(prog.stages) == 6
            @test prog.entry == :E_1

            scm = StaticConfigurationModel(poisson_pgf(κ_se), prog)
            result = build_edge_system(scm)
            eqs = ModelingToolkit.equations(result.system)
            @test length(eqs) == 14                    # 13 in 0.1, + the §J.8 accumulator
            @test haskey(result.variables, :θ)
            @test haskey(result.variables, :R)
            @test haskey(result.observables, :S)
        end
    end

    # ---- Added by WP1 (not part of the pre-refactor suite) ------------------------------------

    @testset "E09 documented Erlang convention (exit rate n·γ)" begin
        # With the exit rate n·γ (the expand_erlang_stages docstring and vignette 10), the expanded chain
        # is Erlang(n, nγ): mean sojourn 1/γ and T = 1 - (nγ/(nγ+β))^n (Sherborne thesis, eq. 2.9).
        # This holds before and after the E09 fix, which makes total_rate set the timing.
        for (n, γv, βv) in ((3, 0.1, 0.2), (5, 0.25, 1 / 6))
            prog = expand_erlang_stages([ErlangStage(:I, n, γv; transmission_rate = βv), DiseaseStage(:R)],
                                        [DiseaseTransition(:I, :R, n * γv)]; entry = :I)
            @test all(tr -> tr.rate ≈ n * γv, prog.transitions)
            block = [Symbol(:I_, i) for i in 1:n]
            idx = Dict(s => i for (i, s) in enumerate(block))
            Q = zeros(n, n)
            for tr in prog.transitions
                i = idx[tr.source]
                Q[i, i] -= tr.rate
                haskey(idx, tr.target) && (Q[i, idx[tr.target]] += tr.rate)
            end
            @test ((-Q) \ ones(n))[1] ≈ 1 / γv rtol = 1e-12        # phase-type mean sojourn
            R0 = basic_reproduction_number(StaticConfigurationModel(poisson_pgf(5.0), prog))
            @test numval(R0) ≈ 5 * (1 - (n * γv / (n * γv + βv))^n) rtol = 1e-10
        end
    end

    check_area("seir_multistage")

    # WP29 regenerated these goldens for new names only (E26_FIXED_NOTE in GoldenTools): every 0.1
    # column of every case is reproduced to the golden tolerance by the per-reaction assembler.
    @testset "0.2 reproduces the 0.1 numbers (WP29)" begin
        for case in load_cases("seir_multistage")
            check_v01(case)
        end
    end
end
