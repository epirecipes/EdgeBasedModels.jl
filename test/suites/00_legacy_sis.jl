# Legacy tests: sis.
#
# Split from the pre-refactor test/runtests.jl of EdgeBasedModels 0.1 (working tree of 2026-09-26) by
# WP1 of DESIGN_NetworkEpiCore.md. Owner after Phase 0: WP29 (legacy removal); WP14 turned build_sis into
# an error.
#
# WP29: SIS has no exact edge-based model (verified issue E01), so nothing here builds an SIS system any
# more. Each 0.1 testset is kept under its name and checks what design §A.7 makes of it:
#   - build_sis / generate_sis (the SIR equation relabelled, LEGACY[E01]): an error naming
#     NodeBasedModels.node_based and NetworkOutbreaks.simulate; SIS through build_edge_system and
#     edge_based is refused too;
#   - sis_model, sirs_model: NetworkEpiCore's ContactModels (the legacy DiseaseProgression is their
#     converted form);
#   - with_reinfection_counting: NetworkEpiCore's lift of a ContactModel (the 0.1 method on
#     DiseaseProgression, which cannot hold several susceptible classes, is an error);
#   - build_sis_reinfection (a pairwise model, correct but not edge-based): an error naming its
#     NodeBasedModels replacement. The numerical properties the 0.1 testsets checked (conservation,
#     saturation, ever-infected = 1 − S_0) belong to that model and are NodeBasedModels' to test;
#     test/suites/deprecations.jl pins the values the replacement must reproduce.

using EdgeBasedModels
using ModelingToolkit
using Symbolics
using Test

import Catalyst

errmsg(f) = try
    f()
    ""
catch e
    sprint(showerror, e)
end

@testset "legacy sis" begin
    @testset "Disease model factories (SIS part)" begin
        # Split from the legacy "Disease model factories" testset (00_legacy_core.jl).
        @parameters β σ γ κ

        @test sis_model(; τ = β, γ = γ) isa ContactModel
        sis = DiseaseProgression(sis_model(; τ = β, γ = γ))
        @test sis.susceptible == :S
        @test sis.entry == :I
        @test [stage.name for stage in sis.stages] == [:I]
        @test length(sis.transitions) == 1
        @test sis.transitions[1].source == :I
        @test sis.transitions[1].target == :S

        # 0.1 (LEGACY-WEAK[E01, E30]): build_sis and build_edge_system(SIS) were compared with each
        # other, tautologically. 0.2: both refuse, with the same migration text.
        pgf = poisson_pgf(κ)
        @test_throws ErrorException build_sis(pgf, β, γ)
        @test_throws ArgumentError build_edge_system(StaticConfigurationModel(pgf, sis))
        @test errmsg(() -> build_edge_system(StaticConfigurationModel(pgf, sis))) ==
              errmsg(() -> throw(ArgumentError(errmsg(() -> build_sis(pgf, β, γ)))))
    end

    @testset "SIS builder" begin
        @parameters β γ κ
        # 0.1 (LEGACY[E01]): build_sis was the SIR compact equation relabelled (one θ ODE); it
        # overestimated the endemic prevalence by about 25% (0.8002 vs SSA 0.6488 at τ = 1/6, γ = 1/4).
        @test_throws ErrorException build_sis(poisson_pgf(κ), β, γ)
        msg = errmsg(() -> build_sis(poisson_pgf(κ), β, γ))
        @test occursin("SIR dynamics relabelled", msg) && occursin("E01", msg)
        @test occursin("NodeBasedModels.node_based(sis_model(), net)", msg) && occursin("NetworkOutbreaks.simulate", msg)
        @test_throws AdmissibilityError edge_based(sis_model(), ConfigurationNetwork(PoissonDegree(5.0)))
    end

    @testset "sirs_model factory" begin
        @parameters β γ ε
        @test sirs_model(τ = β, γ = γ, ε = ε) isa ContactModel
        prog = DiseaseProgression(sirs_model(τ = β, γ = γ, ε = ε))
        stage_names = [s.name for s in prog.stages]
        @test :I in stage_names
        @test :R in stage_names
        @test any(tr -> tr.source == :I && tr.target == :R, prog.transitions)
        @test any(tr -> tr.source == :R && tr.target == :S, prog.transitions)
        # build_edge_system does not support re-susceptibilisation (no exact edge-based model); the
        # factory itself succeeds, which is what API parity with NodeBasedModels requires.
        @test_throws ArgumentError build_edge_system(StaticConfigurationModel(poisson_pgf(4.0), prog))
    end

    @testset "Reinfection counting (Keeling et al. 2016, Approx. 1)" begin
        # 0.2: NetworkEpiCore's with_reinfection_counting on ContactModels (the 0.1 method on the
        # legacy DiseaseProgression is an error: it cannot hold the counted susceptible classes).
        @testset "Structural lift of the SIS model" begin
            lifted = with_reinfection_counting(sis_model(), 0)  # S → I → S
            @test susceptible_species(lifted) == [:S_0]
            @test sort(setdiff(species_names(lifted), susceptible_species(lifted))) == [:I_0]
            @test entry_species(lifted) == [:I_0]

            lifted3 = with_reinfection_counting(sis_model(), 3)
            @test first(susceptible_species(lifted3)) == :S_0
            # S_1, S_2, S_3, I_1, I_2, I_3 besides S_0
            @test sort(setdiff(species_names(lifted3), [:S_0])) == [:I_1, :I_2, :I_3, :S_1, :S_2, :S_3]
            # infection from S_0 enters I_1
            @test all(c.product === :I_1 for c in contacts(lifted3) if c.recipient === :S_0)
            # I_p → S_p recovery transitions, p = 1..3
            recoveries = [(t.from, t.to) for t in node_transitions(lifted3)]
            @test (:I_1, :S_1) in recoveries
            @test (:I_2, :S_2) in recoveries
            @test (:I_3, :S_3) in recoveries
            @test_throws ErrorException with_reinfection_counting(DiseaseProgression(sis_model()), 3)
        end

        @testset "Structural lift of SIRS" begin
            lifted = with_reinfection_counting(sirs_model(), 2)  # S → I → R → S
            # Non-S_0 species: I_1, I_2, R_1, R_2, S_1, S_2
            @test sort(setdiff(species_names(lifted), [:S_0])) == [:I_1, :I_2, :R_1, :R_2, :S_1, :S_2]
            transitions = [(t.from, t.to) for t in node_transitions(lifted)]
            # Recovery I_p → R_p preserves p
            @test (:I_1, :R_1) in transitions
            @test (:I_2, :R_2) in transitions
            # Waning R_p → S_p preserves p
            @test (:R_1, :S_1) in transitions
            @test (:R_2, :S_2) in transitions
        end

        @testset "build_sis_reinfection: removed (a pairwise model; NodeBasedModels)" begin
            # The four 0.1 testsets of build_sis_reinfection (edge variables and initialisation at L = 0,
            # difference from build_sis at L = 3, conservation and saturation at L = 4, ever-infected
            # = 1 − S_0 at L = 1) tested the pairwise model that moved to NodeBasedModels.
            pgf = poisson_pgf(5.0)
            for L in (0, 1, 3, 4)
                @test_throws ErrorException build_sis_reinfection(pgf, 0.5, 1.0, L)
            end
            msg = errmsg(() -> build_sis_reinfection(pgf, 0.5, 1.0, 1))
            @test occursin("NodeBasedModels.node_based(with_reinfection_counting(sis_model(; τ, γ), L)", msg)
            @test occursin("reinfection_totals", msg)
            # the model it names is admissible for the pairwise back end and not for the edge-based one
            counted = with_reinfection_counting(sis_model(τ = 0.5, γ = 1.0), 1)
            @test !is_admissible(counted, :edge_based; network = ConfigurationNetwork(PoissonDegree(5.0)))
            @test is_admissible(counted, :pairwise; network = ConfigurationNetwork(PoissonDegree(5.0)))
        end

        @testset "Lifted-name helpers" begin
            @test base_compartment_of(:S_3) == :S
            @test base_compartment_of(:I_12) == :I
            @test base_compartment_of(:θ) == :θ
            @test infection_count_of(:S_3) == 3
        end
    end
end
