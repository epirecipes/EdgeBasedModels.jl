# Legacy tests: catalyst.
#
# Split verbatim from the pre-refactor test/runtests.jl of EdgeBasedModels 0.1 (working tree of
# 2026-09-26) by WP1 of DESIGN_NetworkEpiCore.md; only comments were added.
# Owner after Phase 0: WP14 (the front end moves to NetworkEpiCoreCatalystExt, WP9).
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

@testset "legacy catalyst" begin
    @testset "Catalyst progression adapter" begin
        @parameters γ
        rn = Catalyst.@reaction_network begin
            γ, I --> R
        end

        progression = progression_from_catalyst(
            rn;
            transmission_rates = Dict(:I => 1, :R => 0),
        )

        @test progression.entry == :I
        @test [stage.name for stage in progression.stages] == [:I, :R]
        @test length(progression.transitions) == 1
        @test progression.transitions[1].source == :I
        @test progression.transitions[1].target == :R
    end

    @testset "Catalyst bimolecular transmission" begin
        # SIR via S + I → 2I (β) and I → R (γ) — fully Catalyst-defined.
        rn = Catalyst.@reaction_network begin
            β, S + I --> 2I
            γ, I --> R
        end
        # LEGACY[E25]: progression_from_catalyst uses the raw reaction rate as the per-edge rate and ignores
        # only_use_rate/substoich; branching is dropped. WP9 replaces it with the NEC Catalyst front end.
        prog = progression_from_catalyst(rn; susceptible = :S, entry = :I)
        β_idx = findfirst(s -> s.name == :I, prog.stages)
        @test β_idx !== nothing
        # Transmission rate should have been inferred from the bimolecular reaction
        # (i.e., it's symbolic rather than the numeric 0 default).
        rate = prog.stages[β_idx].transmission_rate
        @test !(rate isa Number)
        @test :β in nameof.(Symbolics.get_variables(rate))
        # Progression I → R recorded
        @test any(tr -> tr.source == :I && tr.target == :R, prog.transitions)
        # Bimolecular reaction without susceptible should throw
        rn_bad = Catalyst.@reaction_network begin
            β, I + R --> 2I
        end
        @test_throws ArgumentError progression_from_catalyst(rn_bad; susceptible = :S, entry = :I)
    end
end
