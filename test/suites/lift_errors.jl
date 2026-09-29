# WP17 acceptance 9 (the §B.7 error texts) and the strictly partial lift (verified issue E19):
# every model with an arrow into a susceptible class is refused by every assembler closure
# (ConfigurationNetwork, WellMixed, MultitypeNetwork) with the AdmissibilityError of §B.7, never
# silently lifted as SIR (the legacy lifted SIS became SIR dynamics) and never with a KeyError
# (the legacy non-static builders). The front-end texts of §B.7 (Catalyst) reach the caller of
# edge_based unchanged.

using EdgeBasedModels
using NetworkEpiCore
using Test

import Catalyst
import Graphs

errtext(f) = try
    f()
    ""
catch e
    sprint(showerror, e)
end
flat(s) = replace(s, r"\s+" => " ")

@testset "lift: admissibility errors (§B.7, E19)" begin
    reg3 = ConfigurationNetwork(RegularDegree(3))
    pois = ConfigurationNetwork(PoissonDegree(5.0))

    @testset "the first §B.7 text, verbatim" begin
        err = try
            edge_based(sis_model(), reg3)
        catch e
            e
        end
        @test err isa AdmissibilityError
        @test sprint(showerror, err) == """
            AdmissibilityError: edge_based(:sis, ConfigurationNetwork(RegularDegree(3))):
              `γ, I --> S` (type resus: node → sus) produces the susceptible species S.
              The edge-based model is exact only when no reaction produces a susceptible class
              (Miller, Slim & Volz 2012, Part I). Back ends that accept this model: node_based
              (pairwise, individual, pair, motif, neighbourhood), simulate, mass_action.
              Try: NodeBasedModels.node_based(model, net; closure = KeelingClosure())."""
    end

    @testset "partial immunity: two reasons, one sentence (§B.7)" begin
        partial = ContactModel(:partial;
            contacts = [Contact(:S, :I1, :I1, :τ1), Contact(:S, :I2, :I2, :τ2), Contact(:R1, :I2, :I12, :(ε * τ2))],
            transitions = [NodeTransition(:I1, :R1, :γ), NodeTransition(:I2, :R2, :γ), NodeTransition(:I12, :R, :γ)])
        txt = flat(errtext(() -> edge_based(partial, pois)))
        @test occursin("`ε*τ2, R1 + I2 --> I12 + I2`: R1 is a second susceptible class (multiple_sus) and is " *
                       "produced by `γ, I1 --> R1` (resus).", txt)
        @test occursin("The edge-based model is exact only when no reaction produces a susceptible class", txt)
    end

    @testset "E19: SIS, SIRS and reinfection-counted models are refused by every closure" begin
        st = strata([:a, :b])
        sbm = sbm_network(st; mean_contacts = [3.0 1.0; 1.0 3.0])
        refused = [sis_model(), sirs_model(), with_reinfection_counting(sis_model(), 1),
                   with_reinfection_counting(sirs_model(), 2)]
        for cm in refused
            @test_throws AdmissibilityError edge_based(cm, pois)
            @test_throws AdmissibilityError edge_based(cm, pois; form = :compact)
            @test_throws AdmissibilityError edge_based(cm, WellMixed(5.0))
            @test_throws AdmissibilityError edge_based(stratify(cm, st), sbm)
            @test_throws AdmissibilityError edge_based(cm, sbm)
        end
        # the lifted SIS names both reasons in one sentence (the old name-based guard missed it)
        txt = flat(errtext(() -> edge_based(with_reinfection_counting(sis_model(), 1), pois)))
        @test occursin("S_1 is a second susceptible class (multiple_sus) and is produced by `γ, I_1 --> S_1` (resus).", txt)
        # the legacy entry point keeps its ArgumentError for SIS (E01)
        @test_throws ArgumentError build_edge_system(StaticConfigurationModel(poisson_pgf(5.0), sis_model(τ = 0.4, γ = 1.0)))
    end

    @testset "the Catalyst front-end texts of §B.7 reach edge_based's caller" begin
        rn_state = Catalyst.@reaction_network begin
            β, S + I --> E + R
            γ, I --> R
        end
        @test occursin("the infector changes state on transmission", flat(errtext(() -> edge_based(rn_state, pois))))
        rn_birth = Catalyst.@reaction_network begin
            β, S + I --> 2I
            μ, 0 --> S
        end
        @test occursin("births change the node set", flat(errtext(() -> edge_based(rn_birth, pois))))
        rn_nonlin = Catalyst.@reaction_network begin
            β * S * I / (1 + a * I), S + I => E + I
            σ, E --> I
        end
        @test occursin("depends on species (non-bilinear incidence)", flat(errtext(() -> edge_based(rn_nonlin, pois))))
    end

    @testset "other refusals" begin
        @test_throws AdmissibilityError edge_based(sir_model(), ExplicitGraph(Graphs.cycle_graph(10)))
        @test_throws ArgumentError edge_based(sir_model(), WellMixed(5.0); form = :compact)
        @test_throws ArgumentError edge_based(sir_model(), pois; form = :bogus)
        # a contact on a layer the network does not have
        lay = ContactModel(:lay; contacts = [Contact(:S, :I, :I, :τ; layer = :home)], transitions = [NodeTransition(:I, :R, :γ)])
        @test_throws AdmissibilityError edge_based(lay, pois)
        @test_throws ArgumentError lift_contributions(lay, pois)
        # MultiplexNetwork has its closure since WP22 (the WP17 fallback refused it): an unlayered contact
        # acts on every layer
        @test lift_contributions(sir_model(), MultiplexNetwork(:a => RegularDegree(3), :b => RegularDegree(3))) isa
              LiftContributions
    end
end
