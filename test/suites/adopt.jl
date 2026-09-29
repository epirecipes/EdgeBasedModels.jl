# EdgeBasedModels adopts NetworkEpiCore (WP14, DESIGN_NetworkEpiCore.md §G.2).
#
# Owner: WP14 → WP29. Covers: the NetworkEpiCore bindings and generics, DegreePGF <:
# DegreeDistribution with provenance, the converters ContactModel ⇄ legacy types, `edge_based` and
# the legacy entry points through the per-reaction assembler (checked against an independent
# Miller ODE, NetworkEpiCore's independent final-size fixed point and Miller's final-size
# relation), Symbol rates (verified issue E10), parameter names (E26: the seed parameters are
# `seed_<X>`, so ρ is an ordinary name), the `initial` keyword, the scenario helpers and the
# package hygiene of 0.2. (Until WP29 the legacy 0.1 builders were reachable here as a fallback;
# they are deleted.)

using EdgeBasedModels
using NetworkEpiCore
using ModelingToolkit
using Symbolics
using Test
using Markdown
using StableRNGs
using OrdinaryDiffEq: Vern9, solve
import OrdinaryDiffEq
import Catalyst
import Graphs
import TOML

const EBM = EdgeBasedModels
const NEC = NetworkEpiCore
const TOL = (reltol = 1e-10, abstol = 1e-12)
const P_BIMODAL = [k == 2 ? 5 / 6 : k == 10 ? 1 / 6 : 0.0 for k in 0:10]

# Independent Miller (2011) final size on a configuration network with seed fraction ρ in I:
# θ∞ = 1 − T + T(1 − ρ)ψ'(θ∞)/ψ'(1), R∞ = 1 − (1 − ρ)ψ(θ∞), T = τ/(τ + γ); solved by bisection.
function miller_final_size(ψ, dψ, τ, γ, ρ)
    T = τ / (τ + γ)
    f(θ) = θ - (1 - T) - T * (1 - ρ) * dψ(θ) / dψ(1.0)
    lo, hi = 0.0, 1.0 - 1e-12                   # f(lo) < 0 < f(hi) away from the trivial root θ = 1
    for _ in 1:200
        mid = (lo + hi) / 2
        f(mid) < 0 ? (lo = mid) : (hi = mid)
    end
    return 1 - (1 - ρ) * ψ(lo)
end

getcurve(sys, sol, X) = compartment(sys, sol, X)

@testset "adopt NetworkEpiCore" begin
    @testset "NetworkEpiCore bindings are re-exported as the same objects" begin
        for n in names(NetworkEpiCore)
            n === :NetworkEpiCore && continue
            @test n in names(EdgeBasedModels)
            @test getfield(EdgeBasedModels, n) === getfield(NetworkEpiCore, n)
        end
        # the 17 names formerly exported by both EBM and NBM, final_size and stratify are NEC's
        for n in (:base_compartment_of, :basic_reproduction_number, :compartment, :compartments,
                  :default_initial_conditions, :disease_free_equilibrium, :epidemic_threshold,
                  :infection_count_of, :mean_degree, :population_fraction, :reinfection_totals,
                  :seir_model, :sir_model, :sirs_model, :sis_model, :solve_epidemic,
                  :with_reinfection_counting, :final_size, :stratify, :model_curves,
                  :NaturalTransformation)
            @test getfield(EdgeBasedModels, n) === getfield(NetworkEpiCore, n)
        end
        @test sir_model() isa ContactModel
        @test !(:compose in names(EdgeBasedModels))         # MTK and Catalyst export compose
        @test :edge_based in names(EdgeBasedModels)
    end

    @testset "EdgeBasedModels adds no method ambiguities (with NEC and its extensions)" begin
        exts = [m for m in (Base.get_extension(NetworkEpiCore, e) for e in
                (:NetworkEpiCoreSymbolicsExt, :NetworkEpiCoreMTKExt, :NetworkEpiCoreCatalystExt,
                 :NetworkEpiCoreGraphsExt)) if m !== nothing]
        @test length(exts) >= 3                            # Symbolics, MTK and Catalyst are loaded
        ebm_mods = (EdgeBasedModels,)                        # the 0.1 legacy submodules are deleted (WP29)
        @test !isdefined(EdgeBasedModels, :_LegacyCategorical) && !isdefined(EdgeBasedModels, :_LegacyReinfection)
        amb = Test.detect_ambiguities(NetworkEpiCore, EdgeBasedModels, exts...; recursive = true)
        mine = [(a, b) for (a, b) in amb if a.module in ebm_mods || b.module in ebm_mods]
        @test isempty(mine)
        # the WP5 case: compartment & co. with two EdgeModelSystems resolve to the canonical method
        sys = build_sir(poisson_pgf(5.0), 0.3, 0.1)
        m = which(compartment, (EdgeModelSystem, EdgeModelSystem, Symbol))
        @test m.sig == Tuple{typeof(compartment), EdgeModelSystem, Any, Symbol}
    end

    @testset "DegreePGF is a DegreeDistribution with provenance" begin
        p5 = poisson_pgf(5.0)
        @test p5 isa DegreeDistribution
        @test p5.distribution == PoissonDegree(5.0)
        pb = polynomial_pgf(P_BIMODAL)
        @test pb.distribution == EmpiricalDegree(2 => 5 / 6, 10 => 1 / 6)
        @test DegreePGF(p5.variable, p5.expression).distribution === nothing
        # NEC interface through the provenance
        @test canonical_text(ConfigurationNetwork(p5)) == canonical_text(ConfigurationNetwork(PoissonDegree(5.0)))
        @test canonical_text(pb) == canonical_text(EmpiricalDegree(P_BIMODAL))
        @test rand(StableRNG(3), p5, 20) == rand(StableRNG(3), PoissonDegree(5.0), 20)
        @test rand(StableRNG(3), pb) == rand(StableRNG(3), EmpiricalDegree(P_BIMODAL))
        @test degree_probabilities(pb) ≈ degree_probabilities(EmpiricalDegree(P_BIMODAL))
        @test is_poisson_type(p5) == is_poisson_type(PoissonDegree(5.0))
        @test is_poisson_type(pb) === nothing
        bare = DegreePGF(p5.variable, p5.expression)
        @test_throws ArgumentError canonical_text(bare)
        @test_throws ArgumentError rand(StableRNG(1), bare)
        # closed forms, also without provenance
        for x in (0.0, 0.3, 0.9)
            @test pgf(p5, x) ≈ exp(5 * (x - 1)) rtol = 1e-14
            @test pgf_derivative(p5, x, 2) ≈ 25 * exp(5 * (x - 1)) rtol = 1e-14
            @test pgf(pb, x) ≈ pgf(EmpiricalDegree(P_BIMODAL), x) rtol = 1e-14
            @test pgf_derivative(pb, x, 1) ≈ pgf_derivative(EmpiricalDegree(P_BIMODAL), x, 1) rtol = 1e-14
        end
        @test mean_degree(ConfigurationNetwork(pb)) ≈ 10 / 3
        @test excess_degree(ConfigurationNetwork(pb)) ≈ 5.0
        @test excess_degree(bare) ≈ 5.0
        @test closure_constant(pb) ≈ 1.5
        @test is_poisson_type(bare) == (α = 5.0, κ = 1.0)      # NEC's numeric test on the symbolic PGF
        # DegreePGF(::DegreeDistribution): the legacy constructors' expressions, and closed forms
        @test isequal(DegreePGF(PoissonDegree(5.0)).expression, p5.expression)
        @test DegreePGF(PoissonDegree(5.0)).distribution == PoissonDegree(5.0)
        @test isequal(DegreePGF(EmpiricalDegree(P_BIMODAL)).expression, pb.expression)
        @test DegreePGF(p5) === p5
        for d in (RegularDegree(6), NegBinDegree(mean = 4, var = 8), BinomialDegree(10, 0.4),
                  PowerLawDegree(2.5; kmin = 2, kmax = 20),
                  MixtureDegree(0.5 => PoissonDegree(2.0), 0.5 => RegularDegree(4)))
            q = DegreePGF(d)
            @test q.distribution == d
            for x in (0.1, 0.5, 0.95)
                @test pgf(q, x) ≈ pgf(d, x) rtol = 1e-12
                @test pgf_derivative(q, x, 2) ≈ pgf_derivative(d, x, 2) rtol = 1e-10
            end
        end
        # a symbolic mean keeps working, with symbolic provenance
        @parameters κ
        pκ = poisson_pgf(κ)
        @test pκ.distribution isa PoissonDegree
        @test isequal(pκ.distribution.mean, κ)
    end

    @testset "ClusteredPGF provenance and ClusteredNetwork" begin
        g = clustered_poisson_pgf(1.0, 2.0)
        @test g.joint == ClusteredDegree(PoissonDegree(1.0), PoissonDegree(2.0))
        @test ClusteredNetwork(g) == ClusteredNetwork(PoissonDegree(1.0), PoissonDegree(2.0))
        @test isequal(ClusteredPGF(ClusteredNetwork(g)).expression, g.expression)
        gj = clustered_pgf([0.1 0.2; 0.3 0.4])
        @test ClusteredNetwork(gj) == ClusteredNetwork([0.1 0.2; 0.3 0.4])
        @test_throws ArgumentError ClusteredNetwork(ClusteredPGF(g.single_var, g.triangle_var, g.expression))
        # generic joint laws use NEC's closed form
        cd = ClusteredDegree(RegularDegree(2), PoissonDegree(1.5))
        h = ClusteredPGF(cd)
        vals = Dict(h.single_var => 0.4, h.triangle_var => 0.7)
        @test EBM._maybe_to_float64(Symbolics.substitute(h.expression, vals)) ≈ pgf(cd, 0.4, 0.7) rtol = 1e-14
        # E03: the 0.1 clustering_coefficient(::ClusteredPGF) value was the fraction of edges in
        # triangles, available under its honest name as NEC's triangle_edge_fraction; it agrees
        # with NEC's closed form on the same network (2·1/(3 + 2·1) = 0.4 for Poisson(3, 1),
        # 12/19 for the joint table), and it is not NEC's transitivity (2/27 for Poisson(3, 1))
        tef(x) = EBM._maybe_to_float64(x)
        g31 = clustered_poisson_pgf(3.0, 1.0)
        @test tef(triangle_edge_fraction(g31)) ≈ 0.4 rtol = 1e-14
        @test tef(triangle_edge_fraction(g31)) ≈ triangle_edge_fraction(ClusteredNetwork(g31)) rtol = 1e-14
        @test tef(triangle_edge_fraction(gj)) ≈ 12 / 19 rtol = 1e-14
        @test tef(triangle_edge_fraction(gj)) ≈ triangle_edge_fraction(ClusteredNetwork(gj)) rtol = 1e-14
        # E03 fixed (WP29): the legacy clustering_coefficient(::ClusteredPGF) is the transitivity now
        @test tef(clustering_coefficient(g31)) ≈ clustering_coefficient(ClusteredNetwork(g31)) rtol = 1e-12
        @test tef(clustering_coefficient(gj)) ≈ clustering_coefficient(ClusteredNetwork(gj)) rtol = 1e-12
        @test clustering_coefficient(ClusteredNetwork(g31)) ≈ 2 / 27 rtol = 1e-12
        @test triangle_edge_fraction(clustered_poisson_pgf(5.0, 0.0)) == 0.0
    end

    @testset "ContactModel ⇄ DiseaseProgression" begin
        progs = [
            EBM._legacy_sir_model(β = 0.3, γ = 0.1),
            EBM._legacy_seir_model(σ = 0.5, β = 0.3, γ = 0.2),
            EBM._legacy_sis_model(β = 0.4, γ = 1.0),
            EBM._legacy_sirs_model(β = 0.4, γ = 1.0, ε = 0.1),
            EBM._legacy_sir_model(),                                   # Symbol rates
            DiseaseProgression([DiseaseStage(:E; transmission_rate = 0.05), DiseaseStage(:I; transmission_rate = 0.3),
                                DiseaseStage(:R)],
                               [DiseaseTransition(:E, :I, 0.5), DiseaseTransition(:I, :R, 0.2)]; entry = :E),
            expand_erlang_stages([ErlangStage(:I, 3, 0.25; transmission_rate = 1 / 6), DiseaseStage(:R)],
                                 [DiseaseTransition(:I, :R, 0.75)]; entry = :I),
            DiseaseProgression([DiseaseStage(:I; transmission_rate = 0.3), DiseaseStage(:R), DiseaseStage(:D)],
                               [DiseaseTransition(:I, :R, 0.1), DiseaseTransition(:I, :D, 0.01)]; susceptible = :U),
        ]
        for prog in progs
            cm = contact_model(prog)
            @test cm isa ContactModel
            @test susceptible_species(cm) == [prog.susceptible]
            back = DiseaseProgression(cm)
            @test back.susceptible === prog.susceptible
            @test back.entry === prog.entry
            @test [s.name for s in back.stages] == [s.name for s in prog.stages]
            @test all(isequal(a.transmission_rate, b.transmission_rate) for (a, b) in zip(back.stages, prog.stages))
            @test [(t.source, t.target) for t in back.transitions] == [(t.source, t.target) for t in prog.transitions]
            @test all(isequal(a.rate, b.rate) for (a, b) in zip(back.transitions, prog.transitions))
            @test isequivalent(contact_model(StaticConfigurationModel(poisson_pgf(5.0), prog)), cm)
        end
        # the canned NEC models and their legacy images
        @test isequivalent(contact_model(DiseaseProgression(sir_model())), sir_model())
        @test isequivalent(contact_model(DiseaseProgression(seir_model())), seir_model())
        @test isequivalent(contact_model(DiseaseProgression(seair_model())), seair_model())
        @test isequivalent(contact_model(EBM._legacy_sir_model(β = :τ)), sir_model())
        @test DiseaseProgression(seir_model()).entry === :E
        # what the legacy type cannot express
        @test_throws ArgumentError DiseaseProgression(twostrain_model())          # two entry states
        @test_throws ArgumentError DiseaseProgression(sirv_model())               # exit S → V
        # the hint names back ends that accept the model, and does not claim that edge_based does
        hint = sprint(showerror, try DiseaseProgression(sirv_model()) catch e; e end)
        @test occursin("NodeBasedModels.node_based", hint) && occursin("NetworkOutbreaks.simulate", hint)
        @test !occursin("edge_based, node_based or simulate accept it", hint)
        @test_throws ArgumentError DiseaseProgression(ContactModel(:rem; contacts = [Contact(:S, :I, :I, :τ)],
                                                                  transitions = [NodeTransition(:I, nothing, :γ)]))
        @test_throws ArgumentError DiseaseProgression(stratify(sir_model(), strata([:a, :b])))
        @test_throws ArgumentError DiseaseProgression(ContactModel(:lay; contacts = [Contact(:S, :I, :I, :τ; layer = :home)],
                                                                  transitions = [NodeTransition(:I, :R, :γ)]))
        # frequency-dependent rates need the network's mean degree
        fd = ContactModel(:fd; contacts = [Contact(:S, :I, :I, :β)], transitions = [NodeTransition(:I, :R, :γ)],
                          convention = FrequencyDependent())
        @test_throws ArgumentError DiseaseProgression(fd)
        fdp = DiseaseProgression(fd, ConfigurationNetwork(PoissonDegree(5.0)))
        @test isequal(fdp.stages[1].transmission_rate, rate_div(:β, 5.0))
        # legacy model types accept a ContactModel
        m = StaticConfigurationModel(poisson_pgf(5.0), sir_model(τ = 0.3, γ = 0.1))
        @test m.progression isa DiseaseProgression && m.progression.stages[1].transmission_rate == 0.3
        @test StaticConfigurationModel(PoissonDegree(5.0), sir_model()).pgf.distribution == PoissonDegree(5.0)
        @test ClusteredConfigurationModel(clustered_poisson_pgf(1.0, 2.0), sir_model()).progression.entry === :I
        @test DynamicConfigurationModel(poisson_pgf(5.0), sir_model(), 0.1, 0.1).progression.entry === :I
        types = [:a, :b]
        pgfs = Dict(t => multivariate_poisson_pgf(types, Dict(:a => 2.5, :b => 2.5)) for t in types)
        mt = MultiTypeConfigurationModel(types = types, pgfs = pgfs, progression = sir_model(τ = 0.3, γ = 0.1))
        @test mt.progression isa DiseaseProgression
    end

    @testset "edge_based is the per-reaction assembler (no legacy builder is reachable)" begin
        net = ConfigurationNetwork(PoissonDegree(5.0))
        sys = edge_based(sir_model(τ = 1 / 6, γ = 1 / 4), net)
        @test sys isa EdgeModelSystem
        @test sys.metadata[:kind] === :assembled
        @test sys.metadata[:model] isa ContactModel
        @test sys.metadata[:network] === net
        @test sys.metadata[:entry] === :I
        # Against an independent transcription of Miller's (2011) compact SIR equation (the
        # 0.1 builder, which this test used to compare with, is deleted):
        # θ' = −τθ + τ(1 − ρ)ψ'(θ)/ψ'(1) + γ(1 − θ), θ(0) = 1, S = (1 − ρ)ψ(θ), ψ(x) = e^{5(x−1)}
        τ, γ, ρ = 1 / 6, 1 / 4, 1e-3
        miller = solve(OrdinaryDiffEq.ODEProblem((θ, _, _) -> -τ * θ + τ * (1 - ρ) * exp(5 * (θ - 1)) + γ * (1 - θ),
                                                 1.0, (0.0, 60.0)), Vern9(); saveat = 1.0, TOL...)
        S_ref = (1 - ρ) .* exp.(5 .* (miller.u .- 1))
        sol = solve_epidemic(sys; tspan = (0.0, 60.0), saveat = 1.0, TOL...)
        @test maximum(abs.(getcurve(sys, sol, :S) .- S_ref)) < 1e-9
        # every legacy entry point goes through it too
        for leg in (build_sir(poisson_pgf(5.0), τ, γ),
                    build_edge_system(StaticConfigurationModel(poisson_pgf(5.0), sir_model(τ = τ, γ = γ))),
                    build_clustered_sir(clustered_poisson_pgf(1.0, 2.0), 0.6, 1.0))
            @test leg.metadata[:kind] === :assembled
        end
        # compact form, and the form keyword is validated first
        sysc = edge_based(sir_model(τ = 1 / 6, γ = 1 / 4), net; form = :compact)
        solc = solve_epidemic(sysc; tspan = (0.0, 60.0), saveat = 1.0, TOL...)
        @test maximum(abs.(getcurve(sysc, solc, :S) .- getcurve(sys, sol, :S))) < 1e-8
        @test_throws ArgumentError edge_based(sir_model(), net; form = :bogus)
        @test_throws ArgumentError edge_based(seir_model(), net; form = :compact)
        # Catalyst and legacy inputs go through contact_model
        rn = Catalyst.@reaction_network begin
            τ, S + I --> 2I
            γ, I --> R
        end
        sysr = edge_based(rn, net)
        solr = solve_epidemic(sysr; p = Dict(:τ => 1 / 6, :γ => 1 / 4), tspan = (0.0, 60.0), saveat = 1.0, TOL...)
        @test maximum(abs.(getcurve(sysr, solr, :S) .- getcurve(sys, sol, :S))) < 1e-10
        sysp = edge_based(EBM._legacy_sir_model(β = 1 / 6, γ = 1 / 4), net)
        solp = solve_epidemic(sysp; tspan = (0.0, 60.0), saveat = 1.0, TOL...)
        @test maximum(abs.(getcurve(sysp, solp, :S) .- getcurve(sys, sol, :S))) < 1e-12
        # refusals: admissibility first (B.7)
        @test_throws AdmissibilityError edge_based(sis_model(), ConfigurationNetwork(RegularDegree(3)))
        @test_throws AdmissibilityError edge_based(sirs_model(), net)
        @test_throws AdmissibilityError edge_based(sir_model(), ExplicitGraph(Graphs.cycle_graph(10)))
        # what the WP14 fallback refused ("not available") is lifted by its descriptor's method now
        for (cm, nw, closure) in ((sirv_model(), net, :configuration), (twostrain_model(), net, :configuration),
                                  (sir_model(), WellMixed(5.0), :well_mixed),
                                  (sir_model(), DynamicNetwork(net, NeighbourExchange(1.0)), :dynamic))
            @test edge_based(cm, nw).metadata[:closure] === closure
        end
        @test edge_based(ContactModel(:mpx; contacts = [Contact(:S, :I, :I, :τa; layer = :a),
                                                         Contact(:S, :I, :I, :τb; layer = :b)],
                                      transitions = [NodeTransition(:I, :R, :γ)]),
                         MultiplexNetwork(:a => RegularDegree(3), :b => RegularDegree(3))).metadata[:closure] === :multiplex
    end

    @testset "edge_based SIR/SEIR/SEAIR/Erlang: conservation and NEC's final size" begin
        # For each (model, network, p, seed), the lowered ODE conserves θ = φ_S + Σ φ_X and
        # S + Σ pop_X = 1, and its long-time cumulative incidence equals NetworkEpiCore's
        # final_size (an independent fixed-point computation from the per-edge transmissibility).
        anchor = Dict(:τ => 1 / 6, :γ => 1 / 4)
        anchor_seir = Dict(:τ => 1 / 6, :γ => 1 / 4, :σ => 1 / 5)
        cases = [
            (sir_model(), ConfigurationNetwork(PoissonDegree(5)), anchor, SeedFraction(:I => 0.01)),
            (sir_model(), ConfigurationNetwork(RegularDegree(6)), anchor, SeedFraction(:I => 0.01)),
            (sir_model(), ConfigurationNetwork(NegBinDegree(mean = 4, var = 8)), anchor, SeedFraction(:I => 0.01)),
            (sir_model(), ConfigurationNetwork(EmpiricalDegree(2 => 5 / 6, 10 => 1 / 6)), anchor, SeedFraction(:I => 0.01)),
            (seir_model(), ConfigurationNetwork(PoissonDegree(5)), anchor_seir, SeedFraction(:E => 0.01)),
            (seair_model(), ConfigurationNetwork(PoissonDegree(5)),
             Dict(:τI => 1 / 6, :τA => 1 / 12, :σ => 1 / 5, :p => 0.6, :γ => 1 / 4), SeedFraction(:E => 0.01)),
            (erlang_stages(sir_model(), :I, 3), ConfigurationNetwork(PoissonDegree(5)), anchor,
             SeedFraction(:I_1 => 0.01)),
        ]
        for (cm, net, p, seed) in cases
            sys = edge_based(cm, net)
            sol = solve_epidemic(sys; p, initial = seed, tspan = (0.0, 600.0), TOL...)
            @test string(sol.retcode) == "Success"
            S = getcurve(sys, sol, :S)
            pops = [k for k in keys(sys.variables) if startswith(string(k), "pop_")]
            @test maximum(abs.(S .+ sum(getcurve(sys, sol, k) for k in pops) .- 1)) < 1e-9
            φs = [k for k in keys(sys.variables) if startswith(string(k), "φ_")]
            θ = getcurve(sys, sol, :θ)
            @test maximum(abs.(θ .- getcurve(sys, sol, :φ_S) .- sum(getcurve(sys, sol, k) for k in φs))) < 1e-9
            @test 1 - S[end] ≈ final_size(cm, net, p; initial = seed) atol = 1e-7
        end
        # the two readings of a model with several infectors: `compartment(sys, sol, :I)` is the
        # legacy observable (all transmitting stages, pop_A + pop_I for SEAIR), while
        # `model_curves(sys, sol)[:I]` is the stage named I (and its :infectious the legacy I)
        sys = edge_based(seair_model(), ConfigurationNetwork(PoissonDegree(5)))
        sol = solve_epidemic(sys; p = Dict(:τI => 1 / 6, :τA => 1 / 12, :σ => 1 / 5, :p => 0.6, :γ => 1 / 4),
                             initial = SeedFraction(:E => 0.01), tspan = (0.0, 60.0), saveat = 1.0, TOL...)
        mc = model_curves(sys, sol)
        @test maximum(abs.(getcurve(sys, sol, :I) .- getcurve(sys, sol, :pop_A) .- getcurve(sys, sol, :pop_I))) < 1e-12
        @test maximum(abs.(mc.values[:I] .- getcurve(sys, sol, :pop_I))) < 1e-10
        @test maximum(abs.(mc.values[:infectious] .- getcurve(sys, sol, :I))) < 1e-10
        @test maximum(getcurve(sys, sol, :pop_A)) > 0.01          # the readings really differ
    end

    @testset "E10: Symbol rates become parameters" begin
        pgf5 = poisson_pgf(5.0)
        for form in (:expanded, :compact)
            sys = build_sir(pgf5, :τ, :γ; form)                     # the acceptance criterion of WP14
            @test Set(Symbol.(ModelingToolkit.parameters(sys.system))) ⊇ Set([:τ, :γ])
            sol = solve_epidemic(sys; p = Dict(:τ => 0.3, :γ => 0.1), tspan = (0.0, 400.0), saveat = 1.0, TOL...)
            ref = build_sir(pgf5, 0.3, 0.1; form)
            solr = solve_epidemic(ref; tspan = (0.0, 400.0), saveat = 1.0, TOL...)
            @test maximum(abs.(getcurve(sys, sol, :S) .- getcurve(ref, solr, :S))) < 1e-10
            # Miller's final-size relation with ρ = 1e-3 (the default seed): R∞ = 0.97411041620
            R∞ = miller_final_size(x -> exp(5(x - 1)), x -> 5exp(5(x - 1)), 0.3, 0.1, 1e-3)
            @test R∞ ≈ 0.9741104162 atol = 1e-9
            @test 1 - getcurve(sys, sol, :S)[end] ≈ R∞ atol = 1e-8
        end
        # NamedTuple and symbolic-parameter keys, NEC distributions, defaults of the canned models
        sysd = build_sir(PoissonDegree(5.0), :τ, :γ)
        @parameters τ γ
        s1 = solve_epidemic(sysd; p = (τ = 0.3, γ = 0.1), tspan = (0.0, 30.0), saveat = 1.0, TOL...)
        s2 = solve_epidemic(sysd; p = Dict(τ => 0.3, γ => 0.1), tspan = (0.0, 30.0), saveat = 1.0, TOL...)
        @test getcurve(sysd, s1, :R) ≈ getcurve(sysd, s2, :R) rtol = 1e-12
        @test getcurve(sysd, s1, :R)[end] ≈ 0.8805791478 atol = 1e-8  # R(30), as in the E10 report
        sysm = edge_based(sir_model(), ConfigurationNetwork(PoissonDegree(5.0)))
        @test Set(Symbol.(ModelingToolkit.parameters(sysm.system))) ⊇ Set([:τ, :γ])
        @test_throws ArgumentError solve_epidemic(sysm; p = Dict(:β => 0.3, :γ => 0.1))   # unknown name
        @test_throws ArgumentError solve_epidemic(sysm; p = Dict(:ρ => 0.2, :τ => 0.3, :γ => 0.1))  # not a parameter
        @test_throws ArgumentError solve_epidemic(sysm; p = Dict(:seed_I => 0.2, :τ => 0.3, :γ => 0.1))  # the seed
        # SEIR and Expr rates
        syss = build_seir(pgf5, :σ, :τ, :γ)
        sols = solve_epidemic(syss; p = Dict(:σ => 0.2, :τ => 0.3, :γ => 0.1), tspan = (0.0, 300.0), saveat = 1.0, TOL...)
        refs = build_seir(pgf5, 0.2, 0.3, 0.1)
        solrs = solve_epidemic(refs; tspan = (0.0, 300.0), saveat = 1.0, TOL...)
        @test maximum(abs.(getcurve(syss, sols, :S) .- getcurve(refs, solrs, :S))) < 1e-10
        syse = edge_based(sir_model(τ = :(2 * a), γ = :γ), ConfigurationNetwork(PoissonDegree(5.0)))
        sole = solve_epidemic(syse; p = Dict(:a => 0.15, :γ => 0.1), tspan = (0.0, 30.0), saveat = 1.0, TOL...)
        @test getcurve(syse, sole, :S) ≈ getcurve(sysd, s1, :S) rtol = 1e-10
        # ErlangStage with a Symbol total rate used to fail with *(::Int64, ::Symbol)
        progE = expand_erlang_stages([ErlangStage(:I, 3, :γ; transmission_rate = :τ), DiseaseStage(:R)],
                                     [DiseaseTransition(:I, :R, :(3γ))])
        @test progE.transitions[1].rate == :(3 * γ)
        sysE = build_edge_system(StaticConfigurationModel(pgf5, progE))
        solE = solve_epidemic(sysE; p = Dict(:τ => 0.3, :γ => 0.1), tspan = (0.0, 60.0), saveat = 1.0, TOL...)
        numE = expand_erlang_stages([ErlangStage(:I, 3, 0.1; transmission_rate = 0.3), DiseaseStage(:R)],
                                    [DiseaseTransition(:I, :R, 0.3)])
        sysN = build_edge_system(StaticConfigurationModel(pgf5, numE))
        solN = solve_epidemic(sysN; tspan = (0.0, 60.0), saveat = 1.0, TOL...)
        @test maximum(abs.(getcurve(sysE, solE, :S) .- getcurve(sysN, solN, :S))) < 1e-10
        # the user's progression keeps its Symbols (usable as Dict keys, e.g. by NetworkOutbreaks)
        m = StaticConfigurationModel(pgf5, EBM._legacy_sir_model())
        build_edge_system(m)
        @test m.progression.stages[1].transmission_rate === :β
        # the clustered and multitype legacy entry points accept Symbol rates too; the dynamic one is
        # a migration error since WP29 (its 0.1 builder was not the MSV model: E05–E07)
        @test build_clustered_sir(clustered_poisson_pgf(1.0, 2.0), :τ, :γ) isa EdgeModelSystem
        @test_throws ArgumentError build_edge_system(DynamicConfigurationModel(pgf5, sir_model(), :η₁, :η₂))
        types = [:a, :b]
        pgfs = Dict(t => multivariate_poisson_pgf(types, Dict(:a => 2.5, :b => 2.5)) for t in types)
        @test (@test_deprecated build_edge_system(MultiTypeConfigurationModel(types = types, pgfs = pgfs,
                                                                               progression = sir_model()))) isa EdgeModelSystem
    end

    @testset "parameter defaults of the model are kept (0.1 kept Catalyst's; p overrides them)" begin
        # Regression (WP14 review): the lowering and the converters dropped parameter_defaults(cm),
        # so a Catalyst model with `@parameters τ = 0.3 γ = 0.1` failed with "Could not evaluate
        # value of parameter γ" where 0.1 solved it. NEC's instantiate and NodeBasedModels fill
        # missing values from the defaults, and an explicit p takes precedence.
        pgf5 = poisson_pgf(5.0)
        net = ConfigurationNetwork(PoissonDegree(5.0))
        rn = Catalyst.@reaction_network begin
            @parameters τ = 0.3 γ = 0.1
            τ, S + I --> 2I
            γ, I --> R
        end
        cm = contact_model(rn)
        @test parameter_defaults(cm) == Dict(:τ => 0.3, :γ => 0.1)
        span = (tspan = (0.0, 30.0), saveat = 1.0, TOL...)
        R30(sys; kw...) = getcurve(sys, solve_epidemic(sys; span..., kw...), :R)[end]
        ref = R30(build_sir(pgf5, 0.3, 0.1))                                     # 0.88057919
        ref_p = R30(build_sir(pgf5, 1 / 6, 0.1))
        ref_c = R30(build_sir(pgf5, 0.3, 0.1; form = :compact))
        clnet = ClusteredNetwork(PoissonDegree(1.0), PoissonDegree(2.0))
        ref_cl = R30(build_clustered_sir(clustered_poisson_pgf(1.0, 2.0), 0.3, 0.1))
        # a 0.1 progression whose rates are Catalyst's own parameters (the 0.1 behaviour)
        cps = Dict(Symbol(Symbolics.getname(q)) => q for q in Catalyst.parameters(rn))
        prog01 = DiseaseProgression([DiseaseStage(:I; transmission_rate = Symbolics.unwrap(cps[:τ])), DiseaseStage(:R)],
                                    [DiseaseTransition(:I, :R, Symbolics.unwrap(cps[:γ]))]; entry = :I)
        paths = [
            "edge_based(rn, net)" => (edge_based(rn, net), ref, ref_p),
            "edge_based(cm, net; form = :compact)" => (edge_based(cm, net; form = :compact), ref_c,
                                                       R30(build_sir(pgf5, 1 / 6, 0.1; form = :compact))),
            "edge_based(rn, ClusteredNetwork)" => (edge_based(rn, clnet), ref_cl,
                                                   R30(build_clustered_sir(clustered_poisson_pgf(1.0, 2.0), 1 / 6, 0.1))),
            "StaticConfigurationModel(pgf, cm)" => (build_edge_system(StaticConfigurationModel(pgf5, cm)), ref, ref_p),
            "StaticConfigurationModel(pgf, DiseaseProgression(cm))" =>
                (build_edge_system(StaticConfigurationModel(pgf5, DiseaseProgression(cm))), ref, ref_p),
            "0.1 progression with Catalyst parameters" =>
                (build_edge_system(StaticConfigurationModel(pgf5, prog01)), ref, ref_p),
        ]
        for (label, (sys, r, rp)) in paths
            @testset "$label" begin
                @test parameter_defaults(sys) == Dict(:τ => 0.3, :γ => 0.1)
                @test R30(sys) ≈ r rtol = 1e-9                                   # no p: the defaults
                @test R30(sys; p = Dict(:τ => 1 / 6)) ≈ rp rtol = 1e-9           # p overrides τ, γ stays 0.1
                @test R30(sys; p = Dict(:τ => 0.3, :γ => 0.1)) ≈ r rtol = 1e-9
                # the lifted parameters carry the defaults as ModelingToolkit defaults, so the
                # system also solves as a plain ODEProblem (as 0.1's did)
                prob = ODEProblem(sys.system, default_initial_conditions(sys), (0.0, 30.0))
                @test getcurve(sys, solve(prob; saveat = 1.0, TOL...), :R)[end] ≈ r rtol = 1e-9
            end
        end
        @test ref ≈ 0.8805791478 atol = 1e-8
        # the legacy type keeps the defaults on its (now symbolic) rates, and contact_model reads
        # them back; rates without a default keep their Symbols
        dp = DiseaseProgression(cm)
        @test !(dp.stages[1].transmission_rate isa Symbol)
        @test parameter_defaults(contact_model(dp)) == Dict(:τ => 0.3, :γ => 0.1)
        @test parameter_defaults(contact_model(prog01)) == Dict(:τ => 0.3, :γ => 0.1)
        @test DiseaseProgression(sir_model()).stages[1].transmission_rate === :τ
        partial = ContactModel(:partial; contacts = [Contact(:S, :I, :I, :τ)], transitions = [NodeTransition(:I, :R, :γ)],
                               defaults = Dict(:τ => 0.3))
        pp = DiseaseProgression(partial)
        @test pp.transitions[1].rate === :γ && !(pp.stages[1].transmission_rate isa Symbol)
        # user defaults on a NetworkEpiCore model, and an Expr rate (frequency-dependent contacts
        # become β/k̄ on the network): the default reaches the parameter inside the expression
        fd = ContactModel(:fd; contacts = [Contact(:S, :I, :I, :β)], transitions = [NodeTransition(:I, :R, :γ)],
                          convention = FrequencyDependent(), defaults = Dict(:β => 1.5, :γ => 0.1))
        sysfd = edge_based(fd, net)
        @test R30(sysfd) ≈ ref rtol = 1e-9                                       # β/5 = 0.3
        @test R30(sysfd; p = Dict(:β => 5 / 6)) ≈ ref_p rtol = 1e-9
        # a default without its parameter in p, with init: init's parameter values beat defaults
        sysu = edge_based(ContactModel(:u; contacts = [Contact(:S, :I, :I, :τ)], transitions = [NodeTransition(:I, :R, :γ)],
                                       defaults = Dict(:τ => 0.3, :γ => 0.1)), net)
        init = default_initial_conditions(sysu)
        τsym = only(q for q in ModelingToolkit.parameters(sysu.system) if Symbol(Symbolics.getname(q)) === :τ)
        init[τsym] = 1 / 6
        @test getcurve(sysu, solve_epidemic(sysu; init, span...), :R)[end] ≈ ref_p rtol = 1e-9
        # no default and no p: still an error (the message is ModelingToolkit's)
        @test_throws Exception solve_epidemic(edge_based(sir_model(), net); span...)
        # the model recorded in the metadata keeps its Symbols
        @test only(contacts(edge_based(rn, net).metadata[:model])).rate === :τ
    end

    @testset "E10/E26: parameter names and the names the assembler generates" begin
        # 0.1 named its seed parameter ρ (ρ_<type> for multitype models), which silently merged
        # with a user parameter of that name (E26); the 0.2 lift names the seeds seed_<X> (design
        # §A.3), so ρ is an ordinary name, and a name that would collide with a generated one is
        # refused loudly.
        pgf5 = poisson_pgf(5.0)
        @parameters ρ βp γp ρ_a
        ref = build_sir(pgf5, 0.3, 0.1)
        solref = solve_epidemic(ref; tspan = (0.0, 30.0), saveat = 1.0, TOL...)
        sρ = build_sir(pgf5, :ρ, :γ)                                              # merged with the seed in 0.1
        @test Set(Symbol.(ModelingToolkit.getname.(ModelingToolkit.parameters(sρ.system)))) == Set([:ρ, :γ, :seed_I, :seed_R])
        solρ = solve_epidemic(sρ; p = Dict(:ρ => 0.3, :γ => 0.1), tspan = (0.0, 30.0), saveat = 1.0, TOL...)
        @test getcurve(sρ, solρ, :S) ≈ getcurve(ref, solref, :S) rtol = 1e-10
        @test build_sir(pgf5, 0.3, ρ) isa EdgeModelSystem                          # a symbolic ρ as well
        @test build_sir(pgf5, βp, ρ; form = :compact) isa EdgeModelSystem
        sκ = build_sir(poisson_pgf(ρ), 0.3, 0.1)                                   # a PGF parameter named ρ
        solκ = solve_epidemic(sκ; p = Dict(ρ => 5.0), tspan = (0.0, 30.0), saveat = 1.0, TOL...)
        @test getcurve(sκ, solκ, :S) ≈ getcurve(ref, solref, :S) rtol = 1e-10
        @test_throws ArgumentError build_sir(pgf5, :t, :γ)                        # t is time
        @test_throws ArgumentError build_sir(pgf5, :θ, :γ)                        # a generated coordinate
        @test_throws ArgumentError build_sir(pgf5, :seed_I, :γ)                   # a seed parameter
        @test_throws ArgumentError build_sir(pgf5, :S, :γ)                        # a species
        rnρ = Catalyst.@reaction_network begin
            β, S + I --> 2I
            ρ, I --> R
        end
        @test edge_based(rnρ, ConfigurationNetwork(PoissonDegree(5.0))) isa EdgeModelSystem
        @test Set(Symbol.(ModelingToolkit.getname.(ModelingToolkit.parameters(build_sir(pgf5, βp, γp).system)))) ==
              Set([:βp, :γp, :seed_I, :seed_R])
        types = [:a, :b]
        pgfs = Dict(t => multivariate_poisson_pgf(types, Dict(:a => 2.5, :b => 2.5)) for t in types)
        mt(; kw...) = @test_deprecated build_edge_system(MultiTypeConfigurationModel(; types, pgfs, kw...))
        @test mt(progression = sir_model(τ = βp, γ = ρ_a)) isa EdgeModelSystem
        # a contact-matrix multiplier named like a 0.1 per-type seed parameter used to be merged
        # silently with that seed; now it is an ordinary parameter, settable with `p` (the (a, b)
        # multiplier matters: c = 0 and c = 1 give different epidemics, and c = 1 equals the default)
        sysc = mt(progression = sir_model(τ = 0.3, γ = 0.1), contact_matrix = Dict((:a, :b) => :ρ_a))
        @test Set(Symbol.(ModelingToolkit.getname.(ModelingToolkit.parameters(sysc.system)))) ==
              Set([:ρ_a, :seed_I_a, :seed_I_b, :seed_R_a, :seed_R_b])
        sys1 = mt(progression = sir_model(τ = 0.3, γ = 0.1))
        Send(sys, sol) = compartment(sys, sol, :S_a)[end] + compartment(sys, sol, :S_b)[end]
        solc1 = solve_epidemic(sysc; p = Dict(:ρ_a => 1.0), tspan = (0.0, 60.0), TOL...)
        solc0 = solve_epidemic(sysc; p = Dict(:ρ_a => 0.0), tspan = (0.0, 60.0), TOL...)
        sol1 = solve_epidemic(sys1; tspan = (0.0, 60.0), TOL...)
        @test Send(sysc, solc1) ≈ Send(sys1, sol1) rtol = 1e-8
        @test Send(sysc, solc0) > Send(sysc, solc1) + 1e-3
        # generated multitype names that collide (E26 B): an ArgumentError naming them, not an
        # opaque ModelingToolkit error
        types2 = [:a, :a_a]
        pgfs2 = Dict(t => multivariate_poisson_pgf(types2, Dict(:a => 2.5, :a_a => 2.5)) for t in types2)
        err = try
            build_edge_system(MultiTypeConfigurationModel(types = types2, pgfs = pgfs2, progression = sir_model(τ = 0.3, γ = 0.1)))
            nothing
        catch e
            e
        end
        @test err isa ArgumentError && occursin("not unique", sprint(showerror, err)) &&
              occursin("θ_a_a_a", sprint(showerror, err))
        # a stage named S next to another susceptible name (E26 C): the 0.1 builders shadowed the φ_S
        # observable; the assembler names the susceptible observables after the susceptible species
        progU = DiseaseProgression([DiseaseStage(:S; transmission_rate = 0.5), DiseaseStage(:R)],
                                   [DiseaseTransition(:S, :R, 0.25)]; susceptible = :U, entry = :S)
        sU = build_edge_system(StaticConfigurationModel(pgf5, progU))
        @test haskey(sU.observables, :U) && haskey(sU.observables, :φ_U) && haskey(sU.variables, :pop_S)
        solU = solve_epidemic(sU; tspan = (0.0, 20.0), saveat = 1.0, TOL...)
        @test compartment(sU, solU, :U) .+ compartment(sU, solU, :pop_S) .+ compartment(sU, solU, :pop_R) ≈
              ones(21) atol = 1e-9
        # realistic names with underscores are fine
        types3 = [:child, :adult, :child_adult]
        pgfs3 = Dict(t => multivariate_poisson_pgf(types3, Dict(u => 2.5 for u in types3)) for t in types3)
        @test (@test_deprecated build_edge_system(MultiTypeConfigurationModel(types = types3, pgfs = pgfs3,
                                                            progression = sir_model(τ = 0.3, γ = 0.1)))) isa EdgeModelSystem
    end

    @testset "initial keyword and kind dispatch" begin
        sys = build_sir(poisson_pgf(5.0), 0.3, 0.1)
        @test default_initial_conditions(sys; initial = SeedFraction(:I => 0.01)) ==
              default_initial_conditions(sys; seed_fraction = 0.01)
        @test default_initial_conditions(sys; initial = SeedFraction(:I => 0.01; default = :S)) ==
              default_initial_conditions(sys; seed_fraction = 0.01)
        @test default_initial_conditions(sys) == default_initial_conditions(sys; seed_fraction = 1e-3)
        # any node species may be seeded (the assembler places seeds in every species, design
        # §D.4; the 0.1 builders seeded only the entry state), e.g. immune nodes in R
        icR = default_initial_conditions(sys; initial = SeedFraction(:I => 0.01, :R => 0.2))
        @test icR[sys.variables[:pop_R]] ≈ 0.2 && icR[sys.variables[:pop_I]] ≈ 0.01
        solR = solve_epidemic(sys; init = icR, tspan = (0.0, 1.0), saveat = 1.0, TOL...)
        @test getcurve(sys, solR, :S)[1] ≈ 0.79 atol = 1e-12
        @test_throws ArgumentError default_initial_conditions(sys; initial = SeedFraction(:X => 0.01))   # not a species
        @test_throws ArgumentError default_initial_conditions(sys; initial = SeedFraction(:I => 0.01), seed_fraction = 0.01)
        @test_throws ArgumentError default_initial_conditions(sys; initial = SeedCount(:I => 10))   # needs N
        @test_throws ArgumentError default_initial_conditions(sys; initial = 0.01)
        seir = build_seir(poisson_pgf(5.0), 0.2, 0.3, 0.1)
        @test default_initial_conditions(seir; initial = SeedFraction(:E => 0.02)) ==
              default_initial_conditions(seir; seed_fraction = 0.02)
        icI = default_initial_conditions(seir; initial = SeedFraction(:I => 0.02))   # seeding I is allowed
        @test icI[seir.variables[:pop_I]] ≈ 0.02 && icI[seir.variables[:pop_E]] == 0
        @test_throws ArgumentError solve_epidemic(sys; init = default_initial_conditions(sys),
                                                  initial = SeedFraction(:I => 0.01))
        # a model with several entry states needs `initial` (the default seeds the unique entry)
        @test_throws ArgumentError default_initial_conditions(edge_based(twostrain_model(), ConfigurationNetwork(PoissonDegree(5.0))))
        # an unknown kind is refused (the assembler adds :assembled)
        odd = EdgeModelSystem(sys.system, sys.variables, sys.observables, Dict{Symbol,Any}(:kind => :unknown))
        @test_throws ArgumentError default_initial_conditions(odd)
    end

    @testset "scenario helpers: edge_based(sc), solve_epidemic(sys, sc), model_curves" begin
        sc = scenario(:sir_pois5)
        sys = edge_based(sc)
        sol = solve_epidemic(sys, sc; TOL...)
        @test sol.t == collect(sc.tgrid)
        mc = model_curves(sys, sol; t = sc.tgrid, label = "edge-based")
        @test mc isa ModelCurves
        @test mc.representation === :edge_based && mc.label == "edge-based"
        @test Set(keys(mc.values)) == Set([:S, :I, :R, :infectious, :cumulative])
        @test mc[:S] .+ mc[:I] .+ mc[:R] ≈ ones(length(sc.tgrid)) atol = 1e-10
        # the accumulator is integrated with the field (§J.8), so it equals 1 − S to the solver
        # tolerance (reltol 1e-10), not to rounding as when 0.1 computed R algebraically
        @test mc[:cumulative] ≈ 1 .- mc[:S] atol = 1e-10
        @test mc[:cumulative][1] ≈ 0.01 atol = 1e-12                             # the seeds are infected
        @test mc[:infectious] == mc[:I]
        # the ODE's final size equals the registry's expected value (NEC's fixed point, 0.8002)
        long = solve_epidemic(sys; p = sc.params, initial = sc.initial, tspan = (0.0, 600.0), TOL...)
        @test 1 - compartment(sys, long, :S)[end] ≈ sc.expected[:final_size] atol = 1e-7
        @test sc.expected[:final_size] ≈ 0.8002039676767994 atol = 1e-8           # EoN, golden/eon
        # a SEIR scenario seeds E
        sce = scenario(:seir_pois5)
        syse = edge_based(sce)
        sole = solve_epidemic(syse, sce; TOL...)
        mce = model_curves(syse, sole; t = sce.tgrid)
        @test Set(keys(mce.values)) == Set([:S, :E, :I, :R, :infectious, :cumulative])
        @test mce[:E][1] ≈ 0.01 atol = 1e-12
        # a legacy multitype system is forwarded to the multitype lift of its stratified model: it
        # records that model, and its default seeding is the 0.1 rule (ρ of every type in its entry
        # state), while `initial` takes seeds by species
        types = [:a, :b]
        pgfs = Dict(t => multivariate_poisson_pgf(types, Dict(:a => 2.5, :b => 2.5)) for t in types)
        mts = @test_deprecated build_edge_system(MultiTypeConfigurationModel(types = types, pgfs = pgfs,
                                                                            progression = sir_model(τ = 0.3, γ = 0.1)))
        @test mts.metadata[:kind] === :assembled && mts.metadata[:closure] === :multitype
        @test default_initial_conditions(mts) ==
              default_initial_conditions(mts; initial = SeedFraction(:I_a => 0.5e-3, :I_b => 0.5e-3))
        @test_throws ArgumentError default_initial_conditions(mts; initial = SeedFraction(:I => 0.01))   # no species I
        mtsol = solve_epidemic(mts; tspan = (0.0, 10.0), saveat = 1.0)
        mcm = model_curves(mts, mtsol)
        @test haskey(mcm.values, :S_a) && haskey(mcm.values, :I_b) && haskey(mcm.values, :cumulative)
        @test mcm[:S_a] ≈ compartment(mts, mtsol, :S_a)
    end

    @testset "factories are one-liners over edge_based" begin
        for d in (poisson_pgf(5.0), PoissonDegree(5.0), ConfigurationNetwork(PoissonDegree(5.0)))
            sys = build_sir(d, 1 / 6, 1 / 4)
            @test sys.metadata[:kind] === :assembled && sys.metadata[:model] isa ContactModel
        end
        a = build_sir(poisson_pgf(5.0), 1 / 6, 1 / 4)
        b = build_sir(PoissonDegree(5.0), 1 / 6, 1 / 4)
        sa = solve_epidemic(a; tspan = (0.0, 60.0), saveat = 1.0, TOL...)
        sb = solve_epidemic(b; tspan = (0.0, 60.0), saveat = 1.0, TOL...)
        @test getcurve(a, sa, :S) ≈ getcurve(b, sb, :S) rtol = 1e-12
        c1 = build_clustered_sir(clustered_poisson_pgf(1.0, 2.0), 0.6, 1.0)
        c2 = build_clustered_sir(ClusteredNetwork(PoissonDegree(1.0), PoissonDegree(2.0)), 0.6, 1.0)
        s1 = solve_epidemic(c1; tspan = (0.0, 20.0), saveat = 1.0, TOL...)
        s2 = solve_epidemic(c2; tspan = (0.0, 20.0), saveat = 1.0, TOL...)
        @test getcurve(c1, s1, :S) ≈ getcurve(c2, s2, :S) rtol = 1e-12
        @test c2.metadata[:network] isa ClusteredNetwork
        @test generate_sir === build_sir && generate_seir === build_seir
        @test_throws ArgumentError build_sir(42, 0.3, 0.1)
    end

    @testset "module docstring example runs (E10: it used to fail)" begin
        codes = String[]
        walk(x) = x isa Markdown.Code ? push!(codes, x.code) :
                  hasproperty(x, :content) ? foreach(walk, x.content) : nothing
        walk(Base.Docs.doc(EdgeBasedModels))
        code = only(filter(c -> occursin("edge_based(", c), codes))
        m = Module(:DocExample)
        Core.eval(m, :(using EdgeBasedModels))
        Base.include_string(m, code)
        @test Core.eval(m, :R30) ≈ 0.8806 atol = 1e-4
        sysF, solF = Core.eval(m, :sysF), Core.eval(m, :solF)
        @test compartment(sysF, solF, :R)[end] ≈ Core.eval(m, :R30) rtol = 1e-6
    end

    @testset "package hygiene (0.2)" begin
        project = TOML.parsefile(joinpath(pkgdir(EdgeBasedModels), "Project.toml"))
        @test VersionNumber(project["version"]) == v"0.2.0"
        @test haskey(project["deps"], "NetworkEpiCore")
        @test project["sources"]["NetworkEpiCore"]["path"] == "../NetworkEpiCore.jl"
        for name in ("Catalyst", "NodeBasedModels", "Graphs", "JSON3", "OrdinaryDiffEq")
            @test !haskey(project["deps"], name)
        end
        for name in ("NetworkOutbreaks", "Catalyst", "Graphs", "StableRNGs", "Statistics", "JSON3")
            @test haskey(project["extras"], name)
            @test name in project["targets"]["test"]
        end
        # §G.1: the module file includes every source file, the stubs of later work packages too
        # (src/system.jl is WP29's)
        srcdir = joinpath(pkgdir(EdgeBasedModels), "src")
        modfile = read(joinpath(srcdir, "EdgeBasedModels.jl"), String)
        included = Set{String}(m.captures[1] for m in eachmatch(r"include\(\"([^\"]+)\"\)", modfile))
        files = Set{String}(relpath(joinpath(root, f), srcdir) for (root, _, fs) in walkdir(srcdir)
                            for f in fs if endswith(f, ".jl"))
        delete!(files, "EdgeBasedModels.jl")
        @test files == included
        @test "system.jl" in included
    end
end
