# The NetworkOutbreaks adapter through `contact_model` (WP14; DESIGN_NetworkEpiCore.md §A.5, §G.2).
#
# Owner: WP14. Acceptance: `OutbreakModel(contact_model(prog), p)` equals the old
# NetworkOutbreaks EdgeBasedModels extension's `OutbreakModel(prog, p)` field by field. This suite
# pins that output (frozen from the old extension) and checks three things against it:
#
# 1. the §A.5 image of `contact_model(prog)`, built here with NetworkOutbreaks' public
#    constructors (each Contact(s, J, X, τ) → OutbreakTransition(s, X, τ, :infection; via = [J]),
#    each node transition → :spontaneous, infectors flagged), i.e. what the converter hands over;
# 2. the old extension itself, while it exists (WP16 deletes it);
# 3. NetworkOutbreaks' own `OutbreakModel(::ContactModel, p)`, once WP16 provides it.
#
# It also carries the "NetworkOutbreaks integration" check of the legacy core suite, ported to
# `contact_model`, and a stochastic check that the edge-based ODE of the same model is the
# large-N limit of the simulation (design §E.2 conventions).

using EdgeBasedModels
using NetworkEpiCore
using Test
using Graphs
using StableRNGs
using Statistics: mean, std
import NetworkOutbreaks as NO

const EBM = EdgeBasedModels

# The §A.5 image of a ContactModel with parameter values p.
function outbreak_image(cm::ContactModel, p)
    inst = instantiate(cm, p)
    trs = NO.OutbreakTransition[]
    for c in contacts(inst)
        push!(trs, NO.OutbreakTransition(c.recipient, c.product, c.rate, :infection; via = [c.infector]))
    end
    for t in node_transitions(inst)
        push!(trs, NO.OutbreakTransition(t.from, t.to, t.rate, :spontaneous))
    end
    infectors = Set(c.infector for c in contacts(inst) if c.rate > 0)
    return NO.OutbreakModel(species_names(inst), [X in infectors for X in species_names(inst)], trs;
                            name = :ebm_outbreak)
end

fields(m::NO.OutbreakModel) = (compartments = m.compartments, infectious = m.infectious,
    transitions = [(t.from, t.to, t.rate, t.type, t.via) for t in m.transitions])

old_adapter_available() = hasmethod(NO.OutbreakModel, Tuple{DiseaseProgression, Dict{Symbol,Float64}})
new_adapter_available() = hasmethod(NO.OutbreakModel, Tuple{ContactModel, Dict{Symbol,Float64}})

# (legacy progression, parameters, the old extension's output, frozen)
const CORPUS = [
    ("SIR, numeric rates", DiseaseProgression(sir_model(τ = 1.5, γ = 1.0)), Dict{Symbol,Float64}(),
     (compartments = [:S, :I, :R], infectious = [false, true, false],
      transitions = [(:S, :I, 1.5, :infection, [:I]), (:I, :R, 1.0, :spontaneous, Symbol[])])),
    ("SIR, Symbol rates", DiseaseProgression(sir_model()), Dict(:τ => 1.5, :γ => 1.0),
     (compartments = [:S, :I, :R], infectious = [false, true, false],
      transitions = [(:S, :I, 1.5, :infection, [:I]), (:I, :R, 1.0, :spontaneous, Symbol[])])),
    ("SEIR", DiseaseProgression(seir_model(τ = 0.3, σ = 0.5, γ = 0.2)), Dict{Symbol,Float64}(),
     (compartments = [:S, :E, :I, :R], infectious = [false, false, true, false],
      transitions = [(:S, :E, 0.3, :infection, [:I]), (:E, :I, 0.5, :spontaneous, Symbol[]),
                     (:I, :R, 0.2, :spontaneous, Symbol[])])),
    ("SEIR, transmitting E", DiseaseProgression([DiseaseStage(:E; transmission_rate = :τE), DiseaseStage(:I; transmission_rate = :τ),
                                                 DiseaseStage(:R)],
                                                [DiseaseTransition(:E, :I, :σ), DiseaseTransition(:I, :R, :γ)]; entry = :E),
     Dict(:τE => 0.05, :τ => 0.3, :σ => 0.5, :γ => 0.2),
     (compartments = [:S, :E, :I, :R], infectious = [false, true, true, false],
      transitions = [(:S, :E, 0.05, :infection, [:E]), (:S, :E, 0.3, :infection, [:I]),
                     (:E, :I, 0.5, :spontaneous, Symbol[]), (:I, :R, 0.2, :spontaneous, Symbol[])])),
    ("SIS", DiseaseProgression(sis_model(τ = 0.4, γ = 1.0)), Dict{Symbol,Float64}(),
     (compartments = [:S, :I], infectious = [false, true],
      transitions = [(:S, :I, 0.4, :infection, [:I]), (:I, :S, 1.0, :spontaneous, Symbol[])])),
    ("two infectious stages", DiseaseProgression([DiseaseStage(:I1; transmission_rate = 0.4), DiseaseStage(:I2; transmission_rate = 0.1),
                                                  DiseaseStage(:R)],
                                                 [DiseaseTransition(:I1, :I2, 0.5), DiseaseTransition(:I2, :R, 0.25)]; entry = :I1),
     Dict{Symbol,Float64}(),
     (compartments = [:S, :I1, :I2, :R], infectious = [false, true, true, false],
      transitions = [(:S, :I1, 0.4, :infection, [:I1]), (:S, :I1, 0.1, :infection, [:I2]),
                     (:I1, :I2, 0.5, :spontaneous, Symbol[]), (:I2, :R, 0.25, :spontaneous, Symbol[])])),
]

@testset "NetworkOutbreaks adapter through contact_model" begin
    @testset "field-by-field equality: $label" for (label, prog, p, expected) in CORPUS
        cm = contact_model(prog)
        @test fields(outbreak_image(cm, p)) == expected
        if old_adapter_available()
            @test fields(NO.OutbreakModel(prog, p)) == expected
        else
            @info "the NetworkOutbreaks EdgeBasedModels extension is gone (WP16); comparing with the frozen output"
        end
        if new_adapter_available()
            @test fields(NO.OutbreakModel(cm, p)) == expected
        end
        # the converter loses nothing: back to the legacy type
        back = DiseaseProgression(cm)
        @test [s.name for s in back.stages] == [s.name for s in prog.stages]
        @test back.entry === prog.entry
    end

    if old_adapter_available()
        @testset "the old extension and the image simulate identically" begin
            prog = DiseaseProgression(sir_model())
            p = Dict(:τ => 1.5, :γ => 1.0)
            g = random_regular_graph(400, 6; rng = StableRNG(7))
            runs(model) = [NO.final_size(t) for t in NO.simulate_ensemble(
                NO.OutbreakSpec(model = model, network = g, initial = NO.SeedFraction(:I => 0.05), tspan = (0.0, 60.0));
                nsims = 8, seed = 123, algorithm = NO.NextReaction()).trajectories]
            @test runs(NO.OutbreakModel(prog, p)) == runs(outbreak_image(contact_model(prog), p))
        end
    end

    # Ported from the legacy core suite (00_legacy_core.jl, "NetworkOutbreaks integration").
    @testset "NetworkOutbreaks integration" begin
        model = outbreak_image(contact_model(DiseaseProgression(sir_model())), Dict(:τ => 1.5, :γ => 1.0))
        @test :S in model.compartments && :I in model.compartments && :R in model.compartments
        @test any(t -> t.from == :S && t.to == :I && t.type == :infection, model.transitions)
        g = random_regular_graph(400, 6; rng = StableRNG(7))
        spec = NO.OutbreakSpec(model = model, network = g, initial = NO.SeedFraction(:I => 0.05),
                               tspan = (0.0, 60.0))
        ens = NO.simulate_ensemble(spec; nsims = 8, seed = 123)
        fs = mean(NO.final_size(t; recovered = :R) for t in ens.trajectories)
        @test 0.10 < fs <= 1.0
    end

    @testset "the edge-based ODE is the large-N limit of the simulation (SIR, Poisson(5))" begin
        # Design §E.2 anchors (τ = 1/6, γ = 1/4, R₀ = 2), 1% seeds in I, t ∈ [0, 60]. A fresh
        # Erdős–Rényi graph G(N, 5/(N−1)) per run (graph r from stable_rng(base + r), run r from
        # stable_rng(base + 2^32 + r)), NextReaction, conditioned on a major outbreak (cumulative
        # incidence minus seeds ≥ 0.05 N).
        N, runs, base = 10_000, 100, 20260926
        cm = sir_model()
        p = Dict(:τ => 1 / 6, :γ => 1 / 4)
        sys = edge_based(cm, ConfigurationNetwork(PoissonDegree(5.0)))
        tgrid = 0.0:1.0:60.0
        sol = solve_epidemic(sys; p, initial = SeedFraction(:I => 0.01), tspan = (0.0, 60.0), saveat = tgrid,
                             reltol = 1e-10, abstol = 1e-12)
        R_eb = compartment(sys, sol, :R)
        I_eb = compartment(sys, sol, :I)
        model = outbreak_image(cm, p)
        iR, iI = model.index_of[:R], model.index_of[:I]
        R_runs, I_runs, finals = Vector{Float64}[], Vector{Float64}[], Float64[]
        for r in 1:runs
            g = erdos_renyi(N, 5 / (N - 1); rng = NO.stable_rng(base + r))
            spec = NO.OutbreakSpec(model = model, network = g, initial = NO.SeedFraction(:I => 0.01),
                                   tspan = (0.0, 60.0))
            traj = NO.simulate(spec; algorithm = NO.NextReaction(), seed = base + 2^32 + r)
            fin = NO.final_size(traj)
            fin - 0.01 >= 0.05 || continue                      # MajorOutbreak(0.05)
            push!(finals, fin)
            push!(R_runs, [traj(t)[iR] / N for t in tgrid])
            push!(I_runs, [traj(t)[iI] / N for t in tgrid])
        end
        n = length(finals)
        @test n >= 0.95runs                                    # P(major) ≈ 1 with 100 seeds
        R_mean = mean(R_runs)
        I_mean = mean(I_runs)
        se_final = std(finals) / sqrt(n)
        D_R = maximum(abs.(R_mean .- R_eb))
        D_I = maximum(abs.(I_mean .- I_eb))
        @info "EB vs NetworkOutbreaks (N = $N, $n of $runs runs major)" D_R D_I mean(finals) se_final R_eb[end]
        # Monte Carlo SE of a mean curve here is ≲ 2e-3; the finite-N bias of G(N, p) is O(1/N).
        @test D_R < 0.01
        @test D_I < 0.01
        @test abs(mean(finals) - R_eb[end]) < 4se_final + 0.005
    end
end
