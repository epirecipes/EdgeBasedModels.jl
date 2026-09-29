# Golden cases: the dynamic fixed-degree (neighbour exchange) edge-based lift.
# Owner: WP21 (DESIGN_NetworkEpiCore.md, section G.2). These replace the Phase-0 goldens of the legacy
# Volz-Meyers-style DynamicConfigurationModel builder (verified issues E05, E06, E07), which WP21 replaced
# by the Miller-Slim-Volz DFD lift `edge_based(model, DynamicNetwork(base, NeighbourExchange(η)))`
# (src/lift/dynamic.jl). The base network and rates are those of the canonical sweep :sir_ne_reg6_eta*
# (section E.3): 6-regular, τ = 1/12, γ = 1/4, seed ρ = 0.01 in the entry state; the Poisson cases use
# the anchors of section E.2 on Poisson(5).

using EdgeBasedModels

const τ = 1 / 12
const γ = 1 / 4
const σ = 1 / 5
const ρ = 0.01

const VALIDATION = "Validated in test/suites/dynamic.jl: the field is the Miller-Slim-Volz DFD field (a symbolic " *
                   "semiconjugacy from a hand transcription), η = 0 is the static lift, and trajectories agree with " *
                   "NetworkOutbreaks' neighbour-exchange process (N = 5000, fresh graph per run) within D∞ < 0.01."

function dynamic_case(name, description, model, degrees, η; notes, setup = Dict{String, Any}())
    return GoldenCase("dynamic", name; description = description, issues = String[], notes = notes,
        run = () -> edge_system_trajectory(
            edge_based(model, DynamicNetwork(degrees, NeighbourExchange(η)));
            T = 100, seed_fraction = ρ,
            setup = merge(Dict{String, Any}("network" => string(degrees), "eta" => η), setup)))
end

legacy_note(issues) = "Replaces the legacy golden of this name, which froze the defective 0.1 builder ($(issues)). "

[
    dynamic_case("dynamic_sir_reg6_eta0",
        "DFD lift, SIR on 6-regular, τ = 1/12, γ = 1/4, η = 0 (the static network), seed ρ = 0.01 in I, t = 0:1:100",
        sir_model(; τ, γ), RegularDegree(6), 0.0;
        notes = legacy_note("E06") * "At η = 0 the θ, φ and pop trajectories are those of the static lift. " * VALIDATION,
        setup = Dict("tau" => τ, "gamma" => γ)),
    dynamic_case("dynamic_sir_reg6_eta01",
        "DFD lift, SIR on 6-regular, τ = 1/12, γ = 1/4, η = 0.1 (:sir_ne_reg6_eta01), seed ρ = 0.01 in I, t = 0:1:100",
        sir_model(; τ, γ), RegularDegree(6), 0.1; notes = VALIDATION,
        setup = Dict("tau" => τ, "gamma" => γ)),
    dynamic_case("dynamic_sir_reg6_eta1",
        "DFD lift, SIR on 6-regular, τ = 1/12, γ = 1/4, η = 1 (:sir_ne_reg6_eta1), seed ρ = 0.01 in I, t = 0:1:100",
        sir_model(; τ, γ), RegularDegree(6), 1.0;
        notes = legacy_note("E05, E06") * "R∞ = 0.74694 (NetworkOutbreaks' DFD reference). " * VALIDATION,
        setup = Dict("tau" => τ, "gamma" => γ)),
    dynamic_case("dynamic_seir_reg6_eta1",
        "DFD lift, SEIR on 6-regular, σ = 1/5, τ = 1/12, γ = 1/4, η = 1, seed ρ = 0.01 in E, t = 0:1:100",
        seir_model(; τ, σ, γ), RegularDegree(6), 1.0;
        notes = legacy_note("E05, E06, E07: SEIR was an SIR model with recovery rate σ") * VALIDATION,
        setup = Dict("tau" => τ, "sigma" => σ, "gamma" => γ)),
    dynamic_case("dynamic_seair_pois5_eta1",
        "DFD lift, SEAIR on Poisson(5), τI = 1/6, τA = 1/12, p = 0.6, σ = 1/5, γ = 1/4, η = 1, seed ρ = 0.01 in E, t = 0:1:100",
        seair_model(; τI = 1 / 6, τA = 1 / 12, p = 0.6, σ, γ), PoissonDegree(5.0), 1.0;
        notes = "Branching at infection and two infectors. " * VALIDATION,
        setup = Dict("tauI" => 1 / 6, "tauA" => 1 / 12, "p" => 0.6, "sigma" => σ, "gamma" => γ)),
    dynamic_case("dynamic_sirv_pois5_eta1",
        "DFD lift, SIR + vaccination S → V on Poisson(5), τ = 1/6, γ = 1/4, ν = 0.02, η = 1, seed ρ = 0.01 in I, t = 0:1:100",
        sirv_model(; τ = 1 / 6, γ, ν = 0.02), PoissonDegree(5.0), 1.0;
        notes = "An exit out of S (the survival factor ξ). " * VALIDATION,
        setup = Dict("tau" => 1 / 6, "gamma" => γ, "nu" => 0.02)),
]
