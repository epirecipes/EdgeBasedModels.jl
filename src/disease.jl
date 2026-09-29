# Legacy disease-progression types (EdgeBasedModels 0.1). In 0.2 the model object is
# NetworkEpiCore's `ContactModel`; these types are kept, with converters both ways
# (`contact_model(prog)` and `DiseaseProgression(cm)`, src/compat.jl), and every builder accepts
# them through `contact_model`.

"""
    DiseaseStage(name; transmission_rate = 0)

A non-susceptible stage of a legacy [`DiseaseProgression`](@ref): a node in this stage transmits
to each susceptible neighbour at the per-contact rate `transmission_rate` (0: not infectious).
"""
struct DiseaseStage
    name::Symbol
    transmission_rate
end

DiseaseStage(name::Symbol; transmission_rate = 0) = DiseaseStage(name, transmission_rate)

"""
    DiseaseTransition(source, target, rate)

A node transition `source → target` at per-capita `rate` in a legacy
[`DiseaseProgression`](@ref); `target` may be the susceptible state (SIS-type models).
"""
struct DiseaseTransition
    source::Symbol
    target::Symbol
    rate
end

"""
    DiseaseProgression(stages, transitions = DiseaseTransition[]; susceptible = :S, entry = nothing)
    DiseaseProgression(cm::ContactModel)

The legacy (EdgeBasedModels 0.1) disease model: one susceptible state, the stages a node passes
through after infection, and the transitions between them. Every transmission puts the newly
infected node in the single `entry` stage (inferred when there is exactly one stage without
incoming transitions).

`DiseaseProgression(cm)` converts a NetworkEpiCore `ContactModel` (see src/compat.jl); it throws
for what this type cannot express: branching at infection (several entry states), several
susceptible classes, removals `X → ∅`, exits out of the susceptible class, layered contacts and
contacts whose recipient is not susceptible. The inverse is `contact_model(prog)`.

This type has no field for parameter defaults; it keeps them the way 0.1 did (Catalyst's
`@parameters τ = 0.3`), as default values carried by symbolic rate parameters. So a rate of `cm`
that uses a parameter with a `parameter_defaults(cm)` entry becomes the symbolic expression of
that rate, whose parameters carry their defaults (and `build_edge_system` solves without `p`),
while the other rates keep their Symbols and Exprs.
"""
struct DiseaseProgression
    susceptible::Symbol
    entry::Symbol
    stages::Vector{DiseaseStage}
    transitions::Vector{DiseaseTransition}
end

function DiseaseProgression(
    stages::Vector{DiseaseStage},
    transitions::Vector{DiseaseTransition} = DiseaseTransition[];
    susceptible::Symbol = :S,
    entry::Union{Nothing, Symbol} = nothing,
)
    isempty(stages) && throw(ArgumentError("at least one non-susceptible stage is required"))

    names = [stage.name for stage in stages]
    length(unique(names)) == length(names) ||
        throw(ArgumentError("stage names must be unique"))
    susceptible in names &&
        throw(ArgumentError("susceptible state $(susceptible) must not be repeated in stages"))

    transition_names = Set(names)
    allowed_targets = union(transition_names, Set([susceptible]))
    for transition in transitions
        transition.source in transition_names ||
            throw(ArgumentError("unknown transition source $(transition.source)"))
        transition.target in allowed_targets ||
            throw(ArgumentError("unknown transition target $(transition.target)"))
    end

    inferred_entry = isnothing(entry) ? infer_entry(names, transitions) : entry
    inferred_entry in transition_names ||
        throw(ArgumentError("entry state $(inferred_entry) must be one of the declared stages"))

    return DiseaseProgression(susceptible, inferred_entry, stages, transitions)
end

# --- Legacy canned progressions ---------------------------------------------------------------
#
# In 0.2 the exported `sir_model`, `seir_model`, `sis_model` and `sirs_model` are NetworkEpiCore's
# (they return a `ContactModel`, with per-contact rate τ). These are the EdgeBasedModels 0.1
# factories that returned a `DiseaseProgression` (with β the per-contact rate); they are reachable
# through the deprecated `edge_sir_model` & co. and through `DiseaseProgression(sir_model())`.

function _legacy_sir_model(; β = :β, γ = :γ, susceptible::Symbol = :S)
    return DiseaseProgression(
        [
            DiseaseStage(:I; transmission_rate = β),
            DiseaseStage(:R; transmission_rate = 0),
        ],
        [DiseaseTransition(:I, :R, γ)];
        susceptible = susceptible,
        entry = :I,
    )
end

function _legacy_seir_model(; σ = :σ, β = :β, γ = :γ, susceptible::Symbol = :S)
    return DiseaseProgression(
        [
            DiseaseStage(:E; transmission_rate = 0),
            DiseaseStage(:I; transmission_rate = β),
            DiseaseStage(:R; transmission_rate = 0),
        ],
        [
            DiseaseTransition(:E, :I, σ),
            DiseaseTransition(:I, :R, γ),
        ];
        susceptible = susceptible,
        entry = :E,
    )
end

function _legacy_sis_model(; β = :β, γ = :γ, susceptible::Symbol = :S)
    return DiseaseProgression(
        [DiseaseStage(:I; transmission_rate = β)],
        [DiseaseTransition(:I, susceptible, γ)];
        susceptible = susceptible,
        entry = :I,
    )
end

function _legacy_sirs_model(; β = :β, γ = :γ, ε = :ε, susceptible::Symbol = :S)
    return DiseaseProgression(
        [
            DiseaseStage(:I; transmission_rate = β),
            DiseaseStage(:R; transmission_rate = 0),
        ],
        [
            DiseaseTransition(:I, :R, γ),
            DiseaseTransition(:R, susceptible, ε),
        ];
        susceptible = susceptible,
        entry = :I,
    )
end

# n·rate for the Erlang sub-stages. Numbers and symbolic expressions multiply as before; a Symbol
# or Expr rate (a named parameter, as in `ErlangStage(:I, 3, :γ)`) becomes the Expr `n * γ`
# through NetworkEpiCore's `rate_mul`, which the builders turn into parameters (`as_parameter`)
# and NetworkOutbreaks evaluates by name, instead of failing with `*(::Int, ::Symbol)`
# (verified issue E10).
_scale_rate(n::Integer, r::Union{Symbol,Expr}) = rate_mul(n, r)
_scale_rate(n::Integer, r) = n * r

function infer_entry(stage_names::Vector{Symbol}, transitions::Vector{DiseaseTransition})
    sources = Set(transition.source for transition in transitions)
    targets = Set(transition.target for transition in transitions)
    candidates = [name for name in stage_names if !(name in targets)]

    if length(candidates) == 1
        return only(candidates)
    end

    if isempty(transitions)
        return first(stage_names)
    end

    length(candidates) == 0 &&
        throw(ArgumentError("could not infer an entry stage because the transition graph is cyclic"))

    throw(ArgumentError("could not infer a unique entry stage; pass entry = :YourStage"))
end

"""
    ErlangStage(name, n_substages, total_rate; transmission_rate=0)

Create an Erlang-distributed stage with `n_substages` sub-stages.
Each sub-stage has rate `n_substages * total_rate`, giving:
- Mean sojourn time: 1/total_rate
- CV: 1/√n_substages
- Distribution: Erlang(n_substages, n_substages * total_rate)
"""
struct ErlangStage
    name::Symbol
    n_substages::Int
    total_rate       # γ: the overall rate (mean sojourn = 1/γ)
    transmission_rate  # β for this stage (0 if non-infectious)
end

ErlangStage(name::Symbol, n::Int, rate; transmission_rate = 0) =
    ErlangStage(name, n, rate, transmission_rate)

"""
    GammaApproxStage(name, mean_sojourn, cv; transmission_rate=0)

Create a stage approximating a gamma distribution with given mean and CV.
Chooses n = round(1/cv²) sub-stages to match the target CV.
"""
function GammaApproxStage(name::Symbol, mean_sojourn, cv; transmission_rate = 0)
    cv > 0 || throw(ArgumentError("cv must be positive"))
    n = max(1, round(Int, 1 / cv^2))
    rate = 1 / mean_sojourn
    ErlangStage(name, n, rate; transmission_rate = transmission_rate)
end

"""
    expand_erlang_stages(stages, transitions; susceptible, entry)

Expand any `ErlangStage` entries into chains of `DiseaseStage` + `DiseaseTransition`.
Returns a `DiseaseProgression` with all stages expanded.

An ErlangStage(:I, 3, γ; transmission_rate=β) expands to:
- Stages: I_1(β), I_2(β), I_3(β)
- Transitions: I_1 →(3γ) I_2 →(3γ) I_3
- Any existing transition FROM :I is redirected FROM :I_3 (last sub-stage)
- Any existing transition TO :I is redirected TO :I_1 (first sub-stage)
"""
function expand_erlang_stages(
    stages::Vector,
    transitions::Vector{DiseaseTransition} = DiseaseTransition[];
    susceptible::Symbol = :S,
    entry::Union{Nothing, Symbol} = nothing,
)
    expanded_stages = DiseaseStage[]
    expanded_transitions = DiseaseTransition[]

    # Map original name → (first_sub, last_sub) for redirect
    name_map_first = Dict{Symbol, Symbol}()
    name_map_last = Dict{Symbol, Symbol}()

    for stage in stages
        if stage isa ErlangStage
            n = stage.n_substages
            sub_rate = _scale_rate(n, stage.total_rate)  # each sub-stage rate

            sub_names = Symbol[]
            for i in 1:n
                sub_name = Symbol(stage.name, "_", i)
                push!(sub_names, sub_name)
                push!(expanded_stages, DiseaseStage(sub_name; transmission_rate = stage.transmission_rate))
            end

            # Chain transitions between sub-stages
            for i in 1:(n-1)
                push!(expanded_transitions, DiseaseTransition(sub_names[i], sub_names[i+1], sub_rate))
            end

            name_map_first[stage.name] = first(sub_names)
            name_map_last[stage.name] = last(sub_names)
        elseif stage isa DiseaseStage
            push!(expanded_stages, stage)
            name_map_first[stage.name] = stage.name
            name_map_last[stage.name] = stage.name
        else
            throw(ArgumentError("unknown stage type: $(typeof(stage))"))
        end
    end

    # Redirect existing transitions
    for tr in transitions
        new_source = get(name_map_last, tr.source, tr.source)
        new_target = get(name_map_first, tr.target, tr.target)
        push!(expanded_transitions, DiseaseTransition(new_source, new_target, tr.rate))
    end

    # Redirect entry
    actual_entry = if !isnothing(entry)
        get(name_map_first, entry, entry)
    else
        nothing
    end

    DiseaseProgression(expanded_stages, expanded_transitions;
                       susceptible = susceptible, entry = actual_entry)
end
