struct DiseaseStage
    name::Symbol
    transmission_rate
end

DiseaseStage(name::Symbol; transmission_rate = 0) = DiseaseStage(name, transmission_rate)

struct DiseaseTransition
    source::Symbol
    target::Symbol
    rate
end

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

function sir_model(; β = :β, γ = :γ, susceptible::Symbol = :S)
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

function seir_model(; σ = :σ, β = :β, γ = :γ, susceptible::Symbol = :S)
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

function sis_model(; β = :β, γ = :γ, susceptible::Symbol = :S)
    return DiseaseProgression(
        [DiseaseStage(:I; transmission_rate = β)],
        [DiseaseTransition(:I, susceptible, γ)];
        susceptible = susceptible,
        entry = :I,
    )
end

"""
    sirs_model(; β=:β, γ=:γ, ε=:ε, susceptible=:S)

SIRS disease progression: S → I → R → S, where ε is the rate of waning immunity.

Note: this factory produces the canonical SIRS [`DiseaseProgression`] for API
parity with `NodeBasedModels.sirs_model`. The Miller EBCM formulation does not
yet support re-susceptibilisation, so `build_edge_system` will currently raise an
error on a SIRS model. Use `NodeBasedModels.jl` for SIRS dynamics on networks.
"""
function sirs_model(; β = :β, γ = :γ, ε = :ε, susceptible::Symbol = :S)
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

function progression_from_catalyst(
    reaction_system::Catalyst.ReactionSystem;
    susceptible::Symbol = :S,
    transmission_rates = Dict{Symbol, Any}(),
    entry::Union{Nothing, Symbol} = nothing,
)
    stages = DiseaseStage[]
    stage_names = Symbol[]

    for specie in Catalyst.species(reaction_system)
        symbol = species_symbol(specie)
        symbol == susceptible && continue  # susceptible is implicit, not a stage
        push!(stage_names, symbol)
        push!(stages, DiseaseStage(symbol; transmission_rate = get(transmission_rates, symbol, 0)))
    end

    transitions = DiseaseTransition[]
    # Map stage name → transmission rate inferred from a bimolecular S+X reaction
    inferred_transmission = Dict{Symbol, Any}()
    inferred_entry = entry

    for reaction in Catalyst.reactions(reaction_system)
        substrates_in_reaction = reaction.substrates
        products_in_reaction = reaction.products
        normalized_rate = Symbolics.simplify(reaction.rate)

        if length(substrates_in_reaction) == 1
            # Unimolecular progression: X --rate--> Y
            length(products_in_reaction) == 1 || throw(ArgumentError(
                "only single-product unimolecular progression reactions are supported"))
            substrate_symbol = species_symbol(only(substrates_in_reaction))
            product_symbol   = species_symbol(only(products_in_reaction))
            push!(transitions,
                  DiseaseTransition(substrate_symbol, product_symbol, normalized_rate))

        elseif length(substrates_in_reaction) == 2
            # Bimolecular transmission: S + X --β--> ... (X is the infector)
            sub_syms = species_symbol.(substrates_in_reaction)
            susceptible in sub_syms || throw(ArgumentError(
                "bimolecular reaction must include the susceptible species `$(susceptible)` " *
                "as one substrate; got $(sub_syms)"))
            infector = sub_syms[findfirst(!=(susceptible), sub_syms)]
            # Use net stoichiometry to determine the new entry stage: the species
            # that gains +1 and is not the infector, OR the infector itself if
            # it gains net +1 (e.g., S + I → 2I).
            net = Dict(species_symbol(sp) => Int(s) for (sp, s) in reaction.netstoich)
            entry_from_rxn = nothing
            for (sp, Δ) in net
                if Δ >= 1 && sp != susceptible
                    entry_from_rxn = sp
                    break
                end
            end
            isnothing(entry_from_rxn) && throw(ArgumentError(
                "could not determine new entry stage from netstoich $(net)"))
            inferred_transmission[infector] = haskey(inferred_transmission, infector) ?
                Symbolics.simplify(inferred_transmission[infector] + normalized_rate) :
                normalized_rate
            inferred_entry = something(inferred_entry, entry_from_rxn)

        else
            throw(ArgumentError("reactions with $(length(substrates_in_reaction)) substrates " *
                                "are not supported (only unimolecular progression or " *
                                "bimolecular S+X transmission)"))
        end
    end

    # Apply inferred transmission rates back into the stages (overrides 0 defaults but
    # respects user-supplied transmission_rates which were already baked in above).
    if !isempty(inferred_transmission)
        stages = [
            haskey(inferred_transmission, s.name) && _is_zero_rate(s.transmission_rate) ?
                DiseaseStage(s.name; transmission_rate = inferred_transmission[s.name]) : s
            for s in stages
        ]
    end

    return DiseaseProgression(stages, transitions;
                              susceptible = susceptible, entry = inferred_entry)
end

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

species_symbol(specie) = Symbol(replace(string(specie), "(t)" => ""))

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
            sub_rate = n * stage.total_rate  # each sub-stage rate

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
