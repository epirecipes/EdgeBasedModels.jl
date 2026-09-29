# Owner: WP17 (DESIGN_NetworkEpiCore.md §A.3, §D.4, §J.2, §J.6, §J.8; work package in §G.2).
#
# The per-reaction edge-based assembler: the ONE lowering routine
#
#     ContactModel × descriptor ──per-reaction contributions──▶ raw SymbolicODE ──▶ MTK System
#
# Every reaction of a T_EB model contributes its own terms to the edge-based (EB) vector field
# (design §D.4; Lean `NEP.ebField`), so branching at infection, several infectors, exits out of the
# susceptible class (vaccination) and removals come for free:
#
#     contact  r = (s + J → X + J, τ):  θ̇ −= τφ_J;  φ̇_J −= τφ_J;
#                                        φ̇_X += τφ_J·qξψ''(θ)/ψ'(1);  pop_X' += τφ_J·qξψ'(θ)
#     transition (X → Y | ∅, a):         φ̇_X −= aφ_X;  φ̇_Y += aφ_X;  pop_X' −= a pop_X;  pop_Y' += a pop_X
#     exit     (s → Y, ν):               ξ̇ −= νξ;  φ̇_Y += νφ_S;  pop_Y' += νS
#
# with S = qξψ(θ), φ_S = qξψ'(θ)/ψ'(1) and q = 1 − Σ_X seed_X. A removal X → ∅ (and an exit
# s → ∅) goes to an auto-added absorbing sink species `:removed` (§J.2), so conservation
# θ = φ_S + Σφ_X and S + Σpop = 1 holds for every T_EB model.
#
# This file holds what is common to every network descriptor:
#
# - `ReactionContribution`, `LiftContributions`, `lift_contributions`, `sum_contributions`, the
#   pushforward `relabel(::LiftContributions, f)` (the open-system composition of §D.3: H1 is
#   `edge_based(glue(A, B), net)` = `sum_contributions` of the parts);
# - the preparation of a model for lifting (`_LiftModel`: typing under Σ, the removal sink,
#   per-contact rates through NetworkEpiCore's `per_contact_rates`, Symbol/Expr rates as
#   parameters through `_lift_rate` of src/compat.jl);
# - closing the field (`symbolic_ode`: ξ is dropped when nothing exits), the cumulative
#   accumulator (§J.8: the fraction ever infected, NetworkOutbreaks' structural definition),
#   the seed parameters `seed_<X>` (§A.3; ebm-core #14 / E26), the MTK system, the metadata and
#   the initial conditions (`default_initial_conditions` of `:assembled` systems).
#
# The descriptor-specific factors (node-S, edge-S, edge-entry, node-entry) are the internal
# "edge closures" of lift/configuration.jl (ConfigurationNetwork, any PGF; the compact form M9),
# lift/wellmixed.jl (WellMixed(κ); M1) and lift/multitype.jl (MultitypeNetwork and stratified
# models, structural zeros skipped). Each closure is a subtype of `_EdgeClosure` implementing
#
#     _edge_closure(net, lm::_LiftModel) -> closure          (builds the coordinates)
#     _closure_kind(cl)::Symbol                               (:configuration, :well_mixed, :multitype)
#     _coordinates(cl)::Vector{_Coordinate}
#     _seed_factors(cl)::Vector{Pair{Symbol,Any}}             (susceptible species => q parameter)
#     _contact_terms(cl, c, τ), _exit_terms(cl, t, to, ν), _transition_terms(cl, t, to, a)
#                                                             -> (terms, node-level flux)
#     _closure_observables(cl, lm, table)                     -> Vector{Pair{Symbol,Any}}
#     _initial_values(cl, lm, ρ)                              -> Dict{Symbol,Float64} by coordinate
#     _seed_expressions(cl, lm, seeds)                        -> Dict{q parameter, expression}
#     _seed_background(cl, lm), _type_of(cl, X), _type_size(cl, a)   (seeding within node types)
#     _network_terms(cl)                                      (network expressions, for name checks)
#     _relabel_coordinate(Val(kind), coordinate, m)           (for the pushforward)
#
# Include order: after lift/edge_based.jl (edge_based, the metadata conventions) and
# src/compat.jl (`_lift_rate`); the closure files follow this one.

export ReactionContribution, LiftContributions, lift_contributions, sum_contributions

# The name of the auto-added absorbing sink of removals X → ∅ (§J.2; NetworkOutbreaks'
# `:removed` compartment). On a MultitypeNetwork there is one sink per node type,
# `removed_<type>`.
const _SINK = :removed

# ---------------------------------------------------------------------------------------------
# Coordinates and the contribution table
# ---------------------------------------------------------------------------------------------

# One coordinate of the EB field. `role` is :θ, :ξ, :φ or :pop. For :φ and :pop, `species` is the
# (partner or node) species; for :θ and :ξ it is the susceptible species whose test node the
# coordinate describes. `types` is (partner type, test type) for :θ and :φ on a typed network
# ((:all, :all) otherwise), (type, type) for :pop and :ξ.
struct _Coordinate
    name::Symbol
    var::Any
    role::Symbol
    species::Symbol
    types::Tuple{Symbol,Symbol}
end

"""
    ReactionContribution

One row of a [`LiftContributions`](@ref) table: the terms that one reaction of a model adds to the
edge-based vector field (design §D.4). Fields:

- `reaction::Symbol`: the reaction's name in the `ContactModel`;
- `type::Symbol`: its T_EB type, `:contact`, `:exit`, `:progress` or `:remove`, or `:process`
  for the one row of a network process (neighbour exchange, dormant contacts), which has no
  node-level flux and acts once on every coordinate (see [`sum_contributions`](@ref));
- `text::String`: the reaction and its rate, e.g. `"S + I → I + I  (τ)"`;
- `from`, `to`: the node-level source and target species (the recipient and the product of a
  contact; a removal `X → ∅` targets the sink `:removed`);
- `flux`: the node-level flux of the reaction (a fraction of all nodes per unit time), the gain
  of `pop_to`; the cumulative-incidence accumulator is built from it;
- `terms::Vector{Pair{Symbol,Any}}`: `coordinate name => term`, the terms of the time
  derivatives of the EB coordinates (`θ`, `ξ`, `φ_X`, `pop_X`, or their typed analogues).
"""
struct ReactionContribution
    reaction::Symbol
    type::Symbol
    text::String
    from::Symbol
    to::Symbol
    flux::Any
    terms::Vector{Pair{Symbol,Any}}
end

"""
    LiftContributions

The per-reaction table of the edge-based lift of a model on a network, returned by
[`lift_contributions`](@ref): the coordinates of the EB field (`coordinates`, name => symbolic
state), the seed factors (`seed_factors`, susceptible species => the parameter `q_<s>`, the
fraction of the nodes of that type that are initially susceptible), the network, the closure
(`:configuration`, `:well_mixed`, `:multitype`, `:heterogeneous`, `:multiplex`, `:clustered`,
`:dynamic`, `:dormant`, `:degree_correlated` or `:mfsh`) and one [`ReactionContribution`](@ref)
per reaction (`contributions`), plus one `:process` row on a `DynamicNetwork`. It iterates over, and can be indexed by position or reaction name
into, its contributions.

Tables are composed with [`sum_contributions`](@ref) (open-system composition: shared
coordinates add their terms) and pushed along species maps with `relabel(table, f)`;
`symbolic_ode(table)` closes the field into a `SymbolicODE` (the exit factor ξ is dropped when no
reaction contributes to it). The cumulative-incidence accumulator is not part of the table: it
depends on the whole model (which states are infected, §J.8) and is added by `edge_based`.
"""
struct LiftContributions
    name::Symbol
    network::NetworkDescriptor
    closure::Symbol
    coordinates::Vector{Pair{Symbol,Any}}
    seed_factors::Vector{Pair{Symbol,Any}}
    contributions::Vector{ReactionContribution}
    coordinate_info::Vector{_Coordinate}
end

Base.length(c::LiftContributions) = length(c.contributions)
Base.iterate(c::LiftContributions, i::Int = 1) =
    i > length(c.contributions) ? nothing : (c.contributions[i], i + 1)
Base.getindex(c::LiftContributions, i::Integer) = c.contributions[i]
function Base.getindex(c::LiftContributions, name::Symbol)
    k = findfirst(r -> r.reaction === name, c.contributions)
    k === nothing && throw(KeyError(name))
    return c.contributions[k]
end

# ---------------------------------------------------------------------------------------------
# Small symbolic helpers
# ---------------------------------------------------------------------------------------------

_state(name::Symbol) = only(@variables $(name)(t_nounits))
_param(name::Symbol) = only(@parameters $(name))
_symname(x) = Symbol(Symbolics.getname(x))

# The value of a number or of a symbolic expression that is a number, else `nothing` (no
# simplification: the argument is a mean degree or another small closed-form constant).
function _numvalue(x)
    x isa Symbolics.Num && return _numvalue(Symbolics.value(x))
    x isa Symbolics.SymbolicUtils.BasicSymbolic && return nothing
    x isa Real && return Float64(x)
    return nothing
end

"""
    _unless_zero(value, d, limit)

`value(d)`, or the κ → 0 limit `limit` where the constant `d` (a mean degree ψ'(1) or
E[k_{a→c}]) vanishes (verified issues E11 and E32, corrected fixes: the rare edges attach
independently of a node's other edges). A numeric zero gives `limit` (and `value` is not
called); a numeric `d` gives `value(Float64(d))`; a symbolic `d` gives
`ifelse(d == 0, limit, value(d))`, so that a network parameter set to 0 at solve time selects the
limit instead of 0/0 (NaN, or 1 once Symbolics folds it).
"""
function _unless_zero(value, d, limit)
    v = _numvalue(d)
    v === nothing && return Symbolics.ifelse(Symbolics.wrap(d) == 0, limit, value(d))
    return iszero(v) ? limit : value(v)
end

"""
    _ratio(n, d, limit)

`n/d` for a constant denominator `d` (a mean degree), with the κ → 0 limit `limit` where `d`
vanishes (`_unless_zero`). The division is never by a function of θ: the entry terms are
pre-cancelled (verified issues E23 and E27).
"""
_ratio(n, d, limit) = _unless_zero(x -> n / x, d, limit)

_sum_terms(xs) = isempty(xs) ? Symbolics.Num(0) : sum(xs)

# ---------------------------------------------------------------------------------------------
# Preparing a model for the lift
# ---------------------------------------------------------------------------------------------

# A model as the assembler sees it: the susceptible set, the node species (non-susceptible
# species, then the sinks of removals), the reaction types under Σ and the lifted rates.
struct _LiftModel
    cm::ContactModel
    Σ::Vector{Symbol}
    nodes::Vector{Symbol}                 # non-susceptible species of the model, then the sinks
    sinks::Vector{Symbol}                 # auto-added sink species (a subset of nodes)
    stratum::Dict{Symbol,Symbol}          # species (and sinks) => stratum label (:all if none)
    contact_rates::Vector{Any}            # lifted per-contact rates, in contact order
    transition_rates::Vector{Any}         # lifted transition rates
    transition_targets::Vector{Symbol}    # targets, with the sink for X → ∅
    transition_types::Vector{Symbol}      # :exit, :progress, :remove
    infectors::Vector{Symbol}
    context::String
end

_species_stratum(cm::ContactModel, X::Symbol) =
    haskey(species_labels(cm), X) ? species_labels(cm)[X].stratum : :all

_sink_name(stratum::Symbol) = stratum === :all ? _SINK : Symbol(_SINK, :_, stratum)

function _reaction_text(c::Contact, τ)
    rhs = c.product === c.infector ? "2$(c.infector)" : "$(c.product) + $(c.infector)"
    return "$(c.recipient) + $(c.infector) → $(rhs)  ($(_rate_text(τ)))"
end
_reaction_text(t::NodeTransition, a) =
    "$(t.from) → $(t.to === nothing ? "∅" : t.to)  ($(_rate_text(a)))"
# Display text of a rate or term: no time arguments, and exact rationals as 5 and (1/6), not
# (5//1) and (1//6).
_rate_text(r) = replace(string(r), "(t)" => "", r"\((-?\d+)//1\)" => s"\1", "//" => "/")

# Is the model a T_EB model under the susceptible set Σ? Throws an ArgumentError naming the
# first offending reaction otherwise. (`edge_based` calls `require_admissible` first, whose
# AdmissibilityError has the design's §B.7 text; this check covers the components passed to
# `lift_contributions`, whose own susceptible set may be empty.)
function _check_teb(cm::ContactModel, Σ::Vector{Symbol}, context; layered::Bool = false)
    S = Set(Σ)
    fail(r, why) = throw(ArgumentError(
        "$context: `$(r.name)` ($(_arrow(r))) $why; the edge-based lift is exact only for T_EB " *
        "models, in which no reaction produces a susceptible class and every contact converts a " *
        "susceptible node (Miller, Slim & Volz 2012, Part I)"))
    for c in contacts(cm)
        c.recipient in S || fail(c, "has the recipient $(c.recipient), which is not susceptible " *
                                    "(type node_contact)")
        c.infector in S && fail(c, "has the susceptible infector $(c.infector) (type sus_contact)")
        c.product in S && fail(c, "produces the susceptible species $(c.product) (type sus_contact)")
        (layered || c.layer === :all) || fail(c, "acts on the layer :$(c.layer) only, and the " *
                                                 "network has no layers")
    end
    for t in node_transitions(cm)
        if t.from in S
            (t.to !== nothing && t.to in S) && fail(t, "moves a node between susceptible classes " *
                                                       "(type sus_move)")
        elseif t.to !== nothing && t.to in S
            fail(t, "produces the susceptible species $(t.to) (type resus)")
        end
    end
    return nothing
end
_arrow(c::Contact) = "$(c.recipient) + $(c.infector) → $(c.product) + $(c.infector)"
_arrow(t::NodeTransition) = "$(t.from) → $(t.to === nothing ? "∅" : t.to)"

function _lift_model(cm::ContactModel, net::NetworkDescriptor, Σ::AbstractVector{Symbol};
                     context::AbstractString)
    Σv = collect(Symbol, Σ)
    for s in Σv
        s in species_names(cm) || throw(ArgumentError(
            "$context: the susceptible species $(s) is not a species of the model"))
    end
    _check_teb(cm, Σv, context; layered = _accepts_layers(net))
    S = Set(Σv)
    nodes = Symbol[x for x in species_names(cm) if !(x in S)]
    stratum = Dict{Symbol,Symbol}(x => _species_stratum(cm, x) for x in species_names(cm))
    sinks = Symbol[]
    targets = Symbol[]
    types = Symbol[]
    for t in node_transitions(cm)
        push!(types, t.from in S ? :exit : t.to === nothing ? :remove : :progress)
        if t.to === nothing
            sink = _sink_name(stratum[t.from])
            if sink in species_names(cm)
                _check_inert_sink(cm, sink, context)
            elseif !(sink in sinks)
                push!(sinks, sink)
                stratum[sink] = stratum[t.from]
            end
            push!(targets, sink)
        else
            push!(targets, t.to)
        end
    end
    append!(nodes, sinks)
    defaults = parameter_defaults(cm)
    τs = isempty(contacts(cm)) ? Any[] : per_contact_rates(cm, net)
    crates = Any[_lift_rate(τ; defaults) for τ in τs]
    trates = Any[_lift_rate(t.rate; defaults) for t in node_transitions(cm)]
    infectors = unique!(Symbol[c.infector for c in contacts(cm)])
    return _LiftModel(cm, Σv, nodes, sinks, stratum, crates, trates, targets, types, infectors,
                      String(context))
end

# A model species with the sink's name may absorb the removals only if it is inert: an absorbing
# class that no reaction leaves and that takes part in no contact.
function _check_inert_sink(cm::ContactModel, sink::Symbol, context)
    inert = !any(t -> t.from === sink, node_transitions(cm)) &&
            !any(c -> sink in (c.recipient, c.infector, c.product), contacts(cm))
    inert || throw(ArgumentError(
        "$context: removals X → ∅ are lowered to the absorbing sink species $(sink) (design " *
        "§J.2), but the model already has a species $(sink) that is not inert (it takes part in " *
        "a contact or is left by a transition); rename that species"))
    return nothing
end

# ---------------------------------------------------------------------------------------------
# Edge closures: the interface (the methods live in lift/configuration.jl, wellmixed.jl,
# multitype.jl)
# ---------------------------------------------------------------------------------------------

abstract type _EdgeClosure end

# Whether a descriptor's closure handles layer-labelled contacts (`Contact(...; layer)`): only a
# layered (multiplex) closure does; its file adds a method.
_accepts_layers(::NetworkDescriptor) = false

_edge_closure(net::NetworkDescriptor, lm::_LiftModel) = throw(ArgumentError(
    "$(lm.context): the per-reaction edge-based assembler has no closure for a " *
    "$(nameof(typeof(net))); it lifts models onto ConfigurationNetwork, WellMixed, " *
    "MultitypeNetwork, ClusteredNetwork, DynamicNetwork, MultiplexNetwork, DegreeCorrelatedNetwork " *
    "and MFSHNetwork descriptors"))

# ---------------------------------------------------------------------------------------------
# lift_contributions, sum_contributions, relabel, symbolic_ode
# ---------------------------------------------------------------------------------------------

"""
    lift_contributions(model, net; susceptible = susceptible_species(model)) -> LiftContributions

The per-reaction table of the edge-based lift of `model` on `net` (a `ConfigurationNetwork`,
`WellMixed`, `MultitypeNetwork`, `MultiplexNetwork`, `ClusteredNetwork`, `DynamicNetwork`,
`DegreeCorrelatedNetwork` or `MFSHNetwork`; for heterogeneous susceptibility, `unstructured(net, st)`
or `lift_contributions(model, net, st)`): for every reaction, the terms it adds to the time
derivatives of the EB coordinates (design §D.4; Lean `NEP.ebField`), each reaction on its own.
The EB vector field of the model is their sum; `symbolic_ode(table)` closes it, and
`symbolic_ode(edge_based(model, net))` is the same field.

`model` is a `ContactModel`, an `OpenContactModel` (its model) or anything `contact_model`
accepts. The model need not be admissible on its own: a component of a gluing, such as a
transition-only model without a susceptible class, is lifted with the coordinates of its own
species, and the parts of a gluing compose by [`sum_contributions`](@ref) (H1, design §D.6):

```julia
net = ConfigurationNetwork(PoissonDegree(5))
tr  = open_model(ContactModel(:tr; contacts = [Contact(:S, :I, :E, :τ)]); legs = [[:S], [:E, :I]])
pr  = open_model(ContactModel(:pr; transitions = [NodeTransition(:E, :I, :σ), NodeTransition(:I, :R, :γ)]);
                 legs = [[:E, :I, :R]])
vector_fields_equal(symbolic_ode(edge_based(glue(tr, pr; on = [:E, :I]), net)),
                    sum_contributions(lift_contributions(tr, net), lift_contributions(pr, net)))   # true
```

`susceptible` sets the susceptible species when the part alone does not show them (a vaccination
part `S → V` has no contact, so pass `susceptible = [:S]` to lift its exit with the factor ξ).
Every reaction must be of a T_EB type under that set (contact, exit, progress or remove);
removals `X → ∅` go to the absorbing sink `:removed` (design §J.2). The coordinates are named as
in the lifted systems: `θ`, `ξ`, `φ_X`, `pop_X` on untyped networks, and `θ_<b>_<a>`,
`φ_<X>_<a>`, `ξ_<s>` on a `MultitypeNetwork` (see [`edge_based`](@ref)); the fraction of initially
susceptible nodes of a type is the parameter `q_<s>` (the lifted system replaces it by
1 − Σ_X seed_X within the type).
"""
function lift_contributions(cm::ContactModel, net::NetworkDescriptor;
                            susceptible = susceptible_species(cm))
    Σ = susceptible isa Symbol ? [susceptible] : collect(Symbol, susceptible)
    context = "lift_contributions(:$(cm.name), $(nameof(typeof(net))))"
    lm = _lift_model(cm, net, Σ; context)
    return _contributions(_edge_closure(net, lm), lm, net)
end
lift_contributions(model, net::NetworkDescriptor; kw...) =
    lift_contributions(contact_model(model), net; kw...)

function _contributions(cl::_EdgeClosure, lm::_LiftModel, net::NetworkDescriptor)
    cm = lm.cm
    rows = ReactionContribution[]
    for (c, τ) in zip(contacts(cm), lm.contact_rates)
        terms, flux = _contact_terms(cl, c, τ)
        push!(rows, ReactionContribution(c.name, :contact, _reaction_text(c, τ), c.recipient,
                                         c.product, flux, terms))
    end
    for (t, a, to, ty) in zip(node_transitions(cm), lm.transition_rates, lm.transition_targets,
                              lm.transition_types)
        terms, flux = ty === :exit ? _exit_terms(cl, t, to, a) : _transition_terms(cl, t, to, a)
        push!(rows, ReactionContribution(t.name, ty, _reaction_text(t, a), t.from, to, flux, terms))
    end
    info = _coordinates(cl)
    return LiftContributions(cm.name, net, _closure_kind(cl),
                             Pair{Symbol,Any}[x.name => x.var for x in info],
                             collect(Pair{Symbol,Any}, _seed_factors(cl)), rows, info)
end

"""
    sum_contributions(tables::LiftContributions...) -> LiftContributions

The open-system composition of edge-based lifts (design §D.3, resource sharers): the union of the
coordinates, identified by name, and the concatenation of the per-reaction contributions, so
that the vector fields of shared coordinates add. With the tables of the parts of a gluing on the
same network (pushed along the inclusions of the gluing with `relabel(table, f)` when the gluing
renames species), `symbolic_ode(sum_contributions(parts...))` equals
`symbolic_ode(edge_based(glue(parts...), net))`: the strictness of the EB lift under gluing (H1,
Lean `NEP.lift_glue`). All tables must be on the same network, and a coordinate shared by name
must be the same class in every table: two tables whose susceptible classes differ on the same
node type (θ is named without its class) are refused with an `ArgumentError`, since a node type
has one susceptible class (relabel one of them first).

A network process (neighbour exchange or dormant contacts on a `DynamicNetwork`) acts once on
every coordinate, so its `:process` row is not added up: the sum drops the process rows of the
tables and, when any of them had one, appends one row rebuilt for the coordinates of the result
(H1 with the process as its own component). The clustered lift is only lax under gluing (design §C.3, F2: the triangle pair
states of species from different parts would be lost), so clustered tables are refused: lift the
glued model.
"""
function sum_contributions(first_table::LiftContributions, rest::LiftContributions...)
    tables = (first_table, rest...)
    first_table.closure === :clustered && throw(ArgumentError(
        "sum_contributions: the clustered (Volz et al. 2011) lift is only lax under gluing (design " *
        "§C.3, F2): the triangle pair states of species from different parts are not a sum of the " *
        "parts' tables; lift the glued model, edge_based(glue(...), net)"))
    for c in rest
        _same_network(c.network, first_table.network) || throw(ArgumentError(
            "sum_contributions: the tables are lifts on different networks ($(first_table.network) " *
            "and $(c.network)); gluing across different networks is not a sum (F5: use a " *
            "MultiplexNetwork)"))
        c.closure === first_table.closure || throw(ArgumentError(
            "sum_contributions: the tables use different closures (:$(first_table.closure), " *
            ":$(c.closure))"))
    end
    info = _Coordinate[]
    seen = Dict{Symbol,_Coordinate}()
    for c in tables, x in c.coordinate_info
        if haskey(seen, x.name)
            y = seen[x.name]
            isequal(y.var, x.var) || throw(ArgumentError(
                "sum_contributions: the coordinate $(x.name) is a different variable in two tables"))
            # θ (and ξ on untyped networks) is named without its susceptible class, and a node
            # type has one susceptible class: the same name with two classes is not a sum
            y.species === x.species || throw(ArgumentError(
                "sum_contributions: the coordinate $(x.name) belongs to the susceptible class " *
                "$(y.species) in one table and $(x.species) in another, but a node type has one " *
                "susceptible class; push one table onto the other's class first " *
                "(relabel(table, Dict(:$(x.species) => :$(y.species))))"))
        else
            seen[x.name] = x
            push!(info, x)
        end
    end
    factors = Pair{Symbol,Any}[]
    for c in tables, (s, q) in c.seed_factors
        any(p -> first(p) === s, factors) || push!(factors, s => q)
    end
    rows = ReactionContribution[r for c in tables for r in c.contributions if r.type !== :process]
    any(r -> r.type === :process, (r for c in tables for r in c.contributions)) &&
        _append_process_row!(rows, first_table.network, first_table.closure, info)
    name = Symbol(join((c.name for c in tables), :_plus_))
    return LiftContributions(name, first_table.network, first_table.closure,
                             Pair{Symbol,Any}[x.name => x.var for x in info], factors, rows, info)
end

# The one `:process` row of a table with the coordinates `info` (lift/dynamic.jl, lift/dormant.jl:
# `_process_row`, `nothing` for a network without a process).
function _append_process_row!(rows::Vector{ReactionContribution}, network, closure::Symbol, info)
    row = _process_row(network, closure, info)
    row === nothing || push!(rows, row)
    return rows
end

function _same_network(a, b)
    (a === b || isequal(a, b)) && return true
    return try
        canonical_text(a) == canonical_text(b)
    catch
        false
    end
end

"""
    relabel(table::LiftContributions, f::AbstractDict{Symbol,Symbol}) -> LiftContributions

Push a table of edge-based contributions forward along the species map `f` (species not in `f`
keep their names): the coordinates of a species X become those of f(X), and the terms are
re-expressed in them, so that coordinates of merged species add (Lean `NEP.lift_map`:
EB(relabel(P, f)) = f_* EB(P)). Use it with the `inclusions` of a gluing (an `OpenContactModel`
records one species map per part) before [`sum_contributions`](@ref).
"""
function NetworkEpiCore.relabel(c::LiftContributions, f::AbstractDict)
    fmap = Dict{Symbol,Symbol}(Symbol(k) => Symbol(v) for (k, v) in f)
    m(x::Symbol) = get(fmap, x, x)
    subst = Dict{Any,Any}()
    newinfo = _Coordinate[]
    byname = Dict{Symbol,_Coordinate}()
    rename = Dict{Symbol,Symbol}()
    for x in c.coordinate_info
        y = _relabel_coordinate(Val(c.closure), x, m)
        if haskey(byname, y.name)
            y = byname[y.name]
        else
            byname[y.name] = y
            push!(newinfo, y)
        end
        rename[x.name] = y.name
        isequal(x.var, y.var) || (subst[x.var] = y.var)
    end
    factors = Pair{Symbol,Any}[]
    for (s, q) in c.seed_factors
        s2 = m(s)
        q2 = _param(Symbol(:q_, s2))
        isequal(q, q2) || (subst[q] = q2)
        any(p -> first(p) === s2, factors) || push!(factors, s2 => q2)
    end
    sub(e) = isempty(subst) ? e : Symbolics.substitute(e, subst)
    # reaction rows are pushed forward; a network process acts once on every coordinate, so its
    # row is rebuilt for the new coordinates (a merging map would otherwise count it twice)
    rows = ReactionContribution[
        ReactionContribution(r.reaction, r.type, r.text, m(r.from), m(r.to), sub(r.flux),
                             Pair{Symbol,Any}[rename[k] => sub(v) for (k, v) in r.terms])
        for r in c.contributions if r.type !== :process]
    any(r -> r.type === :process, c.contributions) &&
        _append_process_row!(rows, c.network, c.closure, newinfo)
    return LiftContributions(c.name, c.network, c.closure,
                             Pair{Symbol,Any}[x.name => x.var for x in newinfo], factors, rows,
                             newinfo)
end

# The closed field of a table: states, right-hand sides, and the substitution that drops unused
# exit factors (ξ ≡ 1 where no reaction contributes to it; design §D.4 "ξ ≡ 1 if there are no
# exits").
function _close(c::LiftContributions)
    rhs = Dict{Symbol,Vector{Any}}(x.name => Any[] for x in c.coordinate_info)
    for r in c.contributions, (k, v) in r.terms
        haskey(rhs, k) || throw(ArgumentError(
            "LiftContributions :$(c.name): the reaction $(r.reaction) contributes to $(k), which is " *
            "not a coordinate of the table"))
        push!(rhs[k], v)
    end
    drop = Dict{Any,Any}()
    for x in c.coordinate_info
        x.role === :ξ && isempty(rhs[x.name]) && (drop[x.var] = 1)
    end
    close(e) = isempty(drop) ? e : Symbolics.substitute(e, drop)
    info = _Coordinate[x for x in c.coordinate_info if !(x.role === :ξ && haskey(drop, x.var))]
    f = Any[close(_sum_terms(rhs[x.name])) for x in info]
    return info, f, drop
end

"""
    symbolic_ode(table::LiftContributions) -> SymbolicODE

The edge-based vector field of a table of per-reaction contributions: the sum of the terms of
every coordinate (the exit factor ξ ≡ 1 is dropped when no reaction contributes to it). Its
parameters are the rate and network parameters and the initially susceptible fractions `q_<s>`.
"""
function NetworkEpiCore.symbolic_ode(c::LiftContributions)
    info, f, _ = _close(c)
    return SymbolicODE(Symbol(c.name, :_edge_based); states = Any[x.var for x in info], rhs = f,
                       parameters = :infer, domain = _probe_domain(info))
end

# Probe boxes for verify/vector_fields_equal: θ in (0.05, 1] where ψ, ψ' do not vanish.
_probe_domain(info) = Pair{Any,Tuple{Float64,Float64}}[x.var => (0.05, 1.0) for x in info
                                                       if x.role in (:θ, :ξ)]

function Base.show(io::IO, c::LiftContributions)
    print(io, "LiftContributions(:", c.name, ", ", length(c.contributions), " reactions, ",
          c.closure, ")")
end

function Base.show(io::IO, ::MIME"text/plain", c::LiftContributions)
    println(io, "LiftContributions :", c.name, " on ", _network_text(c.network), "  (", c.closure,
            " closure)")
    print(io, "  coordinates  ", join((string(first(p)) for p in c.coordinates), ", "))
    if !isempty(c.seed_factors)
        print(io, "\n  seed factors ", join(("$(last(p)) (initially susceptible fraction of $(first(p)))"
                                            for p in c.seed_factors), ", "))
    end
    width = maximum((textwidth(string(k)) for r in c.contributions for (k, _) in r.terms); init = 1)
    for (i, r) in enumerate(c.contributions)
        print(io, "\n  [", i, "] ", r.text, "   ", r.type)
        for (k, v) in r.terms
            print(io, "\n        ", rpad(string(k, "'"), width + 2), " += ", _rate_text(v))
        end
    end
end

function _network_text(net)
    s = sprint(show, net)
    while true                        # strip type parameters, innermost first
        s2 = replace(s, r"\{[^{}]*\}" => "")
        s2 == s && return s
        s = s2
    end
end

# ---------------------------------------------------------------------------------------------
# Infected states and the cumulative accumulator (design §J.8)
# ---------------------------------------------------------------------------------------------

# The species a node counts as infected in (design §J.8): NetworkEpiCore's `infected_species`, the
# one implementation shared by the edge-based, pairwise and stochastic back ends (an infector, or a
# state on a status-preserving path from the product of an infection to an infector; tracing
# contacts and vaccination are not infections), in the order of the lifted node species. The
# removal sinks the lift adds are never infected.
function _infected_species(lm::_LiftModel)
    inf = Set{Symbol}(infected_species(lm.cm))
    return Symbol[x for x in lm.nodes if x in inf && !(x in lm.sinks)]
end

# d(cumulative)/dt: the flux of every reaction that takes a node from a non-infected into an
# infected state (the infections among the contacts, importations S → E among the exits, and
# transitions such as V → E). The seeds in infected states are its initial value.
function _cumulative_rhs(c::LiftContributions, infected::Vector{Symbol})
    inf = Set(infected)
    terms = Any[]
    for r in c.contributions
        r.to in inf || continue
        (r.type === :contact || r.type === :exit || !(r.from in inf)) && push!(terms, r.flux)
    end
    return _sum_terms(terms)
end

# ---------------------------------------------------------------------------------------------
# Names: generated names must not collide with the model's parameters or with each other (E26)
# ---------------------------------------------------------------------------------------------

# `generated`: every name the assembler creates (states, observables, q_<s>, seed_<X>);
# `own`: the symbolic variables it created (states and q parameters); `exprs`: the expressions of
# the system. A variable of `exprs` that the assembler did not create is a rate or network
# parameter, and its name must not be a generated one (a parameter θ next to the state θ(t), or a
# rate parameter q_S, would otherwise be silently confused with the generated variable; the old
# seed parameter ρ was, verified issue E26). The generated names must also be distinct.
function _check_generated_names(lm::_LiftModel, generated::Vector{Symbol}, own, exprs,
                                network_exprs)
    context = lm.context
    dup = unique!(Symbol[n for n in generated if count(==(n), generated) > 1])
    isempty(dup) || throw(ArgumentError(
        "$context: the names of the generated variables collide: $(join(sort!(dup), ", ")); the " *
        "assembler joins species and type names with \"_\", so rename the species or the node " *
        "types"))
    gen = Set(generated)
    pnames = Set{Symbol}(_pname(p) for p in rate_parameters(lm.cm))
    for (group, skip_own) in ((exprs, true), (network_exprs, false))
        for e in group, v in _variables_of(e)
            skip_own && any(o -> isequal(v, o), own) && continue
            any(o -> isequal(v, o), own) && _is_state_var(v) && continue
            n = _symname(v)
            n === :t || push!(pnames, n)
        end
    end
    bad = sort!(Symbol[n for n in pnames if n in gen])
    isempty(bad) || throw(ArgumentError(
        "$context: the parameter name(s) $(join(bad, ", ")) collide with names the edge-based " *
        "assembler generates (θ, ξ, the φ_/pop_ coordinates, cumulative, the observables, the " *
        "initially susceptible fractions q_<s> and the seed fractions seed_<X>); rename the " *
        "parameter(s)"))
    return nothing
end

_variables_of(e) = (e isa Symbolics.Num || e isa Symbolics.SymbolicUtils.BasicSymbolic) ?
                   Symbolics.get_variables(e) : ()
# A state θ(t) is a call of a variable on time; a parameter is a plain symbol.
_is_state_var(v) = Symbolics.iscall(Symbolics.unwrap(v))

# ---------------------------------------------------------------------------------------------
# Assembly: contributions → raw SymbolicODE → MTK system
# ---------------------------------------------------------------------------------------------

# The generic assembly of the expanded form (every closure).
function _assemble(cm::ContactModel, net::NetworkDescriptor; name::Symbol, context::AbstractString)
    lm = _lift_model(cm, net, susceptible_species(cm); context)
    cl = _edge_closure(net, lm)
    table = _contributions(cl, lm, net)
    info, f, drop = _close(table)
    closeξ(e) = isempty(drop) ? e : Symbolics.substitute(e, drop)
    raw = SymbolicODE(Symbol(name, :_edge_based); states = Any[x.var for x in info], rhs = f,
                      parameters = :infer, domain = _probe_domain(info))
    infected = _infected_species(lm)
    cum = _state(:cumulative)
    cum_rhs = closeξ(_cumulative_rhs(table, infected))
    obs = Pair{Symbol,Any}[k => closeξ(v) for (k, v) in _closure_observables(cl, lm, table)]
    seeds = Dict{Symbol,Any}(X => _param(Symbol(:seed_, X)) for X in lm.nodes if !(X in lm.sinks))
    qsub = _seed_expressions(cl, lm, seeds)
    obsnames = unique!(Symbol[first(o) for o in obs])
    generated = vcat(Symbol[x.name for x in table.coordinate_info], Symbol[:cumulative], obsnames,
                     Symbol[_symname(q) for q in keys(qsub)], Symbol[_symname(v) for v in values(seeds)])
    own = vcat(Any[x.var for x in table.coordinate_info], Any[cum], collect(keys(qsub)))
    _check_generated_names(lm, generated, own, vcat(f, Any[last(o) for o in obs], cum_rhs),
                           _network_terms(cl))
    sub(e) = Symbolics.substitute(e, qsub)
    D = D_nounits
    eqs = Equation[D(x.var) ~ sub(fx) for (x, fx) in zip(info, f)]
    push!(eqs, D(cum) ~ sub(cum_rhs))
    obsvars = Dict{Symbol,Any}()
    for (k, e) in obs
        haskey(obsvars, k) && continue
        v = _state(k)
        obsvars[k] = v
        # a constant observable (the excess hazard of an edgeless network) is a Float64 like the rest
        e = sub(e)
        c = _numvalue(e)
        push!(eqs, v ~ (c === nothing ? e : Symbolics.Num(c)))
    end
    compiled = mtkcompile(System(eqs, t_nounits; name))
    variables = Dict{Symbol,Any}(x.name => x.var for x in info)
    variables[:cumulative] = cum
    _add_recovered_alias!(variables, lm)
    md = _assembled_metadata(cm, net, lm, cl, table, raw, seeds, qsub, infected; form = :expanded)
    md[:coords] = Dict{Symbol,Any}(x.name => x.var for x in info)
    md[:ic] = (initial; N = nothing) -> _initial_conditions(cl, lm, info, cum, seeds, infected,
                                                            initial; N)
    return EdgeModelSystem(compiled, variables, obsvars, md)
end

# The legacy variable `:R`. A species called R owns the name: `:R` is its population `pop_R`
# (none when R is the susceptible class, whose node-S is already the observable `:R`, or when
# `pop_R` is not a variable). Otherwise `:R` is the population of the unique recovered class (a
# node species that is not an infector and is left by no transition), when there is exactly one.
# (For S + I → I, I → R, R → D the recovered class is D, but `:R` must not name it.)
function _add_recovered_alias!(variables, lm::_LiftModel)
    haskey(variables, :R) && return variables
    if :R in lm.Σ || :R in lm.nodes
        :R in lm.nodes && haskey(variables, :pop_R) && (variables[:R] = variables[:pop_R])
        return variables
    end
    left = Set(t.from for t in node_transitions(lm.cm))
    rec = Symbol[X for X in lm.nodes if !(X in lm.infectors) && !(X in left)]
    if length(rec) == 1 && haskey(variables, Symbol(:pop_, only(rec)))
        variables[:R] = variables[Symbol(:pop_, only(rec))]
    end
    return variables
end

function _assembled_metadata(cm, net, lm, cl, table, raw, seeds, qsub, infected; form::Symbol)
    md = Dict{Symbol,Any}()
    md[:kind] = :assembled
    md[:form] = form
    md[:closure] = _closure_kind(cl)
    md[:model] = cm
    md[:network] = net
    md[:raw] = raw
    md[:contributions] = table
    md[:seed_params] = seeds
    md[:q] = Dict{Symbol,Any}(s => (param = q, value = qsub[q]) for (s, q) in _seed_factors(cl))
    md[:infected] = infected
    md[:sinks] = copy(lm.sinks)
    md[:susceptible] = length(lm.Σ) == 1 ? only(lm.Σ) : copy(lm.Σ)
    md[:parameter_defaults] = Dict{Symbol,Float64}(parameter_defaults(cm))
    entries = entry_species(cm)
    length(entries) == 1 && (md[:entry] = only(entries))
    return md
end

"""
    symbolic_ode(sys::EdgeModelSystem) -> SymbolicODE

The uncompiled edge-based vector field of a system built by the per-reaction assembler
(`metadata[:raw]`): the closed field of [`lift_contributions`](@ref), with the initially
susceptible fractions as parameters `q_<s>` and without the cumulative-incidence accumulator (an
observer of the trajectory, not part of the field). Compare fields with `vector_fields_equal`.
A system built by hand, without `metadata[:raw]`, is an `ArgumentError`.
"""
function NetworkEpiCore.symbolic_ode(sys::EdgeModelSystem)
    raw = get(sys.metadata, :raw, nothing)
    raw === nothing && throw(ArgumentError(
        "symbolic_ode: this edge-based system records no uncompiled vector field (metadata[:kind] = " *
        ":$(get(sys.metadata, :kind, :unknown))); build it with edge_based"))
    return raw
end

# ---------------------------------------------------------------------------------------------
# Initial conditions of assembled systems
# ---------------------------------------------------------------------------------------------

function _default_initial_conditions(::Val{:assembled}, sys::EdgeModelSystem;
                                     initial = nothing, ε = 1e-3, seed_fraction = nothing,
                                     N = nothing)
    if initial === nothing
        ρ = Float64(something(seed_fraction, ε))
        # a system forwarded from a 0.1 model type records its 0.1 seeding rule (`seed_fraction`
        # in every node type's entry state), otherwise the unique entry state is seeded (§E.2)
        rule = get(sys.metadata, :default_seed, nothing)
        initial = rule === nothing ? default_seed(sys.metadata[:model], ρ) : rule(ρ)
    elseif seed_fraction !== nothing
        throw(ArgumentError("default_initial_conditions: pass either `initial` or `seed_fraction`, not both"))
    end
    initial isa SeedSpec || throw(ArgumentError(
        "default_initial_conditions: initial must be a SeedSpec such as SeedFraction(:I => 0.01); " *
        "got $(typeof(initial))"))
    return sys.metadata[:ic](initial; N)
end

# The seed fractions of the node species (fractions of ALL nodes, §J.6), validated.
function _seeds(lm::_LiftModel, background, initial::SeedSpec; N = nothing)
    pairs = seed_fractions(initial; N, background)
    ρ = Dict{Symbol,Float64}(X => 0.0 for X in lm.nodes if !(X in lm.sinks))
    given = Dict{Symbol,Float64}()
    for (X, v) in pairs
        haskey(given, X) && throw(ArgumentError("default_initial_conditions: $(X) is seeded twice"))
        given[X] = v
        X in lm.Σ && continue
        haskey(ρ, X) || throw(ArgumentError(
            "default_initial_conditions: $(initial) seeds $(X), which is not a node species of the " *
            "model (node species: $(join((x for x in lm.nodes if !(x in lm.sinks)), ", ")))"))
        (isfinite(v) && v >= 0) || throw(ArgumentError(
            "default_initial_conditions: the seed fraction of $(X) must be finite and ≥ 0; got $v"))
        ρ[X] = v
    end
    return ρ, given
end

# Within each node type, the seeds must leave a non-negative susceptible fraction, and a seed
# fraction given explicitly for a susceptible species must be the one the other seeds leave.
function _check_susceptible_seeds(cl::_EdgeClosure, lm::_LiftModel, ρ, given)
    for s in lm.Σ
        a = _type_of(cl, s)
        n = _type_size(cl, a)
        used = sum((v for (X, v) in ρ if _type_of(cl, X) === a); init = 0.0)
        where = a === :all ? "" : " of the node type $(a) (size $(n))"
        used <= n * (1 + 1e-12) || throw(ArgumentError(
            "default_initial_conditions: the seed fractions$(where) sum to $(used), more than " *
            "$(n); seed fractions are fractions of all nodes (design §J.6)"))
        if haskey(given, s) && abs(given[s] - (n - used)) > 1e-8
            throw(ArgumentError(
                "default_initial_conditions: $(s) is given the fraction $(given[s]), but the other " *
                "seeds$(where) leave $(n - used) of the nodes susceptible"))
        end
    end
    return nothing
end

function _initial_conditions(cl::_EdgeClosure, lm::_LiftModel, info, cum, seeds, infected,
                             initial::SeedSpec; N = nothing)
    ρ, given = _seeds(lm, _seed_background(cl, lm), initial; N)
    _check_susceptible_seeds(cl, lm, ρ, given)
    values = _initial_values(cl, lm, ρ)
    ic = Dict{Any,Float64}()
    for x in info
        ic[x.var] = values[x.name]
    end
    ic[cum] = sum((ρ[X] for X in infected if haskey(ρ, X)); init = 0.0)
    for (X, p) in seeds
        ic[p] = ρ[X]
    end
    return ic
end
