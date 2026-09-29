# Owner: WP17 (DESIGN_NetworkEpiCore.md §A.3, §C.2, §C.3, §D.5 M1; work package in §G.2).
#
# The WellMixed(κ) closure of the per-reaction assembler (lift/assembler.jl). Each node makes κ
# fleeting contacts per unit time with uniformly random partners, so a contact's partner is in X
# with probability x_X = pop_X: the edge and node coordinates coincide, no edge is used up, and
# θ is the integrated hazard per contact (design §C.3):
#
#     θ̇ = −Σ_r τ_r x_{J_r},   S = qξe^{κ(θ−1)},   x_X gains κτ_r x_{J_r} S (contact r),
#     ξ̇ = −Σ_e ν_e ξ,          x_Y gains ν_e S (exit e);  transitions move x as in mass action.
#
# This is the unit of the lift (M1): (θ; x) ↦ (S = qe^{κ(θ−1)}, x) conjugates it to the mass-action
# ODE of c_κ P, `mass_action(cm; κ)` (a quotient semiconjugacy with exits or removals).

struct _WellMixedClosure <: _EdgeClosure
    κ::Any
    s::Union{Symbol,Nothing}
    info::Vector{_Coordinate}
    θ::Any
    ξ::Any
    q::Any
    pop::Dict{Symbol,Any}
end

_closure_kind(::_WellMixedClosure) = :well_mixed
_coordinates(cl::_WellMixedClosure) = cl.info
_seed_factors(cl::_WellMixedClosure) = cl.s === nothing ? Pair{Symbol,Any}[] : [cl.s => cl.q]
_type_of(::_WellMixedClosure, ::Symbol) = :all
_type_size(::_WellMixedClosure, ::Symbol) = 1.0
_seed_background(cl::_WellMixedClosure, ::_LiftModel) = cl.s
_network_terms(cl::_WellMixedClosure) = Any[cl.κ]

function _edge_closure(net::WellMixed, lm::_LiftModel)
    s = _single_susceptible(lm)
    info = _untyped_coordinates(lm, s; edges = false)
    get(name) = (k = findfirst(x -> x.name === name, info); k === nothing ? nothing : info[k].var)
    pop = Dict{Symbol,Any}(X => get(Symbol(:pop_, X)) for X in lm.nodes)
    q = s === nothing ? nothing : _param(Symbol(:q_, s))
    return _WellMixedClosure(net.κ, s, info, get(:θ), get(:ξ), q, pop)
end

_node_S(cl::_WellMixedClosure) = cl.q * cl.ξ * exp(cl.κ * (cl.θ - 1))

function _contact_terms(cl::_WellMixedClosure, c::Contact, τ)
    h = τ * cl.pop[c.infector]
    flux = cl.κ * h * _node_S(cl)
    return Pair{Symbol,Any}[:θ => -h, Symbol(:pop_, c.product) => flux], flux
end

function _exit_terms(cl::_WellMixedClosure, t::NodeTransition, to::Symbol, ν)
    flux = ν * _node_S(cl)
    return Pair{Symbol,Any}[:ξ => -ν * cl.ξ, Symbol(:pop_, to) => flux], flux
end

function _transition_terms(cl::_WellMixedClosure, t::NodeTransition, to::Symbol, a)
    flux = a * cl.pop[t.from]
    return Pair{Symbol,Any}[Symbol(:pop_, t.from) => -flux, Symbol(:pop_, to) => flux], flux
end

_closure_observables(cl::_WellMixedClosure, lm::_LiftModel, ::LiftContributions) =
    _untyped_common_observables(cl, lm, _node_S(cl))

function _initial_values(cl::_WellMixedClosure, lm::_LiftModel, ρ)
    v = Dict{Symbol,Float64}(:θ => 1.0, :ξ => 1.0)
    for X in lm.nodes
        v[Symbol(:pop_, X)] = get(ρ, X, 0.0)
    end
    return v
end

_seed_expressions(cl::_WellMixedClosure, lm::_LiftModel, seeds) =
    Dict{Any,Any}(cl.q => 1 - _sum_terms(Any[seeds[X] for X in lm.nodes if haskey(seeds, X)]))

"""
    edge_based(cm::ContactModel, net::WellMixed; name = :edge_based_model, form = :expanded)

The edge-based lift on `WellMixed(κ)`: fleeting contacts with uniformly random partners, κ per
node per unit time, so the per-capita infection hazard is κ Σ_r τ_r x_{J_r} (design §C.2). The
coordinates are `θ` (the integrated per-contact hazard, θ(0) = 1), `ξ` (with exits) and
`pop_X` = x_X, with S = qξe^{κ(θ−1)}. It is the unit of the lift (M1): conjugate to the
mass-action ODE `mass_action(cm; κ)` of the model with contact rates κτ. With a
`FrequencyDependent` model (β·S·I on fractions) the per-contact rate is τ = β/κ, so the lift
equals the model's mass-action ODE for every κ. See the `ConfigurationNetwork` method for the
seeding, the observables and the cumulative accumulator; only the expanded form exists.
"""
function edge_based(cm::ContactModel, net::WellMixed; name::Symbol = :edge_based_model,
                    form::Symbol = :expanded)
    form === :expanded || throw(ArgumentError(
        "edge_based on a WellMixed network has only the expanded form; got form = :$form"))
    require_admissible(cm, :edge_based; network = net)
    return _assemble(cm, net; name, context = _lift_context(cm, net))
end

"""
    _well_mixed_unit(sys::EdgeModelSystem) -> Semiconjugacy

The well-mixed unit M1 (design §D.5) of a system lifted on `WellMixed(κ)`: the map
(θ, ξ, x) ↦ (S = qξe^{κ(θ−1)}, x) from its uncompiled field (`symbolic_ode(sys)`) to the
mass-action ODE `mass_action(cm; κ)` of the model. It is a conjugacy for exit-free models without
removals (onto S ∈ (0, q]) and a quotient semiconjugacy otherwise (ξ, and the removal sink, are
forgotten). `verify(_well_mixed_unit(sys))` checks it.
"""
function _well_mixed_unit(sys::EdgeModelSystem)
    md = sys.metadata
    get(md, :closure, nothing) === :well_mixed || throw(ArgumentError(
        "_well_mixed_unit: the system was not lifted on a WellMixed network"))
    cm, net = md[:model], md[:network]
    src = md[:raw]
    tgt = mass_action(cm; κ = net.κ)
    coords = md[:coords]
    s = md[:susceptible]
    θ = coords[:θ]
    ξ = get(coords, :ξ, 1)
    q = md[:q][s].param
    map = Pair{Any,Any}[]
    for (X, v) in zip(state_names(tgt), tgt.states)
        push!(map, v => (X === s ? q * ξ * exp(net.κ * (θ - 1)) : coords[Symbol(:pop_, X)]))
    end
    exact = !haskey(coords, :ξ) && isempty(md[:sinks])
    return Semiconjugacy(:well_mixed_unit, src, tgt, map, Pair{Any,Any}[],
                         exact ? :conjugacy : :semiconjugacy, :exact,
                         [Evidence(:paper, "Miller, Slim & Volz 2012, Part II (papers/1106.6319v1.md:103-111)"),
                          Evidence(:symbolic, "EdgeBasedModels test/suites/lift_wellmixed.jl")])
end
