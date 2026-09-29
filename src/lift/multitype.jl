# Owner: WP17 (DESIGN_NetworkEpiCore.md §A.3, §C.2, §C.3, §D.5 M10, §D.6 H7/H8, §J.6; work
# package in §G.2).
#
# The MultitypeNetwork closure of the per-reaction assembler (lift/assembler.jl): typed
# configuration networks (`sbm_network`, `unstructured`, any `MultivariateDegree` per type) with
# stratified models (`stratify`, `disjoint_union`), the multitype edge-based model of Miller &
# Volz (2013, §3.3). A type-a node has the joint degree PGF ψ_a(x) = E[Π_b x_b^{k_{a→b}}] and
# the fraction n_a of the nodes; each species carries a stratum (its node type).
#
# Coordinates, only for the edge classes that exist (E[k_{a→b}] > 0; structural zeros are
# skipped, so absent blocks produce no coordinates and no NaN: ebm-core #11, verified issues E11
# and E32):
#
#     θ_<b>_<a>   P(an edge from a type-b partner has not transmitted to a type-a test node)
#     φ_<Y>_<a>   the same edge, with the (type-b) partner in the species Y
#     pop_<Y>     the fraction of ALL nodes in Y;  ξ_<s>, q_<s> per susceptible species s
#
# with S_a = n_a q_a ξ_a ψ_a(θ_{·→a}) and φ_{s_a, c} = q_a ξ_a ∂_cψ_a(θ_{·→a})/∂_cψ_a(1). A contact
# s_a + J_b → X_a + J_b at rate τ contributes θ̇_{b→a} −= τφ_{J_b,a}, φ̇_{J_b,a} −= τφ_{J_b,a},
# φ̇_{X_a,c} += τφ_{J_b,a}·q_aξ_a∂_b∂_cψ_a/∂_cψ_a(1) for every c, and
# pop_{X_a}' += τφ_{J_b,a}·n_a q_a ξ_a ∂_bψ_a; transitions and exits act within the type.
# Seeds are fractions of ALL nodes (§J.6): SeedFraction(:I_a => ρ) puts ρN nodes of type a in I_a,
# so the within-type fraction, the initial φ_{I_a,·}, is ρ/n_a.

struct _MultitypeClosure <: _EdgeClosure
    net::MultitypeNetwork
    types::Vector{Symbol}
    n::Dict{Symbol,Float64}
    degrees::Dict{Symbol,MultivariateDegree}
    index::Dict{Symbol,Int}
    type_of::Dict{Symbol,Symbol}               # species (and sinks) => node type
    sus::Dict{Symbol,Symbol}                   # node type => its susceptible species (of the part)
    info::Vector{_Coordinate}
    θ::Dict{Tuple{Symbol,Symbol},Any}          # (partner type b, test type a) => θ_{b→a}
    ξ::Dict{Symbol,Any}                        # node type => ξ
    q::Dict{Symbol,Any}                        # node type => q
    φ::Dict{Tuple{Symbol,Symbol},Any}          # (species Y, test type a) => φ_{Y,a}
    pop::Dict{Symbol,Any}
    cache::Dict{Any,Any}                       # ψ_a and its partial derivatives
end

_closure_kind(::_MultitypeClosure) = :multitype
_coordinates(cl::_MultitypeClosure) = cl.info
_seed_factors(cl::_MultitypeClosure) = Pair{Symbol,Any}[s => cl.q[a] for (a, s) in cl.sus]
_type_of(cl::_MultitypeClosure, X::Symbol) = cl.type_of[X]
_type_size(cl::_MultitypeClosure, a::Symbol) = cl.n[a]
_seed_background(::_MultitypeClosure, ::_LiftModel) = nothing
_network_terms(cl::_MultitypeClosure) =
    vcat(collect(Any, values(cl.cache)),
         Any[_mean(cl, a, c) for a in cl.types for c in cl.types if _has_class(cl, a, c)])

# Do type-a nodes have type-b partners (E[k_{a→b}] ≠ 0 identically)? By reciprocity, the same as
# (b, a). A symbolic mean is not a structural zero (its runtime zero is guarded by `_ratio`).
_has_class(cl::_MultitypeClosure, a::Symbol, b::Symbol) =
    !cl.net.structural_zero[cl.index[a], cl.index[b]]

_mt_theta_name(b::Symbol, a::Symbol) = Symbol(:θ_, b, :_, a)
_mt_phi_name(Y::Symbol, a::Symbol) = Symbol(:φ_, Y, :_, a)

function _edge_closure(net::MultitypeNetwork, lm::_LiftModel)
    # heterogeneous susceptibility (design §L.7): species without a stratum on node types that are
    # independent of the network (`unstructured(net, st)`) are shared; lift/heterogeneous.jl
    _heterogeneous_susceptibility(lm) && _unstructured_degrees(net) !== nothing &&
        return _heterogeneous_closure(net, lm)
    types = collect(Symbol, net.types)
    index = Dict{Symbol,Int}(a => i for (i, a) in enumerate(types))
    n = Dict{Symbol,Float64}(a => net.sizes[i] for (a, i) in index)
    degrees = Dict{Symbol,MultivariateDegree}(a => net.degrees[i] for (a, i) in index)
    type_of = Dict{Symbol,Symbol}()
    for X in vcat(lm.Σ, lm.nodes)
        a = lm.stratum[X]
        a in types || throw(ArgumentError(
            "$(lm.context): the species $(X) " *
            (a === :all ? "has no stratum" : "belongs to the stratum $(a), which is not a node type") *
            "; on a MultitypeNetwork (types $(join(types, ", "))) every species must be labelled " *
            "with its node type (use stratify(model, strata(...)) or disjoint_union)"))
        type_of[X] = a
    end
    sus = Dict{Symbol,Symbol}()
    for s in lm.Σ
        a = type_of[s]
        haskey(sus, a) && throw(ArgumentError(
            "$(lm.context): the node type $(a) has two susceptible classes, $(sus[a]) and $(s)"))
        sus[a] = s
    end
    Z = net.structural_zero
    has(a, b) = !Z[index[a], index[b]]
    info = _Coordinate[]
    θ = Dict{Tuple{Symbol,Symbol},Any}()
    ξ = Dict{Symbol,Any}()
    q = Dict{Symbol,Any}()
    for a in types
        haskey(sus, a) || continue
        s = sus[a]
        for b in types
            has(a, b) || continue
            name = _mt_theta_name(b, a)
            θ[(b, a)] = _state(name)
            push!(info, _Coordinate(name, θ[(b, a)], :θ, s, (b, a)))
        end
        name = Symbol(:ξ_, s)
        ξ[a] = _state(name)
        push!(info, _Coordinate(name, ξ[a], :ξ, s, (a, a)))
        q[a] = _param(Symbol(:q_, s))
    end
    φ = Dict{Tuple{Symbol,Symbol},Any}()
    pop = Dict{Symbol,Any}()
    for Y in lm.nodes
        b = type_of[Y]
        for a in types
            has(a, b) || continue
            name = _mt_phi_name(Y, a)
            φ[(Y, a)] = _state(name)
            push!(info, _Coordinate(name, φ[(Y, a)], :φ, Y, (b, a)))
        end
    end
    for Y in lm.nodes
        name = Symbol(:pop_, Y)
        pop[Y] = _state(name)
        b = type_of[Y]
        push!(info, _Coordinate(name, pop[Y], :pop, Y, (b, b)))
    end
    return _MultitypeClosure(net, types, n, degrees, index, type_of, sus, info, θ, ξ, q, φ, pop,
                             Dict{Any,Any}())
end

# ψ_a at θ_{·→a} and its partial derivatives ∂_{b₁}⋯ψ_a (NetworkEpiCore's closed forms), cached.
function _ψ(cl::_MultitypeClosure, a::Symbol, bs::Symbol...)
    key = (a, bs...)
    haskey(cl.cache, key) && return cl.cache[key]
    x(b) = haskey(cl.θ, (b, a)) ? cl.θ[(b, a)] : 1.0
    m = cl.degrees[a]
    v = isempty(bs) ? pgf(m, x) : pgf_derivative(m, x, bs...)
    cl.cache[key] = v
    return v
end
_mean(cl::_MultitypeClosure, a::Symbol, c::Symbol) = mean_degree(cl.degrees[a], c)   # E[k_{a→c}]

_node_S(cl::_MultitypeClosure, a::Symbol) = cl.n[a] * cl.q[a] * cl.ξ[a] * _ψ(cl, a)
# φ_{s_a, c}: the type-a partner of a type-c test node is susceptible (limit: independent attachment)
_edge_S(cl::_MultitypeClosure, a::Symbol, c::Symbol) =
    _ratio(cl.q[a] * cl.ξ[a] * _ψ(cl, a, c), _mean(cl, a, c), cl.q[a] * cl.ξ[a] * _ψ(cl, a))

function _contact_terms(cl::_MultitypeClosure, c::Contact, τ)
    a, b = cl.type_of[c.recipient], cl.type_of[c.infector]
    cl.type_of[c.product] === a || throw(ArgumentError(
        "the contact `$(c.name)` turns a node of type $(a) ($(c.recipient)) into $(c.product) of " *
        "type $(cl.type_of[c.product]); node types are fixed on a MultitypeNetwork"))
    _has_class(cl, a, b) || return Pair{Symbol,Any}[], Symbolics.Num(0)   # no a–b edges
    h = τ * cl.φ[(c.infector, a)]
    qξ = cl.q[a] * cl.ξ[a]
    flux = h * cl.n[a] * qξ * _ψ(cl, a, b)
    terms = Pair{Symbol,Any}[_mt_theta_name(b, a) => -h, _mt_phi_name(c.infector, a) => -h]
    for e in cl.types
        _has_class(cl, e, a) || continue
        entry = _ratio(qξ * _ψ(cl, a, b, e), _mean(cl, a, e), qξ * _ψ(cl, a, b))
        push!(terms, _mt_phi_name(c.product, e) => h * entry)
    end
    push!(terms, Symbol(:pop_, c.product) => flux)
    return terms, flux
end

function _exit_terms(cl::_MultitypeClosure, t::NodeTransition, to::Symbol, ν)
    a = cl.type_of[t.from]
    cl.type_of[to] === a || throw(ArgumentError(
        "the exit `$(t.name)` moves a node of type $(a) into $(to) of type $(cl.type_of[to]); node " *
        "types are fixed on a MultitypeNetwork"))
    flux = ν * _node_S(cl, a)
    terms = Pair{Symbol,Any}[Symbol(:ξ_, t.from) => -ν * cl.ξ[a]]
    for e in cl.types
        _has_class(cl, e, a) || continue
        push!(terms, _mt_phi_name(to, e) => ν * _edge_S(cl, a, e))
    end
    push!(terms, Symbol(:pop_, to) => flux)
    return terms, flux
end

function _transition_terms(cl::_MultitypeClosure, t::NodeTransition, to::Symbol, a)
    X = t.from
    b = cl.type_of[X]
    cl.type_of[to] === b || throw(ArgumentError(
        "the transition `$(t.name)` moves a node of type $(b) ($(X)) into $(to) of type " *
        "$(cl.type_of[to]); node types are fixed on a MultitypeNetwork (stratify has no " *
        "transitions between strata)"))
    flux = a * cl.pop[X]
    terms = Pair{Symbol,Any}[]
    for e in cl.types
        _has_class(cl, e, b) || continue
        push!(terms, _mt_phi_name(X, e) => -a * cl.φ[(X, e)], _mt_phi_name(to, e) => a * cl.φ[(X, e)])
    end
    push!(terms, Symbol(:pop_, X) => -flux, Symbol(:pop_, to) => flux)
    return terms, flux
end

# Observables: per susceptible species s_a, the node-S S_a (named s_a) and the edge-S of every
# class, φ_<s_a>_<c>; the totals `:S` (when no species owns the name), `:I` and `:infectious`;
# and the legacy per-class hazards `edge_hazard_<b>_<a>` and `excess_hazard_<a>_<c>`.
function _closure_observables(cl::_MultitypeClosure, lm::_LiftModel, ::LiftContributions)
    obs = Pair{Symbol,Any}[]
    total = Any[]
    for a in cl.types
        haskey(cl.sus, a) || continue
        s = cl.sus[a]
        S = _node_S(cl, a)
        push!(total, S)
        push!(obs, s => S)
        for c in cl.types
            _has_class(cl, c, a) && push!(obs, _mt_phi_name(s, c) => _edge_S(cl, a, c))
        end
    end
    (:S in lm.nodes || :S in lm.Σ) || push!(obs, :S => _sum_terms(total))
    infectious = _sum_terms(Any[cl.pop[J] for J in lm.infectors])
    push!(obs, :I => infectious, :infectious => infectious)
    append!(obs, _mt_hazard_observables(cl, lm))
    return obs
end

# The hazards of the legacy multitype builder, for every class that has a θ coordinate:
#
#     edge_hazard_<b>_<a>   = Σ_{contacts s_a + J_b} τ φ_{J_b,a} = −θ̇_{b→a}
#     excess_hazard_<a>_<c> = Σ_b edge_hazard_<b>_<a> ∂_c∂_bψ_a / ∂_cψ_a  (at θ_{·→a})
#
# the rate at which the type-a partner of a type-c test node is infected through its other edges
# (φ_{s_a,c} decays at this rate plus the exits). Observables only: the division by ∂_cψ_a(θ)
# never enters the field (E27). Where a symbolic mean E[k_{a→c}] is 0 at solve time, φ_{s_a,c}
# is the κ → 0 limit q_aξ_aψ_a(θ) (independent attachment) and the excess hazard is that of
# E11's corrected fix, Σ_b edge_hazard_<b>_<a> ∂_bψ_a/ψ_a: still the decay rate of φ_{s_a,c},
# and continuous in the mean (not 0/0).
function _mt_hazard_observables(cl::_MultitypeClosure, lm::_LiftModel)
    h = Dict{Tuple{Symbol,Symbol},Any}(k => Symbolics.Num(0) for k in keys(cl.θ))
    for (c, τ) in zip(contacts(lm.cm), lm.contact_rates)
        a, b = cl.type_of[c.recipient], cl.type_of[c.infector]
        haskey(h, (b, a)) && (h[(b, a)] += τ * cl.φ[(c.infector, a)])
    end
    obs = Pair{Symbol,Any}[]
    for a in cl.types, b in cl.types
        haskey(h, (b, a)) && push!(obs, Symbol(:edge_hazard_, b, :_, a) => h[(b, a)])
    end
    for a in cl.types
        haskey(cl.sus, a) || continue
        hb = [b for b in cl.types if haskey(h, (b, a))]
        limit = _sum_terms(Any[h[(b, a)] * _ψ(cl, a, b) for b in hb]) / _ψ(cl, a)
        for c in cl.types
            _has_class(cl, a, c) || continue
            excess = _unless_zero(_mean(cl, a, c), limit) do _
                _sum_terms(Any[h[(b, a)] * _ψ(cl, a, c, b) for b in hb]) / _ψ(cl, a, c)
            end
            push!(obs, Symbol(:excess_hazard_, a, :_, c) => excess)
        end
    end
    return obs
end

# θ = ξ = 1; φ_{Y,·}(0) = ρ_Y/n_type (the within-type fraction) and pop_Y(0) = ρ_Y (§J.6).
function _initial_values(cl::_MultitypeClosure, lm::_LiftModel, ρ)
    v = Dict{Symbol,Float64}()
    for x in cl.info
        v[x.name] = x.role in (:θ, :ξ) ? 1.0 :
                    x.role === :pop ? get(ρ, x.species, 0.0) :
                    get(ρ, x.species, 0.0) / cl.n[cl.type_of[x.species]]
    end
    return v
end

# q_<s_a> = 1 − Σ_{X of type a} seed_X/n_a.
function _seed_expressions(cl::_MultitypeClosure, lm::_LiftModel, seeds)
    out = Dict{Any,Any}()
    for (a, s) in cl.sus
        own = Any[seeds[X] for X in lm.nodes if haskey(seeds, X) && cl.type_of[X] === a]
        out[cl.q[a]] = 1 - _sum_terms(own) / cl.n[a]
    end
    return out
end

function _relabel_coordinate(::Val{:multitype}, x::_Coordinate, m)
    X = m(x.species)
    name = x.role === :θ ? x.name :
           x.role === :ξ ? Symbol(:ξ_, X) :
           x.role === :φ ? _mt_phi_name(X, last(x.types)) : Symbol(:pop_, X)
    var = name === x.name ? x.var : _state(name)
    return _Coordinate(name, var, x.role, X, x.types)
end

"""
    edge_based(cm::ContactModel, net::MultitypeNetwork; name = :edge_based_model, form = :expanded)

The multitype edge-based lift (Miller & Volz 2013, §3.3) of a stratified model on a typed
configuration network: `stratify(model, st)` on `sbm_network(st; mean_contacts)` or
`unstructured(net, st)`, `disjoint_union(:a => A, :b => B)` on a network with the matching
types, or any model whose species are labelled with the node types. Every node type has one
susceptible class; node types are fixed, so contacts and transitions stay within the recipient's
type. A model with shared species (without a stratum) on `unstructured(net, st)` is heterogeneous
susceptibility and is lifted as `edge_based(model, net, st)` (design §L.7; see that method). Coordinates exist only for the edge classes that the network has (structural zeros
E[k_{a→b}] = 0 are skipped, so absent blocks produce neither coordinates nor NaN):

- `θ_<b>_<a>`: the probability that an edge from a type-b partner has not transmitted to a
  type-a test node (the argument x_b of ψ_a);
- `φ_<Y>_<a>`: the same edge, with its partner in the species `Y` (e.g. `φ_I_b_a`, `φ_S_b_a` for
  the susceptible observable);
- `pop_<Y>`: the fraction of **all** nodes in Y; `ξ_<s>` for a type with exits; `cumulative`;

with S_a = n_a q_a ξ_a ψ_a(θ_{·→a}). Seeds are fractions of all nodes (design §J.6):
`SeedFraction(:I_a => 0.005, :I_b => 0.005)` seeds 1% of a network with n_a = n_b = 1/2; the seed
fraction of X is the parameter `seed_X`, and q_a = 1 − Σ_{X of type a} seed_X/n_a. A background
`SeedFraction(...; default = :S_a)` would give S_a the complement over all nodes, not within type
a, so it is refused (an `ArgumentError`) unless the two agree; name only the seeded species (the
susceptible fractions follow). Observables: `S_a` (each
susceptible species), `φ_<s_a>_<c>`, the totals `:S` (when free), `:I` and `:infectious`, and the
legacy hazards `edge_hazard_<b>_<a>` (θ̇_{b→a} = −edge_hazard_<b>_<a>) and
`excess_hazard_<a>_<c>` (the rate at which the type-a partner of a type-c test node is infected
through its other edges, so that φ_{s_a,c} decays at this rate plus the exits; where a symbolic
E[k_{a→c}] is 0 at solve time, the κ → 0 limit Σ_b edge_hazard_<b>_<a>·∂_bψ_a/ψ_a of verified
issue E11). Stratified contact rates must be per-contact (`PerContact`). With one
stratum, or on `unstructured(net, st)` with proportional seeds, the lift reproduces the untyped
one (M10).
"""
function edge_based(cm::ContactModel, net::MultitypeNetwork; name::Symbol = :edge_based_model,
                    form::Symbol = :expanded)
    form === :expanded || throw(ArgumentError(
        "edge_based on a MultitypeNetwork has only the expanded form; got form = :$form"))
    require_admissible(cm, :edge_based; network = net)
    context = _lift_context(cm, net)
    # heterogeneous susceptibility (design §L.7): a model with shared (unlabelled) species on
    # `unstructured(net, st)` is the lift of lift/heterogeneous.jl, which also places shared seeds
    # as NetworkOutbreaks does; `edge_based(cm, net, st)` is the same system
    _heterogeneous_susceptibility(cm) && _unstructured_degrees(net) !== nothing &&
        return _assemble_heterogeneous(cm, net; name, context)
    return _assemble(cm, net; name, context)
end

# Heterogeneous susceptibility (lift/heterogeneous.jl): every susceptible class carries a stratum
# and some other species does not (it is shared by the node types). A model whose susceptible
# classes carry no stratum is not stratified at all and gets the multitype closure's error.
_heterogeneous_susceptibility(cm::ContactModel) =
    _heterogeneous_susceptibility(Dict{Symbol,Symbol}(X => _species_stratum(cm, X) for X in species_names(cm)),
                                  susceptible_species(cm))
_heterogeneous_susceptibility(lm::_LiftModel) = _heterogeneous_susceptibility(lm.stratum, lm.Σ)
function _heterogeneous_susceptibility(stratum::AbstractDict, Σ)
    isempty(Σ) && return any(==(:all), values(stratum)) && any(!=(:all), values(stratum))
    all(s -> stratum[s] !== :all, Σ) || return false
    return any(X -> !(X in Σ) && stratum[X] === :all, keys(stratum))
end
