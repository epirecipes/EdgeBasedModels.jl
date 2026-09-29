# Owner: WP22 (DESIGN_NetworkEpiCore.md §A.3, §A.6, §C.2, §C.3, §D.4, §D.6 H6; work package in
# §G.2; verified issues E12 and E13).
#
# The MultiplexNetwork closure of the per-reaction assembler (lift/assembler.jl): independent
# configuration-network layers ℓ = 1, …, L on one node set, with the joint degree PGF
# Ψ(x) = Π_ℓ ψ_ℓ(x_ℓ) (Miller & Volz 2013, PLoS ONE 8:e69162, §2.2.4 "multiple modes of
# transmission"; the seeded form of Jacobsen, Burch, Tien & Rempała 2018, J. Biol. Dyn.
# 12:746–788, eq. (13), after Miller 2014, PLoS ONE 9:e101421). Coordinates:
#
#     θ_<ℓ>       P(a layer-ℓ edge has not transmitted to the test node)
#     φ_<X>_<ℓ>   the same edge, with the partner in the species X
#     pop_<X>     the fraction of nodes in X;   ξ the exit factor;   q the initially susceptible fraction
#
# with S = qξΨ(θ) and φ_{S,m} = qξ∂_mΨ(θ)/∂_mΨ(1), ∂_mΨ(1) = ψ_m'(1). A contact
# s + J → X + J at rate τ on layer ℓ (on every layer when `layer = :all`, with the same τ; design
# §C.2) contributes, for each layer ℓ it acts on,
#
#     θ̇_ℓ −= τφ_{J,ℓ};   φ̇_{J,ℓ} −= τφ_{J,ℓ};   pop_X' += τφ_{J,ℓ}·qξ∂_ℓΨ(θ);
#     φ̇_{X,m} += τφ_{J,ℓ}·qξ∂_ℓ∂_mΨ(θ)/ψ_m'(1)   for EVERY layer m,
#
# the cross-layer factor: a node infected along a layer-ℓ edge has all its edges in the other
# layers (∂_ℓ∂_mΨ = ψ_ℓ'ψ_m'Π_{n≠ℓ,m}ψ_n for m ≠ ℓ, ψ_ℓ''Π_{n≠ℓ}ψ_n for m = ℓ). Transitions and
# exits act on every layer's φ. The mean degree ψ_m'(1) is the only divisor (a layer of mean degree
# 0 takes the κ → 0 limit of verified issues E11/E32, so no NaN), and θ_m = φ_{S,m} + Σ_X φ_{X,m}
# holds on every layer. R₀ is the spectral radius of the (layer × entry) next-generation matrix,
# never the sum of the layer R₀s (E12).
#
# Also here: the `form = :compact` reduction of SIR-shaped models (Jacobsen et al. eq. (13); the
# multiplex analogue of M9), the factory `build_multiplex_sir` (both its §A.6 form and the 0.1
# tuple form, which now returns an EdgeModelSystem: E13), and the corrected `multiplex_R0` and
# `susceptible_fraction` (E12, E13). They replace the 0.1 definitions of src/multiplex.jl, which
# WP29 deleted; the two 0.1 data types `NetworkLayer` and `MultiplexModel` are kept at the end of
# this file.

# ---------------------------------------------------------------------------------------------
# The closure
# ---------------------------------------------------------------------------------------------

struct _MultiplexClosure <: _EdgeClosure
    net::MultiplexNetwork
    layers::Vector{Symbol}
    s::Union{Symbol,Nothing}           # the susceptible species (nothing: a part without one)
    info::Vector{_Coordinate}
    θ::Dict{Symbol,Any}                # layer => θ_ℓ
    ξ::Any
    q::Any
    φ::Dict{Tuple{Symbol,Symbol},Any}  # (species, layer) => φ_<X>_<ℓ>
    pop::Dict{Symbol,Any}
    ψ::Dict{Symbol,Any}                # layer => ψ_ℓ(θ_ℓ), ψ_ℓ'(θ_ℓ), ψ_ℓ''(θ_ℓ), ψ_ℓ'(1)
    ψ1::Dict{Symbol,Any}
    ψ2::Dict{Symbol,Any}
    k̄::Dict{Symbol,Any}
end

_closure_kind(::_MultiplexClosure) = :multiplex
_coordinates(cl::_MultiplexClosure) = cl.info
_seed_factors(cl::_MultiplexClosure) = cl.s === nothing ? Pair{Symbol,Any}[] : [cl.s => cl.q]
_type_of(::_MultiplexClosure, ::Symbol) = :all
_type_size(::_MultiplexClosure, ::Symbol) = 1.0
_seed_background(cl::_MultiplexClosure, ::_LiftModel) = cl.s
_network_terms(cl::_MultiplexClosure) =
    cl.s === nothing ? Any[] :
    vcat(Any[cl.ψ[ℓ] for ℓ in cl.layers], Any[cl.ψ1[ℓ] for ℓ in cl.layers],
         Any[cl.ψ2[ℓ] for ℓ in cl.layers], Any[cl.k̄[ℓ] for ℓ in cl.layers])

# Layer-labelled contacts (`Contact(...; layer = :home)`) are lifted by this closure only.
_accepts_layers(::MultiplexNetwork) = true

_mpx_theta_name(ℓ::Symbol) = Symbol(:θ_, ℓ)
_mpx_phi_name(X::Symbol, ℓ::Symbol) = Symbol(:φ_, X, :_, ℓ)

# The layers a contact acts on: its own, or every layer for `layer = :all` (design §C.2).
function _contact_layers(cl::_MultiplexClosure, c::Contact)
    c.layer === :all && return cl.layers
    c.layer in cl.layers || throw(ArgumentError(
        "the contact `$(c.name)` is on the layer :$(c.layer), which is not a layer of the " *
        "multiplex network (layers: $(join(cl.layers, ", "))); use one of them or layer = :all"))
    return Symbol[c.layer]
end

function _edge_closure(net::MultiplexNetwork, lm::_LiftModel)
    layers = layer_names(net)
    s = _single_susceptible(lm)
    info = _Coordinate[]
    θ = Dict{Symbol,Any}()
    ξ = nothing
    q = nothing
    if s !== nothing
        for ℓ in layers
            name = _mpx_theta_name(ℓ)
            θ[ℓ] = _state(name)
            push!(info, _Coordinate(name, θ[ℓ], :θ, s, (ℓ, ℓ)))
        end
        ξ = _state(:ξ)
        push!(info, _Coordinate(:ξ, ξ, :ξ, s, (:all, :all)))
        q = _param(Symbol(:q_, s))
    end
    φ = Dict{Tuple{Symbol,Symbol},Any}()
    for X in lm.nodes, ℓ in layers
        name = _mpx_phi_name(X, ℓ)
        φ[(X, ℓ)] = _state(name)
        push!(info, _Coordinate(name, φ[(X, ℓ)], :φ, X, (ℓ, ℓ)))
    end
    pop = Dict{Symbol,Any}()
    for X in lm.nodes
        name = Symbol(:pop_, X)
        pop[X] = _state(name)
        push!(info, _Coordinate(name, pop[X], :pop, X, (:all, :all)))
    end
    ψ, ψ1, ψ2, k̄ = (Dict{Symbol,Any}() for _ in 1:4)
    if s !== nothing
        for ℓ in layers
            d = net[ℓ].degrees
            ψ[ℓ] = pgf(d, θ[ℓ])
            ψ1[ℓ] = pgf_derivative(d, θ[ℓ], 1)
            ψ2[ℓ] = pgf_derivative(d, θ[ℓ], 2)
            k̄[ℓ] = mean_degree(d)
        end
    end
    cl = _MultiplexClosure(net, layers, s, info, θ, ξ, q, φ, pop, ψ, ψ1, ψ2, k̄)
    for c in contacts(lm.cm)
        _contact_layers(cl, c)                     # every layer label must be a layer
    end
    return cl
end

# The joint PGF Ψ(θ) = Π_ℓ ψ_ℓ(θ_ℓ) and its partial derivatives, as products of the layer factors.
_mpx_others(cl::_MultiplexClosure, skip::Symbol...) =
    prod((cl.ψ[n] for n in cl.layers if !(n in skip)); init = 1)
_mpx_Ψ(cl::_MultiplexClosure) = _mpx_others(cl)
_mpx_∂Ψ(cl::_MultiplexClosure, ℓ::Symbol) = cl.ψ1[ℓ] * _mpx_others(cl, ℓ)
_mpx_∂∂Ψ(cl::_MultiplexClosure, ℓ::Symbol, m::Symbol) =
    ℓ === m ? cl.ψ2[ℓ] * _mpx_others(cl, ℓ) : cl.ψ1[ℓ] * cl.ψ1[m] * _mpx_others(cl, ℓ, m)

# The four factors with weight w = qξ (w = q in the compact form, which has no exits), and their
# κ → 0 limits where a layer's mean degree vanishes (the rare edge attaches independently of the
# node's other edges, E11/E32).
_mpx_node_S(cl::_MultiplexClosure, w) = w * _mpx_Ψ(cl)
_mpx_edge_S(cl::_MultiplexClosure, m::Symbol, w) =
    _ratio(w * _mpx_∂Ψ(cl, m), cl.k̄[m], w * _mpx_Ψ(cl))
_mpx_node_entry(cl::_MultiplexClosure, ℓ::Symbol, w) = w * _mpx_∂Ψ(cl, ℓ)
_mpx_edge_entry(cl::_MultiplexClosure, ℓ::Symbol, m::Symbol, w) =
    _ratio(w * _mpx_∂∂Ψ(cl, ℓ, m), cl.k̄[m], w * _mpx_∂Ψ(cl, ℓ))
_mpx_w(cl::_MultiplexClosure) = cl.q * cl.ξ

function _contact_terms(cl::_MultiplexClosure, c::Contact, τ)
    w = _mpx_w(cl)
    terms = Pair{Symbol,Any}[]
    fluxes = Any[]
    for ℓ in _contact_layers(cl, c)
        h = τ * cl.φ[(c.infector, ℓ)]
        push!(terms, _mpx_theta_name(ℓ) => -h, _mpx_phi_name(c.infector, ℓ) => -h)
        for m in cl.layers
            push!(terms, _mpx_phi_name(c.product, m) => h * _mpx_edge_entry(cl, ℓ, m, w))
        end
        f = h * _mpx_node_entry(cl, ℓ, w)
        push!(terms, Symbol(:pop_, c.product) => f)
        push!(fluxes, f)
    end
    return terms, _sum_terms(fluxes)
end

function _exit_terms(cl::_MultiplexClosure, t::NodeTransition, to::Symbol, ν)
    w = _mpx_w(cl)
    flux = ν * _mpx_node_S(cl, w)
    terms = Pair{Symbol,Any}[:ξ => -ν * cl.ξ]
    for m in cl.layers
        push!(terms, _mpx_phi_name(to, m) => ν * _mpx_edge_S(cl, m, w))
    end
    push!(terms, Symbol(:pop_, to) => flux)
    return terms, flux
end

function _transition_terms(cl::_MultiplexClosure, t::NodeTransition, to::Symbol, a)
    X = t.from
    flux = a * cl.pop[X]
    terms = Pair{Symbol,Any}[]
    for m in cl.layers
        push!(terms, _mpx_phi_name(X, m) => -a * cl.φ[(X, m)], _mpx_phi_name(to, m) => a * cl.φ[(X, m)])
    end
    push!(terms, Symbol(:pop_, X) => -flux, Symbol(:pop_, to) => flux)
    return terms, flux
end

# The edge hazard of layer ℓ, Σ over the contacts acting on ℓ of τφ_{J,ℓ} (θ̇_ℓ = −hazard).
_mpx_hazard(cl::_MultiplexClosure, lm::_LiftModel, ℓ::Symbol) =
    _sum_terms(Any[τ * cl.φ[(c.infector, ℓ)] for (c, τ) in zip(contacts(lm.cm), lm.contact_rates)
                   if c.layer === :all || c.layer === ℓ])

# Observables: the node-S (the susceptible species' name, and `:S` unless another species owns
# it), `:I` and `:infectious` (the fraction in infector states), and per layer the edge-S
# `φ_<s>_<ℓ>` and the edge hazard `edge_hazard_<ℓ>`.
function _closure_observables(cl::_MultiplexClosure, lm::_LiftModel, ::LiftContributions)
    w = _mpx_w(cl)
    obs = _untyped_common_observables(cl, lm, _mpx_node_S(cl, w))
    for ℓ in cl.layers
        push!(obs, _mpx_phi_name(cl.s, ℓ) => _mpx_edge_S(cl, ℓ, w))
    end
    for ℓ in cl.layers
        push!(obs, Symbol(:edge_hazard_, ℓ) => _mpx_hazard(cl, lm, ℓ))
    end
    return obs
end

# θ_ℓ(0) = ξ(0) = 1 and φ_{X,ℓ}(0) = pop_X(0) = ρ_X on every layer (design §E.2); the sinks
# start empty.
function _initial_values(cl::_MultiplexClosure, lm::_LiftModel, ρ)
    v = Dict{Symbol,Float64}(:ξ => 1.0)
    for ℓ in cl.layers
        v[_mpx_theta_name(ℓ)] = 1.0
    end
    for X in lm.nodes
        for ℓ in cl.layers
            v[_mpx_phi_name(X, ℓ)] = get(ρ, X, 0.0)
        end
        v[Symbol(:pop_, X)] = get(ρ, X, 0.0)
    end
    return v
end

# q_<s> = 1 − Σ_X seed_X.
_seed_expressions(cl::_MultiplexClosure, lm::_LiftModel, seeds) =
    Dict{Any,Any}(cl.q => 1 - _sum_terms(Any[seeds[X] for X in lm.nodes if haskey(seeds, X)]))

function _relabel_coordinate(::Val{:multiplex}, x::_Coordinate, m)
    X = m(x.species)
    x.role in (:θ, :ξ) && return _Coordinate(x.name, x.var, x.role, X, x.types)
    name = x.role === :φ ? _mpx_phi_name(X, first(x.types)) : Symbol(:pop_, X)
    var = name === x.name ? x.var : _state(name)
    return _Coordinate(name, var, x.role, X, x.types)
end

# ---------------------------------------------------------------------------------------------
# edge_based on a multiplex network
# ---------------------------------------------------------------------------------------------

"""
    edge_based(cm::ContactModel, net::MultiplexNetwork; name = :edge_based_model, form = :expanded)

The multiplex edge-based lift (Miller & Volz 2013, PLoS ONE 8:e69162, §2.2.4; the seeded form of
Jacobsen, Burch, Tien & Rempała 2018, J. Biol. Dyn. 12:746–788, eq. (13)) of a T_EB model on
independent configuration-network layers sharing one node set, `MultiplexNetwork(:home =>
RegularDegree(3), :comm => PoissonDegree(5))`. A contact `Contact(s, J, X, τ; layer = ℓ)`
transmits along the edges of layer ℓ only; `layer = :all` transmits along every layer with the
same τ (design §C.2). Every contact, transition, exit and removal contributes its own terms (see
[`lift_contributions`](@ref)), so branching, several infectors, exits (ξ) and removals (to the
sink `:removed`) are lifted exactly, as on a `ConfigurationNetwork`.

Coordinates, with ψ_ℓ the degree PGF of layer ℓ and Ψ(x) = Π_ℓ ψ_ℓ(x_ℓ):

- `θ_<ℓ>`: the probability that a layer-ℓ edge has not transmitted to a test node; `ξ` (exits only);
- `φ_<X>_<ℓ>`: a layer-ℓ edge that has not transmitted, with its partner in X; `pop_<X>`;
  `cumulative` (the fraction ever infected, seeds included);

with S = qξΨ(θ) and φ_{S,ℓ} = qξψ_ℓ'(θ_ℓ)Π_{m≠ℓ}ψ_m(θ_m)/ψ_ℓ'(1): the cross-layer factor
Π_{m≠ℓ}ψ_m(θ_m) is the probability that the partner at the end of a layer-ℓ edge has not been
infected through its other layers. A contact on layer ℓ feeds φ_{X,m} on **every** layer m. Seeds,
parameters and observables follow the configuration lift: `seed_<X>` parameters set by
`default_initial_conditions(sys; initial)`, θ_ℓ(0) = ξ(0) = 1, φ_{X,ℓ}(0) = pop_X(0) = ρ_X;
observables `S` (and the susceptible species' name), `:I`/`:infectious`, `φ_<s>_<ℓ>` and
`edge_hazard_<ℓ>` (θ̇_ℓ = −edge_hazard_<ℓ>). Per-contact rates follow the model's convention
with the layer's mean degree for a layer contact and the total for `:all` (design §B.6).

`form = :compact` gives, for SIR-shaped models (contacts s + I → 2I on any layers, one transition
I → R or I → ∅, no exits, seeds in I), Jacobsen et al.'s eq. (13): θ̇_ℓ = −τ_ℓθ_ℓ + τ_ℓφ_{S,ℓ} +
γ(1 − θ_ℓ) and Ṙ = γ(1 − S − R), with τ_ℓ the total rate of the contacts on layer ℓ; it is exact on
the invariant set {τ_ℓφ_{R,ℓ} + γθ_ℓ = γ for every ℓ} of the expanded form.

R₀ on a multiplex is the spectral radius of the (layer × entry) next-generation matrix
(`basic_reproduction_number(cm, net, p)`), never the sum of the layer R₀s (verified issue E12).
Two identical layers with equal τ are the configuration network of the summed degree only
because the layers are independent: in general the lift is not that of the product PGF (design
§D.6 H6), since stubs pair within layers.

```julia
net = MultiplexNetwork(:home => RegularDegree(3), :comm => PoissonDegree(5))
cm  = ContactModel(:sir_mpx; contacts = [Contact(:S, :I, :I, 0.18; layer = :home),
                                         Contact(:S, :I, :I, 0.06; layer = :comm)],
                   transitions = [NodeTransition(:I, :R, 0.25)])
sys = edge_based(cm, net)
sol = solve_epidemic(sys; initial = SeedFraction(:I => 0.01), tspan = (0.0, 80.0))
compartment(sys, sol, :cumulative)[end]
```
"""
function edge_based(cm::ContactModel, net::MultiplexNetwork; name::Symbol = :edge_based_model,
                    form::Symbol = :expanded)
    form in (:expanded, :compact) ||
        throw(ArgumentError("form must be :compact or :expanded, got :$form"))
    require_admissible(cm, :edge_based; network = net)
    context = _lift_context(cm, net)
    form === :compact && return _assemble_multiplex_compact(cm, net; name, context)
    return _assemble(cm, net; name, context)
end

# ---------------------------------------------------------------------------------------------
# The compact form (Jacobsen et al. 2018 eq. (13); M9 layer by layer)
# ---------------------------------------------------------------------------------------------

# The SIR shape on a multiplex: every contact is s + I → 2I (on any layer), one transition I → R
# (R may be the removal sink), no exits and no other species.
function _multiplex_compact_shape(lm::_LiftModel)
    cm = lm.cm
    fail() = throw(ArgumentError(
        "$(lm.context): form = :compact supports SIR-shaped models only (Jacobsen et al. 2018 " *
        "eq. (13)): contacts s + I → 2I on any layers, one transition I → R or I → ∅, no exits " *
        "and no other species; use form = :expanded for this model"))
    cs = contacts(cm)
    ts = node_transitions(cm)
    (!isempty(cs) && length(ts) == 1) || fail()
    t = only(ts)
    I = t.from
    s = first(cs).recipient
    all(c -> c.recipient === s && c.infector === I && c.product === I, cs) || fail()
    only(lm.transition_types) !== :exit || fail()
    R = only(lm.transition_targets)
    Set(lm.nodes) == Set([I, R]) || fail()
    return s, I, R, only(lm.transition_rates)
end

function _assemble_multiplex_compact(cm::ContactModel, net::MultiplexNetwork; name::Symbol,
                                     context::AbstractString)
    lm = _lift_model(cm, net, susceptible_species(cm); context)
    s, I, R, γ = _multiplex_compact_shape(lm)
    cl = _edge_closure(net, lm)
    layers = cl.layers
    q = cl.q
    θs = Any[cl.θ[ℓ] for ℓ in layers]
    popR = cl.pop[R]
    # the total per-contact rate on each layer (a contact on :all counts on every layer)
    τℓ = Dict{Symbol,Any}(ℓ => _sum_terms(Any[τ for (c, τ) in zip(contacts(cm), lm.contact_rates)
                                              if c.layer === :all || c.layer === ℓ]) for ℓ in layers)
    S = _mpx_node_S(cl, q)
    φS = Dict{Symbol,Any}(ℓ => _mpx_edge_S(cl, ℓ, q) for ℓ in layers)
    fθ = Any[-τℓ[ℓ] * cl.θ[ℓ] + τℓ[ℓ] * φS[ℓ] + γ * (1 - cl.θ[ℓ]) for ℓ in layers]
    fR = γ * (1 - S - popR)
    raw = SymbolicODE(Symbol(name, :_edge_based_compact); states = vcat(θs, Any[popR]),
                      rhs = vcat(fθ, Any[fR]), parameters = :infer,
                      domain = Pair{Any,Tuple{Float64,Float64}}[θ => (0.05, 1.0) for θ in θs])
    seed = _param(Symbol(:seed_, I))
    qsub = Dict{Any,Any}(q => 1 - seed)
    popname, popIname = Symbol(:pop_, R), Symbol(:pop_, I)
    popI = 1 - S - popR
    obs = Pair{Symbol,Any}[s => S]
    s !== :S && _alias_free(lm, :S) && push!(obs, :S => S)
    push!(obs, popIname => popI, :I => popI, :infectious => popI, :cumulative => 1 - S)
    for ℓ in layers
        push!(obs, _mpx_phi_name(s, ℓ) => φS[ℓ])
    end
    obsnames = unique!(Symbol[first(o) for o in obs])
    θnames = Symbol[_mpx_theta_name(ℓ) for ℓ in layers]
    generated = vcat(θnames, Symbol[popname], obsnames, Symbol[_symname(q), _symname(seed)])
    _check_generated_names(lm, generated, vcat(θs, Any[popR, q]),
                           vcat(fθ, Any[fR], Any[last(o) for o in obs]), _network_terms(cl))
    sub(e) = Symbolics.substitute(e, qsub)
    D = D_nounits
    eqs = Equation[D(x) ~ sub(f) for (x, f) in zip(θs, fθ)]
    push!(eqs, D(popR) ~ sub(fR))
    obsvars = Dict{Symbol,Any}()
    for (k, e) in obs
        haskey(obsvars, k) && continue
        v = _state(k)
        obsvars[k] = v
        push!(eqs, v ~ sub(e))
    end
    compiled = mtkcompile(System(eqs, t_nounits; name))
    variables = Dict{Symbol,Any}(n => θ for (n, θ) in zip(θnames, θs))
    variables[popname] = popR
    variables[popIname] = obsvars[popIname]
    _add_recovered_alias!(variables, lm)
    table = _contributions(cl, lm, net)
    seeds = Dict{Symbol,Any}(I => seed)
    md = _assembled_metadata(cm, net, lm, cl, table, raw, seeds, qsub, Symbol[I]; form = :compact)
    md[:coords] = Dict{Symbol,Any}(vcat([n => θ for (n, θ) in zip(θnames, θs)], [popname => popR]))
    md[:ic] = function (initial; N = nothing)
        ρ, given = _seeds(lm, s, initial; N)
        _check_susceptible_seeds(cl, lm, ρ, given)
        get(ρ, R, 0.0) == 0 || throw(ArgumentError(
            "default_initial_conditions: the compact form seeds only $(I) (its invariant set has " *
            "φ_$(R)_ℓ(0) = 0); use form = :expanded to seed $(R)"))
        ic = Dict{Any,Float64}(θ => 1.0 for θ in θs)
        ic[popR] = 0.0
        ic[seed] = ρ[I]
        return ic
    end
    return EdgeModelSystem(compiled, variables, obsvars, md)
end

# ---------------------------------------------------------------------------------------------
# The factory (design §A.6) and the 0.1 tuple form (verified issue E13)
# ---------------------------------------------------------------------------------------------

# A layer's degree distribution: a NetworkEpiCore distribution (a legacy DegreePGF included) or
# the distribution of a ConfigurationNetwork.
_mpx_degrees(d::DegreeDistribution) = d
_mpx_degrees(n::ConfigurationNetwork) = n.degrees
_mpx_degrees(x) = throw(ArgumentError(
    "a multiplex layer needs a degree distribution (e.g. RegularDegree(3), PoissonDegree(5), a " *
    "legacy DegreePGF) or a ConfigurationNetwork; got $(typeof(x))"))

# One recovery rate shared by every layer (Miller & Volz 2013 §2.2.4 and Jacobsen et al. eq. (13)
# assume a node-level recovery rate that does not depend on the layer).
function _mpx_shared_recovery(γs)
    isempty(γs) && throw(ArgumentError("build_multiplex_sir: no layers given"))
    γ = first(γs)
    same(a, b) = (a isa Real && b isa Real && !(a isa Symbolics.Num) && !(b isa Symbolics.Num)) ?
                 isapprox(a, b) : isequal(a, b)
    for g in γs
        same(g, γ) || throw(ArgumentError(
            "build_multiplex_sir: the recovery rate is a property of the node, not of the layer, so " *
            "every layer must give the same γ (got $(join(string.(γs), ", "))); for layer-dependent " *
            "progression write the ContactModel and use edge_based(cm, MultiplexNetwork(...))"))
    end
    return γ
end

"""
    build_multiplex_sir(ℓ₁ => (degrees₁, τ₁), ℓ₂ => (degrees₂, τ₂), ...; γ, name = :multiplex_sir,
                        form = :expanded) -> EdgeModelSystem
    build_multiplex_sir(layers::Vector{<:Tuple}; name = :multiplex_sir, form = :expanded)
        -> EdgeModelSystem

The edge-based SIR model on a multiplex network of independent layers with per-contact rates τ_ℓ
(Miller & Volz 2013, PLoS ONE 8:e69162, §2.2.4, multiple modes of transmission; seeded as in
Jacobsen, Burch, Tien & Rempała 2018, J. Biol. Dyn. 12:746–788, eq. (13), after Miller 2014, PLoS
ONE 9:e101421). Equivalent to

```julia
edge_based(ContactModel(name; contacts = [Contact(:S, :I, :I, τ_ℓ; layer = ℓ) for each layer],
                        transitions = [NodeTransition(:I, :R, γ)]),
           MultiplexNetwork(ℓ₁ => degrees₁, ℓ₂ => degrees₂, ...); name, form)
```

(see [`edge_based`](@ref)). A layer's degrees are a NetworkEpiCore degree distribution
(`RegularDegree(3)`, `PoissonDegree(5)`), a legacy [`DegreePGF`](@ref) (`poisson_pgf(3.0)`) or a
`ConfigurationNetwork`. Rates may be numbers, Symbols (parameters set with `p` in
[`solve_epidemic`](@ref)), expressions or symbolic parameters. There is one recovery rate γ for
every layer: it belongs to the node. A vector of such pairs is accepted too.

The second form takes the 0.1 layers `(name, degrees, τ, γ)` (every γ equal). **It changed in
0.2** (verified issue E13): it returns an `EdgeModelSystem` instead of a
`(system, u0, tspan, p)` tuple, and seeds a fraction ρ of the nodes with θ_ℓ(0) = 1 and
S(0) = 1 − ρ (`default_initial_conditions(sys; initial = SeedFraction(:I => ρ))` or
`solve_epidemic(sys; initial, tspan)`), instead of the unphysical θ_ℓ(0) = 1 − 10⁻⁶ without a
seed; the `tspan` keyword is ignored (a deprecation warning), pass it to `solve_epidemic`.
`form = :compact` gives the 0.1 shape (one θ_ℓ per layer and R); the default expanded form adds
the φ coordinates.

The epidemic threshold is R₀ = ρ(K) ([`multiplex_R0`](@ref)), not the sum of the layer R₀s.

```julia
sys = build_multiplex_sir(:home => (RegularDegree(3), 0.18), :comm => (PoissonDegree(5), 0.06); γ = 0.25)
sol = solve_epidemic(sys; initial = SeedFraction(:I => 0.01), tspan = (0.0, 80.0))
compartment(sys, sol, :R)[end]
```
"""
function build_multiplex_sir(layer::Pair{Symbol,<:Tuple}, layers::Pair{Symbol,<:Tuple}...;
                             γ, name::Symbol = :multiplex_sir, form::Symbol = :expanded)
    all_layers = (layer, layers...)
    for (ℓ, v) in all_layers
        length(v) == 2 || throw(ArgumentError(
            "build_multiplex_sir: layer :$(ℓ) must be given as :$(ℓ) => (degrees, τ); got $(v)"))
    end
    cs = Contact[Contact(:S, :I, :I, last(v); layer = ℓ) for (ℓ, v) in all_layers]
    cm = ContactModel(name; contacts = cs, transitions = [NodeTransition(:I, :R, γ)])
    net = MultiplexNetwork(Pair{Symbol,ConfigurationNetwork}[
        ℓ => ConfigurationNetwork(_mpx_degrees(first(v))) for (ℓ, v) in all_layers])
    return edge_based(cm, net; name, form)
end

build_multiplex_sir(layers::Vector{<:Pair{Symbol,<:Tuple}}; kw...) = build_multiplex_sir(layers...; kw...)
build_multiplex_sir(layers::Vector{<:Tuple}; kw...) = _build_multiplex_sir_tuples(layers; kw...)
build_multiplex_sir(layers::Vector{Any}; kw...) = _build_multiplex_sir_tuples(layers; kw...)

function _build_multiplex_sir_tuples(layers::AbstractVector; tspan = nothing,
                                     name::Symbol = :multiplex_sir, form::Symbol = :expanded)
    tspan === nothing || Base.depwarn(
        "build_multiplex_sir(layers; tspan): the tspan keyword is deprecated and ignored, since " *
        "build_multiplex_sir now returns an EdgeModelSystem; pass tspan to " *
        "solve_epidemic(sys; initial, tspan) (verified issue E13)",
        :build_multiplex_sir)
    _check_legacy_layers(layers, "build_multiplex_sir")
    γ = _mpx_shared_recovery(Any[l[4] for l in layers])
    pairs = [Symbol(l[1]) => (l[2], l[3]) for l in layers]
    return build_multiplex_sir(pairs...; γ, name, form)
end

function _check_legacy_layers(layers, fname)
    isempty(layers) && throw(ArgumentError("$fname: no layers given"))
    for l in layers
        (l isa Tuple && length(l) == 4) || throw(ArgumentError(
            "$fname: each layer must be a (name, degrees, τ, γ) tuple; got $(l)"))
    end
    return nothing
end

# ---------------------------------------------------------------------------------------------
# multiplex_R0 (verified issue E12) and susceptible_fraction (E13)
# ---------------------------------------------------------------------------------------------

_mpx_numeric(x) = x isa Real && !(x isa Symbolics.Num)

"""
    multiplex_R0(layers) -> R₀

The basic reproduction number of the multiplex SIR model of the 0.1 layers `(name, degrees, τ, γ)`
(every γ equal; see [`build_multiplex_sir`](@ref)): the spectral radius of the layer
next-generation matrix

    K = diag(T)·M,   T_i = τ_i/(τ_i + γ),   M_ii = ψ_i''(1)/ψ_i'(1),   M_ij = ψ_j'(1) (i ≠ j),

obtained by linearising θ̇_i at the disease-free state (Jacobsen, Burch, Tien & Rempała 2018,
J. Biol. Dyn. 12:746–788, App. A.1: R₀ is the spectral radius of the NGM). K is similar to the
expected-offspring matrix (T_i ψ_i''(1)/ψ_i'(1) within a layer, T_iψ_i'(1) from a layer-j case
into layer i), so the entries are not per-layer "contributions" and do not add: R₀ equals the
sum Σ_i T_iψ_i''(1)/ψ_i'(1) of the layer R₀s only when det K = 0 (for example independent
Poisson layers), and can be larger or smaller otherwise (verified issue E12; 0.1 returned the
sum). Numeric layers give a `Float64` for any number of layers; symbolic rates or degrees give the
closed form for one or two layers, (K₁₁ + K₂₂)/2 + √(((K₁₁ − K₂₂)/2)² + K₁₂K₂₁).

For any model on a `MultiplexNetwork`, use `basic_reproduction_number(cm, net, p)`
(NetworkEpiCore's numeric next-generation matrix over (layer, entry) blocks).
"""
function multiplex_R0(layers::Union{AbstractVector,Tuple})
    _check_legacy_layers(layers, "multiplex_R0")
    ls = collect(layers)
    for l in ls, r in (l[3], l[4])
        (r isa Symbol || r isa Expr) && throw(ArgumentError(
            "multiplex_R0: the rate $(r) is a name, not a value; give numbers or symbolic parameters, " *
            "or use basic_reproduction_number(cm, net, p) with the parameter values p"))
    end
    γ = _mpx_shared_recovery(Any[l[4] for l in ls])
    n = length(ls)
    T = Any[l[3] / (l[3] + γ) for l in ls]
    ds = [_mpx_degrees(l[2]) for l in ls]
    k = Any[pgf_derivative(d, 1.0, 1) for d in ds]                         # ψ_i'(1)
    κ = Any[(_mpx_numeric(k[i]) && iszero(k[i])) ? 0.0 : pgf_derivative(ds[i], 1.0, 2) / k[i]
            for i in 1:n]                                                   # ψ_i''(1)/ψ_i'(1)
    K = [T[i] * (i == j ? κ[i] : k[j]) for i in 1:n, j in 1:n]
    all(_mpx_numeric, K) && return Float64(maximum(abs, eigvals(Float64.(K))))
    n == 1 && return K[1, 1]
    if n == 2
        a, b, c, d = K[1, 1], K[1, 2], K[2, 1], K[2, 2]
        return (a + d) / 2 + sqrt(((a - d) / 2)^2 + b * c)
    end
    throw(ArgumentError("multiplex_R0: symbolic rates or degrees are supported for up to 2 layers " *
                        "(the spectral radius has no closed form beyond); got $(n) layers"))
end

"""
    susceptible_fraction(pgfs::Vector{<:DegreeDistribution}, θ::Vector{<:Real}; ρ = 0)
    susceptible_fraction(net::MultiplexNetwork, θ::AbstractVector; ρ = 0)

The susceptible fraction S = (1 − ρ)Π_ℓ ψ_ℓ(θ_ℓ) of a multiplex network with layer PGFs ψ_ℓ at
the edge variables θ_ℓ (in layer order), when a fraction ρ of the nodes was seeded (verified
issue E13: 0.1 had no seed factor).
"""
function susceptible_fraction(pgfs::Vector{<:DegreeDistribution}, θ::Vector{<:Real}; ρ::Real = 0)
    length(pgfs) == length(θ) || throw(ArgumentError(
        "susceptible_fraction: $(length(pgfs)) layers but $(length(θ)) values of θ"))
    return (1 - ρ) * prod(pgf(d, x) for (d, x) in zip(pgfs, θ))
end
function susceptible_fraction(net::MultiplexNetwork, θ::AbstractVector; ρ::Real = 0)
    length(net.layers) == length(θ) || throw(ArgumentError(
        "susceptible_fraction: the network has $(length(net.layers)) layers but $(length(θ)) " *
        "values of θ were given"))
    return (1 - ρ) * prod(pgf(last(l).degrees, x) for (l, x) in zip(net.layers, θ))
end

"""
    basic_reproduction_number(layers::AbstractVector{<:Tuple})

R₀ of the multiplex SIR model of the 0.1 layers `(name, degrees, τ, γ)`: the same as
[`multiplex_R0`](@ref)`(layers)`, the spectral radius of the layer next-generation matrix
(verified issue E12).
"""
basic_reproduction_number(layers::AbstractVector{<:Tuple}) = multiplex_R0(layers)

# ---------------------------------------------------------------------------------------------
# The 0.1 multiplex data types (kept for compatibility; no builder consumes them)
# ---------------------------------------------------------------------------------------------

"""
    NetworkLayer(name, pgf, progression)

A layer of a multiplex network in EdgeBasedModels 0.1: a name, a legacy [`DegreePGF`](@ref)
and a [`DiseaseProgression`](@ref). Kept so that 0.1 code constructing it still loads; no
function of EdgeBasedModels consumes it. Multiplex models are
`edge_based(model, MultiplexNetwork(ℓ₁ => ConfigurationNetwork(d₁), …))` with layer-labelled
contacts, or [`build_multiplex_sir`](@ref).
"""
struct NetworkLayer
    name::Symbol
    pgf::DegreePGF
    progression::DiseaseProgression
end

"""
    MultiplexModel(layers::Vector{NetworkLayer})

A multiplex model of EdgeBasedModels 0.1 (a vector of [`NetworkLayer`](@ref)s). Kept so that 0.1
code constructing it still loads; no function of EdgeBasedModels consumes it (see
[`build_multiplex_sir`](@ref) and `edge_based(model, ::MultiplexNetwork)`).
"""
struct MultiplexModel
    layers::Vector{NetworkLayer}
end
