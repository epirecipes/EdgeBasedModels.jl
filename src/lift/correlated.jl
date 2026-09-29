# Owner: WP36a (DESIGN_NetworkEpiCore.md §K WP36a, §C.3; work package in §K).
#
# The DegreeCorrelatedNetwork closure of the per-reaction assembler (lift/assembler.jl): the edge-based model on a
# configuration network with degree correlations between neighbours (the joint-degree or "2K" model), with one θ per
# degree class (Wang, Ma, Cao & Li 2018, J. Theor. Biol. 454:164, papers/degreecorrelation.md, eqs (21)–(24); the
# multitype edge-based framework of Miller & Volz 2013). Degree classes k have node fractions p_k and the edge-end
# matrix e (NetworkEpiCore `degree_correlated`), so a degree-k node's neighbours have degree l with probability
# Q(l | k) = e_kl/Σ_m e_km, independently. Coordinates, per degree class k > 0 of the (support-restricted, E20)
# descriptor:
#
#     θ_<k>      P(an edge into a degree-k test node has not transmitted)
#     φ_<Y>_<k>  the same edge, with its partner in the species Y
#     pop_<Y>    the fraction of all nodes in Y;  ξ, the exit survival factor
#
# The partner of an edge into a degree-k node has degree l with probability Q(l | k), and its other l − 1 edges point
# into a degree-l node, so it is susceptible with probability qξθ_l^{l−1}:
#
#     S = qξ Σ_k p_k θ_k^k,   φ_{s,k} = qξ Σ_l Q(l | k) θ_l^{l−1}.
#
# A contact s + J → X + J at rate τ contributes θ̇_k −= τφ_{J,k}, φ̇_{J,k} −= τφ_{J,k},
# φ̇_{X,k} += τ qξ Σ_l Q(l | k)(l − 1)θ_l^{l−2} φ_{J,l} (the entry factor, pre-cancelled) and
# pop_X' += τ qξ Σ_k p_k k θ_k^{k−1} φ_{J,k}; transitions act on φ_{·,k} and pop as on a configuration network, and an
# exit s → Y at rate ν gives ξ̇ −= νξ, φ̇_{Y,k} += νφ_{s,k}, pop_Y' += νS. Linearised at the disease-free state, the
# φ_{J,k} rows give Wang et al.'s next-generation matrix D_kl = (l − 1)Q(l | k) times the transmissibility; with
# Q(l | k) = q_l (no correlation, r = 0) every θ_k equals the configuration-model θ and the lift is the configuration
# lift of ψ = Σ_k p_k x^k. The closure is the quotient of the multitype lift of `MultitypeNetwork(net)` by the symmetry
# θ_{l→k} = θ_{l→k′} (the partner's other edges do not depend on the test node's degree): K coordinates per species
# instead of K².
#
# It also bridges the legacy `CorrelatedPGF` (src/pgf.jl) to the descriptor, with the support restriction of verified
# issue E20.

# ---------------------------------------------------------------------------------------------
# The closure
# ---------------------------------------------------------------------------------------------

struct _CorrelatedClosure <: _EdgeClosure
    net::DegreeCorrelatedNetwork
    s::Union{Symbol,Nothing}           # the susceptible species (nothing: a part without one)
    classes::Vector{Symbol}            # :k<degree>, the types of MultitypeNetwork(net)
    edged::Vector{Int}                 # the classes with edges (degree > 0), which have coordinates
    Q::Matrix{Float64}                 # Q[i, j] = Q(degree j | degree i); zero rows for degree 0
    info::Vector{_Coordinate}
    θ::Dict{Int,Any}                   # class => θ_<k>
    ξ::Any
    q::Any
    φ::Dict{Tuple{Symbol,Int},Any}     # (species Y, class) => φ_<Y>_<k>
    pop::Dict{Symbol,Any}
end

_closure_kind(::_CorrelatedClosure) = :degree_correlated
_coordinates(cl::_CorrelatedClosure) = cl.info
_seed_factors(cl::_CorrelatedClosure) = cl.s === nothing ? Pair{Symbol,Any}[] : [cl.s => cl.q]
_type_of(::_CorrelatedClosure, ::Symbol) = :all
_type_size(::_CorrelatedClosure, ::Symbol) = 1.0
_seed_background(cl::_CorrelatedClosure, ::_LiftModel) = cl.s
_network_terms(::_CorrelatedClosure) = Any[]       # the descriptor is numeric

_dc_class(k::Integer) = Symbol("k", k)
_dc_theta_name(cls::Symbol) = Symbol(:θ_, cls)
_dc_phi_name(Y::Symbol, cls::Symbol) = Symbol(:φ_, Y, :_, cls)

# x^n with the exponents 0 and 1 written out (no θ^0 terms in the field).
_dc_pow(x, n::Integer) = n == 0 ? 1 : n == 1 ? x : x^n

function _edge_closure(net::DegreeCorrelatedNetwork, lm::_LiftModel)
    strat = [X for X in species_names(lm.cm) if lm.stratum[X] !== :all]
    isempty(strat) || throw(ArgumentError(
        "$(lm.context): the species $(join(strat, ", ")) carry strata, but the node types of a " *
        "DegreeCorrelatedNetwork are its degree classes ($(join((_dc_class(k) for k in net.degrees), ", "))), " *
        "which the lift tracks itself; lift an unstratified model, or a model stratified over the degree classes on " *
        "MultitypeNetwork(net)"))
    s = _single_susceptible(lm)
    K = length(net.degrees)
    classes = Symbol[_dc_class(k) for k in net.degrees]
    edged = Int[i for i in 1:K if net.degrees[i] > 0]
    Q = zeros(K, K)
    for i in edged
        row = @view net.edge_ends[i, :]
        Q[i, :] .= row ./ sum(row)
    end
    info = _Coordinate[]
    θ = Dict{Int,Any}()
    ξ = nothing
    q = nothing
    if s !== nothing
        for i in edged
            name = _dc_theta_name(classes[i])
            θ[i] = _state(name)
            push!(info, _Coordinate(name, θ[i], :θ, s, (:all, classes[i])))
        end
        ξ = _state(:ξ)
        push!(info, _Coordinate(:ξ, ξ, :ξ, s, (:all, :all)))
        q = _param(Symbol(:q_, s))
    end
    φ = Dict{Tuple{Symbol,Int},Any}()
    for Y in lm.nodes, i in edged
        name = _dc_phi_name(Y, classes[i])
        φ[(Y, i)] = _state(name)
        push!(info, _Coordinate(name, φ[(Y, i)], :φ, Y, (:all, classes[i])))
    end
    pop = Dict{Symbol,Any}()
    for Y in lm.nodes
        name = Symbol(:pop_, Y)
        pop[Y] = _state(name)
        push!(info, _Coordinate(name, pop[Y], :pop, Y, (:all, :all)))
    end
    return _CorrelatedClosure(net, s, classes, edged, Q, info, θ, ξ, q, φ, pop)
end

_dc_degree(cl::_CorrelatedClosure, i::Int) = cl.net.degrees[i]

# qξ-free factors: the node-S of class i (θ_i^{k_i}) and the partner-S of class j (θ_j^{l_j−1}). Its derivative in θ_j,
# the entry factor (l_j − 1)θ_j^{l_j−2}, is written out in `_contact_terms` with the numeric coefficient Q(l_j | k_i).
_dc_node_factor(cl::_CorrelatedClosure, i::Int) = _dc_degree(cl, i) == 0 ? 1 : _dc_pow(cl.θ[i], _dc_degree(cl, i))
_dc_partner_factor(cl::_CorrelatedClosure, j::Int) = _dc_pow(cl.θ[j], _dc_degree(cl, j) - 1)

_node_S(cl::_CorrelatedClosure) =
    cl.q * cl.ξ * _sum_terms(Any[cl.net.probabilities[i] * _dc_node_factor(cl, i) for i in eachindex(cl.classes)])
# φ_{s,k}: the partner of an edge into a degree-k node is susceptible
_edge_S(cl::_CorrelatedClosure, i::Int) =
    cl.q * cl.ξ * _sum_terms(Any[cl.Q[i, j] * _dc_partner_factor(cl, j) for j in cl.edged if cl.Q[i, j] > 0])

function _contact_terms(cl::_CorrelatedClosure, c::Contact, τ)
    J = c.infector
    qξ = cl.q * cl.ξ
    terms = Pair{Symbol,Any}[]
    for i in cl.edged
        h = τ * cl.φ[(J, i)]
        push!(terms, _dc_theta_name(cl.classes[i]) => -h, _dc_phi_name(J, cl.classes[i]) => -h)
    end
    for i in cl.edged
        gain = Any[(cl.Q[i, j] * (_dc_degree(cl, j) - 1)) * _dc_pow(cl.θ[j], _dc_degree(cl, j) - 2) * cl.φ[(J, j)]
                   for j in cl.edged if cl.Q[i, j] > 0 && _dc_degree(cl, j) > 1]
        isempty(gain) || push!(terms, _dc_phi_name(c.product, cl.classes[i]) => τ * qξ * _sum_terms(gain))
    end
    flux = τ * qξ * _sum_terms(Any[(cl.net.probabilities[i] * _dc_degree(cl, i)) *
                                   _dc_pow(cl.θ[i], _dc_degree(cl, i) - 1) * cl.φ[(J, i)] for i in cl.edged])
    push!(terms, Symbol(:pop_, c.product) => flux)
    return terms, flux
end

function _exit_terms(cl::_CorrelatedClosure, t::NodeTransition, to::Symbol, ν)
    flux = ν * _node_S(cl)
    terms = Pair{Symbol,Any}[:ξ => -ν * cl.ξ]
    for i in cl.edged
        push!(terms, _dc_phi_name(to, cl.classes[i]) => ν * _edge_S(cl, i))
    end
    push!(terms, Symbol(:pop_, to) => flux)
    return terms, flux
end

function _transition_terms(cl::_CorrelatedClosure, t::NodeTransition, to::Symbol, a)
    X = t.from
    flux = a * cl.pop[X]
    terms = Pair{Symbol,Any}[]
    for i in cl.edged
        push!(terms, _dc_phi_name(X, cl.classes[i]) => -a * cl.φ[(X, i)],
              _dc_phi_name(to, cl.classes[i]) => a * cl.φ[(X, i)])
    end
    push!(terms, Symbol(:pop_, X) => -flux, Symbol(:pop_, to) => flux)
    return terms, flux
end

# Observables: the node-S under the susceptible species' name (and `:S`), `:I` and `:infectious`
# (lift/configuration.jl), and per degree class the susceptible fraction `<s>_<k>` (of ALL nodes: p_k qξθ_k^k), the
# edge-S `φ_<s>_<k>` and the edge hazard `edge_hazard_<k>` = Σ_r τ_r φ_{J_r,k} = −θ̇_k.
function _closure_observables(cl::_CorrelatedClosure, lm::_LiftModel, ::LiftContributions)
    s = cl.s
    obs = _untyped_common_observables(cl, lm, _node_S(cl))
    for (i, cls) in enumerate(cl.classes)
        push!(obs, Symbol(s, :_, cls) => cl.q * cl.ξ * cl.net.probabilities[i] * _dc_node_factor(cl, i))
    end
    for i in cl.edged
        push!(obs, _dc_phi_name(s, cl.classes[i]) => _edge_S(cl, i))
    end
    for i in cl.edged
        h = _sum_terms(Any[τ * cl.φ[(c.infector, i)] for (c, τ) in zip(contacts(lm.cm), lm.contact_rates)])
        push!(obs, Symbol(:edge_hazard_, cl.classes[i]) => h)
    end
    return obs
end

# θ = ξ = 1 and φ_{Y,k}(0) = pop_Y(0) = ρ_Y: seeds are placed uniformly, whatever their degree (design §E.2).
function _initial_values(cl::_CorrelatedClosure, lm::_LiftModel, ρ)
    v = Dict{Symbol,Float64}()
    for x in cl.info
        v[x.name] = x.role in (:θ, :ξ) ? 1.0 : get(ρ, x.species, 0.0)
    end
    return v
end

# q_<s> = 1 − Σ_X seed_X.
_seed_expressions(cl::_CorrelatedClosure, lm::_LiftModel, seeds) =
    Dict{Any,Any}(cl.q => 1 - _sum_terms(Any[seeds[X] for X in lm.nodes if haskey(seeds, X)]))

function _relabel_coordinate(::Val{:degree_correlated}, x::_Coordinate, m)
    X = m(x.species)
    x.role in (:θ, :ξ) && return _Coordinate(x.name, x.var, x.role, X, x.types)
    name = x.role === :φ ? _dc_phi_name(X, last(x.types)) : Symbol(:pop_, X)
    return _Coordinate(name, name === x.name ? x.var : _state(name), x.role, X, x.types)
end

# ---------------------------------------------------------------------------------------------
# edge_based on a degree-correlated network
# ---------------------------------------------------------------------------------------------

"""
    edge_based(cm::ContactModel, net::DegreeCorrelatedNetwork; name = :edge_based_model, form = :expanded)
    edge_based(model, c::CorrelatedPGF; kw...)

The edge-based lift of a T_EB model on a configuration network with degree correlations (the joint-degree or "2K"
model built by `degree_correlated(p, e)` or `degree_correlated(d; r)`): the model of Wang, Ma, Cao & Li (2018,
J. Theor. Biol. 454:164, eqs (21)–(24)) with one θ per degree class, extended reaction by reaction as in the other
lifts (branching, several infectors, exits with the survival factor ξ, removals to the sink `:removed`). A degree-k
node's neighbours have degree l with probability Q(l | k) = e_kl/Σ_m e_km, independently; the descriptor is restricted
to the support of the degree law, so empty degree classes create no coordinates (verified issue E20).

Coordinates, per degree class k > 0 (named `k2`, `k10`, … as the types of `MultitypeNetwork(net)`):

- `θ_<k>` (e.g. `θ_k2`): the probability that an edge into a degree-k test node has not transmitted;
- `φ_<Y>_<k>`: the same edge, with its partner in the species `Y` (e.g. `φ_I_k10`);
- `pop_<Y>`: the fraction of all nodes in Y; `ξ` when the model has exits; `cumulative` (the fraction ever infected);

with S = qξ Σ_k p_k θ_k^k and the edge-S φ_{s,k} = qξ Σ_l Q(l | k) θ_l^{l−1}, q = 1 − Σ_X seed_X. A contact
s + J → X + J at per-contact rate τ gives θ̇_k = −τφ_{J,k} + … and the entry term
φ̇_{X,k} += τqξ Σ_l Q(l | k)(l − 1)θ_l^{l−2}φ_{J,l}, so for SIR
θ̇_k = −τφ_{I,k}, φ̇_{I,k} = −(τ + γ)φ_{I,k} + τq Σ_l (l − 1)Q(l | k)θ_l^{l−2}φ_{I,l} (Wang et al. eq. (23)).
Seeds are placed uniformly over the nodes (φ_{X,k}(0) = pop_X(0) = ρ_X). The model must be unstratified, with one
susceptible class (the degree classes are the node types, tracked by the lift); a model stratified over the degree
classes is lifted on `MultitypeNetwork(net)`, of which this lift is the exact quotient (K θ's instead of K²).

Observables: the susceptible species' name `s` and `:S` (unless another species is called S), `:I` and `:infectious`
(the fraction in infector states), and per degree class `<s>_<k>` (the susceptible degree-k nodes as a fraction of
all nodes, p_k qξθ_k^k; also for k = 0), `φ_<s>_<k>` (the edge-S) and `edge_hazard_<k>` (θ̇_k = −edge_hazard_<k>).
Solve with `solve_epidemic(sys; p, initial = SeedFraction(:I => ρ), tspan)` and read the curves with
[`compartment`](@ref) and [`model_curves`](@ref).

Linearised at the disease-free state, the field's next-generation matrix is T·D with D_kl = (l − 1)Q(l | k) for SIR
(T = τ/(τ + γ); in general the per-edge transmissibilities of the entry states), so R₀ = T ρ(D), which is
NetworkEpiCore's `basic_reproduction_number(cm, net, p)` (the multitype form over edge kinds l → k). Under Newman's
r-mixing, assortativity r > 0 never lowers R₀ below the uncorrelated κ_ex T (E20); on the bimodal {2, 10} law of the
scenarios `:sir_dc_bim_*`, R₀ = 2.74, 2 and 1.48 for r = 0.5, 0 and −0.5. With r = 0 (Q(l | k) = l p_l/⟨k⟩) every
θ_k is the configuration-model θ and the lift reproduces the configuration lift of
`ConfigurationNetwork(EmpiricalDegree(p))`. Only the expanded form exists (`form = :compact` is an `ArgumentError`).

The second form lifts a legacy `CorrelatedPGF` through [`degree_correlated`](@ref)`(c)`.

```julia
net = degree_correlated(EmpiricalDegree(2 => 5/6, 10 => 1/6); r = 0.5)      # scenario :sir_dc_bim_r05
sys = edge_based(sir_model(τ = 1/6, γ = 1/4), net)
sol = solve_epidemic(sys; initial = SeedFraction(:I => 0.01), tspan = (0.0, 60.0))
compartment(sys, sol, :cumulative)[end]            # ≈ 0.387 (NetworkEpiCore final_size: 0.3869)
```
"""
function edge_based(cm::ContactModel, net::DegreeCorrelatedNetwork; name::Symbol = :edge_based_model,
                    form::Symbol = :expanded)
    form === :expanded || throw(ArgumentError(
        "edge_based on a DegreeCorrelatedNetwork has only the expanded form; got form = :$form"))
    require_admissible(cm, :edge_based; network = net)
    return _assemble(cm, net; name, context = _lift_context(cm, net))
end

edge_based(model, c::CorrelatedPGF; kw...) = edge_based(model, NetworkEpiCore.degree_correlated(c); kw...)

"""
    degree_correlated(c::CorrelatedPGF; rtol = 1e-8) -> DegreeCorrelatedNetwork

The NetworkEpiCore descriptor of a legacy `CorrelatedPGF` (`correlated_pgf`, `neutral_correlated_pgf`,
`assortative_correlated_pgf`): the edge-end matrix e[k+1, l+1] = (k p_k/⟨k⟩)·Q[k+1, l+1] of its degree
probabilities p and mixing matrix Q, restricted to the degrees with p_k > 0. The restriction removes the empty
degree classes whose rows the legacy matrices fill (`assortative_correlated_pgf` puts r on their diagonal), and with
them the spurious eigenvalues r(k − 1) that make the legacy `correlated_R0` too large on zero-padded distributions
(verified issue E20): `basic_reproduction_number(model, degree_correlated(c), p)` and the lift
`edge_based(model, degree_correlated(c))` use only the classes that have nodes. Q must satisfy detailed balance,
k p_k Q(l | k) = l p_l Q(k | l) (e symmetric), as the neutral and assortative constructors do; otherwise
`DegreeCorrelatedNetwork` throws an `ArgumentError`.

```julia
c = assortative_correlated_pgf([0.0, 0.0, 1.0, 0.0, 0.0, 0.0], 0.5)     # a 2-regular ring, zero-padded to degree 5
net = degree_correlated(c)                                              # one class, degree 2
basic_reproduction_number(sir_model(), net, Dict(:τ => 0.9, :γ => 0.1))   # 0.9 = T (legacy correlated_R0: 1.8)
```
"""
function NetworkEpiCore.degree_correlated(c::CorrelatedPGF; rtol::Real = 1e-8)
    p = c.degree_probs
    K = length(p)
    kbar = sum((i - 1) * p[i] for i in 1:K)
    kbar > 0 || throw(ArgumentError("degree_correlated: the CorrelatedPGF has mean degree 0 (no edges)"))
    e = [(i - 1) * p[i] / kbar * c.mixing_matrix[i, j] for i in 1:K, j in 1:K]
    return NetworkEpiCore.degree_correlated(p, e; rtol)
end
