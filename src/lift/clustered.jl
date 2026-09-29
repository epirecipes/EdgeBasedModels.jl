# Owner: WP20 (DESIGN_NetworkEpiCore.md §A.3, §C.3; work package in §G.2 or §K).
#
# The ClusteredNetwork closure of the per-reaction assembler (lift/assembler.jl): the edge-based
# model of Volz, Miller, Galvani & Ancel Meyers (2011, PLoS Comput Biol 7:e1002042;
# papers/clustering1.md) on the Newman–Miller clustered configuration model, in which a node has
# s single stubs and belongs to t triangles, (s, t) ~ g(x, y) = E[xˢyᵗ] (`ClusteredDegree`). It
# replaces the legacy clustered builder, which treated the two partners of a triangle as two
# independent edges (S = g(θ₂, θ₃²): verified issue E02).
#
# Coordinates of a test node u (modified not to transmit), with susceptible class s, node species
# 𝒩 (every non-susceptible species, then the removal sink) and q = 1 − Σ seeds:
#
#     θ₂           P(a single edge has not transmitted to u)
#     θ₃           P(neither partner of a triangle has transmitted to u)
#     φ2_X         a single edge that has not transmitted, with its partner in X
#     pop_X        the fraction of nodes in X;  ξ, the exit survival factor (models with exits)
#     φ3_X_Y       (X, Y ∈ 𝒩) the triangle pair state of Volz et al.: the two partners are in X and
#                  Y and neither has transmitted to u (unordered, as in the paper: φ3_I_R counts
#                  both orders)
#     χ_X          (X ∈ 𝒩) the triangle state conditional on a susceptible partner: given that the
#                  other partner v is susceptible, the probability that the partner w is in X and
#                  has not transmitted to u (equivalently: w's state when both of its triangle mates
#                  are inert, and w has transmitted to neither)
#
# with S = qξ g(θ₂, θ₃), the single-edge partner φ2_S = qξ g_x(θ₂,θ₃)/g_x(1,1) and the
# susceptible factor of a triangle partner σ = χ_S = qξ g_y(θ₂,θ₃)/g_y(1,1). The pair states that
# contain s are σ-multiples (the outside histories of the two partners are independent on a tree
# of triangles): φ3_S_S = σ² and φ3_S_X = 2σχ_X. The field of one reaction, with the ordered pair
# probabilities O_XY (O_XX = φ3_X_X, O_XY = φ3_X_Y/2):
#
#     contact (s + J → X + J, τ):   H₂ = τφ2_J;  H₃ = 2τ(σχ_J + Σ_Y O_JY);  θ₂' −= H₂;  θ₃' −= H₃
#                                   φ2_J' −= H₂;  φ2_X' += qξ(H₂g_xx + H₃g_xy)/g_x(1,1)
#                                   pop_X' += qξ(g_xH₂ + g_yH₃)
#                                   χ_X' += E_T := qξ(H₂g_xy + H₃g_yy)/g_y(1,1);  χ_J' −= 2τχ_J
#                                   O_PQ' −= τ(1{P = J} + 1{Q = J})O_PQ         (transmission to u)
#                                   O_XJ', O_JX' += τσχ_J                  (inside the triangle)
#                                   O_XY', O_YX' += E_Tχ_Y  for every Y       (from outside)
#     transition (A → B, a):        φ2, pop and χ move from A to B; O_AQ → O_BQ and O_PA → O_PB
#     exit (s → Y, ν):              ξ' −= νξ;  φ2_Y' += νφ2_S;  pop_Y' += νS;  χ_Y' += νσ;
#                                   O_YZ', O_ZY' += νσχ_Z
#
# Every divisor is a constant (g_x(1,1), g_y(1,1)): the entry terms are pre-cancelled against φ2_S
# and σ (verified issues E23, E27), so high-degree polynomial laws are safe and no symbolic
# simplification of polynomial ratios is ever needed. A block without edges (g_x(1,1) = 0: no
# single edges; g_y(1,1) = 0: no triangles) has no coordinates (verified issue E11: no phantom θ),
# and a symbolic mean that is 0 at solve time selects the κ → 0 limit (independent attachment:
# φ2_S, σ → qξg(θ₂, θ₃)) instead of 0/0. For SIR the triangle block is exactly Volz's equations,
# e.g. φ_SI' = 2Aφ_SS − (A + 2β + γ)φ_SI with φ_SI = 2σχ_I and A = −d ln g_y/dt. Conservation:
# θ₂ = φ2_S + Σφ2_X, θ₃ = φ3_S_S + Σ_X φ3_S_X + Σ_{X ≤ Y} φ3_X_Y and S + Σpop = 1.
#
# The field is additive over reactions, but a reaction's pair terms involve every species of the
# model (a transition A → B moves O_AQ for every Q), so the clustered lift is only lax under
# gluing (design §C.3, F2): lift the glued model, not its parts (`relabel` of a clustered table
# is refused).
#
# Scope (design §C.3, §G.2 WP20, risk R5): SIR-shaped and SEIR-shaped models, validated against
# exact stochastic simulation on Newman–Miller graphs (test/suites/clustered.jl). The field above
# is written for every T_EB model with one susceptible class; other shapes are refused until they
# are validated (general T_EB models: WP36d, lift/clustered_general.jl, which opens the gate by
# adding `_clustered_supported(::Val{:general}) = true`).

# ---------------------------------------------------------------------------------------------
# The closure
# ---------------------------------------------------------------------------------------------

struct _ClusteredClosure <: _EdgeClosure
    net::ClusteredNetwork
    s::Symbol                                 # the susceptible species
    nodes::Vector{Symbol}                     # node species (pair-state order)
    index::Dict{Symbol,Int}
    info::Vector{_Coordinate}
    hasL::Bool                                # single edges exist (g_x(1,1) not a numeric 0)
    hasT::Bool                                # triangles exist (g_y(1,1) not a numeric 0)
    θ2::Any                                   # θ₂ (1.0 without single edges)
    θ3::Any                                   # θ₃ (1.0 without triangles)
    ξ::Any
    q::Any
    φ2::Dict{Symbol,Any}
    pop::Dict{Symbol,Any}
    χ::Dict{Symbol,Any}
    U::Dict{Tuple{Symbol,Symbol},Any}         # unordered pair states, key (X, Y) with index X ≤ Y
    g::Dict{Tuple{Int,Int},Any}               # ∂ˣⁱ∂ʸʲ g at (θ₂, θ₃), i + j ≤ 2
    gx1::Any                                  # g_x(1,1) = E[s]
    gy1::Any                                  # g_y(1,1) = E[t]
end

_closure_kind(::_ClusteredClosure) = :clustered
_coordinates(cl::_ClusteredClosure) = cl.info
_seed_factors(cl::_ClusteredClosure) = Pair{Symbol,Any}[cl.s => cl.q]
_type_of(::_ClusteredClosure, ::Symbol) = :all
_type_size(::_ClusteredClosure, ::Symbol) = 1.0
_seed_background(cl::_ClusteredClosure, ::_LiftModel) = cl.s
_network_terms(cl::_ClusteredClosure) = vcat(collect(Any, values(cl.g)), Any[cl.gx1, cl.gy1])

_relabel_coordinate(::Val{:clustered}, ::_Coordinate, _) = throw(ArgumentError(
    "relabel: the clustered (Volz et al. 2011) lift is only lax under gluing (design §C.3, F2: a " *
    "transition moves the triangle pair states of every other species), so its tables cannot be " *
    "pushed forward and summed; lift the glued model with edge_based(glue(...), net)"))

_cl_pair_name(X::Symbol, Y::Symbol) = Symbol(:φ3_, X, :_, Y)
_cl_pair_key(cl::_ClusteredClosure, X::Symbol, Y::Symbol) =
    cl.index[X] <= cl.index[Y] ? (X, Y) : (Y, X)
# The ordered pair probability O_XY (partner 1 in X, partner 2 in Y) of two node species.
_cl_ordered(cl::_ClusteredClosure, X::Symbol, Y::Symbol) =
    X === Y ? cl.U[(X, X)] : cl.U[_cl_pair_key(cl, X, Y)] / 2

# ∂ˣⁱ∂ʸʲ g at (x, y), NetworkEpiCore's closed forms (generic in x, y: Float64 or symbolic).
_cl_g(net::ClusteredNetwork, x, y, i::Int, j::Int) =
    (i == 0 && j == 0) ? pgf(net, x, y) : pgf_derivative(net, x, y, i, j)

# Is a mean degree a structural zero (a numeric 0)? A symbolic mean is not: its zero at solve time
# is handled by `_ratio`/`_unless_zero` (the κ → 0 limit).
function _cl_has(mean)
    v = _numvalue(mean)
    return v === nothing || !iszero(v)
end

function _edge_closure(net::ClusteredNetwork, lm::_LiftModel)
    isempty(lm.Σ) && throw(ArgumentError(
        "$(lm.context): the clustered (Volz et al. 2011) lift needs the model's susceptible class; " *
        "it is only lax under gluing (design §C.3, F2), so parts of a gluing without one cannot be " *
        "lifted on their own; lift the glued model"))
    s = _single_susceptible(lm)
    nodes = copy(lm.nodes)
    index = Dict{Symbol,Int}(X => i for (i, X) in enumerate(nodes))
    gx1 = _cl_g(net, 1.0, 1.0, 1, 0)
    gy1 = _cl_g(net, 1.0, 1.0, 0, 1)
    hasL, hasT = _cl_has(gx1), _cl_has(gy1)
    all = (:all, :all)
    info = _Coordinate[]
    add(name, role, X, types = all) = (v = _state(name); push!(info, _Coordinate(name, v, role, X, types)); v)
    θ2 = hasL ? add(:θ₂, :θ, s) : 1.0
    θ3 = hasT ? add(:θ₃, :θ, s) : 1.0
    ξ = add(:ξ, :ξ, s)
    φ2 = Dict{Symbol,Any}()
    pop = Dict{Symbol,Any}()
    χ = Dict{Symbol,Any}()
    U = Dict{Tuple{Symbol,Symbol},Any}()
    if hasL
        for X in nodes
            φ2[X] = add(Symbol(:φ2_, X), :φ, X)
        end
    end
    for X in nodes
        pop[X] = add(Symbol(:pop_, X), :pop, X)
    end
    if hasT
        for X in nodes
            χ[X] = add(Symbol(:χ_, X), :χ, X)
        end
        for (i, X) in enumerate(nodes), Y in nodes[i:end]
            U[(X, Y)] = add(_cl_pair_name(X, Y), :pair, X, (X, Y))
        end
    end
    g = Dict{Tuple{Int,Int},Any}((i, j) => _cl_g(net, θ2, θ3, i, j)
                                 for (i, j) in ((0, 0), (1, 0), (0, 1), (2, 0), (1, 1), (0, 2)))
    return _ClusteredClosure(net, s, nodes, index, info, hasL, hasT, θ2, θ3, ξ, _param(Symbol(:q_, s)),
                             φ2, pop, χ, U, g, gx1, gy1)
end

# The four factors and their κ → 0 limits (independent attachment, verified issue E11).
_node_S(cl::_ClusteredClosure) = cl.q * cl.ξ * cl.g[(0, 0)]
_edge_S(cl::_ClusteredClosure) =                                          # φ2_S
    _ratio(cl.q * cl.ξ * cl.g[(1, 0)], cl.gx1, cl.q * cl.ξ * cl.g[(0, 0)])
_sigma(cl::_ClusteredClosure) =                                           # χ_S
    _ratio(cl.q * cl.ξ * cl.g[(0, 1)], cl.gy1, cl.q * cl.ξ * cl.g[(0, 0)])

# 2 Σ_{Y ∈ {s} ∪ 𝒩} O_JY: the expected number of partners in J of a triangle that has not
# transmitted to the test node (so θ₃' = −Σ_r τ_r ·this), e.g. φ_SI + 2φ_II + φ_IR for SIR.
_cl_exposure(cl::_ClusteredClosure, J::Symbol) =
    2 * (_sigma(cl) * cl.χ[J] + _sum_terms(Any[_cl_ordered(cl, J, Y) for Y in cl.nodes]))

# An ordered accumulator of the terms of one reaction.
struct _ClTerms
    names::Vector{Symbol}
    vals::Dict{Symbol,Vector{Any}}
end
_ClTerms() = _ClTerms(Symbol[], Dict{Symbol,Vector{Any}}())
function _cl_add!(T::_ClTerms, name::Symbol, v)
    haskey(T.vals, name) || (push!(T.names, name); T.vals[name] = Any[])
    push!(T.vals[name], v)
    return T
end
# add an ORDERED pair contribution to its unordered coordinate (U_XY' = O_XY' + O_YX')
_cl_add_pair!(T::_ClTerms, cl::_ClusteredClosure, X::Symbol, Y::Symbol, v) =
    _cl_add!(T, _cl_pair_name(_cl_pair_key(cl, X, Y)...), v)
_cl_terms(T::_ClTerms) = Pair{Symbol,Any}[n => _sum_terms(T.vals[n]) for n in T.names]

function _contact_terms(cl::_ClusteredClosure, c::Contact, τ)
    J, X = c.infector, c.product
    T = _ClTerms()
    qξ = cl.q * cl.ξ
    g = cl.g
    H2 = cl.hasL ? τ * cl.φ2[J] : nothing
    H3 = cl.hasT ? τ * _cl_exposure(cl, J) : nothing
    # the rates at which the test node (a single-edge partner, a triangle partner) is infected
    # through reaction r along its other edges, times its susceptible factor (pre-cancelled)
    lin(a, b) = _sum_terms(Any[x for x in ((H2 === nothing ? nothing : H2 * a),
                                            (H3 === nothing ? nothing : H3 * b)) if x !== nothing])
    flux = qξ * lin(g[(1, 0)], g[(0, 1)])
    if cl.hasL
        _cl_add!(T, :θ₂, -H2)
        _cl_add!(T, Symbol(:φ2_, J), -H2)
        _cl_add!(T, Symbol(:φ2_, X), _ratio(qξ * lin(g[(2, 0)], g[(1, 1)]), cl.gx1, flux))
    end
    if cl.hasT
        _cl_add!(T, :θ₃, -H3)
    end
    _cl_add!(T, Symbol(:pop_, X), flux)
    if cl.hasT
        σ = _sigma(cl)
        ET = _ratio(qξ * lin(g[(1, 1)], g[(0, 2)]), cl.gy1, flux)
        _cl_add!(T, Symbol(:χ_, X), ET)
        _cl_add!(T, Symbol(:χ_, J), -2 * τ * cl.χ[J])
        for P in cl.nodes, Q in cl.nodes                  # a J partner transmits to the test node
            m = (P === J) + (Q === J)
            m == 0 || _cl_add_pair!(T, cl, P, Q, -m * τ * _cl_ordered(cl, P, Q))
        end
        _cl_add_pair!(T, cl, X, J, τ * σ * cl.χ[J])     # inside the triangle: J infects the S partner
        _cl_add_pair!(T, cl, J, X, τ * σ * cl.χ[J])
        for Y in cl.nodes                                 # the S partner is infected from outside
            _cl_add_pair!(T, cl, X, Y, ET * cl.χ[Y])
            _cl_add_pair!(T, cl, Y, X, ET * cl.χ[Y])
        end
    end
    return _cl_terms(T), flux
end

function _transition_terms(cl::_ClusteredClosure, t::NodeTransition, to::Symbol, a)
    A, B = t.from, to
    T = _ClTerms()
    flux = a * cl.pop[A]
    if cl.hasL
        _cl_add!(T, Symbol(:φ2_, A), -a * cl.φ2[A])
        _cl_add!(T, Symbol(:φ2_, B), a * cl.φ2[A])
    end
    _cl_add!(T, Symbol(:pop_, A), -flux)
    _cl_add!(T, Symbol(:pop_, B), flux)
    if cl.hasT
        _cl_add!(T, Symbol(:χ_, A), -a * cl.χ[A])
        _cl_add!(T, Symbol(:χ_, B), a * cl.χ[A])
        for P in cl.nodes, Q in cl.nodes
            if P === A
                o = a * _cl_ordered(cl, P, Q)
                _cl_add_pair!(T, cl, P, Q, -o)
                _cl_add_pair!(T, cl, B, Q, o)
            end
            if Q === A
                o = a * _cl_ordered(cl, P, Q)
                _cl_add_pair!(T, cl, P, Q, -o)
                _cl_add_pair!(T, cl, P, B, o)
            end
        end
    end
    return _cl_terms(T), flux
end

function _exit_terms(cl::_ClusteredClosure, t::NodeTransition, to::Symbol, ν)
    Y = to
    T = _ClTerms()
    flux = ν * _node_S(cl)
    _cl_add!(T, :ξ, -ν * cl.ξ)
    cl.hasL && _cl_add!(T, Symbol(:φ2_, Y), ν * _edge_S(cl))
    _cl_add!(T, Symbol(:pop_, Y), flux)
    if cl.hasT
        σ = _sigma(cl)
        _cl_add!(T, Symbol(:χ_, Y), ν * σ)
        for Z in cl.nodes
            _cl_add_pair!(T, cl, Y, Z, ν * σ * cl.χ[Z])
            _cl_add_pair!(T, cl, Z, Y, ν * σ * cl.χ[Z])
        end
    end
    return _cl_terms(T), flux
end

# Observables: the node-S (`:S` and the susceptible species' name), `:I` and `:infectious`, the
# single-edge partner φ2_<s>, the triangle factors χ_<s> = σ, φ3_<s>_<s> = σ² and φ3_<s>_<X> =
# 2σχ_X (the pair states with a susceptible partner, unordered), and the hazards `edge_hazard2`
# (θ₂' = −edge_hazard2) and `edge_hazard3` (θ₃' = −edge_hazard3). Aliases `:φ2_S`, `:χ_S` for a
# susceptible class not called S (unless a species owns the name).
function _closure_observables(cl::_ClusteredClosure, lm::_LiftModel, ::LiftContributions)
    s = cl.s
    obs = _untyped_common_observables(cl, lm, _node_S(cl))
    alias(name, v) = (s !== :S && !(name in lm.nodes) && push!(obs, name => v))
    if cl.hasL
        φS = _edge_S(cl)
        push!(obs, Symbol(:φ2_, s) => φS)
        alias(:φ2_S, φS)
    end
    if cl.hasT
        σ = _sigma(cl)
        push!(obs, Symbol(:χ_, s) => σ)
        alias(:χ_S, σ)
        push!(obs, _cl_pair_name(s, s) => σ^2)
        for X in cl.nodes
            push!(obs, _cl_pair_name(s, X) => 2 * σ * cl.χ[X])
        end
    end
    rows = collect(zip(contacts(lm.cm), lm.contact_rates))
    cl.hasL && push!(obs, :edge_hazard2 => _sum_terms(Any[τ * cl.φ2[c.infector] for (c, τ) in rows]))
    cl.hasT && push!(obs, :edge_hazard3 => _sum_terms(Any[τ * _cl_exposure(cl, c.infector) for (c, τ) in rows]))
    return obs
end

# θ₂(0) = θ₃(0) = ξ(0) = 1, φ2_X(0) = pop_X(0) = χ_X(0) = ρ_X and, for independently seeded
# partners, φ3_X_X(0) = ρ_X², φ3_X_Y(0) = 2ρ_Xρ_Y (so θ₃(0) = (q + Σρ)² = 1); the sinks start empty.
function _initial_values(cl::_ClusteredClosure, lm::_LiftModel, ρ)
    r(X) = get(ρ, X, 0.0)
    v = Dict{Symbol,Float64}(:θ₂ => 1.0, :θ₃ => 1.0, :ξ => 1.0)
    for X in cl.nodes
        v[Symbol(:φ2_, X)] = r(X)
        v[Symbol(:pop_, X)] = r(X)
        v[Symbol(:χ_, X)] = r(X)
    end
    for (X, Y) in keys(cl.U)
        v[_cl_pair_name(X, Y)] = X === Y ? r(X)^2 : 2 * r(X) * r(Y)
    end
    return v
end

# q_<s> = 1 − Σ_X seed_X.
_seed_expressions(cl::_ClusteredClosure, lm::_LiftModel, seeds) =
    Dict{Any,Any}(cl.q => 1 - _sum_terms(Any[seeds[X] for X in lm.nodes if haskey(seeds, X)]))

# ---------------------------------------------------------------------------------------------
# Which models the clustered lift accepts (design §C.3: SIR required, SEIR stretch)
# ---------------------------------------------------------------------------------------------

# The shape of a model: `:sir` (one contact s + I → 2I, one transition I → R or I → ∅, no exits,
# no other species), `:seir` (one contact s + I → E + I, the transitions E → I and I → R or
# I → ∅, no exits, no other species) or `:general` (every other T_EB model).
function _clustered_shape(lm::_LiftModel)
    cs, ts = contacts(lm.cm), node_transitions(lm.cm)
    (length(lm.Σ) == 1 && length(cs) == 1 && !any(==(:exit), lm.transition_types)) || return :general
    c = only(cs)
    I, X = c.infector, c.product
    if X === I && length(ts) == 1
        t = only(ts)
        R = only(lm.transition_targets)
        (t.from === I && Set(lm.nodes) == Set([I, R])) && return :sir
    elseif X !== I && length(ts) == 2
        E = X
        pairs = Set((t.from, to) for (t, to) in zip(ts, lm.transition_targets))
        R = [to for (t, to) in zip(ts, lm.transition_targets) if t.from === I]
        if length(R) == 1 && !(only(R) in (E, I)) && (E, I) in pairs &&
           Set(lm.nodes) == Set([E, I, only(R)])
            return :seir
        end
    end
    return :general
end

"""
    _clustered_supported(::Val{shape}) -> Bool

Whether the clustered edge-based lift accepts models of `shape` (see `_clustered_shape`):
`:sir` and `:seir`, validated against exact stochastic simulation on Newman–Miller graphs
(design §C.3, §G.2 WP20). The field is written for every T_EB model with one susceptible class;
WP36d (lift/clustered_general.jl) accepts `:general` models once they are validated by adding
the method `_clustered_supported(::Val{:general}) = true`.
"""
_clustered_supported(::Val{:sir}) = true
_clustered_supported(::Val{:seir}) = true
_clustered_supported(::Val) = false

function _require_clustered_shape(lm::_LiftModel)
    shape = _clustered_shape(lm)
    _clustered_supported(Val(shape)) && return shape
    throw(ArgumentError(
        "$(lm.context): the clustered edge-based lift (Volz et al. 2011, triangle pair states) " *
        "supports SIR-shaped models (s + I → 2I, I → R or I → ∅) and SEIR-shaped models " *
        "(s + I → E + I, E → I, I → R or I → ∅) only (design §C.3); this model is of another shape " *
        "(exits, several contacts or infectors, other stages). NodeBasedModels (Keeling's clustered " *
        "pairwise closure, approximate) and NetworkOutbreaks (exact stochastic simulation on sampled " *
        "clustered graphs) accept it"))
end

# ---------------------------------------------------------------------------------------------
# edge_based and lift_contributions on a clustered network
# ---------------------------------------------------------------------------------------------

"""
    edge_based(cm::ContactModel, net::ClusteredNetwork; name = :edge_based_model, form = :expanded)

The edge-based model of Volz, Miller, Galvani & Ancel Meyers (2011) on the Newman–Miller
clustered configuration model `net` (s single edges and t triangles per node, (s, t) ~
`net.joint`), with the triangle pair states that couple the two partners of a triangle. SIR- and
SEIR-shaped models are accepted (s + I → 2I, I → R; s + I → E + I, E → I, I → R; removals I → ∅
go to the sink `:removed`); other models raise an `ArgumentError` naming the back ends that
accept them, and `require_admissible(cm, :edge_based; network = net)` is checked first (SIS and
SIRS raise an `AdmissibilityError`). Only `form = :expanded` exists.

Coordinates (every divisor in the field is a constant, so polynomial laws of any degree are safe;
a block without edges has no coordinates):

- `θ₂`, the probability that a single edge has not transmitted to a test node, and `θ₃`, that
  neither partner of a triangle has; S = qξ g(θ₂, θ₃) with q = 1 − Σ seeds;
- `φ2_X`, `pop_X` for every non-susceptible species X (and the sink): single edges whose partner
  is in X and has not transmitted, and the fraction of nodes in X;
- `φ3_X_Y` (X, Y non-susceptible, unordered as in Volz et al.): triangles whose partners are in
  X and Y, neither having transmitted; `χ_X`: given that one partner is susceptible, the
  probability that the other is in X and has not transmitted (so the pair states with a
  susceptible partner are the observables `φ3_S_S` = χ_S² and `φ3_S_X` = 2χ_S χ_X);
- `cumulative`, the fraction ever infected (seeds included).

Observables: `:S` (and the susceptible species' name), `:I`, `:infectious`, `φ2_S` (the
single-edge partner is susceptible, qξg_x/g_x(1,1)), `χ_S` (a triangle partner's susceptible
factor, qξg_y/g_y(1,1)), `φ3_S_S`, `φ3_S_X`, `edge_hazard2` = −θ₂' and `edge_hazard3` = −θ₃'. The
variable `:R` is the recovered population. Conservation: θ₂ = φ2_S + Σφ2_X,
θ₃ = φ3_S_S + Σφ3_S_X + Σφ3_X_Y and S + Σpop = 1. For SIR the triangle block is exactly the
system of Volz et al. (φ_SI = φ3_S_I, …); with no triangles the lift is the configuration-model
lift of g(x, 1), with no single edges that of the triangles alone.

Seeding, parameters, `solve_epidemic`, `model_curves` and `symbolic_ode` work as for the other
assembled systems (see `edge_based` on a `ConfigurationNetwork`); the lift is only lax under
gluing (design §C.3), so lift a glued model as a whole.

```julia
net = ClusteredNetwork(PoissonDegree(1.0), PoissonDegree(2.0))
sys = edge_based(sir_model(; τ = 0.6, γ = 1.0), net)
sol = solve_epidemic(sys; initial = SeedFraction(:I => 1e-3), tspan = (0.0, 40.0))
compartment(sys, sol, :cumulative)[end]          # 0.7125 (Volz et al.; exact SSA 0.7121 ± 0.0002)
```
"""
function edge_based(cm::ContactModel, net::ClusteredNetwork; name::Symbol = :edge_based_model,
                    form::Symbol = :expanded)
    form === :expanded || throw(ArgumentError(
        "edge_based on a ClusteredNetwork has only the expanded form; got form = :$form"))
    require_admissible(cm, :edge_based; network = net)
    context = _lift_context(cm, net)
    _require_clustered_shape(_lift_model(cm, net, susceptible_species(cm); context))
    return _assemble(cm, net; name, context)
end

"""
    lift_contributions(model, net::ClusteredNetwork; susceptible = susceptible_species(model))

The per-reaction table of the clustered (Volz et al. 2011) lift of a whole model (see
[`edge_based`](@ref) on a `ClusteredNetwork` for the coordinates). The model must be one the
clustered lift accepts. Unlike the configuration-model lift, the clustered lift is only lax
under gluing (design §C.3): a transition moves the triangle pair states of every other species,
so the tables of the parts of a gluing do not add up to the table of the glued model, and
`relabel` of a clustered table is refused.
"""
function lift_contributions(cm::ContactModel, net::ClusteredNetwork;
                            susceptible = susceptible_species(cm))
    Σ = susceptible isa Symbol ? [susceptible] : collect(Symbol, susceptible)
    context = "lift_contributions(:$(cm.name), ClusteredNetwork)"
    lm = _lift_model(cm, net, Σ; context)
    cl = _edge_closure(net, lm)
    _require_clustered_shape(lm)
    return _contributions(cl, lm, net)
end

# ---------------------------------------------------------------------------------------------
# The basic reproduction number on a tree of triangles (verified issue E04)
# ---------------------------------------------------------------------------------------------

# q_k: the probability that an infective, from the entry state, transmits to none of k given
# susceptible contacts (phase-type absorption over the non-susceptible states: a state J
# transmits along each edge at Σ_{r: J_r = J} τ_r while the node is in J). `rate` returns the
# (possibly symbolic) value of a model rate.
function _cl_no_transmission(lm::_LiftModel, entry::Symbol, k::Integer, rate)
    nodes = lm.nodes
    idx = Dict{Symbol,Int}(X => i for (i, X) in enumerate(nodes))
    n = length(nodes)
    τJ = Any[0 for _ in 1:n]
    for (c, τ) in zip(contacts(lm.cm), lm.contact_rates)
        τJ[idx[c.infector]] += rate(τ)
    end
    out = [Any[] for _ in 1:n]                # (target, rate) of each transition
    for (t, a, to, ty) in zip(node_transitions(lm.cm), lm.transition_rates, lm.transition_targets,
                              lm.transition_types)
        ty === :exit && continue
        push!(out[idx[t.from]], (idx[to], rate(a)))
    end
    # absorbing states (no transitions): q = 1 if they never transmit, 0 if they transmit forever
    A = Matrix{Any}(undef, n, n)
    fill!(A, 0)
    b = Any[0 for _ in 1:n]
    for i in 1:n
        if isempty(out[i])
            A[i, i] = 1
            b[i] = _numvalue(τJ[i]) == 0 ? 1 : 0
            continue
        end
        A[i, i] = k * τJ[i] + _sum_terms(Any[a for (_, a) in out[i]])
        for (j, a) in out[i]
            A[i, j] -= a
        end
    end
    sym = any(x -> _numvalue(x) === nothing, vcat(vec(A), b))
    if sym
        x = Symbolics.Num.(A) \ Symbolics.Num.(b)
        return x[idx[entry]]
    end
    return (Float64.(_numvalue.(A)) \ Float64.(_numvalue.(b)))[idx[entry]]
end

_cl_isnum(x) = _numvalue(x) !== nothing
_cl_sqrt(x) = _cl_isnum(x) ? sqrt(_numvalue(x)) : sqrt(x)         # never simplified (E04)

"""
    _clustered_reproduction_number(cm, net::ClusteredNetwork; p = nothing, kind = :generation)
    _clustered_reproduction_number(sys::EdgeModelSystem; p = nothing, kind = :generation)

The basic reproduction number of an SIR- or SEIR-shaped model on the clustered network `net`,
from the tree-of-triangles branching process of Volz et al. (2011) (verified issue E04,
corrected fix). With q_k the probability that an infective transmits to none of k given contacts
(phase-type absorption from the entry state), T = 1 − q₁ and c = q₁ − q₂ (the probability that
the index infects one given triangle partner but not the other), and the moments of g at (1, 1):

- `kind = :generation` (the default): the Perron root of the 3-type generation matrix
  [A B 0; C D c; C D 0] with A = T g_xx/g_x, B = 2T g_xy/g_x, C = T g_xy/g_y, D = 2T g_yy/g_y
  (children reached along a single edge, directly in a triangle, and through the other partner
  of a triangle); it matches the simulated generation growth ratio;
- `kind = :clump`: R_* = ρ([T g_xx/g_x, μ g_xy/g_x; T g_xy/g_y, μ g_yy/g_y]) with μ = 2T(1 + c),
  the expected number infected in a triangle; it has the same threshold (R₀ = 1 ⇔ R_* = 1).

Without triangles both reduce to T g_xx/g_x; without single edges the blocks of the line type
are dropped. Numeric rates (or numeric values in `p`, by name, over the model's
`parameter_defaults`) give a `Float64`. Symbolic rates
give a closed form when one exists (`kind = :clump`, a law with g_xx g_yy = g_xy², such as
independent Poisson singles and triangles, or one block empty); otherwise `:generation` needs
numeric rates and throws an `ArgumentError` pointing to `kind = :clump`. No square root is ever
passed to `Symbolics.simplify` (it mangles them, E04).
"""
function _clustered_reproduction_number(cm::ContactModel, net::ClusteredNetwork;
                                        p::Union{Nothing,AbstractDict} = nothing,
                                        kind::Symbol = :generation)
    kind in (:generation, :clump) || throw(ArgumentError(
        "kind must be :generation or :clump; got :$kind"))
    context = "basic_reproduction_number(:$(cm.name), ClusteredNetwork)"
    lm = _lift_model(cm, net, susceptible_species(cm); context)
    # one contact and one entry state: the offspring types below (a model with several entry
    # states or infectors needs typed offspring, even where the lift accepts it)
    _require_clustered_shape(lm) in (:sir, :seir) || throw(ArgumentError(
        "$context: the tree-of-triangles R₀ is implemented for SIR- and SEIR-shaped models only"))
    rate = if p === nothing
        identity
    else
        # p by name, over the model's parameter defaults (the semantics of solve_epidemic)
        pd = Dict{Symbol,Any}(parameter_defaults(cm))
        merge!(pd, Dict{Symbol,Any}(Symbol(k) => v for (k, v) in pairs(p)))
        r -> _cl_rate_value(r, pd)
    end
    entry = only(contacts(cm)).product
    q1 = _cl_no_transmission(lm, entry, 1, rate)
    q2 = _cl_no_transmission(lm, entry, 2, rate)
    T = 1 - q1
    c = q1 - q2
    m(i, j) = _cl_g(net, 1.0, 1.0, i, j)
    gx, gy, gxx, gxy, gyy = m(1, 0), m(0, 1), m(2, 0), m(1, 1), m(0, 2)
    hasL, hasT = _cl_has(gx), _cl_has(gy)
    (hasL || hasT) || return zero(T)
    hasT || return T * gxx / gx
    if kind === :clump
        μ = 2 * T * (1 + c)
        hasL || return μ * gyy / gy
        a, b, cc, d = T * gxx / gx, μ * gxy / gx, T * gxy / gy, μ * gyy / gy
        return (a + d + _cl_sqrt((a - d)^2 + 4 * b * cc)) / 2
    end
    D = 2 * T * gyy / gy
    hasL || return (D + _cl_sqrt(D^2 + 4 * c * D)) / 2
    A, B, C = T * gxx / gx, 2 * T * gxy / gx, T * gxy / gy
    K = Any[A B 0; C D c; C D 0]
    if all(_cl_isnum, K)
        return maximum(real, eigvals(Float64.(_numvalue.(K))))
    end
    # A D − B C = 2T²(g_xx g_yy − g_xy²)/(g_x g_y): the rank-deficient case has a closed form
    det = gxx * gyy - gxy^2
    if _cl_isnum(det) && abs(_numvalue(det)) <= 1e-12 * max(1.0, abs(_numvalue(gxx * gyy)))
        return (A + D + _cl_sqrt((A + D)^2 + 4 * c * D)) / 2
    end
    throw(ArgumentError(
        "$context: the generation-based R₀ of a clustered law with g_xx g_yy ≠ g_xy² is the root of " *
        "a cubic and needs numeric rates (pass p = Dict(...)); use kind = :clump for the " *
        "closed-form clump reproduction number R_*, which has the same threshold"))
end

function _clustered_reproduction_number(sys::EdgeModelSystem; kw...)
    net = get(sys.metadata, :network, nothing)
    cm = get(sys.metadata, :model, nothing)
    (net isa ClusteredNetwork && cm isa ContactModel) || throw(ArgumentError(
        "_clustered_reproduction_number: the system is not an edge-based model on a ClusteredNetwork"))
    return _clustered_reproduction_number(cm, net; kw...)
end

# A rate's value with parameters given by name (NetworkEpiCore's `rate_value` for Real, Symbol and
# Expr rates; symbolic rates are substituted by name).
function _cl_rate_value(r, p::AbstractDict)
    if r isa Symbolics.Num || r isa Symbolics.SymbolicUtils.BasicSymbolic   # (Num <: Real)
        sub = Dict{Any,Any}()
        for v in Symbolics.get_variables(r)
            n = _symname(v)
            haskey(p, n) && (sub[v] = p[n])
        end
        x = Symbolics.substitute(r, sub; fold = Val(true))
        v = _numvalue(x)
        v === nothing && throw(ArgumentError("p does not give every parameter of the rate $(r)"))
        return v
    end
    return Float64(rate_value(r, p))
end
