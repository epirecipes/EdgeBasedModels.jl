# Owner: WP36d (DESIGN_NetworkEpiCore.md §K; work package in §G.2 or §K).
#
# Clustered networks beyond SIR: the edge-based model of Volz, Miller, Galvani & Ancel Meyers
# (2011, PLoS Comput Biol 7:e1002042; papers/clustering1.md), with triangle pair states, for
# every T_EB model with one susceptible class. This covers SEIR, SEAIR (branching after latency
# and two infectors), Erlang stages, several strains (several entry states), exits from the
# susceptible class (vaccination, importation) and removals to the sink.
#
# The field
# ---------
# lift/clustered.jl (WP20) writes the per-reaction field of the clustered closure for any T_EB
# model with one susceptible class s, and gates it to SIR- and SEIR-shaped models
# (`_clustered_supported`). This file opens the gate for every other shape (`:general`). The field
# needs no change beyond SIR, because none of the steps below uses the shape of the model.
#
# Take a test node u modified not to transmit, and a triangle {u, v, w}. On the tree of lines and
# triangles, the outsides of v and of w (their other lines and triangles) are independent of
# each other and of the triangle.
#
# 1. v is susceptible iff it was not seeded, has not exited, was not infected from outside and
#    was not infected by w. So P(v ∈ s, w ∈ s) = σ², with σ = qξ g_y(θ₂, θ₃)/g_y(1, 1), and
#    P(v ∈ s, w ∈ X, w has not transmitted to u) = σ χ_X. Here χ_X is a one-node quantity: a node
#    with a triangle partner's outside and two inert triangle mates. It enters X_r from s at
#    E_T,r, the share of −σ' due to reaction r (outside infections are attributed to reactions
#    exactly, as in the configuration lift). It follows the node transitions. It leaves at 2τ_r
#    while in the infector J_r, because it transmits to u or to v, and the second moves the pair
#    to (X_r, J_r). An exit s → Y moves σ to χ_Y at rate ν.
#    Several contacts add their rates, several infectors add their exposures, branching sends each
#    reaction's share to its own product, and an exit is one more way to leave s.
# 2. A pair state O_XY in which neither partner is susceptible changes as follows:
#    - it gains from (s, Y) at the outside rate E_T,r χ_Y, when v enters X_r;
#    - it gains at τ_r σ χ_{J_r} inside the triangle, when w, in the infector J_r, infects v;
#    - it moves with the transitions of either partner;
#    - it loses τ_r O_XY for each partner in J_r, which transmits to u.
# 3. The two hazards are θ₃' = −Σ_r τ_r E[number of partners in J_r that have not transmitted]
#    and θ₂' = −Σ_r τ_r φ2_{J_r}.
#
# The WP36d test suite checks this field in two ways:
# - to 1e-8 against an independent ordered, S-explicit transcription of the pair-state rules,
#   which has no χ coordinates and divides by g_x(θ) and g_y(θ) as the paper does;
# - against exact stochastic simulation on Newman–Miller graphs (NetworkOutbreaks), including on
#   the canonical scenarios :seir_clust_s2t2 and :seair_clust_s2t2.
#
# What is still refused, and by whom:
# - several susceptible classes (a stratified model or heterogeneous susceptibility), and
#   layer-labelled contacts, which are AdmissibilityErrors of `require_admissible`;
# - SIS and SIRS, which are not T_EB;
# - `relabel` of a clustered table, because the lift is only lax under gluing (design §C.3, F2).
#
# The reproduction number and the other threshold quantities
# ----------------------------------------------------------
# WP20's tree-of-triangles R₀ (verified issue E04) has one offspring type per edge kind, so it
# needs one entry state. `_clustered_general_reproduction_number` types the offspring by edge kind
# AND entry state:
# - a child reached along a line has the excess law g_x/g_x(1,1);
# - a child infected inside a triangle has the excess law g_y/g_y(1,1);
# - the expected numbers of children of each entry are computed exactly from small CTMCs of a
#   line (2 nodes) and of a triangle (3 nodes, with the within-triangle races) seeded by the
#   index in its entry state.
# NetworkEpiCore refuses threshold analysis on a ClusteredNetwork (it needs the triangle pair
# states). `_clustered_threshold(f, sys, vals)` gives R₀, the next-generation matrix, the per-edge
# transmissibility and the early growth rate of a clustered system for every model the lift
# accepts. It is the body for analysis.jl's extension point `_numeric_threshold(::Val{:clustered},
# f, sys, vals; kw...)`, and the owner of lift/clustered.jl wires it there.

# ---------------------------------------------------------------------------------------------
# The gate: every T_EB model with one susceptible class
# ---------------------------------------------------------------------------------------------

# lift/clustered.jl classifies a model as :sir, :seir or :general; the field is written for all
# three and validated for all three (test/suites/clustered.jl, test/suites/clustered_general.jl).
_clustered_supported(::Val{:general}) = true

# ---------------------------------------------------------------------------------------------
# The reproduction number on a tree of triangles, for general models
# ---------------------------------------------------------------------------------------------

# The numeric epidemic data of a model, over its non-susceptible species (`lm.nodes`: model
# order, then the removal sinks):
# - `contacts`: (infector index, product index, τ) for each contact of positive rate;
# - `out[i]`: (target index, rate) for each transition of positive rate out of species i.
# Exits from the susceptible class do not act on infected nodes. As in NetworkEpiCore's
# next-generation matrix, they are evaluated at the disease-free state ξ = 1.
struct _CliqueRates
    nodes::Vector{Symbol}
    contacts::Vector{Tuple{Int,Int,Float64}}
    out::Vector{Vector{Tuple{Int,Float64}}}
end

# The value of a model rate, with parameter values by name, as a finite non-negative Float64.
function _clg_rate_value(r, pd::AbstractDict, context::AbstractString)
    v = try
        rate_value(r, pd)
    catch e
        e isa ArgumentError || rethrow()
        throw(ArgumentError(
            "$context: the rate $(r) has no numeric value ($(sprint(showerror, e))); the " *
            "clustered reproduction number needs numeric rates (pass p = Dict(name => value))"))
    end
    x = _numvalue(v)
    (x === nothing || !isfinite(x) || x < 0) && throw(ArgumentError(
        "$context: the rate $(r) must be a finite non-negative number at the given parameters " *
        "(pass p = Dict(name => value)); got $(v)"))
    return x
end

# Parameter values by name: the model's `parameter_defaults`, overridden by `p` (keys may be
# Symbols, strings or symbolic parameters).
function _clg_params(cm::ContactModel, p)
    pd = Dict{Symbol,Any}(parameter_defaults(cm))
    p === nothing && return pd
    for (k, v) in pairs(p)
        pd[k isa Symbol ? k : k isa AbstractString ? Symbol(k) : _pname(k)] = v
    end
    return pd
end

# The network moment ∂ⁱₓ∂ʲ_y g(1, 1) as a Float64. Symbolic network parameters, such as Poisson
# means declared with @parameters, are substituted by name from `pd`.
function _clg_moment(net::ClusteredNetwork, i::Int, j::Int, pd::AbstractDict, context::AbstractString)
    m = pgf_derivative(net, 1.0, 1.0, i, j)
    v = _numvalue(m)
    if v === nothing
        sub = Dict{Any,Any}()
        for x in Symbolics.get_variables(m)
            n = _symname(x)
            haskey(pd, n) && (sub[x] = pd[n])
        end
        v = _numvalue(Symbolics.substitute(m, sub; fold = Val(true)))
    end
    (v === nothing || !isfinite(v)) && throw(ArgumentError(
        "$context: the clustered reproduction number needs a network with numeric means; pass " *
        "the network's parameters by name in p (∂^$(i)_x ∂^$(j)_y g(1, 1) = $(m))"))
    return Float64(v)
end

function _clique_rates(cm::ContactModel, net::ClusteredNetwork, lm::_LiftModel, pd::AbstractDict, context)
    index = Dict{Symbol,Int}(X => i for (i, X) in enumerate(lm.nodes))
    cs = Tuple{Int,Int,Float64}[]
    for (c, τ) in zip(contacts(cm), per_contact_rates(cm, net))
        v = _clg_rate_value(τ, pd, context)
        v > 0 && push!(cs, (index[c.infector], index[c.product], v))
    end
    out = [Tuple{Int,Float64}[] for _ in lm.nodes]
    for (t, to, ty) in zip(node_transitions(cm), lm.transition_targets, lm.transition_types)
        ty === :exit && continue
        v = _clg_rate_value(t.rate, pd, context)
        v > 0 && push!(out[index[t.from]], (index[to], v))
    end
    return _CliqueRates(copy(lm.nodes), cs, out)
end

"""
    _clique_offspring(R::_CliqueRates, entry::Int, K::Int) -> Vector{Float64}

The expected number of infections, by product species, among the K − 1 initially susceptible
members of a K-clique whose index has just entered the species `entry`. K = 2 is a line (the
per-edge transmissibilities T_{e→x}); K = 3 is a triangle, with the within-triangle races, in
which a partner infected by the index may infect the other partner first. The computation is an
exact absorption computation on the continuous-time Markov chain of the members' states (0 is
susceptible). Only the states from which an infection is still reachable are kept, so a
recurrent class without an infector contributes nothing.
"""
function _clique_offspring(R::_CliqueRates, entry::Int, K::Int)
    n = length(R.nodes)
    start = zeros(Int, K)
    start[1] = entry
    ids = Dict{Vector{Int},Int}(start => 1)
    states = [start]
    moves = Vector{Vector{Tuple{Int,Float64,Int}}}()       # (next state, rate, product or 0)
    function id!(s, m, x)
        s2 = copy(s)
        s2[m] = x
        return get!(ids, s2) do
            push!(states, s2)
            length(states)
        end
    end
    i = 0
    while i < length(states)
        i += 1
        s = states[i]
        mv = Tuple{Int,Float64,Int}[]
        for m in 1:K
            if s[m] > 0
                for (b, a) in R.out[s[m]]
                    push!(mv, (id!(s, m, b), a, 0))
                end
            else
                for m2 in 1:K, (J, X, τ) in R.contacts
                    s[m2] == J && push!(mv, (id!(s, m, X), τ, X))
                end
            end
        end
        push!(moves, mv)
    end
    # live states: an infection is reachable from them
    live = [any(mv -> mv[3] > 0, moves[j]) for j in eachindex(states)]
    changed = true
    while changed
        changed = false
        for j in eachindex(states)
            if !live[j] && any(mv -> live[mv[1]], moves[j])
                live[j] = true
                changed = true
            end
        end
    end
    live[1] || return zeros(n)
    L = findall(live)
    pos = Dict{Int,Int}(j => k for (k, j) in enumerate(L))
    A = zeros(length(L), length(L))
    B = zeros(length(L), n)
    for (k, j) in enumerate(L), (nxt, rate, x) in moves[j]
        A[k, k] += rate
        haskey(pos, nxt) && (A[k, pos[nxt]] -= rate)
        x > 0 && (B[k, x] += rate)
    end
    return vec((A \ B)[pos[1], :])
end

# The probability that an infective that has just entered `entry` transmits along none of k
# given edges (the phase-type absorption q_k of WP20's R₀, computed here independently).
function _clique_escape(R::_CliqueRates, entry::Int, k::Int)
    n = length(R.nodes)
    τ = zeros(n)
    for (J, _, t) in R.contacts
        τ[J] += t
    end
    # species from which an infector is reachable (from the others, nothing is ever transmitted)
    live = τ .> 0
    changed = true
    while changed
        changed = false
        for i in 1:n
            if !live[i] && any(o -> live[first(o)], R.out[i])
                live[i] = true
                changed = true
            end
        end
    end
    live[entry] || return 1.0
    L = findall(live)
    pos = Dict{Int,Int}(j => m for (m, j) in enumerate(L))
    A = zeros(length(L), length(L))
    b = zeros(length(L))
    for (m, i) in enumerate(L)
        A[m, m] += k * τ[i]
        for (j, a) in R.out[i]
            A[m, m] += a
            haskey(pos, j) ? (A[m, pos[j]] -= a) : (b[m] += a)    # to a dead species: escaped
        end
    end
    return (A \ b)[pos[entry]]
end


"""
    _clustered_general_ngm(cm, net::ClusteredNetwork; p = nothing, kind = :clump) -> Matrix{Float64}

The tree-of-triangles next-generation matrix of a T_EB model with one susceptible class on the
clustered network `net`, whose spectral radius is [`_clustered_general_reproduction_number`](@ref)
(see there for the notation, the two kinds and the numeric requirements).

- `kind = :clump`: the typed clump matrix M, rows and columns (L, e) for e in
  `entry_species(cm)`, then (T, e): row (L, e) is [n_L T_{e→·}  n_T μ_{e→·}] and row (T, e) is
  [m_L T_{e→·}  m_T μ_{e→·}].
- `kind = :generation` (one entry state): the generation matrix of verified issue E04,
  [A B 0; C D c; C D 0] over (L, Δ1, Δ2): a child reached along a line, a child infected directly
  in a triangle, and a child infected through the other partner of its triangle.

The blocks of an edge kind the network lacks are dropped. A network without edges, or a model
without an entry state, gives the 0×0 matrix.
"""
function _clustered_general_ngm(cm::ContactModel, net::ClusteredNetwork;
                                p::Union{Nothing,AbstractDict} = nothing, kind::Symbol = :clump,
                                context::AbstractString = "basic_reproduction_number(:$(cm.name), ClusteredNetwork)")
    kind in (:clump, :generation) || throw(ArgumentError(
        "kind must be :clump or :generation; got :$kind"))
    require_admissible(cm, :edge_based; network = net)
    lm = _lift_model(cm, net, susceptible_species(cm); context)
    _single_susceptible(lm)
    pd = _clg_params(cm, p)
    R = _clique_rates(cm, net, lm, pd, context)
    mom(i, j) = _clg_moment(net, i, j, pd, context)
    gx, gy = mom(1, 0), mom(0, 1)
    hasL, hasT = !iszero(gx), !iszero(gy)
    (hasL || hasT) || return zeros(0, 0)
    nL, nT = hasL ? (mom(2, 0) / gx, mom(1, 1) / gx) : (0.0, 0.0)
    mL, mT = hasT ? (mom(1, 1) / gy, mom(0, 2) / gy) : (0.0, 0.0)
    index = Dict{Symbol,Int}(X => i for (i, X) in enumerate(R.nodes))
    entries = [index[X] for X in entry_species(cm)]
    isempty(entries) && return zeros(0, 0)
    if kind === :generation
        length(entries) == 1 || throw(ArgumentError(
            "$context: the generation-based R₀ needs one entry state; this model has " *
            "$(join(entry_species(cm), ", ")) (use kind = :clump, the typed clump reproduction " *
            "number, which has the same threshold)"))
        e = only(entries)
        q1, q2 = _clique_escape(R, e, 1), _clique_escape(R, e, 2)
        T, c = 1 - q1, q1 - q2
        hasT || return fill(T * nL, 1, 1)
        D = 2 * T * mT
        hasL || return [D c; D 0.0]
        A, B, C = T * nL, 2 * T * nT, T * mL
        return [A B 0.0; C D c; C D 0.0]
    end
    Tl = [_clique_offspring(R, e, 2)[entries] for e in entries]    # T_{e→x}
    μt = hasT ? [_clique_offspring(R, e, 3)[entries] for e in entries] : nothing
    k = length(entries)
    blocks = Symbol[]
    hasL && push!(blocks, :line)
    hasT && push!(blocks, :triangle)
    M = zeros(k * length(blocks), k * length(blocks))
    for (bi, from) in enumerate(blocks), a in 1:k, (bj, to) in enumerate(blocks)
        excess = from === :line ? (to === :line ? nL : nT) : (to === :line ? mL : mT)
        row = to === :line ? Tl[a] : μt[a]
        for x in 1:k
            M[(bi - 1) * k + a, (bj - 1) * k + x] = excess * row[x]
        end
    end
    return M
end

_clg_spectral_radius(K::AbstractMatrix) = isempty(K) ? 0.0 : Float64(maximum(abs, eigvals(K)))

"""
    _clustered_general_reproduction_number(cm, net::ClusteredNetwork; p = nothing, kind = :clump)
    _clustered_general_reproduction_number(sys::EdgeModelSystem; p = nothing, kind = :clump)

The reproduction number of a T_EB model with one susceptible class on the clustered network
`net` (s single edges and t triangles per node, (s, t) ~ `net.joint`). It comes from the
tree-of-triangles branching process of Volz et al. (2011), with the offspring typed by edge kind
and entry state, so it also covers models with several entry states, such as two strains.
Numeric rates are required: the model's `parameter_defaults`, overridden by `p` (by name).
Symbolic network means (e.g. `PoissonDegree(κs)` with `@parameters κs`) are taken from `p` by
name too. Exits from the susceptible class are evaluated at the disease-free state ξ = 1, as in
NetworkEpiCore's `next_generation_matrix`.

Notation:
- line moments n_L = g_xx/g_x and n_T = g_xy/g_x, the expected excess lines and triangles of a
  node reached along a line;
- triangle moments m_L = g_xy/g_y and m_T = g_yy/g_y, those of a node infected inside a triangle;
- T_{e→x}, the expected infections into x along a line from an index that entered e;
- μ_{e→x}, the expected infections into x in a triangle with two susceptible partners, races
  included (`_clique_offspring`).

- `kind = :clump` (the default, any model) is R_* = ρ(M), the spectral radius of the typed clump
  matrix. M has rows (L, e) = [n_L T_{e→·}  n_T μ_{e→·}] and rows (T, e) =
  [m_L T_{e→·}  m_T μ_{e→·}]. Every infection in a triangle is counted as a child of the
  triangle's index, which makes this an exact multitype branching process with the threshold of
  the epidemic (R_* = 1 ⇔ the early growth rate of the lifted field is 0). For one entry state
  it is WP20's `kind = :clump`, with μ = 2T(1 + q₁ − q₂).
- `kind = :generation` (one entry state only) is WP20's generation-based R₀: the Perron root of
  [A B 0; C D c; C D 0]. Here A = T n_L, B = 2T n_T, C = T m_L, D = 2T m_T and c = q₁ − q₂, where
  q_k is the probability that an infective transmits along none of k given edges.

Without triangles, both kinds are the configuration-model value T_{e→x} n_L (typed by entry). A
block without edges (g_x(1,1) = 0 or g_y(1,1) = 0) is dropped. The matrices are
[`_clustered_general_ngm`](@ref).
"""
_clustered_general_reproduction_number(cm::ContactModel, net::ClusteredNetwork;
                                       p::Union{Nothing,AbstractDict} = nothing, kind::Symbol = :clump) =
    _clg_spectral_radius(_clustered_general_ngm(cm, net; p, kind))

_clustered_general_reproduction_number(sys::EdgeModelSystem; kw...) =
    _clustered_general_reproduction_number(_clg_system(sys, "_clustered_general_reproduction_number")...; kw...)

# The model and network of a system lifted on a ClusteredNetwork.
function _clg_system(sys::EdgeModelSystem, fname::AbstractString)
    net = get(sys.metadata, :network, nothing)
    cm = get(sys.metadata, :model, nothing)
    (net isa ClusteredNetwork && cm isa ContactModel) || throw(ArgumentError(
        "$(fname): the system is not an edge-based model on a ClusteredNetwork"))
    return cm, net
end

# ---------------------------------------------------------------------------------------------
# Threshold quantities of a clustered system (analysis.jl's `_numeric_threshold` extension point)
# ---------------------------------------------------------------------------------------------

"""
    _clustered_threshold(f, sys::EdgeModelSystem, vals::AbstractDict{Symbol}; kind = nothing, from = nothing)

The threshold quantity `f` of a system lifted on a `ClusteredNetwork`, for every model the
clustered lift accepts. `vals` gives numeric parameter values by name, including any symbolic
network means. NetworkEpiCore refuses threshold analysis on a `ClusteredNetwork`, so this is the
body for analysis.jl's extension point `_numeric_threshold(::Val{:clustered}, f, sys, vals; kw...)`.

- `next_generation_matrix`: K = [`_clustered_general_ngm`](@ref). With one entry state (SIR,
  SEIR, SEAIR, Erlang stages) and `kind = nothing`, it is the generation matrix of verified
  issue E04 over (L, Δ1, Δ2). That is WP20's default, and its Perron root matches the simulated
  generation growth ratio. With several entry states (two strains, cross infection), it is the
  typed clump matrix over (L, e), then (T, e), with e in `entry_species` order. Both kinds have
  the epidemic threshold, and `kind = :clump` or `:generation` forces one.
- `basic_reproduction_number`: ρ(K).
- `transmissibility`: T = 1 − q₁, the probability that a node entering `from` transmits across
  one given edge. `from` defaults to the unique entry state. T does not depend on the network.
- `early_growth_rate`: the leading eigenvalue of the Jacobian of the lifted field
  (`symbolic_ode(sys)`) at the disease-free state, θ = ξ = q = 1 and every other coordinate 0.
  It is taken over the coordinates that can lead to a transmission: φ2_X and χ_X for X in the
  transmission chain, and the triangle pair states that contain such an X. That subsystem is
  closed at first order. The field is not linear in q (triangle pair states), so the F − V split
  of the other closures does not apply, but sign(r) = sign(R₀ − 1).

Exits from the susceptible class are evaluated at ξ = 1, as in NetworkEpiCore.
"""
function _clustered_threshold end

_clg_default_kind(cm::ContactModel, kind) =
    kind === nothing ? (length(entry_species(cm)) == 1 ? :generation : :clump) : kind

function _clustered_threshold(::typeof(next_generation_matrix), sys::EdgeModelSystem, vals::AbstractDict;
                              kind::Union{Nothing,Symbol} = nothing, kw...)
    cm, net = _clg_system(sys, "next_generation_matrix")
    return _clustered_general_ngm(cm, net; p = vals, kind = _clg_default_kind(cm, kind),
                                  context = "next_generation_matrix(:$(cm.name), ClusteredNetwork)")
end

_clustered_threshold(::typeof(basic_reproduction_number), sys::EdgeModelSystem, vals::AbstractDict; kw...) =
    _clg_spectral_radius(_clustered_threshold(next_generation_matrix, sys, vals; kw...))

function _clustered_threshold(::typeof(transmissibility), sys::EdgeModelSystem, vals::AbstractDict;
                              from::Union{Nothing,Symbol} = nothing, kw...)
    cm, net = _clg_system(sys, "transmissibility")
    context = "transmissibility(:$(cm.name), ClusteredNetwork)"
    require_admissible(cm, :edge_based; network = net)
    lm = _lift_model(cm, net, susceptible_species(cm); context)
    _single_susceptible(lm)
    R = _clique_rates(cm, net, lm, _clg_params(cm, vals), context)
    X = if from === nothing
        entries = entry_species(cm)
        length(entries) == 1 || throw(ArgumentError(
            "$context: the model has $(isempty(entries) ? "no entry state" : "the entry states " *
            join(entries, ", ")); pass from = <state>"))
        only(entries)
    else
        from
    end
    i = findfirst(==(X), R.nodes)
    i === nothing && throw(ArgumentError(
        "$context: from = :$X is not a non-susceptible species of the model ($(join(R.nodes, ", ")))"))
    return 1 - _clique_escape(R, i, 1)
end

function _clustered_threshold(::typeof(early_growth_rate), sys::EdgeModelSystem, vals::AbstractDict; kw...)
    fname = "early_growth_rate"
    cm, _ = _clg_system(sys, fname)
    table = sys.metadata[:contributions]
    raw = sys.metadata[:raw]
    info = table.coordinate_info
    chain = _transmission_chain(cm)
    transmitting(x) = (x.role in (:φ, :χ) && x.species in chain) ||
                      (x.role === :pair && (first(x.types) in chain || last(x.types) in chain))
    states = collect(raw.states)
    idx = Int[]
    for (i, s) in enumerate(states)
        k = findfirst(x -> isequal(x.var, s), info)
        k === nothing && throw(ArgumentError("$(fname): the state $(s) is not an edge-based coordinate"))
        transmitting(info[k]) && push!(idx, i)
    end
    isempty(idx) && throw(ArgumentError(
        "$(fname): the model :$(cm.name) has no state from which a transmission can follow"))
    # the disease-free state: θ₂ = θ₃ = ξ = 1 and q = 1, every φ2, pop, χ and pair state 0
    dfe = Dict{Any,Any}(x.var => (x.role in (:θ, :ξ) ? 1 : 0) for x in info)
    for (_, q) in table.seed_factors
        dfe[q] = 1
    end
    J = Symbolics.jacobian(collect(raw.rhs)[idx], states[idx])
    Jn = _evaluate(map(e -> Symbolics.substitute(e, dfe; fold = Val(true)), J), vals, fname)
    return Float64(maximum(real, eigvals(Jn)))
end

_clustered_threshold(f, sys::EdgeModelSystem, vals; kw...) = throw(ArgumentError(
    "$(nameof(f)): no threshold method for a system lifted on a ClusteredNetwork (the clustered " *
    "lift gives next_generation_matrix, basic_reproduction_number, transmissibility and " *
    "early_growth_rate)"))

# analysis.jl's extension point (design §G.1: a lift file adds its closure's method by dispatch).
# Every model the clustered lift accepts reaches the tree-of-triangles threshold quantities here.
_numeric_threshold(::Val{:clustered}, f, sys::EdgeModelSystem, vals; kw...) =
    _clustered_threshold(f, sys, vals; kw...)
