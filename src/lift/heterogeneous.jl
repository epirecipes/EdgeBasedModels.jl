# Owner: WP36f (DESIGN_NetworkEpiCore.md §K WP36f, §B.2, §C.2 `unstructured`, §D.5 M10; work package in §K).
#
# Heterogeneous susceptibility: several susceptible classes on one configuration network, as fixed node attributes
# that do not influence the contact structure (Miller & Volz 2013, PLoS ONE 8:e69162, §2.2.2 "Heterogeneous
# infectiousness and susceptibility"; papers/miller_volz.md). The classes are the strata `st` of
# `unstructured(net, st)`: a node's class a is drawn with probability n_a independently of its degree, so its
# partners' classes are independent of everything else. The model labels each susceptible class with its stratum
# (one per stratum); every other species is either class-specific (labelled, such as I_a) or shared (unlabelled: the
# node's state no longer records its class, as for S_lo + I → I + I, S_hi + I → I + I).
#
# Coordinates (ψ is the degree PGF of `net`; the partner of a random edge is a uniformly random node in law, because
# its class and its initial state are independent of its degree):
#
#     θ_<a>      P(an edge into a class-a test node has not transmitted), one per susceptibility class a
#     φ_<Y>_<a>  the same edge, with its partner in the species Y (of any class, or of Y's class)
#     pop_<Y>    the fraction of ALL nodes in Y;  ξ_<s>, the exit survival factor of the susceptible class s
#
# with S_a = n_a q_a ξ_a ψ(θ_a) and φ_{s_a} = n_a q_a ξ_a ψ'(θ_a)/ψ'(1) (the partner is susceptible of class a; it does
# not depend on the test node's class). q_a is the fraction of class-a nodes initially susceptible. Per reaction
# (design §D.4, the configuration closure with the class of the recipient):
#
#     contact  s_a + J → X + J (τ):  θ̇_a −= τφ_{J,a};  φ̇_{J,a} −= τφ_{J,a};
#                                     φ̇_{X,e} += τφ_{J,a}·n_a q_a ξ_a ψ''(θ_a)/ψ'(1) for every class e;
#                                     pop_X' += τφ_{J,a}·n_a q_a ξ_a ψ'(θ_a)
#     transition X → Y | ∅ (r):       φ̇_{X,e} −= rφ_{X,e}, φ̇_{Y,e} += rφ_{X,e} for every e;  pop_X' −= r pop_X, pop_Y' += r pop_X
#     exit     s_a → Y (ν):           ξ̇_a −= νξ_a;  φ̇_{Y,e} += νφ_{s_a} for every e;  pop_Y' += νS_a
#
# so θ_e = Σ_a φ_{s_a} + Σ_Y φ_{Y,e} for every class e, and Σ_a S_a + Σ_Y pop_Y = 1 (removals go to the sinks, §J.2).
#
# M10 (the acceptance of WP36f). On unstructured(net, st) the multitype lift of lift/multitype.jl (K² coordinates
# θ_{b→a}, conditional on the partner's type) has the quotient
#
#     θ_a = Σ_b n_b θ_{b→a},  φ_{Y,a} = Σ_b n_b φ_{Y_b,a} (Y shared; n_b φ_{Y_b,a} for Y of class b),  pop_Y = Σ_b pop_{Y_b}
#
# because ψ_a(x) = ψ(Σ_b n_b x_b), so ∂_bψ_a = n_bψ' and ∂_b∂_cψ_a = n_b n_cψ'' (a linear semiconjugacy onto this
# field, verified in test/suites/heterogeneous.jl). A shared species is the image of its implicit stratification
# Y ↦ Y_b, which is why this closure accepts unlabelled species while the multitype lift does not; a fully stratified
# model is lifted here with K instead of K² edge coordinates. With one class, or with equal rates in every class and
# proportional seeds, it reproduces the untyped configuration lift (the unit law M10).
#
# Seeding follows NetworkOutbreaks on the typed graph of unstructured(net, st) (sample_graph(::MultitypeNetwork)'s
# TypedGraph; design §J.6): the compartments of a class are placed on the nodes of that class first, the shared
# compartments uniformly among the nodes still free, and every other node of class a starts in its susceptible class;
# the resulting q_a are parameters of the system, set by `default_initial_conditions`.
#
# Entry points: `edge_based(model, net, st)` and `lift_contributions(model, net, st)` below, and (design §L.7)
# `edge_based(model, unstructured(net, st))`, `edge_based(sc::Scenario)` and `lift_contributions(model,
# unstructured(net, st))`, which lift/multitype.jl hands to `_assemble_heterogeneous` and `_heterogeneous_closure`
# when the susceptible classes carry strata and some other species does not.
#
# Include order: after lift/assembler.jl (`_EdgeClosure`, `_LiftModel`, `_contributions`, `_close`, `_state`, …) and
# lift/multitype.jl.

# ---------------------------------------------------------------------------------------------
# The closure
# ---------------------------------------------------------------------------------------------

struct _HeterogeneousClosure <: _EdgeClosure
    net::MultitypeNetwork                     # unstructured(base, st): the node types are the classes
    degrees::DegreeDistribution               # the base degree law ψ
    classes::Vector{Symbol}                   # the strata, in network order
    n::Dict{Symbol,Float64}                   # class => its fraction of the nodes
    class_of::Dict{Symbol,Symbol}             # species (and sinks) => class, or :all (shared)
    sus::Dict{Symbol,Symbol}                  # class => its susceptible species
    info::Vector{_Coordinate}
    θ::Dict{Symbol,Any}                       # class => θ_<a>
    ξ::Dict{Symbol,Any}                       # class => ξ_<s_a>
    q::Dict{Symbol,Any}                       # class => q_<s_a>
    φ::Dict{Tuple{Symbol,Symbol},Any}         # (species Y, test class a) => φ_<Y>_<a>
    pop::Dict{Symbol,Any}
    ψ::Dict{Symbol,NTuple{3,Any}}             # class => (ψ, ψ', ψ'') at θ_a
    k̄::Any                                    # ψ'(1)
end

_closure_kind(::_HeterogeneousClosure) = :heterogeneous
_coordinates(cl::_HeterogeneousClosure) = cl.info
_seed_factors(cl::_HeterogeneousClosure) =
    Pair{Symbol,Any}[cl.sus[a] => cl.q[a] for a in cl.classes if haskey(cl.sus, a)]
_type_of(cl::_HeterogeneousClosure, X::Symbol) = cl.class_of[X]
_type_size(cl::_HeterogeneousClosure, a::Symbol) = a === :all ? 1.0 : cl.n[a]
_seed_background(::_HeterogeneousClosure, ::_LiftModel) = nothing
_network_terms(cl::_HeterogeneousClosure) =
    vcat(Any[x for a in cl.classes if haskey(cl.ψ, a) for x in cl.ψ[a]], Any[cl.k̄])

_het_theta_name(a::Symbol) = Symbol(:θ_, a)
_het_phi_name(Y::Symbol, a::Symbol) = Symbol(:φ_, Y, :_, a)

"""
    _unstructured_degrees(net::MultitypeNetwork) -> Union{DegreeDistribution,Nothing}

The common degree law ψ when the node types of `net` are independent of the network, as built by
`unstructured(base, st)`: every type has the law `SplitDegrees(ψ, b => n_b, …)` with the same ψ and the weights
equal to the type sizes. `nothing` otherwise. (The criterion of NetworkOutbreaks' `sample_graph`, which samples such
a network as a configuration graph of ψ with independent node types.)
"""
function _unstructured_degrees(net::MultitypeNetwork)
    all(m -> m isa SplitDegrees, net.degrees) || return nothing
    total = first(net.degrees).total
    sizes = Dict(zip(net.types, net.sizes))
    for m in net.degrees
        m.total == total || return nothing
        w = Dict(m.weights)
        keys(w) == keys(sizes) || return nothing
        all(isapprox(w[b], sizes[b]; rtol = 1e-12, atol = 1e-15) for b in keys(sizes)) || return nothing
    end
    return total
end

function _heterogeneous_closure(net::MultitypeNetwork, lm::_LiftModel)
    d = _unstructured_degrees(net)
    d === nothing && throw(ArgumentError(
        "$(lm.context): heterogeneous susceptibility (susceptible classes as fixed node attributes, with shared " *
        "species) needs node types that are independent of the network, as built by unstructured(net, st); on a " *
        "structured MultitypeNetwork stratify every species (stratify(model, st)) and use the multitype lift " *
        "edge_based(model, net)"))
    classes = collect(Symbol, net.types)
    n = Dict{Symbol,Float64}(a => Float64(net.sizes[i]) for (i, a) in enumerate(classes))
    class_of = Dict{Symbol,Symbol}()
    for X in vcat(lm.Σ, lm.nodes)
        a = lm.stratum[X]
        (a === :all || a in classes) || throw(ArgumentError(
            "$(lm.context): the species $(X) belongs to the stratum $(a), which is not one of the classes " *
            "$(join(classes, ", ")) of the network"))
        class_of[X] = a
    end
    sus = Dict{Symbol,Symbol}()
    for s in lm.Σ
        a = class_of[s]
        a === :all && throw(ArgumentError(
            "$(lm.context): the susceptible species $(s) has no stratum; with heterogeneous susceptibility every " *
            "susceptible class is labelled with its class (SpeciesLabel(:S; stratum = :a)), one per class of " *
            "$(join(classes, ", "))"))
        haskey(sus, a) && throw(ArgumentError(
            "$(lm.context): the class $(a) has two susceptible species, $(sus[a]) and $(s)"))
        sus[a] = s
    end
    info = _Coordinate[]
    θ = Dict{Symbol,Any}()
    ξ = Dict{Symbol,Any}()
    q = Dict{Symbol,Any}()
    ψ = Dict{Symbol,NTuple{3,Any}}()
    for a in classes
        haskey(sus, a) || continue
        s = sus[a]
        name = _het_theta_name(a)
        θ[a] = _state(name)
        push!(info, _Coordinate(name, θ[a], :θ, s, (:all, a)))
        name = Symbol(:ξ_, s)
        ξ[a] = _state(name)
        push!(info, _Coordinate(name, ξ[a], :ξ, s, (a, a)))
        q[a] = _param(Symbol(:q_, s))
        ψ[a] = (pgf(d, θ[a]), pgf_derivative(d, θ[a], 1), pgf_derivative(d, θ[a], 2))
    end
    φ = Dict{Tuple{Symbol,Symbol},Any}()
    for Y in lm.nodes, a in classes
        name = _het_phi_name(Y, a)
        φ[(Y, a)] = _state(name)
        push!(info, _Coordinate(name, φ[(Y, a)], :φ, Y, (class_of[Y], a)))
    end
    pop = Dict{Symbol,Any}()
    for Y in lm.nodes
        name = Symbol(:pop_, Y)
        pop[Y] = _state(name)
        push!(info, _Coordinate(name, pop[Y], :pop, Y, (class_of[Y], class_of[Y])))
    end
    return _HeterogeneousClosure(net, d, classes, n, class_of, sus, info, θ, ξ, q, φ, pop, ψ, mean_degree(d))
end

# The four factors of class a (design §D.4), each with the κ → 0 limit of verified issues E11/E32 where ψ'(1) = 0.
_het_σ(cl::_HeterogeneousClosure, a::Symbol) = cl.n[a] * cl.q[a] * cl.ξ[a]
_het_node_S(cl::_HeterogeneousClosure, a::Symbol) = _het_σ(cl, a) * cl.ψ[a][1]
_het_edge_S(cl::_HeterogeneousClosure, a::Symbol) =
    _ratio(_het_σ(cl, a) * cl.ψ[a][2], cl.k̄, _het_σ(cl, a) * cl.ψ[a][1])
_het_node_entry(cl::_HeterogeneousClosure, a::Symbol) = _het_σ(cl, a) * cl.ψ[a][2]
_het_edge_entry(cl::_HeterogeneousClosure, a::Symbol) =
    _ratio(_het_σ(cl, a) * cl.ψ[a][3], cl.k̄, _het_σ(cl, a) * cl.ψ[a][2])

# Classes are fixed node attributes: a node of class a may enter a species of class a or a shared one, and a node
# in a shared species (whose class its state does not record) may only enter shared species.
function _het_check_target(cl::_HeterogeneousClosure, r, from::Symbol, to::Symbol)
    a, b = cl.class_of[from], cl.class_of[to]
    (b === :all || b === a) && return nothing
    what = a === :all ? "a node in the shared species $(from), whose state does not record its class," :
           "a node of class $(a) ($(from))"
    throw(ArgumentError(
        "the reaction `$(r.name)` moves $(what) into $(to) of class $(b); the classes are fixed node attributes, so " *
        "a node may enter only species of its own class or shared (unlabelled) species"))
end

function _contact_terms(cl::_HeterogeneousClosure, c::Contact, τ)
    a = cl.class_of[c.recipient]
    _het_check_target(cl, c, c.recipient, c.product)
    h = τ * cl.φ[(c.infector, a)]
    flux = h * _het_node_entry(cl, a)
    entry = _het_edge_entry(cl, a)
    terms = Pair{Symbol,Any}[_het_theta_name(a) => -h, _het_phi_name(c.infector, a) => -h]
    for e in cl.classes
        push!(terms, _het_phi_name(c.product, e) => h * entry)
    end
    push!(terms, Symbol(:pop_, c.product) => flux)
    return terms, flux
end

function _exit_terms(cl::_HeterogeneousClosure, t::NodeTransition, to::Symbol, ν)
    a = cl.class_of[t.from]
    _het_check_target(cl, t, t.from, to)
    flux = ν * _het_node_S(cl, a)
    edge = _het_edge_S(cl, a)
    terms = Pair{Symbol,Any}[Symbol(:ξ_, t.from) => -ν * cl.ξ[a]]
    for e in cl.classes
        push!(terms, _het_phi_name(to, e) => ν * edge)
    end
    push!(terms, Symbol(:pop_, to) => flux)
    return terms, flux
end

function _transition_terms(cl::_HeterogeneousClosure, t::NodeTransition, to::Symbol, r)
    X = t.from
    _het_check_target(cl, t, X, to)
    flux = r * cl.pop[X]
    terms = Pair{Symbol,Any}[]
    for e in cl.classes
        push!(terms, _het_phi_name(X, e) => -r * cl.φ[(X, e)], _het_phi_name(to, e) => r * cl.φ[(X, e)])
    end
    push!(terms, Symbol(:pop_, X) => -flux, Symbol(:pop_, to) => flux)
    return terms, flux
end

# Observables: per susceptible class s_a its node-S (named s_a) and edge-S φ_<s_a> (the partner of an edge is
# susceptible of class a, whatever the class of the test node); the totals `:S` (when no species owns the name),
# `:I` and `:infectious` (the fraction in the infector states); and the per-class hazards `edge_hazard_<a>`
# (θ̇_a = −edge_hazard_<a>).
function _closure_observables(cl::_HeterogeneousClosure, lm::_LiftModel, ::LiftContributions)
    obs = Pair{Symbol,Any}[]
    total = Any[]
    for a in cl.classes
        haskey(cl.sus, a) || continue
        s = cl.sus[a]
        S = _het_node_S(cl, a)
        push!(total, S)
        push!(obs, s => S, Symbol(:φ_, s) => _het_edge_S(cl, a))
    end
    (:S in lm.nodes || :S in lm.Σ) || push!(obs, :S => _sum_terms(total))
    infectious = _sum_terms(Any[cl.pop[J] for J in lm.infectors])
    push!(obs, :I => infectious, :infectious => infectious)
    hazard = Dict{Symbol,Vector{Any}}(a => Any[] for a in keys(cl.sus))
    for (c, τ) in zip(contacts(lm.cm), lm.contact_rates)
        a = cl.class_of[c.recipient]
        push!(hazard[a], τ * cl.φ[(c.infector, a)])
    end
    for a in cl.classes
        haskey(cl.sus, a) && push!(obs, Symbol(:edge_hazard_, a) => _sum_terms(hazard[a]))
    end
    return obs
end

# θ = ξ = 1 and φ_{Y,a}(0) = pop_Y(0) = ρ_Y (a fraction of all nodes, for every test class a).
function _initial_values(cl::_HeterogeneousClosure, lm::_LiftModel, ρ)
    v = Dict{Symbol,Float64}()
    for x in cl.info
        v[x.name] = x.role in (:θ, :ξ) ? 1.0 : get(ρ, x.species, 0.0)
    end
    return v
end

function _relabel_coordinate(::Val{:heterogeneous}, x::_Coordinate, m)
    X = m(x.species)
    name = x.role === :θ ? x.name :
           x.role === :ξ ? Symbol(:ξ_, X) :
           x.role === :φ ? _het_phi_name(X, last(x.types)) : Symbol(:pop_, X)
    var = name === x.name ? x.var : _state(name)
    return _Coordinate(name, var, x.role, X, x.types)
end

# ---------------------------------------------------------------------------------------------
# Seeding: NetworkOutbreaks' placement on the typed graph of unstructured(net, st) (§J.6)
# ---------------------------------------------------------------------------------------------

"""
    _het_susceptible_fractions(cl, lm, initial; N) -> (ρ, σ)

The seed fractions ρ_X of the node species (fractions of all nodes) and the initial fraction σ_a of all nodes in each
susceptible class, in the large-N limit of NetworkOutbreaks' seeding of a stratified model on the typed graph of
`unstructured(net, st)` (the `_seed_nodes!` method for a `TypedGraph`):

1. the compartments of class a (labelled species, the susceptible class s_a included when `initial` names it) are
   placed on the class-a nodes: T_a + G_a ≤ n_a, where G_a is the named fraction of s_a;
2. the shared compartments, L in total, are placed uniformly at random among the f_a = n_a − T_a − G_a nodes of
   every class that are still free (F = Σ_a f_a ≥ L), so a fraction f_a/F of them comes from class a;
3. every other node of class a starts in s_a: σ_a = G_a + f_a(1 − L/F).

A `default` compartment takes every node that step 3 would put in a susceptible class, so it must be a shared
species (NetworkOutbreaks refuses a default with a stratum on a typed graph).
"""
function _het_susceptible_fractions(cl::_HeterogeneousClosure, lm::_LiftModel, initial::SeedSpec; N = nothing)
    bg = initial.default
    if bg !== nothing
        (bg in lm.nodes && !(bg in lm.sinks)) || throw(ArgumentError(
            "default_initial_conditions: $(initial) names the default compartment $(bg), which is not a node " *
            "species of the model; with heterogeneous susceptibility the unseeded nodes of class a start in its " *
            "susceptible class, so omit `default`"))
        cl.class_of[bg] === :all || throw(ArgumentError(
            "default_initial_conditions: $(initial) names the default compartment $(bg) of class " *
            "$(cl.class_of[bg]), but the unseeded nodes of every class would start there; with heterogeneous " *
            "susceptibility the unseeded nodes of class a start in its susceptible class, so omit `default` (as " *
            "NetworkOutbreaks does on the typed graph)"))
    end
    ρ = Dict{Symbol,Float64}(X => 0.0 for X in lm.nodes if !(X in lm.sinks))
    G = Dict{Symbol,Float64}(a => 0.0 for a in cl.classes)
    T = Dict{Symbol,Float64}(a => 0.0 for a in cl.classes)
    L = 0.0
    seen = Set{Symbol}()
    for (X, v) in seed_fractions(initial; N)
        X in seen && throw(ArgumentError("default_initial_conditions: $(X) is seeded twice"))
        push!(seen, X)
        (isfinite(v) && v >= 0) || throw(ArgumentError(
            "default_initial_conditions: the seed fraction of $(X) must be finite and ≥ 0; got $v"))
        if X in lm.Σ
            G[cl.class_of[X]] += v
        elseif haskey(ρ, X)
            ρ[X] = v
            a = cl.class_of[X]
            a === :all ? (L += v) : (T[a] += v)
        else
            throw(ArgumentError(
                "default_initial_conditions: $(initial) seeds $(X), which is not a species of the model " *
                "(species: $(join(vcat(lm.Σ, [x for x in lm.nodes if !(x in lm.sinks)]), ", ")))"))
        end
    end
    tol = 1e-12
    f = Dict{Symbol,Float64}()
    for a in cl.classes
        used = T[a] + G[a]
        used <= cl.n[a] * (1 + tol) || throw(ArgumentError(
            "default_initial_conditions: $(initial) places $(used) of the nodes in compartments of class $(a), but " *
            "the class has $(cl.n[a]) of them (seed fractions are fractions of all nodes, design §J.6)"))
        f[a] = max(cl.n[a] - used, 0.0)
    end
    F = sum(values(f); init = 0.0)
    L <= F + tol || throw(ArgumentError(
        "default_initial_conditions: $(initial) seeds $(L) of the nodes in shared compartments, but only $(F) are " *
        "left after the compartments of the classes"))
    σ = Dict{Symbol,Float64}()
    for a in cl.classes
        σ[a] = F > 0 ? G[a] + f[a] * max(1 - L / F, 0.0) : G[a]
    end
    return ρ, σ
end

function _het_initial_conditions(cl::_HeterogeneousClosure, lm::_LiftModel, info, cum, infected,
                                 initial::SeedSpec; N = nothing)
    ρ, σ = _het_susceptible_fractions(cl, lm, initial; N)
    values = _initial_values(cl, lm, ρ)
    ic = Dict{Any,Float64}()
    for x in info
        ic[x.var] = values[x.name]
    end
    for (a, q) in cl.q
        ic[q] = σ[a] / cl.n[a]
    end
    ic[cum] = sum((ρ[X] for X in infected if haskey(ρ, X)); init = 0.0)
    return ic
end

# ---------------------------------------------------------------------------------------------
# Assembly (the expanded form of lift/assembler.jl `_assemble`, with this closure and its seeding)
# ---------------------------------------------------------------------------------------------

"""
    _heterogeneous_lift(cm::ContactModel, net::MultitypeNetwork; name = :edge_based_model, form = :expanded)

The heterogeneous-susceptibility lift of `cm` on `net = unstructured(base, st)` (see
[`edge_based`](@ref)`(cm, base, st)`): admissibility, then the closure `_HeterogeneousClosure`, the per-reaction
table, the cumulative accumulator and the MTK system. Internal; `edge_based(cm, net::MultitypeNetwork)` hands
heterogeneous-susceptibility models to `_assemble_heterogeneous` (design §L.7).
"""
function _heterogeneous_lift(cm::ContactModel, net::MultitypeNetwork; name::Symbol = :edge_based_model,
                             form::Symbol = :expanded)
    form === :expanded || throw(ArgumentError(
        "edge_based with heterogeneous susceptibility has only the expanded form; got form = :$form"))
    require_admissible(cm, :edge_based; network = net)
    return _assemble_heterogeneous(cm, net; name, context = _lift_context(cm, net))
end

function _assemble_heterogeneous(cm::ContactModel, net::MultitypeNetwork; name::Symbol, context::AbstractString)
    lm = _lift_model(cm, net, susceptible_species(cm); context)
    cl = _heterogeneous_closure(net, lm)
    table = _contributions(cl, lm, net)
    info, f, drop = _close(table)
    closeξ(e) = isempty(drop) ? e : Symbolics.substitute(e, drop)
    raw = SymbolicODE(Symbol(name, :_edge_based); states = Any[x.var for x in info], rhs = f, parameters = :infer,
                      domain = _probe_domain(info))
    infected = _infected_species(lm)
    cum = _state(:cumulative)
    cum_rhs = closeξ(_cumulative_rhs(table, infected))
    obs = Pair{Symbol,Any}[k => closeξ(v) for (k, v) in _closure_observables(cl, lm, table)]
    qs = Any[q for (_, q) in _seed_factors(cl)]
    obsnames = unique!(Symbol[first(o) for o in obs])
    generated = vcat(Symbol[x.name for x in table.coordinate_info], Symbol[:cumulative], obsnames,
                     Symbol[_symname(q) for q in qs])
    own = vcat(Any[x.var for x in table.coordinate_info], Any[cum], qs)
    _check_generated_names(lm, generated, own, vcat(f, Any[last(o) for o in obs], cum_rhs), _network_terms(cl))
    D = D_nounits
    eqs = Equation[D(x.var) ~ fx for (x, fx) in zip(info, f)]
    push!(eqs, D(cum) ~ cum_rhs)
    obsvars = Dict{Symbol,Any}()
    for (k, e) in obs
        haskey(obsvars, k) && continue
        v = _state(k)
        obsvars[k] = v
        c = _numvalue(e)
        push!(eqs, v ~ (c === nothing ? e : Symbolics.Num(c)))
    end
    compiled = mtkcompile(System(eqs, t_nounits; name))
    variables = Dict{Symbol,Any}(x.name => x.var for x in info)
    variables[:cumulative] = cum
    _add_recovered_alias!(variables, lm)
    # q_<s> is a parameter set from `initial` (not an expression of seed parameters): the NetworkOutbreaks placement
    # of step 2 of `_het_susceptible_fractions` is not a polynomial in the seed fractions. `p` may not set it.
    qparams = Dict{Symbol,Any}(s => q for (s, q) in _seed_factors(cl))
    md = _assembled_metadata(cm, net, lm, cl, table, raw, qparams, Dict{Any,Any}(q => q for q in qs), infected;
                             form = :expanded)
    md[:classes] = (names = copy(cl.classes), sizes = Float64[cl.n[a] for a in cl.classes],
                    susceptible = Dict(cl.sus), base = ConfigurationNetwork(cl.degrees))
    md[:coords] = Dict{Symbol,Any}(x.name => x.var for x in info)
    md[:ic] = (initial; N = nothing) -> _het_initial_conditions(cl, lm, info, cum, infected, initial; N)
    return EdgeModelSystem(compiled, variables, obsvars, md)
end

# ---------------------------------------------------------------------------------------------
# The verbs
# ---------------------------------------------------------------------------------------------

"""
    edge_based(cm::ContactModel, net::ConfigurationNetwork, st::Strata; name = :edge_based_model, form = :expanded)
    edge_based(model, net::ConfigurationNetwork, st::Strata; kw...)

The edge-based model of `cm` on the configuration network `net` whose nodes carry the fixed attributes `st` (a
`Strata`: names and population fractions n_a), assigned independently of the network: the network
`unstructured(net, st)`. This is **heterogeneous susceptibility** (Miller & Volz 2013, §2.2.2): each susceptible
class of `cm` is labelled with its stratum (`SpeciesLabel(:S; stratum = :a)`, one per stratum), and every other
species is either class-specific (labelled with a stratum) or shared (unlabelled; the node's state no longer records
its class). For example two susceptibility classes that share I and R:

```julia
st  = strata([:lo, :hi]; sizes = [0.4, 0.6])
het = ContactModel(:sir_het; contacts = [Contact(:S_lo, :I, :I, :τ_lo), Contact(:S_hi, :I, :I, :τ_hi)],
                   transitions = [NodeTransition(:I, :R, :γ)],
                   labels = Dict(:S_lo => SpeciesLabel(:S; stratum = :lo), :S_hi => SpeciesLabel(:S; stratum = :hi)))
sys = edge_based(het, ConfigurationNetwork(PoissonDegree(5.0)), st)
sol = solve_epidemic(sys; p = Dict(:τ_lo => 0.05, :τ_hi => 0.3, :γ => 0.25), initial = SeedFraction(:I => 0.01),
                     tspan = (0.0, 60.0))
compartment(sys, sol, :S_lo)[end], compartment(sys, sol, :cumulative)[end]
```

NetworkOutbreaks simulates the same model with `simulate(het, unstructured(net, st); …)`. Coordinates (ψ is the degree
PGF of `net`; K classes give K edge coordinates θ, against K² for the multitype lift):

- `θ_<a>`: the probability that an edge into a class-a test node has not transmitted; `ξ_<s>`, the exit survival
  factor of a susceptible class with exits;
- `φ_<Y>_<a>`: the same edge, with its partner in the species Y (e.g. `φ_I_lo`, `φ_R_hi`);
- `pop_<Y>`: the fraction of **all** nodes in Y (removals `X → ∅` go to `removed`, or `removed_<a>` for a
  class-specific X, design §J.2); `cumulative`, the fraction ever infected (§J.8);

with S_a = n_a q_a ξ_a ψ(θ_a). Every reaction contributes its terms (design §D.4, with the recipient's class), so
branching, several infectors, exits (vaccination of one class) and removals are lifted exactly; a node may enter only
species of its own class or shared species (an `ArgumentError` otherwise). The system is the quotient of the
multitype lift of the implicitly stratified model on `unstructured(net, st)` (θ_a = Σ_b n_b θ_{b→a}, M10), and
with one class, or with the same rates in every class and proportional seeds, the untyped configuration lift.

Seeding (`solve_epidemic(sys; initial)`, [`default_initial_conditions`](@ref)) follows NetworkOutbreaks on the typed
graph: fractions are of all nodes (design §J.6); a class-specific compartment is seeded on its class, a shared one
uniformly among the nodes still free, and every other node of class a starts in its susceptible class (without
`initial`, the unique entry state is seeded with `ε = 10⁻³`, uniformly). The fraction of class-a nodes initially
susceptible is the parameter `q_<s>`, set from `initial`. Observables: each susceptible class `s` (its node-S) and
`φ_<s>` (the partner of an edge is susceptible of that class), the totals `:S` (when free), `:I` and `:infectious`,
and `edge_hazard_<a>` (θ̇_a = −edge_hazard_<a>). `basic_reproduction_number`, `next_generation_matrix` and
`early_growth_rate` linearise the lifted field (R₀ = κ_ex Σ_a n_a T_a for SIR with a shared I); `final_size(sys;
initial, method = :ode)` integrates it. Only `form = :expanded` exists, and rates must be per contact (`PerContact`),
as for every stratified model.

A model with several susceptible classes on a plain `ConfigurationNetwork` (`edge_based(het, net)`) has no class
sizes and is refused (`:multiple_sus`); pass the strata here, or lift on the typed network:
`edge_based(het, unstructured(net, st))` (and `edge_based(sc)` for a scenario on it) is the same system (design §L.7).
"""
function edge_based(cm::ContactModel, net::ConfigurationNetwork, st::Strata; name::Symbol = :edge_based_model,
                    form::Symbol = :expanded)
    return _heterogeneous_lift(cm, unstructured(net, st); name, form)
end
edge_based(model, net::ConfigurationNetwork, st::Strata; kw...) = edge_based(contact_model(model), net, st; kw...)

"""
    lift_contributions(model, net::ConfigurationNetwork, st::Strata; susceptible = susceptible_species(model))
        -> LiftContributions

The per-reaction table of the heterogeneous-susceptibility lift [`edge_based`](@ref)`(model, net, st)` (closure
`:heterogeneous`): for every reaction, the terms it adds to the time derivatives of `θ_<a>`, `ξ_<s>`, `φ_<Y>_<a>` and
`pop_<Y>`. As for the other closures, the parts of a gluing compose with [`sum_contributions`](@ref) (H1) and are
pushed along species maps with `relabel(table, f)`; `symbolic_ode(table)` is the field, with the initially
susceptible fractions `q_<s>` as parameters. A part need not have a susceptible class (a transition-only part is
lifted with the φ and pop coordinates of its species).
"""
function lift_contributions(cm::ContactModel, net::ConfigurationNetwork, st::Strata;
                            susceptible = susceptible_species(cm))
    Σ = susceptible isa Symbol ? [susceptible] : collect(Symbol, susceptible)
    unet = unstructured(net, st)
    context = "lift_contributions(:$(cm.name), $(nameof(typeof(net))), $(st))"
    lm = _lift_model(cm, unet, Σ; context)
    return _contributions(_heterogeneous_closure(unet, lm), lm, unet)
end
lift_contributions(model, net::ConfigurationNetwork, st::Strata; kw...) =
    lift_contributions(contact_model(model), net, st; kw...)

# ---------------------------------------------------------------------------------------------
# Threshold quantities
# ---------------------------------------------------------------------------------------------

# The field is linear in the initially susceptible fractions q_<s> (every gain of a contact carries n_a q_a ξ_a), so
# the linearisation at the disease-free state (θ = ξ = q = 1, every φ and pop 0) splits as J(q = 1) = F − V with
# V = −J(q = 0), exactly as for the other linearisable closures: analysis.jl lists :heterogeneous in
# `_LINEARISABLE_CLOSURES`, so `next_generation_matrix`, `basic_reproduction_number` (symbolic for up to two entry
# coordinates) and `early_growth_rate` of these systems come from `_eb_linearisation`. There is no single per-edge
# transmissibility (it depends on the recipient's class), so `transmissibility(sys)` is an ArgumentError, and
# `final_size(sys; initial)` integrates the ODE (NetworkEpiCore's fixed point assigns every species to a node type).
