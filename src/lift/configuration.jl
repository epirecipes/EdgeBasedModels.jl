# Owner: WP17 (DESIGN_NetworkEpiCore.md §A.3, §C.3, §D.4, §D.5 M9; work package in §G.2).
#
# The ConfigurationNetwork closure of the per-reaction assembler (lift/assembler.jl): any degree
# distribution ψ (every NetworkEpiCore family, a legacy DegreePGF, symbolic parameters), the four
# factors
#
#     node-S      S   = qξψ(θ)                  edge-S      φ_S = qξψ'(θ)/ψ'(1)
#     node-entry  qξψ'(θ)                       edge-entry  qξψ''(θ)/ψ'(1)   (pre-cancelled)
#
# and the method `edge_based(cm::ContactModel, net::ConfigurationNetwork; name, form)`, which takes
# over from the legacy fallback of lift/edge_based.jl by dispatch (design §G.1). `form = :compact`
# is Miller's two-equation form of SIR-shaped models (M9: the invariant set W = {τφ_R + γθ = γ}
# of the expanded form, on which the projection to (θ, R) is a conjugacy).

# ---------------------------------------------------------------------------------------------
# The closure
# ---------------------------------------------------------------------------------------------

struct _ConfigurationClosure <: _EdgeClosure
    degrees::DegreeDistribution
    s::Union{Symbol,Nothing}          # the susceptible species (nothing: a part without one)
    info::Vector{_Coordinate}
    θ::Any
    ξ::Any
    q::Any
    φ::Dict{Symbol,Any}
    pop::Dict{Symbol,Any}
    ψ::Any                            # ψ(θ), ψ'(θ), ψ''(θ) and the mean degree ψ'(1)
    ψ1::Any
    ψ2::Any
    k̄::Any
end

_closure_kind(::_ConfigurationClosure) = :configuration
_coordinates(cl::_ConfigurationClosure) = cl.info
_seed_factors(cl::_ConfigurationClosure) = cl.s === nothing ? Pair{Symbol,Any}[] : [cl.s => cl.q]
_type_of(::_ConfigurationClosure, ::Symbol) = :all
_type_size(::_ConfigurationClosure, ::Symbol) = 1.0
_seed_background(cl::_ConfigurationClosure, ::_LiftModel) = cl.s
_network_terms(cl::_ConfigurationClosure) = cl.s === nothing ? Any[] : Any[cl.ψ, cl.ψ1, cl.ψ2, cl.k̄]

# Coordinate names on untyped networks (configuration and well-mixed): θ, ξ, φ_X, pop_X; the
# initially susceptible fraction is the parameter q_<s>.
_untyped_name(role::Symbol, X::Symbol) =
    role === :θ ? :θ : role === :ξ ? :ξ : role === :φ ? Symbol(:φ_, X) : Symbol(:pop_, X)

function _untyped_coordinates(lm::_LiftModel, s; edges::Bool = true)
    info = _Coordinate[]
    all = (:all, :all)
    if s !== nothing
        push!(info, _Coordinate(:θ, _state(:θ), :θ, s, all))
        push!(info, _Coordinate(:ξ, _state(:ξ), :ξ, s, all))
    end
    for role in (edges ? (:φ, :pop) : (:pop,)), X in lm.nodes
        name = _untyped_name(role, X)
        push!(info, _Coordinate(name, _state(name), role, X, all))
    end
    return info
end

function _single_susceptible(lm::_LiftModel)
    isempty(lm.Σ) && return nothing
    length(lm.Σ) == 1 || throw(ArgumentError(
        "$(lm.context): an untyped network has one node type, so the model may have one " *
        "susceptible class; it has $(join(lm.Σ, ", ")) (use stratify(model, st) on a " *
        "MultitypeNetwork for strata)"))
    return only(lm.Σ)
end

function _edge_closure(net::ConfigurationNetwork, lm::_LiftModel)
    s = _single_susceptible(lm)
    info = _untyped_coordinates(lm, s)
    get(name) = (k = findfirst(x -> x.name === name, info); k === nothing ? nothing : info[k].var)
    φ = Dict{Symbol,Any}(X => get(Symbol(:φ_, X)) for X in lm.nodes)
    pop = Dict{Symbol,Any}(X => get(Symbol(:pop_, X)) for X in lm.nodes)
    d = net.degrees
    if s === nothing
        return _ConfigurationClosure(d, s, info, nothing, nothing, nothing, φ, pop, nothing, nothing,
                                     nothing, nothing)
    end
    θ = get(:θ)
    return _ConfigurationClosure(d, s, info, θ, get(:ξ), _param(Symbol(:q_, s)), φ, pop,
                                 pgf(d, θ), pgf_derivative(d, θ, 1), pgf_derivative(d, θ, 2),
                                 mean_degree(d))
end

# The four factors (and their κ → 0 limits where the mean degree vanishes).
_node_S(cl::_ConfigurationClosure) = cl.q * cl.ξ * cl.ψ
_edge_S(cl::_ConfigurationClosure) = _ratio(cl.q * cl.ξ * cl.ψ1, cl.k̄, cl.q * cl.ξ * cl.ψ)
_node_entry(cl::_ConfigurationClosure) = cl.q * cl.ξ * cl.ψ1
_edge_entry(cl::_ConfigurationClosure) = _ratio(cl.q * cl.ξ * cl.ψ2, cl.k̄, cl.q * cl.ξ * cl.ψ1)

function _contact_terms(cl::_ConfigurationClosure, c::Contact, τ)
    h = τ * cl.φ[c.infector]
    flux = h * _node_entry(cl)
    terms = Pair{Symbol,Any}[:θ => -h, Symbol(:φ_, c.infector) => -h,
                             Symbol(:φ_, c.product) => h * _edge_entry(cl),
                             Symbol(:pop_, c.product) => flux]
    return terms, flux
end

function _exit_terms(cl::_ConfigurationClosure, t::NodeTransition, to::Symbol, ν)
    flux = ν * _node_S(cl)
    terms = Pair{Symbol,Any}[:ξ => -ν * cl.ξ, Symbol(:φ_, to) => ν * _edge_S(cl),
                             Symbol(:pop_, to) => flux]
    return terms, flux
end

function _transition_terms(cl::_ConfigurationClosure, t::NodeTransition, to::Symbol, a)
    X = t.from
    flux = a * cl.pop[X]
    terms = Pair{Symbol,Any}[Symbol(:φ_, X) => -a * cl.φ[X], Symbol(:φ_, to) => a * cl.φ[X],
                             Symbol(:pop_, X) => -flux, Symbol(:pop_, to) => flux]
    return terms, flux
end

# Observables of an untyped lift: the node-S (`:S`, and the susceptible species' own name), the
# legacy `:I` and `:infectious` (the fraction in the infector states), and for configuration
# networks the edge-S `:φ_S`, the edge hazard Σ_r τ_r φ_{J_r} (so θ̇ = −edge_hazard) and the legacy
# excess hazard edge_hazard·ψ''(θ)/ψ'(θ) (an observable only, never simplified: E27), the rate at
# which φ_S decays apart from the exits. Where the mean degree vanishes it is the κ → 0 limit of
# E11 that φ_S itself takes (φ_S = qξψ(θ), so edge_hazard·ψ'(θ)/ψ(θ)), not 0/0; that is 0, since
# ψ ≡ 1 on an edgeless network.
function _untyped_common_observables(cl, lm::_LiftModel, S)
    s = cl.s
    obs = Pair{Symbol,Any}[s => S]
    _alias_free(lm, :S) && s !== :S && push!(obs, :S => S)
    infectious = _sum_terms(Any[cl.pop[J] for J in lm.infectors])
    push!(obs, :I => infectious, :infectious => infectious)
    return obs
end

# May an alias name (:S, :φ_S) be used? Not when a node species would own it.
_alias_free(lm::_LiftModel, name::Symbol) =
    !(name in lm.nodes) && !(name === :φ_S && :S in lm.nodes)

function _closure_observables(cl::_ConfigurationClosure, lm::_LiftModel, ::LiftContributions)
    obs = _untyped_common_observables(cl, lm, _node_S(cl))
    φS = _edge_S(cl)
    push!(obs, Symbol(:φ_, cl.s) => φS)
    cl.s !== :S && _alias_free(lm, :φ_S) && push!(obs, :φ_S => φS)
    hazard = _sum_terms(Any[τ * cl.φ[c.infector] for (c, τ) in zip(contacts(lm.cm), lm.contact_rates)])
    excess = _unless_zero(_ -> hazard * cl.ψ2 / cl.ψ1, cl.k̄, hazard * cl.ψ1 / cl.ψ)
    push!(obs, :edge_hazard => hazard, :excess_hazard => excess)
    return obs
end

# θ(0) = ξ(0) = 1 and φ_X(0) = pop_X(0) = ρ_X (design §E.2); the sinks start empty.
function _initial_values(cl::_ConfigurationClosure, lm::_LiftModel, ρ)
    v = Dict{Symbol,Float64}(:θ => 1.0, :ξ => 1.0)
    for X in lm.nodes
        v[Symbol(:φ_, X)] = get(ρ, X, 0.0)
        v[Symbol(:pop_, X)] = get(ρ, X, 0.0)
    end
    return v
end

# q_<s> = 1 − Σ_X seed_X.
_seed_expressions(cl::_ConfigurationClosure, lm::_LiftModel, seeds) =
    Dict{Any,Any}(cl.q => 1 - _sum_terms(Any[seeds[X] for X in lm.nodes if haskey(seeds, X)]))

function _relabel_coordinate(::Union{Val{:configuration},Val{:well_mixed}}, x::_Coordinate, m)
    X = m(x.species)
    x.role in (:θ, :ξ) && return _Coordinate(x.name, x.var, x.role, X, x.types)
    name = _untyped_name(x.role, X)
    return _Coordinate(name, _state(name), x.role, X, x.types)
end

# ---------------------------------------------------------------------------------------------
# edge_based on a configuration network
# ---------------------------------------------------------------------------------------------

"""
    edge_based(cm::ContactModel, net::ConfigurationNetwork; name = :edge_based_model, form = :expanded)
    edge_based(cm::ContactModel, net::WellMixed; name, form = :expanded)
    edge_based(cm::ContactModel, net::MultitypeNetwork; name, form = :expanded)

The per-reaction edge-based lift of a T_EB model (design §D.4): every contact, transition, exit
and removal contributes its own terms (see [`lift_contributions`](@ref)), so branching at
infection, several infectors, several strains, exits out of the susceptible class (vaccination,
with the survival factor ξ) and removals `X → ∅` (to the absorbing sink `:removed`, design §J.2)
are all lifted exactly. `require_admissible(cm, :edge_based; network = net)` is checked first
(SIS and SIRS raise the `AdmissibilityError` of design §B.7).

Coordinates, on a `ConfigurationNetwork(d)` with degree PGF ψ (any family, including a legacy
`DegreePGF`):

- `θ`, the probability that an edge has not transmitted to a test node; `ξ`, the exit survival
  factor (present only when the model has exits);
- `φ_X` and `pop_X` for every non-susceptible species X (and the sink): edges to a partner in X
  that have not transmitted, and the fraction of nodes in X;
- `cumulative`, the fraction ever infected, seeds included (design §E.2, §J.8: an infection is a
  contact whose product can reach an infector, as in NetworkOutbreaks' `final_size`);

with `S = qξψ(θ)`, `φ_S = qξψ'(θ)/ψ'(1)` and q = 1 − Σ_X seed_X. The seed fraction of X is the
parameter `seed_X` (design §A.3), set by [`default_initial_conditions`](@ref)`(sys; initial)` with
θ(0) = ξ(0) = 1 and φ_X(0) = pop_X(0) = ρ_X; any node species may be seeded, and the default is the
unique entry state (`default_seed`). Observables: the susceptible species' name `s` and `φ_<s>`
(also under the names `:S` and `:φ_S` unless another species is called S, E26), `:I` and
`:infectious` (the fraction in infector states: pop_A + pop_I for SEAIR), `:edge_hazard`
(θ̇ = −edge_hazard) and `:excess_hazard` = edge_hazard·ψ''(θ)/ψ'(θ) (the rate at which φ_S decays
apart from the exits; 0 on a network of mean degree 0). The variable `:R` is `pop_R` when a
species is called R, and otherwise the population of the unique recovered class (if there is
one).

`form = :compact` gives Miller's two-equation form of an SIR-shaped model (one contact
`s + I → 2I`, one transition `I → R` or `I → ∅`, no exits; seeds in I only): states `θ` and
`pop_R` with θ̇ = −τθ + τφ_s + γ(1 − θ) and Ṙ = γ(1 − S − R), exact on the invariant set of the
expanded form (M9). Its observables are those above without the hazards, plus `pop_I` = 1 − S − R
(also a variable, so that every species has a population), `:cumulative` = 1 − S and the legacy
`ψ_θ` = ψ(θ). Its `metadata[:contributions]` is the per-reaction table of the expanded form, so
`symbolic_ode(metadata[:contributions])` is the expanded field, while `symbolic_ode(sys)` is the
two-equation field (the reduction on that invariant set). `WellMixed(κ)` and `MultitypeNetwork`
descriptors have only the expanded form.

`symbolic_ode(sys)` returns the uncompiled vector field (without the accumulator), and
`metadata[:contributions]` the per-reaction table of the expanded field. The mean degree ψ'(1) is
the only divisor in the field, so
high-degree polynomial PGFs are safe (E23, E27), and a mean degree that is 0 (numeric, or a
symbolic one at solve time) selects the κ → 0 limit of E11 and E32 in the field and in the
observables (φ_S = qξψ(θ)), rather than 0/0.

```julia
sys = edge_based(sirv_model(; τ = 1/6, γ = 1/4, ν = 0.02), ConfigurationNetwork(PoissonDegree(5)))
sol = solve_epidemic(sys; initial = SeedFraction(:I => 0.01), tspan = (0.0, 60.0))
compartment(sys, sol, :pop_V)[end], compartment(sys, sol, :cumulative)[end]
```
"""
function edge_based(cm::ContactModel, net::ConfigurationNetwork; name::Symbol = :edge_based_model,
                    form::Symbol = :expanded)
    form in (:expanded, :compact) ||
        throw(ArgumentError("form must be :compact or :expanded, got :$form"))
    require_admissible(cm, :edge_based; network = net)
    context = _lift_context(cm, net)
    form === :compact && return _assemble_compact(cm, net; name, context)
    return _assemble(cm, net; name, context)
end

# ---------------------------------------------------------------------------------------------
# The compact form (M9)
# ---------------------------------------------------------------------------------------------

# The SIR shape of a model, or an ArgumentError: one contact s + I → 2I, one transition I → R
# (R may be the removal sink) and nothing else.
function _compact_shape(lm::_LiftModel)
    cm = lm.cm
    fail() = throw(ArgumentError(
        "$(lm.context): form = :compact supports SIR-shaped models only (Miller's two-equation form, " *
        "M9): one contact s + I → 2I, one transition I → R or I → ∅, no exits and no other " *
        "species; use form = :expanded for this model"))
    cs = contacts(cm)
    ts = node_transitions(cm)
    (length(cs) == 1 && length(ts) == 1) || fail()
    c, t = only(cs), only(ts)
    I = c.infector
    (c.product === I && t.from === I && only(lm.transition_types) !== :exit) || fail()
    R = only(lm.transition_targets)
    Set(lm.nodes) == Set([I, R]) || fail()
    return c.recipient, I, R, only(lm.contact_rates), only(lm.transition_rates)
end

function _assemble_compact(cm::ContactModel, net::ConfigurationNetwork; name::Symbol,
                           context::AbstractString)
    lm = _lift_model(cm, net, susceptible_species(cm); context)
    s, I, R, τ, γ = _compact_shape(lm)
    cl = _edge_closure(net, lm)
    θ = cl.θ
    popR = cl.pop[R]
    q = cl.q
    # with ξ ≡ 1 (no exits)
    ψ, ψ1, k̄ = cl.ψ, cl.ψ1, cl.k̄
    S = q * ψ
    φS = _ratio(q * ψ1, k̄, q * ψ)
    fθ = -τ * θ + τ * φS + γ * (1 - θ)
    fR = γ * (1 - S - popR)
    raw = SymbolicODE(Symbol(name, :_edge_based_compact); states = Any[θ, popR], rhs = Any[fθ, fR],
                      parameters = :infer,
                      domain = Pair{Any,Tuple{Float64,Float64}}[θ => (0.05, 1.0)])
    seed = _param(Symbol(:seed_, I))
    qsub = Dict{Any,Any}(q => 1 - seed)
    popname, popIname = Symbol(:pop_, R), Symbol(:pop_, I)
    popI = 1 - S - popR
    # The species names come first, and the first of two equal names wins (as in the expanded
    # form); the aliases :S and :φ_S are the susceptible's only when no other species owns S (E26).
    obs = Pair{Symbol,Any}[s => S]
    s !== :S && _alias_free(lm, :S) && push!(obs, :S => S)
    push!(obs, popIname => popI, :I => popI, :infectious => popI, :cumulative => 1 - S,
          Symbol(:φ_, s) => φS)
    s !== :S && _alias_free(lm, :φ_S) && push!(obs, :φ_S => φS)
    push!(obs, :ψ_θ => ψ)                                          # the legacy observable ψ(θ)
    obsnames = unique!(Symbol[first(o) for o in obs])
    generated = vcat(Symbol[:θ, popname], obsnames, Symbol[_symname(q), _symname(seed)])
    _check_generated_names(lm, generated, Any[θ, popR, q], vcat(Any[fθ, fR], Any[last(o) for o in obs]),
                           _network_terms(cl))
    sub(e) = Symbolics.substitute(e, qsub)
    D = D_nounits
    eqs = Equation[D(θ) ~ sub(fθ), D(popR) ~ sub(fR)]
    obsvars = Dict{Symbol,Any}()
    for (k, e) in obs
        haskey(obsvars, k) && continue
        v = _state(k)
        obsvars[k] = v
        push!(eqs, v ~ sub(e))
    end
    compiled = mtkcompile(System(eqs, t_nounits; name))
    # pop_<I> is also a variable, so that every species has its population under pop_<X> (the
    # name model_curves looks up), whatever the infector is called
    variables = Dict{Symbol,Any}(:θ => θ, popname => popR, popIname => obsvars[popIname])
    _add_recovered_alias!(variables, lm)
    info = _Coordinate[_Coordinate(:θ, θ, :θ, s, (:all, :all)),
                       _Coordinate(popname, popR, :pop, R, (:all, :all))]
    table = _contributions(cl, lm, net)
    seeds = Dict{Symbol,Any}(I => seed)
    md = _assembled_metadata(cm, net, lm, cl, table, raw, seeds, qsub, Symbol[I]; form = :compact)
    md[:coords] = Dict{Symbol,Any}(:θ => θ, popname => popR)
    md[:ic] = function (initial; N = nothing)
        ρ, given = _seeds(lm, s, initial; N)
        _check_susceptible_seeds(cl, lm, ρ, given)
        get(ρ, R, 0.0) == 0 || throw(ArgumentError(
            "default_initial_conditions: the compact form seeds only $(I) (its invariant set has " *
            "φ_$(R)(0) = 0); use form = :expanded to seed $(R)"))
        return Dict{Any,Float64}(θ => 1.0, popR => 0.0, seed => ρ[I])
    end
    return EdgeModelSystem(compiled, variables, obsvars, md)
end
