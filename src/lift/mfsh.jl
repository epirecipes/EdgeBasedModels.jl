# Owner: WP36c (DESIGN_NetworkEpiCore.md §C.3, §D.5 Λ3, §J.2, §K WP36c).
#
# The mean-field social heterogeneity (MFSH) closure of the per-reaction assembler
# (lift/assembler.jl): Miller, Slim & Volz (2012), Part II §3.2.2 (papers/1106.6319v1.md:153-161),
# the actual-degree formulation, for every T_EB model (SIR, SEIR, SEAIR with branching and two
# infectors, several strains, exits such as vaccination, removals to the sink `:removed`, §J.2).
#
# The network is `MFSHNetwork(d)`: every node has k ~ d stubs, and at every instant each stub is
# joined to a stub drawn at random from all the stubs of the population, so successive contacts are
# independent (fleeting contacts with heterogeneous activity). A stub of a test node therefore
# meets a partner in X with probability π_X, the fraction of all stubs that belong to X nodes, and
# θ, the probability that a stub has not transmitted to the test node, obeys θ̇ = −θ Σ_r τ_r π_{J_r}.
# There is no partnership memory: the probability that a stub has not transmitted and joins an X
# node is θπ_X (the φ_X of the static and dynamic closures). The coordinates are θ, ξ (with exits)
# and, for every non-susceptible species X (and the removal sink), π_X and pop_X:
#
#     contact  r = (s + J → X + J, τ):  θ̇ −= τθπ_J;  π̇_X += τθπ_J·qξ(ψ'(θ) + θψ''(θ))/ψ'(1);
#                                        pop_X' += τθπ_J·qξψ'(θ)
#     transition (X → Y | ∅, a):         π and pop of X move to Y at rate a
#     exit     (s → Y, ν):               ξ̇ −= νξ;  π̇_Y += νπ_S;  pop_Y' += νS
#
# with S = qξψ(θ), π_S = qξθψ'(θ)/ψ'(1), q = 1 − Σ_X seed_X and θ(0) = ξ(0) = 1,
# π_X(0) = pop_X(0) = ρ_X (uniform seeds). A contact moves the stubs of the converted nodes: a node
# of degree k leaves S at rate kτπ_J, so the stub flux carries the weight k²P(k)θᵏ, i.e.
# θ(ψ'(θ) + θψ''(θ)). Conservation: π_S + Σπ_X = 1 and S + Σpop_X = 1.
#
# This is the η → ∞ slow manifold of the neighbour-exchange closure of lift/dynamic.jl (χ = θ²,
# φ_X = θπ_X), design §D.5 Λ3, and on a κ-regular degree distribution it is the well-mixed lift
# WellMixed(κ) (M1) under θ_WM = 1 + ln θ, π_X = pop_X (MSV §3.3.1). For SIR-shaped models the
# invariant τπ_R + γ ln θ = 0 (seeds in I only) reduces it to MSV's single equation
# θ̇ = −τθ + τθ·π_S − γθ ln θ, Ṙ = γ(1 − S − R): `form = :compact`.

# ---------------------------------------------------------------------------------------------
# The closure
# ---------------------------------------------------------------------------------------------

struct _MFSHClosure <: _EdgeClosure
    degrees::DegreeDistribution
    s::Union{Symbol,Nothing}          # the susceptible species (nothing: a part without one)
    info::Vector{_Coordinate}
    θ::Any
    ξ::Any
    q::Any
    stub::Dict{Symbol,Any}           # π_X, the stub fractions
    pop::Dict{Symbol,Any}
    ψ::Any                            # ψ(θ), ψ'(θ), ψ''(θ) and the mean degree ψ'(1)
    ψ1::Any
    ψ2::Any
    k̄::Any
end

_closure_kind(::_MFSHClosure) = :mfsh
_coordinates(cl::_MFSHClosure) = cl.info
_seed_factors(cl::_MFSHClosure) = cl.s === nothing ? Pair{Symbol,Any}[] : [cl.s => cl.q]
_type_of(::_MFSHClosure, ::Symbol) = :all
_type_size(::_MFSHClosure, ::Symbol) = 1.0
_seed_background(cl::_MFSHClosure, ::_LiftModel) = cl.s
_network_terms(cl::_MFSHClosure) = cl.s === nothing ? Any[] : Any[cl.ψ, cl.ψ1, cl.ψ2, cl.k̄]

# Coordinate names: θ, ξ, π_X (stub fractions) and pop_X.
_mfsh_name(role::Symbol, X::Symbol) =
    role === :θ ? :θ : role === :ξ ? :ξ : role === :π ? Symbol(:π_, X) : Symbol(:pop_, X)

function _edge_closure(net::MFSHNetwork, lm::_LiftModel)
    s = _single_susceptible(lm)
    all = (:all, :all)
    info = _Coordinate[]
    if s !== nothing
        push!(info, _Coordinate(:θ, _state(:θ), :θ, s, all))
        push!(info, _Coordinate(:ξ, _state(:ξ), :ξ, s, all))
    end
    for role in (:π, :pop), X in lm.nodes
        name = _mfsh_name(role, X)
        push!(info, _Coordinate(name, _state(name), role, X, all))
    end
    get(name) = (k = findfirst(x -> x.name === name, info); k === nothing ? nothing : info[k].var)
    stub = Dict{Symbol,Any}(X => get(_mfsh_name(:π, X)) for X in lm.nodes)
    pop = Dict{Symbol,Any}(X => get(_mfsh_name(:pop, X)) for X in lm.nodes)
    d = net.degrees
    if s === nothing
        return _MFSHClosure(d, s, info, nothing, nothing, nothing, stub, pop, nothing, nothing,
                            nothing, nothing)
    end
    θ = get(:θ)
    return _MFSHClosure(d, s, info, θ, get(:ξ), _param(Symbol(:q_, s)), stub, pop, pgf(d, θ),
                        pgf_derivative(d, θ, 1), pgf_derivative(d, θ, 2), mean_degree(d))
end

# The factors, with the κ → 0 limits of E11/E32 where the mean degree vanishes (ψ^{(n+1)}/ψ'(1)
# becomes ψ^{(n)}, as in lift/configuration.jl and lift/dynamic.jl, so that dπ_S/dθ equals the
# stub entry factor in the limit too).
_node_S(cl::_MFSHClosure) = cl.q * cl.ξ * cl.ψ
_node_entry(cl::_MFSHClosure) = cl.q * cl.ξ * cl.ψ1
_stub_S(cl::_MFSHClosure) = _ratio(cl.q * cl.ξ * cl.θ * cl.ψ1, cl.k̄, cl.q * cl.ξ * cl.θ * cl.ψ)
_stub_entry(cl::_MFSHClosure) =
    _ratio(cl.q * cl.ξ * (cl.ψ1 + cl.θ * cl.ψ2), cl.k̄, cl.q * cl.ξ * (cl.ψ + cl.θ * cl.ψ1))

function _contact_terms(cl::_MFSHClosure, c::Contact, τ)
    h = τ * cl.θ * cl.stub[c.infector]
    flux = h * _node_entry(cl)
    terms = Pair{Symbol,Any}[:θ => -h, _mfsh_name(:π, c.product) => h * _stub_entry(cl),
                             _mfsh_name(:pop, c.product) => flux]
    return terms, flux
end

function _exit_terms(cl::_MFSHClosure, t::NodeTransition, to::Symbol, ν)
    flux = ν * _node_S(cl)
    terms = Pair{Symbol,Any}[:ξ => -ν * cl.ξ, _mfsh_name(:π, to) => ν * _stub_S(cl),
                             _mfsh_name(:pop, to) => flux]
    return terms, flux
end

function _transition_terms(cl::_MFSHClosure, t::NodeTransition, to::Symbol, a)
    X = t.from
    flux = a * cl.pop[X]
    terms = Pair{Symbol,Any}[_mfsh_name(:π, X) => -a * cl.stub[X], _mfsh_name(:π, to) => a * cl.stub[X],
                             _mfsh_name(:pop, X) => -flux, _mfsh_name(:pop, to) => flux]
    return terms, flux
end

# The hazards of the contacts: Σ_r τ_r π_{J_r}, the infection hazard of one stub (a susceptible node
# with k stubs is infected at rate k times it), and Σ_r τ_r θπ_{J_r} = −θ̇.
_mfsh_stub_hazard(cl::_MFSHClosure, lm::_LiftModel) =
    _sum_terms(Any[τ * cl.stub[c.infector] for (c, τ) in zip(contacts(lm.cm), lm.contact_rates)])

# Observables: the node-S under the susceptible species' name and `:S`, `:I`, `:infectious` (the
# common observables of untyped lifts), the stub-S `π_<s>` (also `:π_S`), the edge-S
# `φ_<s>` = θπ_S (also `:φ_S`: a stub has not transmitted and joins a susceptible node, the φ_S of
# the static and dynamic lifts), `:edge_hazard` = −θ̇ and `:stub_hazard`.
function _closure_observables(cl::_MFSHClosure, lm::_LiftModel, ::LiftContributions)
    obs = _untyped_common_observables(cl, lm, _node_S(cl))
    πS = _stub_S(cl)
    push!(obs, _mfsh_name(:π, cl.s) => πS)
    (cl.s !== :S && !(:S in lm.nodes) && !(:π_S in lm.nodes)) && push!(obs, :π_S => πS)
    push!(obs, Symbol(:φ_, cl.s) => cl.θ * πS)
    cl.s !== :S && _alias_free(lm, :φ_S) && push!(obs, :φ_S => cl.θ * πS)
    λ = _mfsh_stub_hazard(cl, lm)
    push!(obs, :edge_hazard => cl.θ * λ, :stub_hazard => λ)
    return obs
end

# θ(0) = ξ(0) = 1 and π_X(0) = pop_X(0) = ρ_X: the seeds are uniform, so the stub-weighted and
# node-weighted fractions agree at t = 0; the sinks start empty.
function _initial_values(cl::_MFSHClosure, lm::_LiftModel, ρ)
    v = Dict{Symbol,Float64}(:θ => 1.0, :ξ => 1.0)
    for X in lm.nodes
        r = get(ρ, X, 0.0)
        v[_mfsh_name(:π, X)] = r
        v[_mfsh_name(:pop, X)] = r
    end
    return v
end

# q_<s> = 1 − Σ_X seed_X.
_seed_expressions(cl::_MFSHClosure, lm::_LiftModel, seeds) =
    Dict{Any,Any}(cl.q => 1 - _sum_terms(Any[seeds[X] for X in lm.nodes if haskey(seeds, X)]))

function _relabel_coordinate(::Val{:mfsh}, x::_Coordinate, m)
    X = m(x.species)
    x.role in (:θ, :ξ) && return _Coordinate(x.name, x.var, x.role, X, x.types)
    name = _mfsh_name(x.role, X)
    return _Coordinate(name, _state(name), x.role, X, x.types)
end

# ---------------------------------------------------------------------------------------------
# edge_based on an MFSH network
# ---------------------------------------------------------------------------------------------

"""
    edge_based(cm::ContactModel, net::MFSHNetwork; name = :edge_based_model, form = :expanded)

The edge-based lift of mean-field social heterogeneity (MFSH; Miller, Slim & Volz 2012, Part II
§3.2.2, the actual-degree formulation): every node has k stubs, k drawn from the degree
distribution `net.degrees` with PGF ψ, and at every instant each stub is joined to a stub drawn at
random from the whole population, so contacts are fleeting and a stub meets a partner in X with
probability π_X, the fraction of all stubs that belong to X nodes. A susceptible node with k stubs
is infected at rate k Σ_r τ_r π_{J_r}. Every T_EB model is lifted reaction by reaction (SIR, SEIR,
SEAIR with branching and two infectors, several strains, exits such as vaccination with the
survival factor ξ, removals `X → ∅` to the sink `:removed`, design §J.2); SIS and SIRS raise the
`AdmissibilityError` of `require_admissible`.

Coordinates (`form = :expanded`, the default): `θ` (the probability that a stub has not
transmitted to its node), `ξ` (with exits), and `π_X` and `pop_X` for every non-susceptible
species X (and the sink), with `cumulative` (the fraction ever infected, seeds included, design
§J.8):

    contact s + J → X + J (τ):  θ̇ −= τθπ_J,  π̇_X += τθπ_J·qξ(ψ'(θ) + θψ''(θ))/ψ'(1),
                                pop_X' += τθπ_J·qξψ'(θ)
    transition X → Y (a):       π_X and pop_X move to Y at rate a
    exit s → Y (ν):             ξ̇ −= νξ,  π̇_Y += νπ_S,  pop_Y' += νS

with S = qξψ(θ), π_S = qξθψ'(θ)/ψ'(1), q = 1 − Σ_X seed_X, θ(0) = ξ(0) = 1 and
π_X(0) = pop_X(0) = ρ_X. Conservation: π_S + Σπ_X = 1 and S + Σpop_X = 1. Seeding,
[`default_initial_conditions`](@ref), the seed parameters `seed_X` and the observables `s`/`:S`,
`:I` and `:infectious` are those of the `ConfigurationNetwork` method; in addition `π_<s>` (also
`:π_S`) is the stub-S, `φ_<s>` (also `:φ_S`) = θπ_S the probability that a stub has not
transmitted and joins a susceptible node, `:edge_hazard` = −θ̇ and `:stub_hazard` =
Σ_r τ_r π_{J_r}, the infection hazard per stub.

`form = :compact` is MSV's own equation for an SIR-shaped model (one contact `s + I → 2I`, one
transition `I → R` or `I → ∅`, no exits; seeds in I only): the states `θ` and `pop_R` with

    θ̇ = −τθ + τθ·π_S − γθ ln θ,   Ṙ = γ(1 − S − R),   S = qψ(θ),  π_S = qθψ'(θ)/ψ'(1),

exact on the invariant set τπ_R + γ ln θ = 0 of the expanded form (with q = 1 it is MSV Part II
§3.2.2 verbatim). Its observables are `s`/`:S`, `pop_I` = 1 − S − R (also a variable), `:I`,
`:infectious`, `:cumulative` = 1 − S and `π_<s>`/`:π_S`; `metadata[:contributions]` is the
per-reaction table of the expanded form and `symbolic_ode(sys)` the two-equation field.

Limits and relations (design §D.5):

- Λ3: `DynamicNetwork(ConfigurationNetwork(d), NeighbourExchange(η))` tends to `MFSHNetwork(d)`
  as η → ∞ (its field has the slow manifold χ = θ², φ_X = θπ_X); this is mass action only when d
  is regular.
- `MFSHNetwork(RegularDegree(κ))` is `WellMixed(κ)`: (θ_WM, ξ, pop) ↦ (e^{θ_WM − 1}, ξ, π = pop,
  pop) maps the well-mixed lift (M1) into this one.
- `basic_reproduction_number(sys)` is τ(κ_ex + 1)/γ for SIR (NetworkEpiCore's MFSH
  next-generation matrix), and `final_size(sys)` solves −ln θ = A + qB(1 − θψ'(θ)/ψ'(1)).

`lift_contributions(cm, net)` gives the per-reaction table. The mean degree ψ'(1) is the only
divisor of the expanded field (a mean degree of 0 selects the κ → 0 limit of verified issues E11
and E32, as for configuration networks).

```julia
sys = edge_based(sir_model(; τ = 1/12, γ = 1/4), MFSHNetwork(PoissonDegree(5)))
sol = solve_epidemic(sys; initial = SeedFraction(:I => 0.01), tspan = (0.0, 100.0))
compartment(sys, sol, :cumulative)[end]            # 0.6687; R₀ = 2 (mass action with R₀ = 2: 0.8002)
```
"""
function edge_based(cm::ContactModel, net::MFSHNetwork; name::Symbol = :edge_based_model,
                    form::Symbol = :expanded)
    form in (:expanded, :compact) ||
        throw(ArgumentError("form must be :compact or :expanded, got :$form"))
    require_admissible(cm, :edge_based; network = net)
    context = _lift_context(cm, net)
    form === :compact && return _assemble_mfsh_compact(cm, net; name, context)
    return _assemble(cm, net; name, context)
end

# ---------------------------------------------------------------------------------------------
# The compact form: MSV Part II §3.2.2
# ---------------------------------------------------------------------------------------------

function _assemble_mfsh_compact(cm::ContactModel, net::MFSHNetwork; name::Symbol,
                                context::AbstractString)
    lm = _lift_model(cm, net, susceptible_species(cm); context)
    s, I, R, τ, γ = _compact_shape(lm)
    cl = _edge_closure(net, lm)
    θ, popR, q = cl.θ, cl.pop[R], cl.q
    # with ξ ≡ 1 (no exits)
    S = q * cl.ψ
    πS = _ratio(q * θ * cl.ψ1, cl.k̄, q * θ * cl.ψ)
    fθ = -τ * θ + τ * θ * πS - γ * θ * log(θ)
    fR = γ * (1 - S - popR)
    raw = SymbolicODE(Symbol(name, :_edge_based_compact); states = Any[θ, popR], rhs = Any[fθ, fR],
                      parameters = :infer,
                      domain = Pair{Any,Tuple{Float64,Float64}}[θ => (0.05, 1.0)])
    seed = _param(Symbol(:seed_, I))
    qsub = Dict{Any,Any}(q => 1 - seed)
    popname, popIname = _mfsh_name(:pop, R), _mfsh_name(:pop, I)
    popI = 1 - S - popR
    # The species names come first, and the first of two equal names wins (as in the expanded
    # form); the aliases :S and :π_S are the susceptible's only when no other species owns them.
    obs = Pair{Symbol,Any}[s => S]
    s !== :S && _alias_free(lm, :S) && push!(obs, :S => S)
    push!(obs, popIname => popI, :I => popI, :infectious => popI, :cumulative => 1 - S,
          _mfsh_name(:π, s) => πS)
    (s !== :S && !(:S in lm.nodes) && !(:π_S in lm.nodes)) && push!(obs, :π_S => πS)
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
    table = _contributions(cl, lm, net)
    seeds = Dict{Symbol,Any}(I => seed)
    md = _assembled_metadata(cm, net, lm, cl, table, raw, seeds, qsub, Symbol[I]; form = :compact)
    md[:coords] = Dict{Symbol,Any}(:θ => θ, popname => popR)
    md[:ic] = function (initial; N = nothing)
        ρ, given = _seeds(lm, s, initial; N)
        _check_susceptible_seeds(cl, lm, ρ, given)
        get(ρ, R, 0.0) == 0 || throw(ArgumentError(
            "default_initial_conditions: the compact form seeds only $(I) (its invariant set has " *
            "π_$(R)(0) = 0); use form = :expanded to seed $(R)"))
        return Dict{Any,Float64}(θ => 1.0, popR => 0.0, seed => ρ[I])
    end
    return EdgeModelSystem(compiled, variables, obsvars, md)
end
