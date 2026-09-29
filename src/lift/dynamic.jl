# Owner: WP21 (DESIGN_NetworkEpiCore.md §A.3, §C.2, §C.3, §D.5 Λ3, §J.2; work package in §G.2).
#
# The dynamic fixed-degree (DFD, neighbour exchange) closure of the per-reaction assembler
# (lift/assembler.jl): Miller, Slim & Volz (2012), Part I §3.2 (papers/1106.6320v1.md:190-222) and
# Part II §3.2.3, with the swap target M_S = π_S = qξθψ'(θ)/ψ'(1) (verified issue E05; Volz 2008
# eq. 9) and the seed factor q = 1 − Σρ (E06), for every T_EB model (E07: SEIR, SEAIR, strains,
# exits and removals, not only SIR).
#
# The network is `DynamicNetwork(base, NeighbourExchange(η))`: every edge breaks at the per-edge
# rate η and its stubs rejoin other breaking stubs at random, so degrees never change. The
# probability φ_S that a stub of the test node has not transmitted and joins a susceptible node
# has no closed form, so it is written φ_S = χ·qξψ'(θ)/ψ'(1), where χ is the partnership memory:
# the probability that neither stub of the current partnership had transmitted before the
# partnership formed (E[θ(σ)²] over the formation time σ of the partnership, θ(0) = 1 for the
# initial ones). In these coordinates the contact and exit terms of φ_S cancel against those of
# qξψ'(θ)/ψ'(1), and the whole effect of the exchange on φ_S is χ̇ = η(θ² − χ): no division by
# ψ'(θ) (the pre-cancelled form of E23/E27), and χ ≡ 1 when η = 0, the static field. The
# coordinates are θ, ξ (with exits), χ, and for every non-susceptible species X (and the removal
# sink, §J.2) φ_X, π_X (the fraction of all stubs that belong to X nodes) and pop_X:
#
#     contact  r = (s + J → X + J, τ):  θ̇ −= τφ_J;  φ̇_J −= τφ_J;  φ̇_X += τφ_J·χqξψ''(θ)/ψ'(1)
#                                        π̇_X += τφ_J·qξ(ψ'(θ) + θψ''(θ))/ψ'(1);  pop_X' += τφ_J·qξψ'(θ)
#     transition (X → Y | ∅, a):         φ, π and pop of X move to Y at rate a
#     exit     (s → Y, ν):               ξ̇ −= νξ;  φ̇_Y += νφ_S;  π̇_Y += νπ_S;  pop_Y' += νS
#     neighbour exchange (η, once):      χ̇ = η(θ² − χ);  φ̇_X += η(θπ_X − φ_X) for every X
#
# with S = qξψ(θ), φ_S = χqξψ'(θ)/ψ'(1), π_S = qξθψ'(θ)/ψ'(1) and θ(0) = ξ(0) = χ(0) = 1,
# φ_X(0) = π_X(0) = pop_X(0) = ρ_X. Conservation: θ = φ_S + Σφ_X, π_S + Σπ_X = 1 and S + Σpop = 1.
# MSV's own variables are φ_S = χqξψ'(θ)/ψ'(1) and π_I = 1 − π_S − π_R, and their field is the
# restriction of this one to the invariant set of these identities (test/suites/dynamic.jl
# verifies the semiconjugacy symbolically). The exchange terms act once on every coordinate, not
# per reaction: they are the table's single row of type `:process`.

# ---------------------------------------------------------------------------------------------
# The closure
# ---------------------------------------------------------------------------------------------

struct _DynamicClosure <: _EdgeClosure
    degrees::DegreeDistribution
    s::Union{Symbol,Nothing}          # the susceptible species (nothing: a part without one)
    nodes::Vector{Symbol}             # the non-susceptible species and sinks (φ/π/pop coordinates)
    info::Vector{_Coordinate}
    θ::Any
    ξ::Any
    χ::Any
    q::Any
    φ::Dict{Symbol,Any}
    stub::Dict{Symbol,Any}           # π_X, the stub fractions
    pop::Dict{Symbol,Any}
    ψ::Any                            # ψ(θ), ψ'(θ), ψ''(θ) and the mean degree ψ'(1)
    ψ1::Any
    ψ2::Any
    k̄::Any
    η::Any                            # the per-edge exchange rate (a number or a parameter)
end

_closure_kind(::_DynamicClosure) = :dynamic
_coordinates(cl::_DynamicClosure) = cl.info
_seed_factors(cl::_DynamicClosure) = cl.s === nothing ? Pair{Symbol,Any}[] : [cl.s => cl.q]
_type_of(::_DynamicClosure, ::Symbol) = :all
_type_size(::_DynamicClosure, ::Symbol) = 1.0
_seed_background(cl::_DynamicClosure, ::_LiftModel) = cl.s
_network_terms(cl::_DynamicClosure) =
    cl.s === nothing ? Any[cl.η] : Any[cl.ψ, cl.ψ1, cl.ψ2, cl.k̄, cl.η]

_stub_name(X::Symbol) = Symbol(:π_, X)

function _edge_closure(net::DynamicNetwork{<:NeighbourExchange}, lm::_LiftModel)
    s = _single_susceptible(lm)
    all = (:all, :all)
    info = _Coordinate[]
    if s !== nothing
        push!(info, _Coordinate(:θ, _state(:θ), :θ, s, all))
        push!(info, _Coordinate(:ξ, _state(:ξ), :ξ, s, all))
        push!(info, _Coordinate(:χ, _state(:χ), :χ, s, all))
    end
    for (role, name) in ((:φ, X -> Symbol(:φ_, X)), (:π, _stub_name), (:pop, X -> Symbol(:pop_, X))),
        X in lm.nodes
        push!(info, _Coordinate(name(X), _state(name(X)), role, X, all))
    end
    get(name) = (k = findfirst(x -> x.name === name, info); k === nothing ? nothing : info[k].var)
    φ = Dict{Symbol,Any}(X => get(Symbol(:φ_, X)) for X in lm.nodes)
    stub = Dict{Symbol,Any}(X => get(_stub_name(X)) for X in lm.nodes)
    pop = Dict{Symbol,Any}(X => get(Symbol(:pop_, X)) for X in lm.nodes)
    d = net.base.degrees
    η = _lift_rate(net.process.η)
    nodes = copy(lm.nodes)
    if s === nothing
        return _DynamicClosure(d, s, nodes, info, nothing, nothing, nothing, nothing, φ, stub, pop,
                               nothing, nothing, nothing, nothing, η)
    end
    θ = get(:θ)
    return _DynamicClosure(d, s, nodes, info, θ, get(:ξ), get(:χ), _param(Symbol(:q_, s)), φ, stub,
                           pop, pgf(d, θ), pgf_derivative(d, θ, 1), pgf_derivative(d, θ, 2),
                           mean_degree(d), η)
end

# The factors, with the κ → 0 limits of E11/E32 where the mean degree vanishes (ψ^{(n+1)}/ψ'(1)
# becomes ψ^{(n)}, as in lift/configuration.jl, so that the identities dπ_S/dθ = stub entry and
# d(qξψ'/ψ'(1))/dθ = edge entry survive the limit).
_node_S(cl::_DynamicClosure) = cl.q * cl.ξ * cl.ψ
_static_edge_S(cl::_DynamicClosure) = _ratio(cl.q * cl.ξ * cl.ψ1, cl.k̄, cl.q * cl.ξ * cl.ψ)
_edge_S(cl::_DynamicClosure) = cl.χ * _static_edge_S(cl)
_stub_S(cl::_DynamicClosure) = _ratio(cl.q * cl.ξ * cl.θ * cl.ψ1, cl.k̄, cl.q * cl.ξ * cl.θ * cl.ψ)
_node_entry(cl::_DynamicClosure) = cl.q * cl.ξ * cl.ψ1
_edge_entry(cl::_DynamicClosure) = cl.χ * _ratio(cl.q * cl.ξ * cl.ψ2, cl.k̄, cl.q * cl.ξ * cl.ψ1)
_stub_entry(cl::_DynamicClosure) =
    _ratio(cl.q * cl.ξ * (cl.ψ1 + cl.θ * cl.ψ2), cl.k̄, cl.q * cl.ξ * (cl.ψ + cl.θ * cl.ψ1))

function _contact_terms(cl::_DynamicClosure, c::Contact, τ)
    h = τ * cl.φ[c.infector]
    flux = h * _node_entry(cl)
    terms = Pair{Symbol,Any}[:θ => -h, Symbol(:φ_, c.infector) => -h,
                             Symbol(:φ_, c.product) => h * _edge_entry(cl),
                             _stub_name(c.product) => h * _stub_entry(cl),
                             Symbol(:pop_, c.product) => flux]
    return terms, flux
end

function _exit_terms(cl::_DynamicClosure, t::NodeTransition, to::Symbol, ν)
    flux = ν * _node_S(cl)
    terms = Pair{Symbol,Any}[:ξ => -ν * cl.ξ, Symbol(:φ_, to) => ν * _edge_S(cl),
                             _stub_name(to) => ν * _stub_S(cl), Symbol(:pop_, to) => flux]
    return terms, flux
end

function _transition_terms(cl::_DynamicClosure, t::NodeTransition, to::Symbol, a)
    X = t.from
    flux = a * cl.pop[X]
    terms = Pair{Symbol,Any}[Symbol(:φ_, X) => -a * cl.φ[X], Symbol(:φ_, to) => a * cl.φ[X],
                             _stub_name(X) => -a * cl.stub[X], _stub_name(to) => a * cl.stub[X],
                             Symbol(:pop_, X) => -flux, Symbol(:pop_, to) => flux]
    return terms, flux
end

"""
    _neighbour_exchange_row(cl::_DynamicClosure) -> Union{ReactionContribution,Nothing}

The terms of the network process of a `DynamicNetwork(base, NeighbourExchange(η))` table, as one
row of type `:process` (reaction name `:neighbour_exchange`, no node-level flux): χ̇ = η(θ² − χ)
and φ̇_X += η(θπ_X − φ_X) for every non-susceptible species X of the table. `nothing` for a table
without a susceptible class (it has no θ; its exchange terms come with the part that has one).
The row acts once on every coordinate, so it is not additive under `sum_contributions` or
natural under `relabel` the way reaction rows are: a sum (or a merging relabel) of DynamicNetwork
tables must keep exactly one process row, rebuilt for the resulting coordinates with
`_process_row`.
"""
function _neighbour_exchange_row(cl::_DynamicClosure)
    cl.s === nothing && return nothing
    return _neighbour_exchange_row(cl.η, cl.θ, cl.χ, cl.s,
                                   Pair{Symbol,Any}[X => (cl.φ[X], cl.stub[X]) for X in cl.nodes])
end

function _neighbour_exchange_row(η, θ, χ, s::Symbol, stubs::AbstractVector)
    terms = Pair{Symbol,Any}[:χ => η * (θ^2 - χ)]
    for (X, (φX, πX)) in stubs
        push!(terms, Symbol(:φ_, X) => η * (θ * πX - φX))
    end
    return ReactionContribution(:neighbour_exchange, :process, "neighbour exchange  ($(_rate_text(η)))",
                                s, Symbol(""), Symbolics.Num(0), terms)
end

"""
    _process_row(network, closure::Symbol, info::AbstractVector) -> Union{ReactionContribution,Nothing}

The single `:process` row of a table of edge-based contributions with the coordinates `info` on
`network`, or `nothing` when the network has no process (every descriptor but
`DynamicNetwork(base, NeighbourExchange(η))`, or a table without θ). `sum_contributions` and a
merging `relabel` must drop the process rows of their inputs and append this one row for the
coordinates of the result, since the exchange acts once on every coordinate.
"""
_process_row(network, closure::Symbol, info::AbstractVector) = nothing
function _process_row(net::DynamicNetwork{<:NeighbourExchange}, closure::Symbol, info::AbstractVector)
    closure === :dynamic || return nothing
    find(role) = (k = findfirst(x -> x.role === role, info); k === nothing ? nothing : info[k])
    θ, χ = find(:θ), find(:χ)
    (θ === nothing || χ === nothing) && return nothing
    φ = Dict{Symbol,Any}(x.species => x.var for x in info if x.role === :φ)
    stubs = Pair{Symbol,Any}[x.species => (φ[x.species], x.var) for x in info
                             if x.role === :π && haskey(φ, x.species)]
    return _neighbour_exchange_row(_lift_rate(net.process.η), θ.var, χ.var, θ.species, stubs)
end

# The table of a DynamicNetwork lift: the per-reaction rows (lift/assembler.jl), then the one row
# of the exchange process.
function _contributions(cl::_DynamicClosure, lm::_LiftModel, net::NetworkDescriptor)
    table = invoke(_contributions, Tuple{_EdgeClosure,_LiftModel,NetworkDescriptor}, cl, lm, net)
    row = _neighbour_exchange_row(cl)
    row === nothing && return table
    return LiftContributions(table.name, table.network, table.closure, table.coordinates,
                             table.seed_factors, vcat(table.contributions, row),
                             table.coordinate_info)
end

# Observables: those of the static lift (the node-S under the susceptible species' name and `:S`,
# `:I`, `:infectious`, `φ_<s>`/`:φ_S`, `:edge_hazard`, `:excess_hazard`) and the stub-S
# `π_<s>`/`:π_S` = qξθψ'(θ)/ψ'(1), the fraction of all stubs that belong to susceptible nodes
# (MSV's π_S, the target of the exchange; E05).
function _closure_observables(cl::_DynamicClosure, lm::_LiftModel, ::LiftContributions)
    obs = _untyped_common_observables(cl, lm, _node_S(cl))
    φS = _edge_S(cl)
    push!(obs, Symbol(:φ_, cl.s) => φS)
    cl.s !== :S && _alias_free(lm, :φ_S) && push!(obs, :φ_S => φS)
    πS = _stub_S(cl)
    push!(obs, _stub_name(cl.s) => πS)
    (cl.s !== :S && !(:S in lm.nodes) && !(:π_S in lm.nodes)) && push!(obs, :π_S => πS)
    hazard = _sum_terms(Any[τ * cl.φ[c.infector] for (c, τ) in zip(contacts(lm.cm), lm.contact_rates)])
    excess = _unless_zero(_ -> hazard * cl.ψ2 / cl.ψ1, cl.k̄, hazard * cl.ψ1 / cl.ψ)
    push!(obs, :edge_hazard => hazard, :excess_hazard => excess)
    return obs
end

# θ(0) = ξ(0) = χ(0) = 1 and φ_X(0) = π_X(0) = pop_X(0) = ρ_X: the seeds are uniform, so the
# stub-weighted and node-weighted fractions agree at t = 0; the sinks start empty.
function _initial_values(cl::_DynamicClosure, lm::_LiftModel, ρ)
    v = Dict{Symbol,Float64}(:θ => 1.0, :ξ => 1.0, :χ => 1.0)
    for X in lm.nodes
        r = get(ρ, X, 0.0)
        v[Symbol(:φ_, X)] = r
        v[_stub_name(X)] = r
        v[Symbol(:pop_, X)] = r
    end
    return v
end

# q_<s> = 1 − Σ_X seed_X.
_seed_expressions(cl::_DynamicClosure, lm::_LiftModel, seeds) =
    Dict{Any,Any}(cl.q => 1 - _sum_terms(Any[seeds[X] for X in lm.nodes if haskey(seeds, X)]))

function _relabel_coordinate(::Val{:dynamic}, x::_Coordinate, m)
    X = m(x.species)
    x.role in (:θ, :ξ, :χ) && return _Coordinate(x.name, x.var, x.role, X, x.types)
    name = x.role === :π ? _stub_name(X) : _untyped_name(x.role, X)
    return _Coordinate(name, _state(name), x.role, X, x.types)
end

# ---------------------------------------------------------------------------------------------
# edge_based on a dynamic network
# ---------------------------------------------------------------------------------------------

"""
    edge_based(cm::ContactModel, net::DynamicNetwork{<:NeighbourExchange}; name = :edge_based_model,
               form = :expanded)

The edge-based lift on a dynamic fixed-degree network `DynamicNetwork(base, NeighbourExchange(η))`
(Miller, Slim & Volz 2012, Part I §3.2 and Part II §3.2.3): each node keeps its degree, drawn from
the base degree distribution ψ, while every edge breaks at the per-edge rate η and its stubs
rejoin other breaking stubs at random. Every T_EB model is lifted reaction by reaction (SIR, SEIR,
SEAIR with branching and two infectors, several strains, exits such as vaccination with the
factor ξ, removals `X → ∅` to the sink `:removed`); SIS and SIRS raise the `AdmissibilityError`
of `require_admissible`. η may be a number or a symbolic parameter (`NeighbourExchange(η)` with
`@parameters η`, solved with `solve_epidemic(sys; p = Dict(:η => 1.0))`).

Coordinates: `θ`, `ξ` (with exits), `χ`, and `φ_X`, `π_X`, `pop_X` for every non-susceptible
species X (and the sink), with `cumulative` (the fraction ever infected, seeds included):

- `θ`: the probability that a stub of a test node has not transmitted to it;
- `χ`: the partnership memory, the probability that neither stub of the current partnership had
  transmitted before it formed; φ_S = χ·qξψ'(θ)/ψ'(1), and χ̇ = η(θ² − χ);
- `φ_X`: a stub has not transmitted and currently joins an X node;
- `π_X`: the fraction of all stubs that belong to X nodes (π_S = qξθψ'(θ)/ψ'(1) is the target
  of the exchange, M_S of Volz 2008 eq. 9: verified issue E05);
- `pop_X`: the fraction of nodes in X; S = qξψ(θ) with q = 1 − Σ_X seed_X (E06).

The exchange adds η(θπ_X − φ_X) to every φ_X: new partners are drawn in proportion to stubs.
Conservation: θ = φ_S + Σφ_X, π_S + Σπ_X = 1, S + Σpop_X = 1. With η = 0, χ ≡ 1 and the θ, φ, pop
equations are exactly those of `edge_based(cm, net.base)` (the static model); as η → ∞ the model
tends to mean-field social heterogeneity with the base's degrees (Λ3): mass action
`mass_action(cm; κ)` only when the base is κ-regular. Seeding, `default_initial_conditions`, the
seed parameters `seed_X` and the observables are those of the `ConfigurationNetwork` method, plus
`π_<s>` (also `:π_S`), the stub-S. Only the expanded form exists (φ_S has no closed form).

`lift_contributions(cm, net)` gives the per-reaction table, whose last row (type `:process`,
`:neighbour_exchange`) holds the exchange terms, once for all coordinates; `symbolic_ode` of the
table is the field of the system.

```julia
net = DynamicNetwork(RegularDegree(6), NeighbourExchange(1.0))
sys = edge_based(sir_model(; τ = 1/12, γ = 1/4), net)
sol = solve_epidemic(sys; initial = SeedFraction(:I => 0.01), tspan = (0.0, 100.0))
compartment(sys, sol, :cumulative)[end]            # 0.74694 (static network: 0.5326)
```
"""
function edge_based(cm::ContactModel, net::DynamicNetwork{<:NeighbourExchange};
                    name::Symbol = :edge_based_model, form::Symbol = :expanded)
    form === :expanded || throw(ArgumentError(
        "edge_based on a DynamicNetwork has only the expanded form (the neighbour-exchange φ_S has " *
        "no closed form, so there is no compact form); got form = :$form"))
    require_admissible(cm, :edge_based; network = net)
    return _assemble(cm, net; name, context = _lift_context(cm, net))
end

function edge_based(cm::ContactModel, net::DynamicNetwork; kw...)
    require_admissible(cm, :edge_based; network = net)
    throw(ArgumentError(
        "$(_lift_context(cm, net)): EdgeBasedModels lifts DynamicNetwork(base, NeighbourExchange(η)) " *
        "(dynamic fixed degree); the edge-based lift of the process $(nameof(typeof(net.process))) " *
        "is not available in this version (design §K, WP36b)"))
end

# ---------------------------------------------------------------------------------------------
# The legacy DynamicConfigurationModel
# ---------------------------------------------------------------------------------------------

const _DYNAMIC_CONFIGURATION_MESSAGE =
    "DynamicConfigurationModel is removed (design §A.7: it returned wrong numbers). Its builder " *
    "copied the printed Volz–Meyers (2007) equations, whose swap target ψ'(θ)/ψ'(1) should be " *
    "M_S = qθψ'(θ)/ψ'(1) (verified issue E05); it had no seed factor q = 1 − ρ, so S(0) = 1, " *
    "S + I + R = 1 + ρ and η = 0 was not the static model (E06); and it turned every model into " *
    "SIR, taking the first transition's rate as the recovery rate and dropping latent stages, while " *
    "the formation rate η₁ was never used (E07). Use the Miller–Slim–Volz dynamic fixed-degree " *
    "lift, which is exact for SIR, SEIR and every other edge-based-admissible model: " *
    "edge_based(contact_model(progression), DynamicNetwork(ConfigurationNetwork(pgf), " *
    "NeighbourExchange(η₂))), where η₂ is the per-edge rate at which edges swap partners and " *
    "η = 0 is the static network. Stubs that stay dormant between partnerships (a formation " *
    "rate η₁) are the dormant-contact process DynamicNetwork(base, DormantContacts(η_form = η₁, " *
    "η_break = η₂)) (design §K, WP36b)."

"""
    _dynamic_configuration_error(model::DynamicConfigurationModel) -> ArgumentError

The migration error of the legacy `build_edge_system(::DynamicConfigurationModel)` (design §A.7:
functionality that returned wrong numbers errors immediately, with a migration message; verified
issues E05, E06, E07). It names the replacement,
`edge_based(contact_model(progression), DynamicNetwork(ConfigurationNetwork(pgf), NeighbourExchange(η₂)))`.
"""
_dynamic_configuration_error(::DynamicConfigurationModel) =
    ArgumentError(_DYNAMIC_CONFIGURATION_MESSAGE)
