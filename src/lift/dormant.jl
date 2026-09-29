# Owner: WP36b (DESIGN_NetworkEpiCore.md §C.3, §J.2, §K WP36b).
#
# The dormant-contact (DC) closure of the per-reaction assembler (lift/assembler.jl): Miller, Slim &
# Volz (2012), Part II §3.2.4 (papers/1106.6319v1.md:175-201; the PDF, p. 10, has the equations with
# the ratios π_X/π that the markdown rendering loses) and Appendix D, for every T_EB model (SIR,
# SEIR, SEAIR with branching and two infectors, several strains, exits such as vaccination with the
# factor ξ, removals to the sink `:removed`, §J.2), with the seed factor q = 1 − Σρ.
#
# The network is `DynamicNetwork(base, DormantContacts(η₁, η₂))` (η₁ = η_form, η₂ = η_break): every
# node has k_m stubs, k_m ~ ψ (the base degree distribution); a stub is active (half of an edge) or
# dormant. Active edges break at rate η₂ and both stubs become dormant; a dormant stub becomes active
# at rate η₁ by pairing with another activating (so uniformly random) dormant stub. At stationarity,
# which the lift assumes at t = 0 as MSV do, a stub is active with probability A = η₁/(η₁ + η₂)
# (MSV's ξ) and dormant with probability D = η₂/(η₁ + η₂) (MSV's π).
#
# Coordinates. The conditional (per-activity-state) forms of MSV's variables, so that the initial
# values never depend on η₁, η₂ (they may be symbolic parameters) and η₂ = 0 (static) and η₁ = 0 (no
# contacts) are regular:
#
#   θ      a stub of the test node has not transmitted to it (θ = Aθ_A + Dθ_D);
#   θ_A    ... given that it is active;  θ_D  ... given that it is dormant (MSV: φ_D = Dθ_D);
#   χ      the partnership memory: φ_S = χ·qξψ'(θ)/ψ'(1) (MSV: φ_S = A·χ·qψ'(θ)/ψ'(1));
#   ξ      the exit survival factor (only with exits);
#   φ_X    an active stub has not transmitted and joins an X node (MSV: φ_X = A·φ_X);
#   α_X    the fraction of the active stubs that belong to X nodes (MSV: ξ_X = A·α_X);
#   π_X    the fraction of the dormant stubs that belong to X nodes (MSV: π_X = D·π_X);
#   pop_X  the fraction of nodes in X;
#
# for every non-susceptible species X (and the sink). The susceptible forms are S = qξψ(θ),
# φ_S = χqξψ'(θ)/ψ'(1), α_S = qξθ_Aψ'(θ)/ψ'(1) and π_S = qξθ_Dψ'(θ)/ψ'(1). With h = τAφ_J, the
# unconditional edge hazard of a contact:
#
#     contact  r = (s + J → X + J, τ):  θ̇ −= h;  θ̇_A −= τφ_J;  φ̇_J −= τφ_J;  φ̇_X += h·χqξψ''(θ)/ψ'(1)
#                                        α̇_X += τφ_J·qξ(ψ'(θ) + Aθ_Aψ''(θ))/ψ'(1)
#                                        π̇_X += h·qξθ_Dψ''(θ)/ψ'(1);  pop_X' += h·qξψ'(θ)
#     transition (X → Y | ∅, a):         φ, α, π and pop of X move to Y at rate a
#     exit     (s → Y, ν):               ξ̇ −= νξ;  φ̇_Y += νφ_S;  α̇_Y += να_S;  π̇_Y += νπ_S;  pop_Y' += νS
#     dormant contacts (η₁, η₂; once):   θ̇_A += η₂(θ_D − θ_A);  θ̇_D += η₁(θ_A − θ_D);  χ̇ = η₂(θ_D² − χ)
#                                        φ̇_X += η₂(θ_Dπ_X − φ_X);  α̇_X += η₂(π_X − α_X);  π̇_X += η₁(α_X − π_X)
#
# (the conditional forms of MSV's η₁φ_Dπ_X/π − η₂φ_X, −η₂ξ_X + η₁π_X and η₂ξ_X − η₁π_X, since
# η₁D/A = η₂ and η₂A/D = η₁). Initial values θ = θ_A = θ_D = χ = ξ = 1 and φ_X = α_X = π_X = pop_X = ρ_X
# (uniform seeds, stubs at stationarity). Each of the conservation laws θ = Aθ_A + Dθ_D,
# θ_A = φ_S + Σφ_X, α_S + Σα_X = 1, π_S + Σπ_X = 1 and S + Σpop_X = 1 is an identity of the field.
# MSV's SIR system (θ, φ_S, φ_I, φ_D, ξ_R, π_R, R) is its restriction to the invariant set of these
# identities (test/suites/dormant.jl verifies the semiconjugacy symbolically). Limits (MSV §3.2.4,
# Appendix D): η₂ = 0 is the static configuration model; η₁ → ∞ is neighbour exchange at η = η₂
# (DFD, lift/dynamic.jl); η₁ → 0 with degrees scaled by 1/A is the dynamic variable-degree (DVD)
# model; η₁ = η₂ → ∞ is MFSH with the per-contact rate τA.

# ---------------------------------------------------------------------------------------------
# The closure
# ---------------------------------------------------------------------------------------------

struct _DormantClosure <: _EdgeClosure
    degrees::DegreeDistribution
    s::Union{Symbol,Nothing}          # the susceptible species (nothing: a part without one)
    nodes::Vector{Symbol}             # the non-susceptible species and sinks
    info::Vector{_Coordinate}
    θ::Any
    θA::Any                           # θ_A, θ_D: non-transmission given active / dormant
    θD::Any
    χ::Any
    ξ::Any
    q::Any
    φ::Dict{Symbol,Any}
    α::Dict{Symbol,Any}              # the composition of the active stubs
    π::Dict{Symbol,Any}              # the composition of the dormant stubs
    pop::Dict{Symbol,Any}
    ψ::Any                            # ψ(θ), ψ'(θ), ψ''(θ) and the mean maximum degree ψ'(1)
    ψ1::Any
    ψ2::Any
    k̄::Any
    η1::Any                           # η_form and η_break (numbers or parameters)
    η2::Any
    A::Any                            # η₁/(η₁ + η₂) and η₂/(η₁ + η₂)
    D::Any
end

_closure_kind(::_DormantClosure) = :dormant
_coordinates(cl::_DormantClosure) = cl.info
_seed_factors(cl::_DormantClosure) = cl.s === nothing ? Pair{Symbol,Any}[] : [cl.s => cl.q]
_type_of(::_DormantClosure, ::Symbol) = :all
_type_size(::_DormantClosure, ::Symbol) = 1.0
_seed_background(cl::_DormantClosure, ::_LiftModel) = cl.s
_network_terms(cl::_DormantClosure) =
    cl.s === nothing ? Any[cl.η1, cl.η2] : Any[cl.ψ, cl.ψ1, cl.ψ2, cl.k̄, cl.η1, cl.η2]

# Coordinate names: θ, θ_A, θ_D, χ, ξ (global) and φ_X, α_X, π_X, pop_X (per species).
const _DORMANT_GLOBAL = (θ = :θ, θA = :θ_A, θD = :θ_D, χ = :χ, ξ = :ξ)
_dormant_name(role::Symbol, X::Symbol) =
    role === :φ ? Symbol(:φ_, X) : role === :α ? Symbol(:α_, X) : role === :π ? Symbol(:π_, X) :
    Symbol(:pop_, X)

# The active fraction A = η₁/(η₁ + η₂) and the dormant fraction D = η₂/(η₁ + η₂), numeric when both
# rates are (DormantContacts guarantees η₁ + η₂ > 0 then).
function _dormant_fractions(η1, η2)
    a, b = _numvalue(η1), _numvalue(η2)
    (a === nothing || b === nothing) && return η1 / (η1 + η2), η2 / (η1 + η2)
    return a / (a + b), b / (a + b)
end

function _edge_closure(net::DynamicNetwork{<:DormantContacts}, lm::_LiftModel)
    s = _single_susceptible(lm)
    all = (:all, :all)
    info = _Coordinate[]
    if s !== nothing
        for role in (:θ, :θA, :θD, :χ, :ξ)
            name = _DORMANT_GLOBAL[role]
            push!(info, _Coordinate(name, _state(name), role, s, all))
        end
    end
    for role in (:φ, :α, :π, :pop), X in lm.nodes
        name = _dormant_name(role, X)
        push!(info, _Coordinate(name, _state(name), role, X, all))
    end
    get(name) = (k = findfirst(x -> x.name === name, info); k === nothing ? nothing : info[k].var)
    byrole(role) = Dict{Symbol,Any}(X => get(_dormant_name(role, X)) for X in lm.nodes)
    η1 = _lift_rate(net.process.η_form)
    η2 = _lift_rate(net.process.η_break)
    A, D = _dormant_fractions(η1, η2)
    d = net.base.degrees
    nodes = copy(lm.nodes)
    if s === nothing
        return _DormantClosure(d, s, nodes, info, nothing, nothing, nothing, nothing, nothing, nothing,
                               byrole(:φ), byrole(:α), byrole(:π), byrole(:pop), nothing, nothing,
                               nothing, nothing, η1, η2, A, D)
    end
    θ = get(:θ)
    return _DormantClosure(d, s, nodes, info, θ, get(:θ_A), get(:θ_D), get(:χ), get(:ξ),
                           _param(Symbol(:q_, s)), byrole(:φ), byrole(:α), byrole(:π), byrole(:pop),
                           pgf(d, θ), pgf_derivative(d, θ, 1), pgf_derivative(d, θ, 2), mean_degree(d),
                           η1, η2, A, D)
end

# The susceptible forms and entry factors, with the κ → 0 limits of E11/E32 where the mean degree
# vanishes (ψ^{(n+1)}/ψ'(1) becomes ψ^{(n)}, as in lift/configuration.jl and lift/dynamic.jl, so
# that each entry factor stays the θ-derivative of its susceptible form).
_qξ(cl::_DormantClosure) = cl.q * cl.ξ
_node_S(cl::_DormantClosure) = _qξ(cl) * cl.ψ
_node_entry(cl::_DormantClosure) = _qξ(cl) * cl.ψ1
_edge_S(cl::_DormantClosure) = _ratio(cl.χ * _qξ(cl) * cl.ψ1, cl.k̄, cl.χ * _qξ(cl) * cl.ψ)
_active_S(cl::_DormantClosure) = _ratio(_qξ(cl) * cl.θA * cl.ψ1, cl.k̄, _qξ(cl) * cl.θA * cl.ψ)
_dormant_S(cl::_DormantClosure) = _ratio(_qξ(cl) * cl.θD * cl.ψ1, cl.k̄, _qξ(cl) * cl.θD * cl.ψ)
_edge_entry(cl::_DormantClosure) = _ratio(cl.χ * _qξ(cl) * cl.ψ2, cl.k̄, cl.χ * _qξ(cl) * cl.ψ1)
_active_entry(cl::_DormantClosure) =
    _ratio(_qξ(cl) * (cl.ψ1 + cl.A * cl.θA * cl.ψ2), cl.k̄, _qξ(cl) * (cl.ψ + cl.A * cl.θA * cl.ψ1))
_dormant_entry(cl::_DormantClosure) = _ratio(_qξ(cl) * cl.θD * cl.ψ2, cl.k̄, _qξ(cl) * cl.θD * cl.ψ1)

function _contact_terms(cl::_DormantClosure, c::Contact, τ)
    J, X = c.infector, c.product
    u = τ * cl.φ[J]                   # per active stub
    h = cl.A * u                      # per stub: the edge hazard of the contact
    flux = h * _node_entry(cl)
    terms = Pair{Symbol,Any}[:θ => -h, :θ_A => -u, _dormant_name(:φ, J) => -u,
                             _dormant_name(:φ, X) => h * _edge_entry(cl),
                             _dormant_name(:α, X) => u * _active_entry(cl),
                             _dormant_name(:π, X) => h * _dormant_entry(cl),
                             _dormant_name(:pop, X) => flux]
    return terms, flux
end

function _exit_terms(cl::_DormantClosure, t::NodeTransition, to::Symbol, ν)
    flux = ν * _node_S(cl)
    terms = Pair{Symbol,Any}[:ξ => -ν * cl.ξ, _dormant_name(:φ, to) => ν * _edge_S(cl),
                             _dormant_name(:α, to) => ν * _active_S(cl),
                             _dormant_name(:π, to) => ν * _dormant_S(cl),
                             _dormant_name(:pop, to) => flux]
    return terms, flux
end

function _transition_terms(cl::_DormantClosure, t::NodeTransition, to::Symbol, a)
    X = t.from
    flux = a * cl.pop[X]
    terms = Pair{Symbol,Any}[]
    for (role, v) in ((:φ, cl.φ[X]), (:α, cl.α[X]), (:π, cl.π[X]))
        push!(terms, _dormant_name(role, X) => -a * v, _dormant_name(role, to) => a * v)
    end
    push!(terms, _dormant_name(:pop, X) => -flux, _dormant_name(:pop, to) => flux)
    return terms, flux
end

"""
    _dormant_contacts_row(cl::_DormantClosure) -> Union{ReactionContribution,Nothing}

The terms of the stub process of a `DynamicNetwork(base, DormantContacts(η₁, η₂))` table, as one
row of type `:process` (reaction name `:dormant_contacts`, no node-level flux): θ̇_A += η₂(θ_D − θ_A),
θ̇_D += η₁(θ_A − θ_D), χ̇ = η₂(θ_D² − χ), and for every non-susceptible species X of the table
φ̇_X += η₂(θ_Dπ_X − φ_X), α̇_X += η₂(π_X − α_X) and π̇_X += η₁(α_X − π_X). `nothing` for a table
without a susceptible class (it has no θ; its process terms come with the part that has one). As
for neighbour exchange (`_neighbour_exchange_row`), the row acts once on every coordinate: a sum
(or a merging relabel) of such tables must keep exactly one process row, rebuilt with
`_process_row` for the coordinates of the result.
"""
function _dormant_contacts_row(cl::_DormantClosure)
    cl.s === nothing && return nothing
    stubs = Pair{Symbol,Any}[X => (cl.φ[X], cl.α[X], cl.π[X]) for X in cl.nodes]
    return _dormant_contacts_row(cl.η1, cl.η2, cl.θA, cl.θD, cl.χ, cl.s, stubs)
end

function _dormant_contacts_row(η1, η2, θA, θD, χ, s::Symbol, stubs::AbstractVector)
    terms = Pair{Symbol,Any}[:θ_A => η2 * (θD - θA), :θ_D => η1 * (θA - θD), :χ => η2 * (θD^2 - χ)]
    for (X, (φX, αX, πX)) in stubs
        push!(terms, _dormant_name(:φ, X) => η2 * (θD * πX - φX),
              _dormant_name(:α, X) => η2 * (πX - αX), _dormant_name(:π, X) => η1 * (αX - πX))
    end
    text = "dormant contacts  (η_form = $(_rate_text(η1)), η_break = $(_rate_text(η2)))"
    return ReactionContribution(:dormant_contacts, :process, text, s, Symbol(""), Symbolics.Num(0),
                                terms)
end

function _process_row(net::DynamicNetwork{<:DormantContacts}, closure::Symbol, info::AbstractVector)
    closure === :dormant || return nothing
    find(role) = (k = findfirst(x -> x.role === role, info); k === nothing ? nothing : info[k])
    θA, θD, χ = find(:θA), find(:θD), find(:χ)
    (θA === nothing || θD === nothing || χ === nothing) && return nothing
    var(role, X) = (k = findfirst(x -> x.role === role && x.species === X, info);
                    k === nothing ? nothing : info[k].var)
    stubs = Pair{Symbol,Any}[]
    for x in info
        x.role === :φ || continue
        a, p = var(:α, x.species), var(:π, x.species)
        (a === nothing || p === nothing) && continue
        push!(stubs, x.species => (x.var, a, p))
    end
    return _dormant_contacts_row(_lift_rate(net.process.η_form), _lift_rate(net.process.η_break),
                                 θA.var, θD.var, χ.var, θA.species, stubs)
end

# The table of a dormant-contact lift: the per-reaction rows (lift/assembler.jl), then the one row
# of the stub process.
function _contributions(cl::_DormantClosure, lm::_LiftModel, net::NetworkDescriptor)
    table = invoke(_contributions, Tuple{_EdgeClosure,_LiftModel,NetworkDescriptor}, cl, lm, net)
    row = _dormant_contacts_row(cl)
    row === nothing && return table
    return LiftContributions(table.name, table.network, table.closure, table.coordinates,
                             table.seed_factors, vcat(table.contributions, row),
                             table.coordinate_info)
end

# Observables: those of every untyped lift (the node-S under the susceptible species' name and
# `:S`, `:I`, `:infectious`), the susceptible forms `φ_<s>` (the edge-S, given active), `α_<s>`
# and `π_<s>` (the susceptible shares of the active and of the dormant stubs), each also under the
# `_S` name unless a species owns it, `:edge_hazard` = Σ_r τ_r Aφ_{J_r} = −θ̇ and `:excess_hazard`,
# the infection hazard of a susceptible partner (edge_hazard·ψ''(θ)/ψ'(θ)).
function _closure_observables(cl::_DormantClosure, lm::_LiftModel, ::LiftContributions)
    obs = _untyped_common_observables(cl, lm, _node_S(cl))
    for (role, e) in ((:φ, _edge_S(cl)), (:α, _active_S(cl)), (:π, _dormant_S(cl)))
        push!(obs, _dormant_name(role, cl.s) => e)
        alias = _dormant_name(role, :S)
        (cl.s !== :S && !(:S in lm.nodes) && !(alias in lm.nodes) && _alias_free(lm, alias)) &&
            push!(obs, alias => e)
    end
    hazard = _sum_terms(Any[τ * cl.A * cl.φ[c.infector] for (c, τ) in zip(contacts(lm.cm), lm.contact_rates)])
    excess = _unless_zero(_ -> hazard * cl.ψ2 / cl.ψ1, cl.k̄, hazard * cl.ψ1 / cl.ψ)
    push!(obs, :edge_hazard => hazard, :excess_hazard => excess)
    return obs
end

# θ = θ_A = θ_D = χ = ξ = 1 and φ_X = α_X = π_X = pop_X = ρ_X at t = 0: the seeds are uniform and
# the stubs at stationarity, so each conditional composition is the node composition; the sinks
# start empty.
function _initial_values(cl::_DormantClosure, lm::_LiftModel, ρ)
    v = Dict{Symbol,Float64}(:θ => 1.0, :θ_A => 1.0, :θ_D => 1.0, :χ => 1.0, :ξ => 1.0)
    for X in lm.nodes, role in (:φ, :α, :π, :pop)
        v[_dormant_name(role, X)] = get(ρ, X, 0.0)
    end
    return v
end

# q_<s> = 1 − Σ_X seed_X.
_seed_expressions(cl::_DormantClosure, lm::_LiftModel, seeds) =
    Dict{Any,Any}(cl.q => 1 - _sum_terms(Any[seeds[X] for X in lm.nodes if haskey(seeds, X)]))

function _relabel_coordinate(::Val{:dormant}, x::_Coordinate, m)
    X = m(x.species)
    x.role in (:θ, :θA, :θD, :χ, :ξ) && return _Coordinate(x.name, x.var, x.role, X, x.types)
    name = _dormant_name(x.role, X)
    return _Coordinate(name, _state(name), x.role, X, x.types)
end

# ---------------------------------------------------------------------------------------------
# edge_based on dormant contacts
# ---------------------------------------------------------------------------------------------

"""
    edge_based(cm::ContactModel, net::DynamicNetwork{<:DormantContacts}; name = :edge_based_model,
               form = :expanded)

The edge-based lift on the dormant-contact network `DynamicNetwork(base, DormantContacts(η_form,
η_break))` of Miller, Slim & Volz (2012), Part II §3.2.4: every node has k_m stubs, k_m drawn from
the base degree distribution ψ; a stub is active (half of an edge) or dormant; each active edge
breaks at rate η₂ = `η_break`, and each dormant stub becomes active at rate η₁ = `η_form` by pairing
with another activating stub, so a new partner is drawn in proportion to dormant stubs. The stubs
are taken at stationarity at t = 0: a stub is active with probability A = η₁/(η₁ + η₂) (MSV's ξ;
the mean degree of the network is A·ψ'(1)) and dormant with probability D = η₂/(η₁ + η₂) (MSV's π).
Every T_EB model is lifted reaction by reaction (SIR, SEIR, SEAIR with branching and two
infectors, several strains, exits such as vaccination with the factor ξ, removals `X → ∅` to the
sink `:removed`); SIS and SIRS raise the `AdmissibilityError` of `require_admissible`. η₁ and η₂
may be numbers or symbolic parameters (`DormantContacts(η₁, η₂)` with `@parameters η₁ η₂`, solved
with `solve_epidemic(sys; p = Dict(:η₁ => 1.0, :η₂ => 0.5))`).

Coordinates (the conditional forms of MSV's variables, so that initial values never depend on
η₁ and η₂), with `cumulative` (the fraction ever infected, seeds included):

- `θ`: a stub of a test node has not transmitted to it; `θ_A`, `θ_D`: the same, given that the
  stub is active or dormant (θ = Aθ_A + Dθ_D; MSV's φ_D = Dθ_D);
- `χ`: the partnership memory, φ_S = χ·qξψ'(θ)/ψ'(1), with χ̇ = η₂(θ_D² − χ);
- `ξ`: the exit survival factor (only when the model has exits);
- `φ_X`: an active stub has not transmitted and joins an X node (MSV's φ_X is Aφ_X);
- `α_X`, `π_X`: the fractions of the active and of the dormant stubs that belong to X nodes (MSV's
  ξ_X = Aα_X and π_X = Dπ_X);
- `pop_X`: the fraction of nodes in X; S = qξψ(θ) with q = 1 − Σ_X seed_X.

The stub process adds η₂(θ_Dπ_X − φ_X) to φ_X, η₂(π_X − α_X) to α_X and η₁(α_X − π_X) to π_X, and
moves θ_A and θ_D towards each other at rates η₂ and η₁. Conservation: θ = Aθ_A + Dθ_D,
θ_A = φ_S + Σφ_X, α_S + Σα_X = 1, π_S + Σπ_X = 1 and S + Σpop_X = 1, with
α_S = qξθ_Aψ'(θ)/ψ'(1) and π_S = qξθ_Dψ'(θ)/ψ'(1). For SIR it is exactly MSV's system (θ, φ_S, φ_I,
φ_D, ξ_R, π_R, R) with the seed factor q, which is its restriction to the invariant set of these
identities. Limits (MSV §3.2.4 and Appendix D): η₂ = 0 is the static model
`edge_based(cm, net.base)`; η₁ → ∞ at fixed η₂ is neighbour exchange
`DynamicNetwork(base, NeighbourExchange(η₂))`; η₁ → 0 with degrees scaled by 1/A is the dynamic
variable-degree model; η₁ = η₂ → ∞ is mean-field social heterogeneity `MFSHNetwork(base)` with the
per-contact rate τA. Seeding, `default_initial_conditions`, the seed parameters `seed_X` and the
node observables are those of the `ConfigurationNetwork` method; the susceptible forms are the
observables `φ_<s>`, `α_<s>` and `π_<s>` (also `:φ_S`, `:α_S`, `:π_S`), with `:edge_hazard` = −θ̇
and `:excess_hazard`. Only the expanded form exists. `basic_reproduction_number(sys; p)`,
`next_generation_matrix(sys; p)` and `early_growth_rate(sys; p)` linearise this field.

`lift_contributions(cm, net)` gives the per-reaction table, whose last row (type `:process`,
`:dormant_contacts`) holds the stub-process terms, once for all coordinates; `symbolic_ode` of the
table is the field of the system.

```julia
net = DynamicNetwork(EmpiricalDegree(2 => 0.5, 8 => 0.5), DormantContacts(η_form = 1, η_break = 1))
sys = edge_based(sir_model(; τ = 1.0, γ = 1.0), net)
sol = solve_epidemic(sys; initial = SeedFraction(:I => 0.01), tspan = (0.0, 20.0))
compartment(sys, sol, :cumulative)[end]            # 0.6266 (:sir_dormant_msv)
```
"""
function edge_based(cm::ContactModel, net::DynamicNetwork{<:DormantContacts};
                    name::Symbol = :edge_based_model, form::Symbol = :expanded)
    form === :expanded || throw(ArgumentError(
        "edge_based on a DynamicNetwork with DormantContacts has only the expanded form (the " *
        "partnership and stub coordinates have no closed form); got form = :$form"))
    require_admissible(cm, :edge_based; network = net)
    return _assemble(cm, net; name, context = _lift_context(cm, net))
end

# ---------------------------------------------------------------------------------------------
# Threshold quantities (the `_numeric_threshold` extension point of analysis.jl)
# ---------------------------------------------------------------------------------------------

# The linearisation of the dormant-contact field at the disease-free state (θ = θ_A = θ_D = χ = ξ =
# 1, q = 1, every φ, α, π and pop 0) over the φ, α and π coordinates of the transmission chain:
# a stub that went dormant carries infection into later partnerships, so the α and π blocks feed
# φ and the edge-only NGM of analysis.jl (`_eb_linearisation`, φ block) does not apply. The field
# is linear in q_<s> and every gain of a contact carries it, so J(q = 1) = F − V with V = −J(q = 0).
# F factors through the contacts: F = Σ_r b_{X_r} h_rᵀ, with h_r the row of ∂(node-level flux of r)
# and b_X the gains per new infection into X (the same for every contact with product X), which
# gives the next-generation matrix by entry state, K_{X←Y} = Σ_{r: X_r = X} h_rᵀV⁻¹b_Y.
struct _DormantLinearisation
    F::Matrix{Float64}
    V::Matrix{Float64}
    entries::Vector{Symbol}
    births::Vector{Vector{Float64}}           # b_X for each entry state
    hazards::Vector{Pair{Symbol,Vector{Float64}}}   # product X_r => h_r, one per contact
end

function _dormant_linearisation(sys::EdgeModelSystem, vals, fname::AbstractString)
    cm, _ = _system_model(sys, fname)
    md = sys.metadata
    table = md[:contributions]
    raw = md[:raw]
    info = table.coordinate_info
    chain = _transmission_chain(cm)
    states = collect(raw.states)
    # every coordinate of the table (ξ too: the per-reaction terms keep it where the closed field
    # has dropped it for want of exits)
    dfe = Dict{Any,Any}(x.var => (x.role in (:θ, :θA, :θD, :χ, :ξ) ? 1 : 0) for x in info)
    idx = Int[]
    for (i, s) in enumerate(states)
        k = findfirst(x -> isequal(x.var, s), info)
        k === nothing && throw(ArgumentError("$(fname): the state $(s) is not an edge-based coordinate"))
        x = info[k]
        (x.role in (:φ, :α, :π) && x.species in chain) && push!(idx, i)
    end
    isempty(idx) && throw(ArgumentError(
        "$(fname): the model :$(cm.name) has no state from which a transmission can follow"))
    block = states[idx]
    qs = [last(sq) for sq in table.seed_factors]
    at(e, qv) = Symbolics.substitute(e, merge(dfe, Dict{Any,Any}(q => qv for q in qs)); fold = Val(true))
    J = Symbolics.jacobian(collect(raw.rhs)[idx], block)
    J1 = _evaluate(at.(J, 1), vals, fname)
    J0 = _evaluate(at.(J, 0), vals, fname)
    # per contact: the flux row h_r and the q-dependent gains per unit flux
    pos = Dict{Symbol,Int}()
    for (j, s) in enumerate(block)
        k = findfirst(x -> isequal(x.var, s), info)
        pos[info[k].name] = j
    end
    names = [x.name for x in info if haskey(pos, x.name)]
    order = [pos[n] for n in names]
    entries = Symbol[]
    births = Vector{Float64}[]
    hazards = Pair{Symbol,Vector{Float64}}[]
    for r in table.contributions
        r.type === :contact || continue
        r.to in chain || continue
        h = vec(_evaluate(at.(Symbolics.jacobian([Symbolics.Num(r.flux)], block), 1), vals, fname))
        push!(hazards, r.to => h)
        r.to in entries && continue
        # the row's terms per block coordinate (a contact whose product is its infector has two
        # terms for the same φ, which add)
        acc = Dict{Symbol,Any}()
        for (k, v) in r.terms
            acc[k] = get(acc, k, 0) + v
        end
        rows = Vector{Symbolics.Num}(undef, length(block))
        for (n, j) in zip(names, order)
            rows[j] = Symbolics.Num(get(acc, n, 0))
        end
        J_r = Symbolics.jacobian(rows, block)
        G = _evaluate(at.(J_r, 1), vals, fname) .- _evaluate(at.(J_r, 0), vals, fname)
        c = findfirst(!iszero, h)
        c === nothing && continue           # no active contacts (η_form = 0): no infections
        push!(entries, r.to)
        push!(births, G[:, c] ./ h[c])
    end
    return _DormantLinearisation(J1 .- J0, -J0, entries, births, hazards)
end

function _numeric_threshold(::Val{:dormant}, ::typeof(next_generation_matrix), sys::EdgeModelSystem, vals;
                            kw...)
    L = _dormant_linearisation(sys, vals, "next_generation_matrix")
    n = length(L.entries)
    K = zeros(n, n)
    for (c, b) in enumerate(L.births)
        y = L.V \ b
        for (X, h) in L.hazards
            i = findfirst(==(X), L.entries)
            i === nothing || (K[i, c] += LinearAlgebra.dot(h, y))
        end
    end
    return K
end

function _numeric_threshold(::Val{:dormant}, ::typeof(basic_reproduction_number), sys::EdgeModelSystem, vals;
                            kw...)
    K = _numeric_threshold(Val(:dormant), next_generation_matrix, sys, vals)
    return isempty(K) ? 0.0 : Float64(maximum(abs, LinearAlgebra.eigvals(K)))
end

function _numeric_threshold(::Val{:dormant}, ::typeof(early_growth_rate), sys::EdgeModelSystem, vals; kw...)
    L = _dormant_linearisation(sys, vals, "early_growth_rate")
    return Float64(maximum(real, LinearAlgebra.eigvals(L.F .- L.V)))
end

_numeric_threshold(::Val{:dormant}, ::typeof(transmissibility), sys::EdgeModelSystem, vals; kw...) =
    throw(ArgumentError(
        "transmissibility: with dormant contacts a stub transmits across successive partnerships, so " *
        "there is no single per-edge transmissibility; use next_generation_matrix(sys; p) or " *
        "basic_reproduction_number(sys; p)"))
