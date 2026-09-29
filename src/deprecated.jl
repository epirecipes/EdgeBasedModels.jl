# Owner: WP14 → WP29 (DESIGN_NetworkEpiCore.md §A.7; work package in §G.2).
#
# Deprecations of EdgeBasedModels 0.2 (MIGRATION.md is the user-facing list). The policy:
#
# - renamed but correct functionality gets one release of `Base.depwarn` shims;
# - functionality that returned wrong numbers, or checked nothing, is an immediate error with a
#   migration message (build_sis, build_sis_reinfection, to_mass_action, compare_models, compose,
#   stratify(::OpenEBCM), verify_functoriality, EBCMFunctor, the metadata-only
#   NaturalTransformation);
# - every shim and every error has a test in test/suites/deprecations.jl.
#
# The 0.1 categorical layer (src/categorical.jl) and reinfection-counting builders
# (src/reinfection_counting.jl) are deleted (WP29): the shims below forward to NetworkEpiCore's
# open models and to `edge_based`, and never reach 0.1 code.

# --- SIS (verified issue E01) ------------------------------------------------------------------

const _SIS_MESSAGE =
    "build_sis returned SIR dynamics relabelled (ebm-core #1, verified issue E01): its θ equation " *
    "was Miller's SIR equation and its I was the cumulative incidence. SIS has no exact " *
    "edge-based model (an arrow into the susceptible class breaks the edge-based construction; " *
    "Miller, Slim & Volz 2012). Use NodeBasedModels.node_based(sis_model(), net) (pairwise " *
    "closures, reinfection counting with with_reinfection_counting) or " *
    "NetworkOutbreaks.simulate(sis_model(), net; …) (exact stochastic simulation)."

"""
    build_sis(pgf, τ, γ; name)          # removed: throws
    generate_sis(pgf, τ, γ; name)       # the same function

Removed in EdgeBasedModels 0.2: the old model was the SIR edge-based equation relabelled as SIS
(verified issue E01), and SIS has no exact edge-based model. The error message names the
replacements: `NodeBasedModels.node_based(sis_model(), net)` and
`NetworkOutbreaks.simulate(sis_model(), net; …)`. `build_edge_system` of an SIS progression and
`edge_based(sis_model(), net)` are errors too.
"""
build_sis(args...; kwargs...) = error(_SIS_MESSAGE)

const _SIS_REINFECTION_MESSAGE =
    "build_sis_reinfection is removed from EdgeBasedModels (design §A.7): it is a pairwise model " *
    "(a configuration-model triple closure with nodes stratified by infection count; Keeling et " *
    "al. 2016, Approximation 1), not an edge-based one, and SIS has no exact edge-based model " *
    "(verified issue E01). The same equations are " *
    "NodeBasedModels.node_based(with_reinfection_counting(sis_model(; τ, γ), L), " *
    "ConfigurationNetwork(d)), solved with initial = SeedFraction(:I_1 => ρ) " *
    "(SeedFraction(:I_0 => ρ) for L = 0) for the 0.1 seeding seed_fraction = ρ; the infection " *
    "totals are reinfection_totals(sys, sol). Stochastic simulations: " *
    "NetworkOutbreaks.simulate(with_reinfection_counting(sis_model(), L), net; …)."

"""
    build_sis_reinfection(pgf, τ, γ, L; name)   # removed: throws

Removed in EdgeBasedModels 0.2 (design §A.7): the pairwise SIS model with nodes stratified by
infection count (Keeling et al. 2016, Approximation 1) is not an edge-based model (SIS has none;
verified issue E01). Its numbers were right, and the same equations are
`NodeBasedModels.node_based(with_reinfection_counting(sis_model(; τ, γ), L), ConfigurationNetwork(d))`
with `initial = SeedFraction(:I_1 => ρ)` (`:I_0` for `L = 0`); the error message says so.
"""
build_sis_reinfection(args...; kwargs...) = error(_SIS_REINFECTION_MESSAGE)

"""
    with_reinfection_counting(prog::DiseaseProgression, L)        # removed: throws
    with_reinfection_counting(model::StaticConfigurationModel, L) # removed: throws

The 0.1 structural lift of a legacy progression is removed: the lifted model has one susceptible
class per infection count, which a `DiseaseProgression` cannot express, and no edge-based model
(it re-susceptibilises). Use NetworkEpiCore's `with_reinfection_counting(cm::ContactModel, L)`
on `contact_model(prog)` (or on `sis_model()`, `sirs_model()`), with NodeBasedModels or
NetworkOutbreaks.
"""
with_reinfection_counting(::Union{DiseaseProgression,StaticConfigurationModel}, ::Integer) =
    error("with_reinfection_counting of a legacy DiseaseProgression or StaticConfigurationModel is " *
          "removed (design §A.7): the counted model has one susceptible class per infection count, " *
          "which a DiseaseProgression cannot express, and it has no edge-based model. Use " *
          "NetworkEpiCore's with_reinfection_counting(contact_model(prog), L) (for example on " *
          "sis_model()) with NodeBasedModels.node_based or NetworkOutbreaks.simulate.")

# --- Mass action (verified issue E08) ------------------------------------------------------------

const _MASS_ACTION_MESSAGE =
    "to_mass_action and compare_models are removed (verified issue E08): they mapped the " *
    "edge-based model to MA(τ·ψ''(1)/ψ'(1), γ), which is not a reduction of it. On a Poisson " *
    "network the exact reduction (Rempała 2023) is MA(β = μτ, γ + τ): the recovery rate must " *
    "become γ + τ, and its I is the edge variable φ_I, not the prevalence (the prevalence needs " *
    "dI/dt = β S φ_I − γ I). Use mass_action(sys; form) on an edge-based system, with form = " *
    ":exact, :edge (Rempała's quotient, exact on Poisson degree distributions), :general, " *
    ":limit (the κ → ∞ limit) or :calibrated (an R₀-matched calibration, not a reduction)."

"""
    to_mass_action(model)      # removed: throws
    compare_models(model; …)   # removed: throws

Removed in EdgeBasedModels 0.2 (verified issue E08): the map ignored the edge-level loss τ, so
the mass-action R₀ and final size were wrong (R₀ 3.33 instead of 2.00 at τ = 1/6, γ = 1/4 on
Poisson(5)). The exact Poisson reduction is Rempała's MA(μτ, γ + τ), whose I is φ_I; see
`mass_action(sys; form)`.
"""
to_mass_action(args...; kwargs...) = error(_MASS_ACTION_MESSAGE)

"""
    compare_models(model; …)   # removed: throws

Removed in EdgeBasedModels 0.2 together with [`to_mass_action`](@ref) (verified issue E08).
"""
compare_models(args...; kwargs...) = error(_MASS_ACTION_MESSAGE)

# --- The legacy categorical layer (verified issues E22, E24) -------------------------------------

const _COMPOSE_MESSAGE =
    "EdgeBasedModels.compose is removed (verified issue E22): a wired composite never built a " *
    "model (and its unreachable coupling broke conservation), and verify_functoriality compared " *
    "θ only, so it could report a composite functorial vacuously. Compose the syntax with " *
    "NetworkEpiCore.glue(A, B; on = [...]) or disjoint_union(:a => A, :b => B), then lift with " *
    "edge_based(model, net); couple populations with stratify(model, strata(names; sizes)) on a " *
    "MultitypeNetwork (sbm_network or unstructured)."

const _FUNCTOR_MESSAGE =
    "EBCMFunctor and verify_functoriality are removed (verified issue E22): the check compared θ " *
    "only, on 50 points, and never tested a wired composite. The lift is edge_based(model, net); " *
    "check laws with NetworkEpiCore's Semiconjugacy/verify and check_naturality, and compare " *
    "systems with vector_fields_equal(symbolic_ode(a), symbolic_ode(b))."

const _STRATIFY_MESSAGE =
    "stratify(::OpenEBCM, strata, mixing) is removed (verified issue E24): it replaced the base " *
    "degree distribution by a multivariate Poisson with the same mean, and accepted mixing " *
    "matrices that no network realises. Use NetworkEpiCore's stratify(model, strata(names; " *
    "sizes)) with a typed network, sbm_network(st; mean_contacts) or " *
    "unstructured(ConfigurationNetwork(d), st), whose reciprocity check enforces " *
    "n_a E[k_ab] = n_b E[k_ba]."

"""
    EdgeBasedModels.compose(m1, m2, wiring)   # removed (unexported): throws

Removed in EdgeBasedModels 0.2 (verified issue E22); use `NetworkEpiCore.glue` and
`edge_based`. (`compose` is no longer exported: ModelingToolkit and Catalyst export the name.)
"""
compose(args...; kwargs...) = error(_COMPOSE_MESSAGE)

"""
    verify_functoriality(m1, m2, wiring; …)   # removed: throws
    EBCMFunctor(name)                          # removed: throws

Removed in EdgeBasedModels 0.2 (verified issue E22): the check was vacuous. Use `edge_based`
and NetworkEpiCore's `verify`, `check_naturality` and `vector_fields_equal`.
"""
verify_functoriality(args...; kwargs...) = error(_FUNCTOR_MESSAGE)

"""
    EBCMFunctor(name)   # removed: throws

Removed in EdgeBasedModels 0.2 together with [`verify_functoriality`](@ref) (verified issue
E22); the lift is `edge_based(model, net)`.
"""
EBCMFunctor(args...; kwargs...) = error(_FUNCTOR_MESSAGE)

const _NATURAL_TRANSFORMATION_MESSAGE =
    "the metadata-only NaturalTransformation(name, source::Type, target::Type, description) of " *
    "EdgeBasedModels 0.1 is removed (design §A.7): it recorded two model types and a description " *
    "and checked nothing, and the description the 0.1 documentation gave it (\"EBCM → " *
    "mass-action; valid when network is Poisson\") stood for the wrong map of verified issue E08. " *
    "NaturalTransformation is now NetworkEpiCore's: " *
    "NaturalTransformation(name; source = :edge_based, target = :mass_action, applies, component) " *
    "between representations, whose components are Semiconjugacy objects checked with verify " *
    "(and check_naturality for gluing). EdgeBasedModels' mass-action reductions are " *
    "mass_action(sys; form)."

# The legacy models of the 0.1 metadata constructor (typed on EdgeBasedModels' model types, so
# that the method is not piracy on NetworkEpiCore's type).
const _LegacyModelType = Union{StaticConfigurationModel,ClusteredConfigurationModel,
                               DynamicConfigurationModel,MultiTypeConfigurationModel}

"""
    NaturalTransformation(name, source::Type, target::Type, description)   # removed: throws

The metadata-only constructor of EdgeBasedModels 0.1 (with a legacy model type as `source`) is
removed (design §A.7): it checked nothing, and its documented use stood for the wrong
mass-action map of verified issue E08. `NaturalTransformation` is NetworkEpiCore's
(re-exported): `NaturalTransformation(name; source, target, applies, component)` between
representations, with `Semiconjugacy` components checked by `verify`.
"""
NetworkEpiCore.NaturalTransformation(name::Symbol, source::Type{<:_LegacyModelType}, target::Type,
                                     description::AbstractString) =
    error(_NATURAL_TRANSFORMATION_MESSAGE)

"""
    Port(name, type)

A typed boundary port of a legacy [`OpenEBCM`](@ref) (deprecated): a species `name` and its role
`type`, one of `:susceptible`, `:infectious`, `:latent` and `:recovered`. NetworkEpiCore's open
models expose legs of species instead (`open_model(cm; legs)`).
"""
struct Port
    name::Symbol
    type::Symbol
end

"""
    OpenEBCM(name, model::OpenContactModel, network, ports)

The legacy open edge-based model (deprecated), built by [`open_sir`](@ref), [`open_seir`](@ref)
and [`tensor`](@ref). Since 0.2 it holds the replacement objects: `model` is NetworkEpiCore's
open model (`open_model(sir_model(; τ, γ); legs)`, or `disjoint_union` for a tensor product) and
`network` the network it lives on (a `ConfigurationNetwork`, or the block-diagonal
`MultitypeNetwork` of a tensor product); `ports` are the 0.1 ports. Lower it with
`edge_based(o)` or `build_edge_system(o)`, which are `edge_based(o.model, o.network)` with the
0.1 seeding (a fraction ρ of each component in its entry state). The 0.1 idiom
`build_edge_system(o.model)` no longer works: `o.model` is an open ContactModel without a network.
"""
struct OpenEBCM
    name::Symbol
    model::OpenContactModel
    network::NetworkDescriptor
    ports::Vector{Port}
end

function Base.show(io::IO, o::OpenEBCM)
    print(io, "OpenEBCM(:", o.name, ", ", length(o.ports), " ports on a ", nameof(typeof(o.network)), ")")
end

# The 0.1 ports of a ContactModel: the susceptible class, then every other species by role.
function _legacy_ports(cm::ContactModel)
    infectors = Set(c.infector for c in contacts(cm))
    left = Set(t.from for t in node_transitions(cm))
    ports = Port[Port(s, :susceptible) for s in susceptible_species(cm)]
    for X in species_names(cm)
        X in susceptible_species(cm) && continue
        type = X in infectors ? :infectious : X in left ? :latent : :recovered
        push!(ports, Port(X, type))
    end
    return ports
end

function _open_ebcm(name::Symbol, cm::ContactModel, pgf)
    legs = [[X] for X in species_names(cm)]
    return OpenEBCM(name, open_model(cm; legs), _net(pgf), _legacy_ports(cm))
end

"""
    edge_based(o::OpenEBCM; name = o.name, form = :expanded) -> EdgeModelSystem
    build_edge_system(o::OpenEBCM; name = o.name)

The edge-based model of a legacy open model: `edge_based(o.model, o.network; name, form)`. The
0.1 seeding is kept as the default of `default_initial_conditions(sys; seed_fraction = ρ)`: a
fraction ρ of every component (of a tensor product: of every node type) starts in its entry
state.
"""
function edge_based(o::OpenEBCM; name::Symbol = o.name, kw...)
    sys = edge_based(o.model, o.network; name, kw...)
    net = o.network
    if net isa MultitypeNetwork
        cm = contact_model(o.model)
        entries = entry_species(cm)
        sizes = Dict(zip(net.types, net.sizes))
        stratum(X) = cm.labels[X].stratum
        sys.metadata[:default_seed] = ρ -> SeedFraction(Pair{Symbol,Float64}[
            X => ρ * sizes[stratum(X)] for X in entries])
    end
    return sys
end
build_edge_system(o::OpenEBCM; name::Symbol = o.name, kw...) = edge_based(o; name, kw...)

"""
    stratify(base::OpenEBCM, strata, mixing)   # removed: throws

The legacy stratification of an `OpenEBCM` is removed (verified issue E24); use
`stratify(cm::ContactModel, strata(names; sizes))` on a `MultitypeNetwork`.
"""
stratify(::OpenEBCM, args...; kwargs...) = error(_STRATIFY_MESSAGE)

"""
    open_sir(pgf, τ, γ; name = :sir)          # deprecated
    open_seir(pgf, σ, τ, γ; name = :seir)     # deprecated

Deprecated: a legacy [`OpenEBCM`](@ref) on the configuration network of `pgf` (a `DegreePGF` or a
NetworkEpiCore degree distribution). It forwards to NetworkEpiCore:
`open_model(sir_model(; τ, γ); legs = [[:S], [:I], [:R]])` on `ConfigurationNetwork(pgf)`, which
`edge_based(o)` lifts.
"""
function open_sir(pgf, β, γ; name::Symbol = :sir)
    Base.depwarn("`open_sir(pgf, τ, γ)` is deprecated: build the open model with " *
                 "`open_model(sir_model(; τ, γ); legs = [[:S], [:I], [:R]])` and lift it with " *
                 "`edge_based(model, ConfigurationNetwork(d))`.", :open_sir)
    return _open_ebcm(name, sir_model(; τ = β, γ), pgf)
end

"""
    open_seir(pgf, σ, τ, γ; name = :seir)   # deprecated

Deprecated: a legacy SEIR [`OpenEBCM`](@ref) (see [`open_sir`](@ref)), forwarding to
`open_model(seir_model(; τ, σ, γ); legs = [[:S], [:E], [:I], [:R]])`.
"""
function open_seir(pgf, σ, β, γ; name::Symbol = :seir)
    Base.depwarn("`open_seir(pgf, σ, τ, γ)` is deprecated: build the open model with " *
                 "`open_model(seir_model(; τ, σ, γ); legs = [[:S], [:E], [:I], [:R]])` and lift it " *
                 "with `edge_based(model, ConfigurationNetwork(d))`.", :open_seir)
    return _open_ebcm(name, seir_model(; τ = β, σ, γ), pgf)
end

"""
    tensor(m1::OpenEBCM, m2::OpenEBCM)   # deprecated

Deprecated: the independent (block-diagonal) composition of two legacy open models on
configuration networks. It forwards to `disjoint_union(m1.name => m1.model, m2.name => m2.model)`
(species `X_<name>`) on the block-diagonal `MultitypeNetwork` with node types `m1.name`,
`m2.name`, equal sizes 1/2 and no cross-type edges (law H8), which `edge_based(tensor(m1, m2))`
lifts. Compartments are fractions of all nodes (design §J.6), so `pop_I_a` is half the 0.1
within-component value; the default seeding seeds a fraction ρ of each component. The component
names must differ. (The 0.1 refusal of latent stages, verified issue E23, is gone with the 0.1
observable that miscounted them.)
"""
function tensor(m1::OpenEBCM, m2::OpenEBCM)
    Base.depwarn("`tensor(m1, m2)` is deprecated: compose ContactModels with " *
                 "`disjoint_union(:a => cm1, :b => cm2)` and lift them on a block-diagonal " *
                 "MultitypeNetwork (no cross-type edges).", :tensor)
    m1.name === m2.name && throw(ArgumentError(
        "tensor: both components are named :$(m1.name); their variables would collide " *
        "(pass name = … to open_sir/open_seir)"))
    for m in (m1, m2)
        m.network isa ConfigurationNetwork || throw(ArgumentError(
            "tensor: component :$(m.name) is not on a configuration network (a tensor product of a " *
            "tensor product); compose the ContactModels with disjoint_union and build the " *
            "MultitypeNetwork directly"))
    end
    types = [m1.name, m2.name]
    net = MultitypeNetwork(types, [0.5, 0.5],
                           MultivariateDegree[IndependentDegrees(m1.name => m1.network.degrees),
                                              IndependentDegrees(m2.name => m2.network.degrees)])
    model = disjoint_union(m1.name => m1.model, m2.name => m2.model)
    ports = Port[Port(Symbol(p.name, :_, m.name), p.type) for m in (m1, m2) for p in m.ports]
    return OpenEBCM(Symbol(m1.name, :_tensor_, m2.name), model, net, ports)
end

# --- The 0.1 canned progressions ----------------------------------------------------------------

"""
    edge_sir_model(; β = :β, γ = :γ, susceptible = :S)                  # deprecated
    edge_seir_model(; σ = :σ, β = :β, γ = :γ, susceptible = :S)         # deprecated
    edge_sis_model(; β = :β, γ = :γ, susceptible = :S)                  # deprecated
    edge_sirs_model(; β = :β, γ = :γ, ε = :ε, susceptible = :S)         # deprecated

Deprecated: the EdgeBasedModels 0.1 factories, returning the legacy [`DiseaseProgression`](@ref)
(β is the per-contact rate). The canned models are now NetworkEpiCore's `sir_model(; τ, γ)` & co.,
which return a `ContactModel` (and are exported by EdgeBasedModels, NodeBasedModels and
NetworkOutbreaks alike); `DiseaseProgression(sir_model())` gives the legacy type.
"""
function edge_sir_model(; kwargs...)
    Base.depwarn("`edge_sir_model` is deprecated: use `sir_model(; τ, γ)`, which returns a " *
                 "ContactModel (`DiseaseProgression(sir_model())` gives the legacy type).",
                 :edge_sir_model)
    return _legacy_sir_model(; kwargs...)
end
"""
    edge_seir_model(; kwargs...)   # deprecated

Deprecated: the EdgeBasedModels 0.1 factory returning the legacy [`DiseaseProgression`](@ref);
use `seir_model(; τ, σ, γ)` (a `ContactModel`); see [`edge_sir_model`](@ref).
"""
function edge_seir_model(; kwargs...)
    Base.depwarn("`edge_seir_model` is deprecated: use `seir_model(; τ, σ, γ)`, which returns a " *
                 "ContactModel (`DiseaseProgression(seir_model())` gives the legacy type).",
                 :edge_seir_model)
    return _legacy_seir_model(; kwargs...)
end
"""
    edge_sis_model(; kwargs...)   # deprecated

Deprecated: the EdgeBasedModels 0.1 factory returning the legacy [`DiseaseProgression`](@ref);
use `sis_model(; τ, γ)` (a `ContactModel`); see [`edge_sir_model`](@ref).
"""
function edge_sis_model(; kwargs...)
    Base.depwarn("`edge_sis_model` is deprecated: use `sis_model(; τ, γ)`, which returns a " *
                 "ContactModel (`DiseaseProgression(sis_model())` gives the legacy type).",
                 :edge_sis_model)
    return _legacy_sis_model(; kwargs...)
end
"""
    edge_sirs_model(; kwargs...)   # deprecated

Deprecated: the EdgeBasedModels 0.1 factory returning the legacy [`DiseaseProgression`](@ref);
use `sirs_model(; τ, γ, ε)` (a `ContactModel`); see [`edge_sir_model`](@ref).
"""
function edge_sirs_model(; kwargs...)
    Base.depwarn("`edge_sirs_model` is deprecated: use `sirs_model(; τ, γ, ε)`, which returns a " *
                 "ContactModel (`DiseaseProgression(sirs_model())` gives the legacy type).",
                 :edge_sirs_model)
    return _legacy_sirs_model(; kwargs...)
end

# --- Catalyst -------------------------------------------------------------------------------------

"""
    progression_from_catalyst(rn; susceptible = :S, transmission_rates = Dict(), entry = nothing,
                              merge_duplicates = true)

Deprecated: use `contact_model(rn)` (NetworkEpiCore's Catalyst front end, loaded with Catalyst),
which keeps branching, validates rate laws and reads frequency-dependent rates. This shim returns
the legacy [`DiseaseProgression`](@ref) of `contact_model(rn)`, with symbolic rates as before; the
parameter defaults of the network (`@parameters τ = 0.3`) stay attached to those rates, so the
model solves without `p`, as in 0.1. A non-zero entry `transmission_rates[X]` sets the per-contact
rate of stage X, overriding the rate that the reactions give it (as in 0.1); a stage without a
non-zero entry keeps the rate of its reactions (0 when no reaction makes it infectious).
Branching at infection, which the old function dropped silently, is now an error, and an `entry`
keyword that disagrees with the reaction network is overridden with a warning. Duplicate
reactions (two `S + I --> 2I` at β₁ and β₂) have their rates added, as in 0.1
(`merge_duplicates = true`, forwarded to `contact_model`; `contact_model(rn)` itself refuses
them unless given `merge_duplicates = true`).
"""
function progression_from_catalyst(rn; susceptible::Symbol = :S,
                                   transmission_rates = Dict{Symbol, Any}(),
                                   entry::Union{Nothing, Symbol} = nothing,
                                   merge_duplicates::Bool = true)
    Base.depwarn("`progression_from_catalyst(rn)` is deprecated: use `contact_model(rn)` and pass " *
                 "the ContactModel to edge_based (or DiseaseProgression(contact_model(rn)) for " *
                 "the legacy type).", :progression_from_catalyst)
    cm = contact_model(rn; merge_duplicates)
    for c in contacts(cm)
        c.recipient === susceptible || throw(ArgumentError(
            "progression_from_catalyst: the transmission reaction `$(c.name)` must have the " *
            "susceptible species `$(susceptible)` as its recipient; got $(c.recipient)"))
    end
    entries = unique(Symbol[c.product for c in contacts(cm)])
    length(entries) <= 1 || throw(ArgumentError(
        "progression_from_catalyst: infection has several entry states ($(join(entries, ", "))); " *
        "the old function silently dropped this branching and the legacy DiseaseProgression " *
        "cannot express it. Use contact_model(rn) with edge_based instead"))
    if !isempty(entries) && entry !== nothing && entry !== only(entries)
        @warn "progression_from_catalyst: entry = :$entry disagrees with the reaction network, " *
              "whose transmission produces :$(only(entries)); the old function used :$entry, " *
              "the result now follows the network"
    end
    defaults = parameter_defaults(cm)
    rates = Dict{Symbol,Any}(c.infector => _symbolic_rate(c.rate, defaults) for c in contacts(cm))
    stages = DiseaseStage[]
    for X in species_names(cm)
        X === susceptible && continue
        given = get(transmission_rates, X, 0)
        rate = !_is_zero_rate(given) ? given : get(rates, X, 0)
        push!(stages, DiseaseStage(X; transmission_rate = rate))
    end
    any(t -> t.to === nothing, node_transitions(cm)) && throw(ArgumentError(
        "progression_from_catalyst: the reaction network removes nodes (X → ∅), which the legacy " *
        "DiseaseProgression cannot express; use contact_model(rn)"))
    transitions = DiseaseTransition[DiseaseTransition(t.from, t.to, _symbolic_rate(t.rate, defaults))
                                    for t in node_transitions(cm)]
    return DiseaseProgression(stages, transitions; susceptible,
                              entry = isempty(entries) ? entry : only(entries))
end

# The 0.1 function returned Catalyst's (unwrapped) symbolic rates, whose parameters carry the
# network's defaults; NetworkEpiCore's front end stores Symbols and Exprs and the defaults by name,
# which `_lift_rate` turns back into the same parameters with the same defaults.
_symbolic_rate(r::Union{Symbol,Expr}, defaults::AbstractDict) = Symbolics.unwrap(_lift_rate(r; defaults))
_symbolic_rate(r, defaults::AbstractDict) = r

# --- Argument order of compartment & co. ---------------------------------------------------------

# The legacy EBM order (sol, sys, X). The solution is typed so that this method is not ambiguous
# with the canonical (sys::EdgeModelSystem, sol, X) (WP5 note; design §A.8).
function compartment(sol::SciMLBase.AbstractTimeseriesSolution, system::EdgeModelSystem, state::Symbol)
    Base.depwarn("`compartment(sol, sys, X)` is deprecated: use `compartment(sys, sol, X)` " *
                 "(the NetworkEpiCore argument order).", :compartment)
    return compartment(system, sol, state)
end
function compartments(sol::SciMLBase.AbstractTimeseriesSolution, system::EdgeModelSystem,
                      states::AbstractVector{Symbol})
    Base.depwarn("`compartments(sol, sys, Xs)` is deprecated: use `compartments(sys, sol, Xs)`.",
                 :compartments)
    return compartments(system, sol, states)
end
function population_fraction(sol::SciMLBase.AbstractTimeseriesSolution, system::EdgeModelSystem,
                             state::Symbol)
    Base.depwarn("`population_fraction(sol, sys, X)` is deprecated: use " *
                 "`population_fraction(sys, sol, X)`.", :population_fraction)
    return population_fraction(system, sol, state)
end
