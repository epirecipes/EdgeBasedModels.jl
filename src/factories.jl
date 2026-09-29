# Owner: WP14 → WP29 (DESIGN_NetworkEpiCore.md §A.6, §A.7; work package in §G.2).
#
# The factories keep their 0.1 positional signatures and are one-liners over `edge_based`
# (src/lift/edge_based.jl): the second argument is the per-contact rate, which 0.1 called β and
# the documentation now calls τ. Symbol rates (the defaults of `sir_model()`, or
# `build_sir(pgf, :τ, :γ)`) become ModelingToolkit parameters in one place, `_lift_rate`
# (src/compat.jl), which fixes verified issue E10.
#
# The legacy model types keep their `build_edge_system` entry points here, and none of them
# reaches a legacy builder (there are none left, WP29): the static and clustered models forward
# to `edge_based`, the multitype model forwards (with a deprecation warning) to the multitype
# lift of its stratified model, and the dynamic model, whose 0.1 builder was not the model it
# claimed to be (verified issues E05–E07), throws a migration error.

_net(d::DegreePGF) = ConfigurationNetwork(d)
_net(d::DegreeDistribution) = ConfigurationNetwork(d)
_net(n::NetworkDescriptor) = n
_net(g::ClusteredPGF) = ClusteredNetwork(g)
_net(x) = throw(ArgumentError(
    "expected a network: a DegreePGF, a NetworkEpiCore DegreeDistribution (e.g. PoissonDegree(5)) " *
    "or a NetworkDescriptor; got $(typeof(x))"))

"""
    build_sir(d, τ, γ; name = :sir_ebm, form = :expanded) -> EdgeModelSystem

The edge-based SIR model with per-contact rate `τ` and recovery rate `γ` on the network `d`: a
legacy [`DegreePGF`](@ref), a NetworkEpiCore degree distribution (`PoissonDegree(5)`), or a
`NetworkDescriptor`. Equivalent to `edge_based(sir_model(; τ, γ), ConfigurationNetwork(d);
name, form)`. Rates may be numbers, Symbols (then parameters, e.g. `build_sir(PoissonDegree(5),
:τ, :γ)` solved with `p = Dict(:τ => 1/6, :γ => 1/4)`), expressions or symbolic parameters.
`form = :compact` gives Miller's two-equation form.
"""
build_sir(d, τ, γ; name::Symbol = :sir_ebm, form::Symbol = :expanded) =
    edge_based(sir_model(; τ, γ), _net(d); name, form)

"""
    build_seir(d, σ, τ, γ; name = :seir_ebm, form = :expanded) -> EdgeModelSystem

The edge-based SEIR model (latency rate `σ`, per-contact rate `τ`, recovery rate `γ`) on the
network `d`; equivalent to `edge_based(seir_model(; τ, σ, γ), ConfigurationNetwork(d); name,
form)`. See [`build_sir`](@ref).
"""
build_seir(d, σ, τ, γ; name::Symbol = :seir_ebm, form::Symbol = :expanded) =
    edge_based(seir_model(; τ, σ, γ), _net(d); name, form)

"""
    build_clustered_sir(g, τ, γ; name = :clustered_sir) -> EdgeModelSystem

The clustered (triangle) edge-based SIR model on `g`, a `ClusteredNetwork` or a legacy
[`ClusteredPGF`](@ref); equivalent to `edge_based(sir_model(; τ, γ), ClusteredNetwork(g))`. A
`ClusteredPGF` without `ClusteredDegree` provenance is built by the legacy clustered builder
directly.
"""
build_clustered_sir(g::Union{ClusteredPGF,ClusteredNetwork}, τ, γ; name::Symbol = :clustered_sir) =
    _clustered_factory(sir_model(; τ, γ), g, name)

"""
    build_clustered_seir(g, σ, τ, γ; name = :clustered_seir) -> EdgeModelSystem

The clustered edge-based SEIR model on `g` (see [`build_clustered_sir`](@ref)).
"""
build_clustered_seir(g::Union{ClusteredPGF,ClusteredNetwork}, σ, τ, γ; name::Symbol = :clustered_seir) =
    _clustered_factory(seir_model(; τ, σ, γ), g, name)

_clustered_factory(cm::ContactModel, g::ClusteredNetwork, name::Symbol) = edge_based(cm, g; name)
_clustered_factory(cm::ContactModel, g::ClusteredPGF, name::Symbol) =
    edge_based(cm, _clustered_network(g); name)

# The clustered network of a legacy clustered PGF. The 0.1 clustered builder (which was not the
# Volz et al. 2011 model, verified issue E02) is gone, so a PGF without `ClusteredDegree`
# provenance can no longer be lowered.
function _clustered_network(g::ClusteredPGF)
    g.joint === nothing && throw(ArgumentError(
        "this ClusteredPGF has no ClusteredDegree provenance, so it cannot be lowered: the 0.1 " *
        "clustered builder that accepted it did not implement the Volz et al. (2011) model " *
        "(verified issue E02) and is removed. Build the PGF with clustered_pgf(joint_probs) or " *
        "clustered_poisson_pgf(κ_single, κ_triangle), or use " *
        "edge_based(model, ClusteredNetwork(ClusteredDegree(…)))"))
    return ClusteredNetwork(g.joint)
end

# `build_sis` is declared here so that the `generate_sis` alias of analysis.jl binds it; its only
# method is the migration error of src/deprecated.jl (verified issue E01).
function build_sis end

"""
    build_edge_system(model; name, form = :expanded) -> EdgeModelSystem

Lower a legacy (0.1) model object to an edge-based ODE system. Every case is the per-reaction
lift of [`edge_based`](@ref), so the system is the same as the one `edge_based` builds (its
variables are named `seed_<X>`, `pop_<X>`, …; verified issue E26):

- `StaticConfigurationModel(pgf, progression)`: `edge_based(contact_model(model),
  ConfigurationNetwork(pgf); name, form)`. An SIS progression is an error (it has no exact
  edge-based model; verified issue E01), and a model that `edge_based` refuses (SIRS, …) throws
  an `ArgumentError` with the admissibility report.
- `ClusteredConfigurationModel`: `edge_based(contact_model(model), ClusteredNetwork(pgf))`, the
  Volz et al. (2011) model (verified issue E02); the PGF must record its `ClusteredDegree`.
- `MultiTypeConfigurationModel` (deprecated): the multitype lift of the stratified model, see
  `build_edge_system(::MultiTypeConfigurationModel)`.
- `DynamicConfigurationModel`: an error naming the replacements (verified issues E05–E07).

Symbol rates become parameters in every case (verified issue E10).
"""
function build_edge_system(model::StaticConfigurationModel;
                           name::Symbol = :edge_based_model,
                           form::Symbol = :expanded)
    form in (:compact, :expanded) || throw(ArgumentError("form must be :compact or :expanded, got :$form"))
    _is_sis_progression(model.progression) && throw(ArgumentError(_SIS_MESSAGE))
    try
        return edge_based(contact_model(model), ConfigurationNetwork(model.pgf); name, form)
    catch err
        # The legacy entry point reported unsupported progressions as ArgumentErrors.
        err isa AdmissibilityError && throw(ArgumentError(sprint(showerror, err)))
        rethrow()
    end
end

function build_edge_system(model::ClusteredConfigurationModel; name::Symbol = :clustered_ebm)
    return _clustered_factory(contact_model(model), model.pgf, name)
end

"""
    build_edge_system(model::DynamicConfigurationModel)   # removed: throws

Removed in EdgeBasedModels 0.2 (verified issues E05, E06, E07): the 0.1 builder was not the
Miller–Slim–Volz dynamic fixed-degree model (a Volz–Meyers equation with a typo, no seed factor,
η₁ unused, every progression built as SIR). The `ArgumentError` (`_dynamic_configuration_error`,
src/lift/dynamic.jl) names the replacements,
`edge_based(contact_model(model), DynamicNetwork(ConfigurationNetwork(pgf), NeighbourExchange(η₂)))`
and the dormant-contact network `DynamicNetwork(…, DormantContacts(η₁, η₂))`.
"""
build_edge_system(model::DynamicConfigurationModel; kw...) = throw(_dynamic_configuration_error(model))

"""
    build_edge_system(model::MultiTypeConfigurationModel; name = :multitype_ebm)   # deprecated

Deprecated: the legacy multitype EBCM, forwarded to the multitype lift
`edge_based(stratify(contact_model(model.progression), st; contact_rates), net; name)`
(Miller & Volz 2013 §3.3), where

- `st` has the legacy types as strata and `net` is the `MultitypeNetwork` of the PGFs'
  provenance degree laws (`multivariate_poisson_pgf` and `independent_pgf` record them; a PGF
  without provenance is an error);
- the type sizes, which the legacy model did not have, are inferred from the edge reciprocity
  n_a E[k_{a→b}] = n_b E[k_{b→a}] of numeric mean degrees (equal sizes within a connected set
  of types when a mean is symbolic, or between unconnected sets); the within-type dynamics do
  not depend on them;
- the contact-matrix entry (b, a) (infector type b, recipient type a) multiplies the per-contact
  rates of infections of type a by type b (verified issue E32(a): a rate multiplier, not a
  mixing matrix).

The 0.1 seeding is kept: `default_initial_conditions(sys; seed_fraction = ρ)` seeds a fraction
ρ **of each type** in its entry state, i.e. `SeedFraction(:I_a => ρ·n_a, …)`. What changes
(MIGRATION.md) is the naming and the normalisation of the design (§A.3, §J.6): compartments are
fractions of **all** nodes (`pop_I_a` is n_a times the 0.1 within-type fraction; divide by n_a,
`sys.metadata[:network].sizes`, for the 0.1 value), and the variables are those of the multitype
lift (`θ_<a>_<b>`, `φ_<X>_<a>_<b>`, `pop_<X>_<a>`, the seed parameters `seed_<X>_<a>`).
"""
function build_edge_system(model::MultiTypeConfigurationModel; name::Symbol = :multitype_ebm)
    Base.depwarn("`build_edge_system(::MultiTypeConfigurationModel)` is deprecated: use " *
                 "`edge_based(stratify(cm, strata(types; sizes); contact_rates), " *
                 "MultitypeNetwork(types, sizes, degrees))`. Compartments are now fractions of " *
                 "all nodes (divide by the type size for the 0.1 within-type fraction).",
                 :build_edge_system)
    cm, net = _multitype_forward(model)
    sys = edge_based(cm, net; name)
    entry = model.progression.entry
    sizes = Dict(zip(net.types, net.sizes))
    # the 0.1 rule: a fraction ρ of every type starts in the entry state
    sys.metadata[:default_seed] = ρ -> SeedFraction(Pair{Symbol,Float64}[
        Symbol(entry, :_, a) => ρ * sizes[a] for a in model.types])
    return sys
end

# The stratified ContactModel and the MultitypeNetwork of a legacy multitype model.
function _multitype_forward(model::MultiTypeConfigurationModel)
    types = model.types
    degrees = Dict{Symbol,MultivariateDegree}()
    for a in types
        d = model.pgfs[a].distribution
        d === nothing && throw(ArgumentError(
            "build_edge_system(::MultiTypeConfigurationModel): the MultivariatePGF of type $(a) has " *
            "no provenance degree law, so it cannot be lowered onto a MultitypeNetwork; build it " *
            "with multivariate_poisson_pgf or independent_pgf, or use edge_based(stratify(cm, st), " *
            "MultitypeNetwork(types, sizes, degrees)) directly"))
        degrees[a] = d
    end
    sizes = _reciprocal_sizes(types, degrees)
    net = MultitypeNetwork(types, sizes, degrees; check_reciprocity = false)
    st = strata(types; sizes)
    cm = contact_model(model.progression)
    mult(b, a) = model.contact_matrix[(b, a)]          # (infector b, recipient a)
    rate(c, a, b) = (m = mult(b, a); _is_one(m) ? c.rate : rate_mul(m, c.rate))
    return stratify(cm, st; contact_rates = rate, name = Symbol(cm.name, :_multitype)), net
end

_is_one(x) = x isa Real && !(x isa Symbolics.Num) && isone(x)

# Type sizes n with n_a E[k_{a→b}] = n_b E[k_{b→a}], from the numeric mean degrees (edge
# reciprocity); equal sizes within a connected set of types whose means are symbolic, and equal
# total weight per connected set.
function _reciprocal_sizes(types::Vector{Symbol}, degrees::Dict{Symbol,MultivariateDegree})
    mean(a, b) = mean_degree(degrees[a], b)
    numeric(x) = x isa Real && !(x isa Symbolics.Num)
    w = Dict{Symbol,Float64}()
    components = Vector{Vector{Symbol}}()
    for root in types
        haskey(w, root) && continue
        w[root] = 1.0
        comp = [root]
        queue = [root]
        while !isempty(queue)
            a = popfirst!(queue)
            for b in types
                haskey(w, b) && continue
                kab, kba = mean(a, b), mean(b, a)
                linked = !(numeric(kab) && iszero(kab)) || !(numeric(kba) && iszero(kba))
                linked || continue
                w[b] = (numeric(kab) && numeric(kba) && kba > 0 && kab > 0) ? w[a] * kab / kba : w[a]
                push!(comp, b)
                push!(queue, b)
            end
        end
        push!(components, comp)
    end
    for comp in components
        total = sum(w[a] for a in comp)
        for a in comp
            w[a] = w[a] / total / length(components)
        end
    end
    return Float64[w[a] for a in types]
end
