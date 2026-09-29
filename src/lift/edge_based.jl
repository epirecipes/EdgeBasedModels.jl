# Owner: WP14 → WP29 (DESIGN_NetworkEpiCore.md §A.3, §G.1 "dispatch-based replacement").
#
# The verb `edge_based(model, net)` and the observation API of lowered systems.
#
# - `edge_based(model, net::NetworkDescriptor)` converts any model through `contact_model` (a
#   Catalyst or ModelingToolkit model, a legacy DiseaseProgression, …).
# - Each descriptor has its own method, in the file of its lift: ConfigurationNetwork
#   (lift/configuration.jl), WellMixed (lift/wellmixed.jl), MultitypeNetwork (lift/multitype.jl,
#   which hands models with shared species on `unstructured(net, st)` to lift/heterogeneous.jl),
#   ClusteredNetwork (lift/clustered.jl), DynamicNetwork (lift/dynamic.jl, lift/dormant.jl),
#   MultiplexNetwork (lift/multiplex.jl), DegreeCorrelatedNetwork (lift/correlated.jl) and
#   MFSHNetwork (lift/mfsh.jl). All of them build the system with the per-reaction assembler
#   (lift/assembler.jl), so every system records `metadata[:kind] = :assembled`.
# - `edge_based(cm::ContactModel, net::NetworkDescriptor)` is the fallback for a descriptor
#   without a lift: it checks admissibility (which refuses `ExplicitGraph`) and throws.
#   (EdgeBasedModels 0.1's builders, which this fallback lowered onto while the assembler was
#   being written, are gone: WP29.)

export edge_based

"""
    edge_based(model, net::NetworkDescriptor; name = :edge_based_model, form = :expanded) -> EdgeModelSystem
    edge_based(model, net::ConfigurationNetwork, st::Strata; kw...)      # heterogeneous susceptibility
    edge_based(sc::Scenario; kw...)

The edge-based (Miller–Slim–Volz) ODE model of `model` on the network `net`: the lift of the
reaction network to its exact large-N limit on a configuration-model random graph. `model` is a
NetworkEpiCore `ContactModel` or anything `contact_model` accepts (a Catalyst `ReactionSystem`, a
ModelingToolkit `System`, a legacy `DiseaseProgression`); rates are converted to per-contact
rates with `per_contact_rates(cm, net)`, and Symbol rates become parameters (solve with
`p = Dict(:τ => …)`). The model's `parameter_defaults` (for example Catalyst's
`@parameters τ = 0.3`) are kept: `solve_epidemic` uses them for the parameters `p` does not give
(see [`parameter_defaults`](@ref)`(sys)`), and the lifted parameters carry them as
ModelingToolkit defaults.

The lift is strictly partial: it requires `require_admissible(cm, :edge_based; network = net)`
(no reaction may produce a susceptible class, so SIS and SIRS are refused with an
`AdmissibilityError` that names the back ends that accept them). Within that class every
reaction contributes its own terms (design §D.4): branching at infection, several infectors,
exits from the susceptible class (vaccination, through the survival factor ξ) and removals
(`X → ∅`, to the absorbing sink `:removed`, §J.2) are lifted exactly, and a `:cumulative`
accumulator records the fraction ever infected (§J.8). The descriptors, each documented at its
method:

- `ConfigurationNetwork(d)` with any degree distribution; `form = :compact` gives Miller's
  two-equation form of SIR-shaped models (M9);
- `WellMixed(κ)` (the mass-action image, M1);
- `MultitypeNetwork` (`sbm_network`, `unstructured`) with stratified models (Miller & Volz 2013
  §3.3), and on `unstructured(net, st)` with shared species: heterogeneous susceptibility, as
  `edge_based(model, net, st)`;
- `ClusteredNetwork` (Volz et al. 2011, triangle pair states);
- `DynamicNetwork(base, NeighbourExchange(η))` (dynamic fixed degree, Miller–Slim–Volz) and
  `DynamicNetwork(base, DormantContacts(η₁, η₂))`;
- `MultiplexNetwork` with layer-labelled contacts (`Contact(...; layer)`);
- `DegreeCorrelatedNetwork` (degree classes, Miller & Volz 2013) and `MFSHNetwork`.

`ExplicitGraph` is not an edge-based object (use `ConfigurationNetwork(EmpiricalDegree(g))` or
NodeBasedModels' individual level). The scenario form lifts `sc.model` on `sc.network`; solve it
with `solve_epidemic(sys, sc)`.

```julia
sys = edge_based(sir_model(), ConfigurationNetwork(PoissonDegree(5.0)))
sol = solve_epidemic(sys; p = Dict(:τ => 0.3, :γ => 0.1), initial = SeedFraction(:I => 1e-3),
                     tspan = (0.0, 30.0))
```
"""
function edge_based end

edge_based(model, net::NetworkDescriptor; kw...) = edge_based(contact_model(model), net; kw...)
edge_based(sc::Scenario; kw...) = edge_based(sc.model, sc.network; kw...)

function edge_based(cm::ContactModel, net::NetworkDescriptor; kw...)
    require_admissible(cm, :edge_based; network = net)
    throw(ArgumentError(
        "$(_lift_context(cm, net)): EdgeBasedModels has no edge-based lift onto a " *
        "$(nameof(typeof(net))); the lifted descriptors are ConfigurationNetwork, WellMixed, " *
        "MultitypeNetwork, ClusteredNetwork, DynamicNetwork, MultiplexNetwork, " *
        "DegreeCorrelatedNetwork and MFSHNetwork (NodeBasedModels and NetworkOutbreaks accept other " *
        "networks)"))
end

_lift_context(cm::ContactModel, net) = "edge_based(:$(cm.name), $(nameof(typeof(net))))"

"""
    parameter_defaults(sys::EdgeModelSystem) -> Dict{Symbol,Float64}

The default parameter values of an edge-based system, by name: the `parameter_defaults` of the
model it was lowered from (Catalyst or ModelingToolkit defaults, or defaults carried by the
symbolic rates of a legacy progression). [`solve_epidemic`](@ref) uses them for the parameters
that `p` does not give, as NetworkEpiCore's `instantiate` and NodeBasedModels do; `p` takes
precedence. Empty for a system without defaults.
"""
function NetworkEpiCore.parameter_defaults(sys::EdgeModelSystem)
    md = sys.metadata
    defaults = Dict{Symbol,Float64}()
    model = get(md, :model, nothing)
    model isa ContactModel && merge!(defaults, parameter_defaults(model))
    merge!(defaults, get(md, :parameter_defaults, _NO_DEFAULTS))
    return defaults
end

# --- Parameters for solve_epidemic (builders.jl) ------------------------------------------------

# Parameter values given by name (or by symbolic parameter), merged into the operating point,
# after the system's parameter defaults (`parameter_defaults(sys)`) for the parameters that
# neither `init` nor `p` sets: p > init > defaults, the NetworkEpiCore semantics of `instantiate`.
function _with_parameter_values(sys::EdgeModelSystem, init, p)
    defaults = parameter_defaults(sys)
    (p === nothing && isempty(defaults)) && return init
    params = ModelingToolkit.parameters(sys.system)
    byname = Dict{Symbol,Any}(Symbol(Symbolics.getname(x)) => x for x in params)
    seeds = Set{Symbol}(Symbol(Symbolics.getname(x)) for x in _seed_parameters(sys))
    op = Dict{Any,Any}(init)
    given = Set{Symbol}(_pname(k) for k in keys(op))
    for (name, v) in defaults
        (haskey(byname, name) && !(name in given) && !(name in seeds)) && (op[byname[name]] = v)
    end
    p === nothing && return op
    for (k, v) in pairs(p)
        name = k isa Symbol ? k : Symbol(Symbolics.getname(k))
        name in seeds && throw(ArgumentError(
            "solve_epidemic: $name is a seed parameter of the system; set the seeds with " *
            "`initial` (or `seed_fraction` in default_initial_conditions), not with p"))
        haskey(byname, name) || throw(ArgumentError(
            "solve_epidemic: the system has no parameter named $name (its parameters: " *
            "$(join(sort!(collect(keys(byname))), ", ")))"))
        op[byname[name]] = v
    end
    return op
end

# The seed parameters of a system: the `seed_<X>` parameters (`:seed_params`, §A.3; the
# heterogeneous lift records its q_<s> there, which `initial` sets as well).
_seed_parameters(sys::EdgeModelSystem) = collect(values(get(sys.metadata, :seed_params, Dict{Symbol,Any}())))

"""
    solve_epidemic(sys::EdgeModelSystem, sc::Scenario; kwargs...)

Solve `sys` with the parameters, seeding, time span and save grid of the scenario `sc`
(`p = sc.params`, `initial = sc.initial`, `tspan = sc.tspan`, `saveat = sc.tgrid`). As in the
keyword form, a parameter that neither `p` nor `init` sets takes its value from
[`parameter_defaults`](@ref)`(sys)` (the defaults of the lowered model), and `p` takes precedence.
"""
solve_epidemic(sys::EdgeModelSystem, sc::Scenario; kwargs...) =
    solve_epidemic(sys; p = sc.params, initial = sc.initial, tspan = sc.tspan, saveat = sc.tgrid,
                   kwargs...)

# --- Observing solutions (the NetworkEpiCore argument order is (sys, sol, X)) ----------------------

"""
    compartment(sys::EdgeModelSystem, sol, X::Symbol) -> Vector

The time series of `X` in a solution of `sys`: an observable (`:S`, `:I`, `:φ_S`, …) or a
variable (`:θ`, `:φ_I`, `:pop_I`, `:cumulative`, `:R`, …); observables win on a name clash. A
species of the model that is neither (such as `:E`) is its population `pop_<X>` (verified issue
E21). The legacy `(sol, sys, X)` order is deprecated.

`:I` is the legacy observable, the fraction in all transmitting stages: for SEAIR it is
`pop_A + pop_I`. The fraction in the stage named I is `compartment(sys, sol, :pop_I)`, which is
also what [`model_curves`](@ref)`(sys, sol)` reports as `:I` (its `:infectious` curve is the
legacy `:I`).
"""
function compartment(system::EdgeModelSystem, sol, state::Symbol)
    if haskey(system.observables, state)
        return sol[system.observables[state]]
    elseif haskey(system.variables, state)
        return sol[system.variables[state]]
    end
    pop = Symbol(:pop_, state)
    haskey(system.variables, pop) && _is_model_species(system, state) && return sol[system.variables[pop]]
    throw(ArgumentError("unknown compartment or observable: $state"))
end

function _is_model_species(sys::EdgeModelSystem, X::Symbol)
    model = get(sys.metadata, :model, nothing)
    return model isa ContactModel && (X in species_names(model) || X in get(sys.metadata, :sinks, Symbol[]))
end

"""
    compartments(sys::EdgeModelSystem, sol, Xs::AbstractVector{Symbol}) -> Dict{Symbol,Vector}

Several compartments at once (see [`compartment`](@ref)).
"""
compartments(system::EdgeModelSystem, sol, states::AbstractVector{Symbol}) =
    Dict(state => compartment(system, sol, state) for state in states)

"""
    population_fraction(sys::EdgeModelSystem, sol, X::Symbol) -> Vector

The fraction of the population in `X` (as [`compartment`](@ref) for edge-based systems).
"""
population_fraction(system::EdgeModelSystem, sol, state::Symbol) = compartment(system, sol, state)

"""
    model_curves(sys::EdgeModelSystem, sol; t = sol.t, label = "edge-based") -> ModelCurves

The curves of a solved edge-based system on the grid `t`, as a NetworkEpiCore `ModelCurves` with
representation `:edge_based`: one curve per species of the lowered model (each susceptible
class's node fraction, then pop_X for every other species), `:infectious` (the fraction in
transmitting stages) and `:cumulative` (the fraction ever infected, including the seeds, §J.8).
`compare(summary, curves)` and the plot recipes accept the result. A system that records no model
gives its observables by name instead.
"""
function model_curves(sys::EdgeModelSystem, sol; t = sol.t, label::AbstractString = "edge-based")
    tt = collect(Float64, t)
    values = Dict{Symbol,Vector{Float64}}()
    model = get(sys.metadata, :model, nothing)
    if model === nothing
        for (k, var) in sys.observables
            values[k] = _curve(sol, var, tt)
        end
    else
        for X in species_names(model)
            var = _species_variable(sys, X)
            var === nothing || (values[X] = _curve(sol, var, tt))
        end
    end
    haskey(sys.observables, :I) && (values[:infectious] = _curve(sol, sys.observables[:I], tt))
    acc = get(sys.observables, :cumulative, get(sys.variables, :cumulative, nothing))
    acc === nothing || (values[:cumulative] = _curve(sol, acc, tt))
    return ModelCurves(tt, values; label, representation = :edge_based)
end

# The variable of species X: a susceptible class is its node-S observable, emitted under the
# species' own name (and as `:S` when no species owns that name, E26); every other species is
# `pop_X`.
function _species_variable(sys::EdgeModelSystem, X::Symbol)
    sus = get(sys.metadata, :susceptible, :S)
    if X === sus || (sus isa AbstractVector && X in sus)
        haskey(sys.observables, X) && return sys.observables[X]
        return get(sys.observables, :S, nothing)
    end
    pop = Symbol(:pop_, X)
    haskey(sys.variables, pop) && return sys.variables[pop]
    haskey(sys.observables, X) && return sys.observables[X]
    return get(sys.variables, X, nothing)
end

_curve(sol, var, t::Vector{Float64}) = Float64[sol(ti; idxs = var) for ti in t]
