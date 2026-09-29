# Owner: WP29 (DESIGN_NetworkEpiCore.md §A.3, §A.6, §A.7; work package in §G.2).
#
# The legacy (0.1) model types and the solve API of lowered systems. EdgeBasedModels 0.2 has no
# legacy builder: every system is built by the per-reaction assembler (src/lift/assembler.jl) or a
# descriptor lift that reuses it. What is left here:
#
# - the 0.1 model types `StaticConfigurationModel`, `DynamicConfigurationModel`,
#   `MultiTypeConfigurationModel` and `ClusteredConfigurationModel`, kept as inputs (their
#   `build_edge_system` entry points are in src/factories.jl: they forward to `edge_based`, or
#   throw a migration error where the 0.1 model was wrong);
# - small helpers on legacy PGFs and progressions that the legacy analysis functions use;
# - the legacy R₀ of the static and clustered model types (verified issues E04, E10, E14, E17);
# - `default_initial_conditions` and `solve_epidemic`, which dispatch on `metadata[:kind]`.

using ModelingToolkit: t_nounits, D_nounits, Equation, System, mtkcompile
using OrdinaryDiffEqDefault: ODEProblem, solve

"""
    StaticConfigurationModel(pgf::DegreePGF, progression::DiseaseProgression)

The legacy (0.1) static configuration-model EBCM: a degree PGF and a disease progression.
`build_edge_system(model)` is `edge_based(contact_model(model), ConfigurationNetwork(pgf))`; the
legacy analysis functions (`final_size`, `epidemic_probability`, `confidence_bands`,
`epidemic_threshold`, `basic_reproduction_number`, `disease_free_equilibrium`) accept it.
"""
struct StaticConfigurationModel
    pgf::DegreePGF
    progression::DiseaseProgression
end

"""
    DynamicConfigurationModel(pgf, progression, η₁, η₂)

The legacy (0.1) dynamic-network EBCM with edge formation rate η₁ and breaking rate η₂. Its
builder was not the Miller–Slim–Volz dynamic fixed-degree model (verified issues E05, E06, E07:
a Volz–Meyers equation with a typo, no seed factor q, η₁ unused and every model built as SIR), so
`build_edge_system(::DynamicConfigurationModel)` throws a migration error naming the replacement,
`edge_based(model, DynamicNetwork(ConfigurationNetwork(d), NeighbourExchange(η)))`. The type is
kept so that such code fails with that message and `contact_model(m)` still converts it.
"""
struct DynamicConfigurationModel
    pgf::DegreePGF
    progression::DiseaseProgression
    η₁  # edge formation rate
    η₂  # edge breaking rate
end

"""
    MultiTypeConfigurationModel(types, pgfs, progression, contact_matrix)

The legacy (0.1) multitype EBCM (use the keyword constructor): one [`MultivariatePGF`](@ref) per
node type, a disease progression shared by the types and per-(infector type, recipient type)
multipliers of the transmission rate. `build_edge_system` forwards it, with a deprecation warning,
to the multitype lift `edge_based(stratify(model, st; contact_rates), MultitypeNetwork(...))`.
"""
struct MultiTypeConfigurationModel
    types::Vector{Symbol}
    pgfs::Dict{Symbol, MultivariatePGF}
    progression::DiseaseProgression
    contact_matrix::Dict{Tuple{Symbol,Symbol}, Any}
end

"""
    ClusteredConfigurationModel(pgf::ClusteredPGF, progression)

The legacy (0.1) clustered EBCM: triangle degrees from the bivariate `pgf` and a disease
progression. `build_edge_system` is `edge_based(contact_model(model), ClusteredNetwork(pgf))`,
the Volz et al. (2011) model (verified issue E02); `basic_reproduction_number` is the
tree-of-triangles R₀ (E04).
"""
struct ClusteredConfigurationModel
    pgf::ClusteredPGF
    progression::DiseaseProgression
end

# --- Helpers on legacy PGFs and progressions (used by the legacy analysis functions) ------------

function _eval_pgf_deriv(pgf::DegreePGF, order::Integer, x)
    deriv = pgf_derivative(pgf, order)
    Symbolics.simplify(Symbolics.substitute(deriv, Dict(pgf.variable => x)))
end

function _maybe_to_float64(x)
    if x isa Symbolics.Num
        simplified = _cleanup_exp_zero(Symbolics.simplify(x))
        value = Symbolics.value(simplified)
        value isa Real && return Float64(value)

        isempty(Symbolics.get_variables(simplified)) || return nothing
        runtime_fn = Symbolics.build_function(simplified; expression = Val{false})
        runtime_fn = runtime_fn isa Tuple ? first(runtime_fn) : runtime_fn
        return Float64(runtime_fn())
    end
    return Float64(x)
end

function _to_float64(x)
    x isa Float64 && return x
    value = _maybe_to_float64(x)
    isnothing(value) &&
        error("Cannot convert symbolic expression with free variables to Float64: $x")
    return value
end

_is_zero_rate(rate) = isequal(rate, 0) || isequal(rate, 0.0)

function _is_sis_progression(prog::DiseaseProgression)
    length(prog.stages) == 1 || return false
    stage = only(prog.stages)
    !_is_zero_rate(stage.transmission_rate) || return false
    length(prog.transitions) == 1 || return false
    tr = only(prog.transitions)
    return tr.source == stage.name && tr.target == prog.susceptible
end

# --- R₀ of the legacy model types ----------------------------------------------------------------

"""
    basic_reproduction_number(model::StaticConfigurationModel)

R₀ = T·ψ''(1)/ψ'(1) of the legacy static model, where T is the probability that an infective
transmits along one given edge, from the absorbing chain of the whole progression (branching,
bypasses and revisited stages included; verified issue E14, where the 0.1 single-stage shortcut
gave 2.5 instead of 1.25 for a progression with an E → R bypass). Symbol and Expr rates become
parameters (E10), and the result is symbolic when a rate or the PGF is. A progression that
returns nodes to the susceptible class (SIS, SIRS, reinfection-counting lifts) is refused with an
`ArgumentError` (E17); a progression without a transmitting stage has R₀ = 0. For a lifted system
use `basic_reproduction_number(sys; p)`.
"""
function basic_reproduction_number(model::StaticConfigurationModel)
    prog = model.progression
    _require_sir_type_analysis(prog, "basic_reproduction_number")
    excess = Symbolics.simplify(_eval_pgf_deriv(model.pgf, 2, 1) / _eval_pgf_deriv(model.pgf, 1, 1))
    return Symbolics.simplify(_edge_transmissibility(prog) * excess)
end

"""
    basic_reproduction_number(model::ClusteredConfigurationModel; kind = :generation)

The tree-of-triangles R₀ of Volz et al. (2011) for the legacy clustered model (verified issue
E04, corrected fix: the 0.1 heuristic T·g_xx/g_x + 2T(1 + T)g_y/g_x gave 2.4375 instead of 2.0027
for κ_s = 1, κ_t = 2, τ = 0.6, γ = 1): `_clustered_reproduction_number(contact_model(model),
ClusteredNetwork(model.pgf); kind)`, see there (`kind = :clump` gives R_*). The clustered PGF
must record its `ClusteredDegree` (`clustered_pgf`, `clustered_poisson_pgf`).
"""
function basic_reproduction_number(model::ClusteredConfigurationModel; kind::Symbol = :generation)
    _require_sir_type_analysis(model.progression, "basic_reproduction_number")
    return _clustered_reproduction_number(contact_model(model), ClusteredNetwork(model.pgf); kind)
end

# --- Default initial conditions and solving ---------------------------------------------------------

"""
    default_initial_conditions(sys::EdgeModelSystem; initial = nothing, ε = 1e-3, seed_fraction = ε, N = nothing)

The initial state (and the seed parameter values) of an edge-based system: θ(0) = 1, and the
seeded fractions from `initial`, a NetworkEpiCore `SeedSpec` such as `SeedFraction(:I => 0.01)`
(fractions of all nodes, design §J.6; a `SeedCount` or `SeedNodes` needs the population size
`N`). Without `initial`, the unique entry state of the model is seeded with `seed_fraction`
(design §E.2); a model with several entry states needs `initial`. The susceptible fraction of
each node type is 1 − Σ_X seed_X within the type, so S(0) = 1 − ρ and φ_entry(0) = pop_entry(0)
= ρ for SIR seeded with ρ. The result is a `Dict` from the system's variables and seed parameters
to values, which `solve_epidemic(sys; init)` and `ODEProblem(sys.system, …)` accept. The method
dispatches on `sys.metadata[:kind]` (`:assembled` for every system of EdgeBasedModels 0.2).
"""
default_initial_conditions(model::EdgeModelSystem; kw...) =
    _default_initial_conditions(Val(_system_kind(model)), model; kw...)

# The kind of a lowered system (design §A.3): `:assembled` for the per-reaction assembler and the
# lifts that reuse it (every system of this version); a system built by hand records none.
_system_kind(sys::EdgeModelSystem) = get(sys.metadata, :kind, :unknown)

_default_initial_conditions(::Val{K}, model::EdgeModelSystem; kw...) where {K} =
    throw(ArgumentError("default_initial_conditions: no method for edge-based systems of kind :$K " *
                        "(build the system with edge_based)"))

"""
    solve_epidemic(sys::EdgeModelSystem; p = nothing, initial = nothing, tspan = (0.0, 100.0),
                   init = nothing, solver = nothing, kwargs...)
    solve_epidemic(sys::EdgeModelSystem, sc::Scenario; kwargs...)

Solve an edge-based system. `p` gives parameter values by name (a `Dict{Symbol}` or a
`NamedTuple`, e.g. `p = Dict(:τ => 0.3, :γ => 0.1)` for a model built with Symbol rates) or by
symbolic parameter; an unknown name is an error, and so is a seed parameter `seed_<X>` (set the
seeds with `initial`). A parameter that neither `p` nor `init` sets takes its value from
[`parameter_defaults`](@ref)`(sys)` (the defaults of the lowered model, e.g. Catalyst's
`@parameters τ = 0.3`): the precedence is p > init > defaults. The initial state is `init` (a full
operating point, e.g. from [`default_initial_conditions`](@ref)) or, when `init` is not given,
`default_initial_conditions(sys; initial)`. Other keywords (`saveat`, `reltol`, …) go to the ODE
solver; `solver` selects the algorithm (the default chooses one automatically). The scenario form
takes `p`, `initial`, `tspan` and `saveat` from the scenario. The method dispatches on
`sys.metadata[:kind]` like `default_initial_conditions`.
"""
solve_epidemic(system::EdgeModelSystem; kw...) = _solve_epidemic(Val(_system_kind(system)), system; kw...)

function _solve_epidemic(::Val, system::EdgeModelSystem;
                         p = nothing, initial = nothing,
                         tspan::Tuple{<:Real, <:Real} = (0.0, 100.0),
                         init = nothing,
                         solver = nothing,
                         kwargs...)
    if init === nothing
        init = default_initial_conditions(system; initial)
    elseif initial !== nothing
        throw(ArgumentError("solve_epidemic: pass either `init` or `initial`, not both"))
    end
    op = _with_parameter_values(system, init, p)
    prob = ODEProblem(system.system, op, (Float64(tspan[1]), Float64(tspan[2])))
    if isnothing(solver)
        return solve(prob; kwargs...)
    end
    return solve(prob, solver; kwargs...)
end
