using ModelingToolkit: t_nounits, D_nounits, Equation, System, mtkcompile
using OrdinaryDiffEqDefault: ODEProblem, solve

struct StaticConfigurationModel
    pgf::DegreePGF
    progression::DiseaseProgression
end

struct EdgeModelSystem
    system
    variables::Dict{Symbol, Any}
    observables::Dict{Symbol, Any}
    metadata::Dict{Symbol, Any}
end

EdgeModelSystem(system, variables::Dict{Symbol, Any}, observables::Dict{Symbol, Any}) =
    EdgeModelSystem(system, variables, observables, Dict{Symbol, Any}())

# --- Helpers for PGF evaluation ---

function _eval_pgf(pgf::DegreePGF, x)
    Symbolics.simplify(Symbolics.substitute(pgf.expression, Dict(pgf.variable => x)))
end

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

function _is_zero_rate(rate)
    isequal(rate, 0) || isequal(rate, 0.0)
end

function _transition_maps(prog::DiseaseProgression)
    incoming = Dict(s.name => DiseaseTransition[] for s in prog.stages)
    outgoing = Dict(s.name => DiseaseTransition[] for s in prog.stages)
    for tr in prog.transitions
        push!(incoming[tr.target], tr)
        push!(outgoing[tr.source], tr)
    end
    return incoming, outgoing
end

function _recovered_stages(prog::DiseaseProgression, outgoing)
    return [
        stage.name for stage in prog.stages
        if _is_zero_rate(stage.transmission_rate) && isempty(outgoing[stage.name])
    ]
end

function _sum_expr(terms::Vector{Any})
    return isempty(terms) ? 0 : foldl(+, terms)
end

function _sum_stage_populations(pop, stage_names)
    return Symbolics.simplify(_sum_expr(Any[pop[name] for name in stage_names]))
end

function _population_stage_equations(prog::DiseaseProgression, pop, incidence, incoming, outgoing, D)
    eqs = Equation[]
    for stage in prog.stages
        pop_var = pop[stage.name]

        inflow_terms = Any[]
        if stage.name == prog.entry
            push!(inflow_terms, incidence)
        end
        for tr in incoming[stage.name]
            push!(inflow_terms, tr.rate * pop[tr.source])
        end
        inflow = _sum_expr(inflow_terms)

        outflow_terms = Any[]
        for tr in outgoing[stage.name]
            push!(outflow_terms, tr.rate * pop_var)
        end
        outflow = _sum_expr(outflow_terms)

        push!(eqs, D(pop_var) ~ Symbolics.simplify(inflow - outflow))
    end
    return eqs
end

function _compact_form_supported(prog::DiseaseProgression)
    length(prog.stages) == 2 || return false

    incoming, outgoing = _transition_maps(prog)
    recovered = _recovered_stages(prog, outgoing)
    length(recovered) == 1 || return false
    prog.entry in recovered && return false
    isempty(incoming[prog.entry]) || return false

    entry_idx = findfirst(s -> s.name == prog.entry, prog.stages)
    isnothing(entry_idx) && return false
    entry_stage = prog.stages[entry_idx]
    !_is_zero_rate(entry_stage.transmission_rate) || return false

    entry_targets = Set(tr.target for tr in outgoing[prog.entry])
    return entry_targets == Set(recovered)
end

function _require_compact_form_supported(prog::DiseaseProgression)
    _compact_form_supported(prog) && return nothing
    throw(ArgumentError(
        "compact form only supports SIR-like progressions with a single infectious " *
        "entry stage and a single recovered sink; use form = :expanded for multi-stage models",
    ))
end

function _default_seed_metadata(entry_var, susceptible_expr)
    return Dict{Symbol, Any}(
        :seed_groups => Any[(; entry = entry_var, susceptible_expr = susceptible_expr)],
    )
end

# --- Convenience constructors ---

function build_sir(pgf::DegreePGF, β, γ;
                   name::Symbol = :sir_ebm,
                   form::Symbol = :expanded)
    progression = DiseaseProgression(
        [
            DiseaseStage(:I; transmission_rate = β),
            DiseaseStage(:R; transmission_rate = 0),
        ],
        [DiseaseTransition(:I, :R, γ)];
        entry = :I,
    )
    return build_edge_system(
        StaticConfigurationModel(pgf, progression);
        name = name,
        form = form,
    )
end

function build_seir(pgf::DegreePGF, σ, β, γ;
                    name::Symbol = :seir_ebm,
                    form::Symbol = :expanded)
    progression = DiseaseProgression(
        [
            DiseaseStage(:E; transmission_rate = 0),
            DiseaseStage(:I; transmission_rate = β),
            DiseaseStage(:R; transmission_rate = 0),
        ],
        [
            DiseaseTransition(:E, :I, σ),
            DiseaseTransition(:I, :R, γ),
        ];
        entry = :E,
    )
    return build_edge_system(
        StaticConfigurationModel(pgf, progression);
        name = name,
        form = form,
    )
end

function build_sis(pgf::DegreePGF, β, γ;
                   name::Symbol = :sis_ebm)
    # SIS: after recovery, the neighbor returns to susceptible. In the EBCM framework,
    # this means φ_I flows back to φ_S rather than to a terminal φ_R. We model this
    # with a single infectious stage where recovery resets the edge to susceptible.
    # The φ_S equation is still algebraic, so we add a "waning" term to the θ equation:
    # dθ/dt = -β·φ_I + γ·(1 - θ)  (recovery restores edges)
    # This uses the compact formulation directly.
    t = t_nounits
    D = D_nounits

    @variables θ(t) S(t) I(t)

    ψ_θ = _eval_pgf(pgf, θ)

    ψ_prime_θ = _eval_pgf_deriv(pgf, 1, θ)
    ψ_prime_1 = _eval_pgf_deriv(pgf, 1, 1)
    ψ_double_θ = _eval_pgf_deriv(pgf, 2, θ)

    phi_S = Symbolics.simplify(ψ_prime_θ / ψ_prime_1)
    phi_I = Symbolics.simplify(θ - phi_S)

    # SIS: θ̇ = −β·φ_I (transmission) + γ·(θ − φ_S) (recovery restores edges)
    # Since φ_I = θ - φ_S, recovery of φ_I returns it to φ_S, effectively restoring θ.
    θ_dot = Symbolics.simplify(-β * phi_I + γ * (1 - θ))

    eqs = Equation[
        D(θ) ~ θ_dot,
        S ~ ψ_θ,
        I ~ 1 - S,
    ]

    sys = System(eqs, t; name = name)
    simplified = mtkcompile(sys)

    variables = Dict{Symbol, Any}(:θ => θ)
    observables = Dict{Symbol, Any}(:S => S, :I => I, :φ_S => phi_S, :φ_I => phi_I)

    return EdgeModelSystem(simplified, variables, observables)
end

function _is_sis_progression(prog::DiseaseProgression)
    length(prog.stages) == 1 || return false
    stage = only(prog.stages)
    !_is_zero_rate(stage.transmission_rate) || return false
    length(prog.transitions) == 1 || return false
    tr = only(prog.transitions)
    return tr.source == stage.name && tr.target == prog.susceptible
end

# --- Main builder ---

function build_edge_system(model::StaticConfigurationModel;
                           name::Symbol = :edge_based_model,
                           form::Symbol = :expanded)
    if _is_sis_progression(model.progression)
        stage = only(model.progression.stages)
        γ_val = only(model.progression.transitions).rate
        return build_sis(model.pgf, stage.transmission_rate, γ_val; name = name)
    end
    if form === :compact
        _require_compact_form_supported(model.progression)
        return _build_compact(model; name = name)
    elseif form === :expanded
        return _build_expanded(model; name = name)
    else
        throw(ArgumentError("form must be :compact or :expanded, got :$form"))
    end
end

# --- Compact Miller formulation ---
# Two ODEs (θ, R) plus algebraic S, I.
# From Miller (2011): θ̇ = −βθ + β·ψ'(θ)/ψ'(1) + γ(1−θ)

function _build_compact(model::StaticConfigurationModel; name::Symbol)
    prog = model.progression
    t = t_nounits
    D = D_nounits

    entry_idx = findfirst(s -> s.name == prog.entry, prog.stages)
    isnothing(entry_idx) && throw(ArgumentError("entry stage not found"))
    β_val = prog.stages[entry_idx].transmission_rate

    recovery_transitions = [tr for tr in prog.transitions if tr.source == prog.entry]
    isempty(recovery_transitions) &&
        throw(ArgumentError("compact form requires at least one recovery transition"))
    γ_val = sum(tr.rate for tr in recovery_transitions)

    @variables θ(t) R(t) S(t) I(t)

    ψ_θ = _eval_pgf(model.pgf, θ)
    ψ_prime_θ = _eval_pgf_deriv(model.pgf, 1, θ)
    ψ_prime_1 = _eval_pgf_deriv(model.pgf, 1, 1)

    # Miller compact equation: θ̇ = −βθ + β·ψ'(θ)/ψ'(1) + γ(1−θ)
    θ_dot = Symbolics.simplify(-β_val * θ + β_val * (ψ_prime_θ / ψ_prime_1) + γ_val * (1 - θ))
    R_dot = Symbolics.simplify(γ_val * (1 - ψ_θ - R))

    eqs = Equation[
        D(θ) ~ θ_dot,
        D(R) ~ R_dot,
        S ~ ψ_θ,
        I ~ 1 - S - R,
    ]

    sys = System(eqs, t; name = name)
    simplified = mtkcompile(sys)

    variables = Dict{Symbol, Any}(:θ => θ, :R => R)
    observables = Dict{Symbol, Any}(:S => S, :I => I, :ψ_θ => ψ_θ)

    return EdgeModelSystem(simplified, variables, observables)
end

# --- Expanded φ-variable formulation ---

function _build_expanded(model::StaticConfigurationModel; name::Symbol)
    prog = model.progression
    t = t_nounits
    D = D_nounits

    θ = only(@variables θ(t))

    # Create φ variables for each non-susceptible stage
    phi = Dict{Symbol, Any}()
    for stage in prog.stages
        varname = Symbol("phi_", stage.name)
        phi[stage.name] = only(@variables $(varname)(t))
    end

    # Susceptible φ is algebraic: φ_S = ψ'(θ)/ψ'(1)
    phi_S = only(@variables $(Symbol("phi_", prog.susceptible))(t))

    # PGF evaluations
    ψ_θ = _eval_pgf(model.pgf, θ)
    ψ_prime_θ = _eval_pgf_deriv(model.pgf, 1, θ)
    ψ_prime_1 = _eval_pgf_deriv(model.pgf, 1, 1)
    ψ_double_θ = _eval_pgf_deriv(model.pgf, 2, θ)

    phi_S_expr = Symbolics.simplify(ψ_prime_θ / ψ_prime_1)

    # Edge hazard: total transmission rate across test edge
    edge_hazard = Symbolics.simplify(sum(
        stage.transmission_rate * phi[stage.name] for stage in prog.stages
    ))

    # Excess hazard: edge_hazard · ψ''(θ)/ψ'(θ)
    excess_hazard = Symbolics.simplify(edge_hazard * ψ_double_θ / ψ_prime_θ)

    S_pop = only(@variables S(t))
    I_pop = only(@variables I(t))
    pop = Dict{Symbol, Any}()
    for stage in prog.stages
        pop[stage.name] = only(@variables $(Symbol("pop_", stage.name))(t))
    end

    incoming, outgoing = _transition_maps(prog)
    recovered = _recovered_stages(prog, outgoing)
    infected = [stage.name for stage in prog.stages if !(stage.name in recovered)]
    incidence = Symbolics.simplify(edge_hazard * ψ_prime_θ)

    # Build equations
    eqs = Equation[]

    # φ_S algebraic constraint
    push!(eqs, phi_S ~ phi_S_expr)

    # θ ODE
    push!(eqs, D(θ) ~ Symbolics.simplify(-edge_hazard))

    # φ ODEs for each disease stage
    for stage in prog.stages
        φ_var = phi[stage.name]

        inflow_terms = Any[]
        if stage.name == prog.entry
            push!(inflow_terms, excess_hazard * phi_S)
        end
        for tr in incoming[stage.name]
            push!(inflow_terms, tr.rate * phi[tr.source])
        end
        inflow = isempty(inflow_terms) ? 0 : foldl(+, inflow_terms)

        outflow_terms = Any[stage.transmission_rate * φ_var]
        for tr in outgoing[stage.name]
            push!(outflow_terms, tr.rate * φ_var)
        end
        outflow = foldl(+, outflow_terms)

        push!(eqs, D(φ_var) ~ Symbolics.simplify(inflow - outflow))
    end

    append!(eqs, _population_stage_equations(prog, pop, incidence, incoming, outgoing, D))
    push!(eqs, S_pop ~ ψ_θ)
    push!(eqs, I_pop ~ _sum_stage_populations(pop, infected))

    sys = System(eqs, t; name = name)
    simplified = mtkcompile(sys)

    variables = Dict{Symbol, Any}(:θ => θ)
    merge!(variables, Dict(Symbol("φ_", k) => v for (k, v) in phi))
    merge!(variables, Dict(Symbol("pop_", k) => v for (k, v) in pop))
    if length(recovered) == 1
        variables[:R] = pop[only(recovered)]
    end

    observables = Dict{Symbol, Any}(
        :S => S_pop,
        :I => I_pop,
        :φ_S => phi_S,
        :edge_hazard => edge_hazard,
        :excess_hazard => excess_hazard,
    )

    metadata = _default_seed_metadata(pop[prog.entry], ψ_θ)
    metadata[:edge_seed_groups] = Any[
        (; entry = phi[prog.entry], theta = θ, phi_S_expr = phi_S_expr),
    ]
    return EdgeModelSystem(simplified, variables, observables, metadata)
end

function _find_terminal_recovery_rate(prog::DiseaseProgression)
    outgoing = Dict(s.name => DiseaseTransition[] for s in prog.stages)
    for tr in prog.transitions
        push!(outgoing[tr.source], tr)
    end
    non_transmitting = Set(s.name for s in prog.stages if _is_zero_rate(s.transmission_rate))
    total = 0
    for stage in prog.stages
        for tr in outgoing[stage.name]
            if tr.target in non_transmitting
                total += tr.rate
            end
        end
    end
    return total
end

# --- R₀ computation ---
# For single-stage SIR: R₀ = β/(β+γ) · ψ''(1)/ψ'(1)
# For multi-stage: uses next-generation matrix approach.
# The transmissibility T = P(transmission before recovery through a single edge)
# is computed as the spectral radius of the edge-level transmission/transition system,
# then multiplied by the excess degree ratio ψ''(1)/ψ'(1).

function basic_reproduction_number(model::StaticConfigurationModel)
    prog = model.progression

    # Network factor: excess degree ratio
    ψ_prime_1 = _eval_pgf_deriv(model.pgf, 1, 1)
    ψ_double_1 = _eval_pgf_deriv(model.pgf, 2, 1)
    excess_degree = Symbolics.simplify(ψ_double_1 / ψ_prime_1)

    # Compute edge-level transmissibility T
    # For a single infectious stage: T = β/(β+γ)
    # For multi-stage (e.g., E->I->R): T is the probability of transmitting before
    # leaving the infectious chain, computed via the product of survival probabilities.
    infectious_stages = [s for s in prog.stages if !_is_zero_rate(s.transmission_rate)]

    if length(infectious_stages) == 1
        # Simple case: single infectious stage
        stage = only(infectious_stages)
        β_val = stage.transmission_rate
        outgoing_rate = sum(tr.rate for tr in prog.transitions if tr.source == stage.name; init = 0)
        total_exit_rate = β_val + outgoing_rate
        T = Symbolics.simplify(β_val / total_exit_rate)
    else
        # Multi-stage: compute transmissibility as 1 - P(no transmission)
        # For a linear chain of infectious stages, the probability of NOT transmitting
        # through a test edge is the product over stages of P(progressing before transmitting).
        # T = 1 - ∏_m [γ_m / (β_m + γ_m)]
        T = _compute_multistage_transmissibility(prog)
    end

    return Symbolics.simplify(T * excess_degree)
end

function _compute_multistage_transmissibility(prog::DiseaseProgression)
    # Build the transition graph for infectious stages
    # For each stage, compute the probability of NOT transmitting and moving to next stage
    # T = 1 - ∏_stages P(not transmitting in that stage)
    survival_product = 1  # P(no transmission through the entire chain)

    outgoing = Dict(s.name => DiseaseTransition[] for s in prog.stages)
    for tr in prog.transitions
        push!(outgoing[tr.source], tr)
    end

    for stage in prog.stages
        β_m = stage.transmission_rate
        if _is_zero_rate(β_m)
            continue  # Non-infectious stage (E, R) - no transmission risk
        end
        # Total exit rate from this stage (progression + transmission)
        progression_rate = sum(tr.rate for tr in outgoing[stage.name]; init = 0)
        total_exit = β_m + progression_rate
        # P(not transmitting in this stage) = progression_rate / total_exit
        survival_product = survival_product * Symbolics.simplify(progression_rate / total_exit)
    end

    return Symbolics.simplify(1 - survival_product)
end

# --- Default initial conditions ---

function default_initial_conditions(model::EdgeModelSystem; ε = 1e-3, seed_fraction = ε)
    ic = Dict{Any, Float64}()
    for (sym, var) in model.variables
        if startswith(string(sym), "θ")
            ic[var] = 1.0 - seed_fraction
        else
            ic[var] = 0.0
        end
    end
    for group in get(model.metadata, :seed_groups, Any[])
        susceptible_value = Symbolics.simplify(Symbolics.substitute(group.susceptible_expr, ic))
        susceptible_numeric = _maybe_to_float64(susceptible_value)
        seed_mass = isnothing(susceptible_numeric) ? seed_fraction :
            max(0.0, 1.0 - susceptible_numeric)
        ic[group.entry] = seed_mass
    end
    # Seed entry edge variable so transmission can start. In Miller's expanded
    # EBCM, φ_S(t) = ψ'(θ)/ψ'(1) is algebraic, and the entry-stage edge
    # probability satisfies φ_entry(0) = θ(0) - φ_S(θ(0)) when other φ's are 0.
    # Without this, φ_entry(0) = 0 implies edge_hazard(0) = 0 and the epidemic
    # never starts. We substitute the full ic dict so the formula works for
    # multivariate (multi-type, clustered) cases where φ_S depends on several θ.
    # Falls back to seed_fraction if substitution remains symbolic.
    # Explicit assignments: list of (var, expr) pairs. Each `expr` is
    # substituted with the current `ic` (after the θ defaults and seed_groups
    # step) and the resulting numeric value is written into `ic[var]`.
    # Used by builders (e.g., `build_sis_reinfection`) that need to seed
    # additional state variables beyond the single entry stage.
    for assignment in get(model.metadata, :explicit_assignments, Any[])
        var, expr = assignment
        substituted = Symbolics.simplify(Symbolics.substitute(expr, ic))
        numeric = _maybe_to_float64(substituted)
        if numeric !== nothing
            ic[var] = numeric
        end
    end
    for assignment in get(model.metadata, :seed_fraction_assignments, Any[])
        ic[assignment.var] = Float64(assignment.value(seed_fraction))
    end
    for group in get(model.metadata, :edge_seed_groups, Any[])
        θ_val = haskey(group, :theta) ? get(ic, group.theta, nothing) : nothing
        phi_S_subst = Symbolics.simplify(Symbolics.substitute(group.phi_S_expr, ic))
        phi_S_numeric = _maybe_to_float64(phi_S_subst)
        if phi_S_numeric !== nothing && θ_val !== nothing
            ic[group.entry] = max(0.0, θ_val - phi_S_numeric)
        elseif phi_S_numeric !== nothing
            # No single θ identified (multivariate case): seed with 1 - φ_S.
            ic[group.entry] = max(0.0, 1.0 - phi_S_numeric)
        else
            ic[group.entry] = seed_fraction
        end
    end
    return ic
end

function compartment(sol, system::EdgeModelSystem, state::Symbol)
    if haskey(system.observables, state)
        return sol[system.observables[state]]
    elseif haskey(system.variables, state)
        return sol[system.variables[state]]
    end
    throw(ArgumentError("unknown compartment or observable: $state"))
end

# Argument-order parity with NodeBasedModels (system, sol, state).
compartment(system::EdgeModelSystem, sol, state::Symbol) = compartment(sol, system, state)

function compartments(sol, system::EdgeModelSystem, states::AbstractVector{Symbol})
    return Dict(state => compartment(sol, system, state) for state in states)
end
compartments(system::EdgeModelSystem, sol, states::AbstractVector{Symbol}) =
    compartments(sol, system, states)

function population_fraction(sol, system::EdgeModelSystem, state::Symbol)
    return compartment(sol, system, state)
end
population_fraction(system::EdgeModelSystem, sol, state::Symbol) =
    population_fraction(sol, system, state)

function solve_epidemic(system::EdgeModelSystem;
                        tspan::Tuple{<:Real, <:Real} = (0.0, 100.0),
                        init = default_initial_conditions(system),
                        solver = nothing,
                        kwargs...)
    prob = ODEProblem(system.system, init, (Float64(tspan[1]), Float64(tspan[2])))
    if isnothing(solver)
        return solve(prob; kwargs...)
    end
    return solve(prob, solver; kwargs...)
end

# ==========================================================================
# Dynamic network model (edge swapping / dormant contacts)
# ==========================================================================

# Serosorting function types: rates can depend on population state
# η₁(π_S, π_I) = formation rate, η₂(π_S, π_I) = breaking rate
# For simple case: η₁, η₂ are constants.

"""
    DynamicConfigurationModel(pgf, progression, η₁, η₂)

Edge-rewiring EBCM with dormant stubs. The current implementation uses a
random-rewiring closure: dormant stubs reconnect to compartments in proportion
to current population fractions, and the active susceptible-edge fraction is
approximated by `ψ'(θ)/ψ'(1)`. This is exact in the static limit `η₁ = η₂ = 0`
and serves as a closure approximation away from that limit.
"""
struct DynamicConfigurationModel
    pgf::DegreePGF
    progression::DiseaseProgression
    η₁  # Edge formation rate (scalar or function of dormant stub fractions)
    η₂  # Edge breaking rate (scalar or function of active stub fractions)
end

function build_edge_system(model::DynamicConfigurationModel;
                           name::Symbol = :dynamic_ebm)
    return _build_dynamic_expanded(model; name = name)
end

function _build_dynamic_expanded(model::DynamicConfigurationModel; name::Symbol)
    prog = model.progression
    t = t_nounits
    D = D_nounits

    incoming, outgoing = _transition_maps(prog)
    recovered = _recovered_stages(prog, outgoing)
    infected = [stage.name for stage in prog.stages if !(stage.name in recovered)]

    θ = only(@variables θ(t))

    # φ variables for each non-susceptible stage
    phi = Dict{Symbol, Any}()
    for stage in prog.stages
        vname = Symbol("φ_", stage.name)
        phi[stage.name] = only(@variables $(vname)(t))
    end

    # φ_S (active susceptible), φ_D (dormant)
    phi_S = only(@variables φ_S(t))
    phi_D = only(@variables φ_D(t))

    # Population-level
    S_pop = only(@variables S(t))
    I_pop = only(@variables I(t))
    pop = Dict{Symbol, Any}()
    for stage in prog.stages
        pop[stage.name] = only(@variables $(Symbol("pop_", stage.name))(t))
    end

    # PGF evaluations
    ψ_θ = _eval_pgf(model.pgf, θ)
    ψ_prime_θ = _eval_pgf_deriv(model.pgf, 1, θ)
    ψ_prime_1 = _eval_pgf_deriv(model.pgf, 1, 1)
    ψ_double_θ = _eval_pgf_deriv(model.pgf, 2, θ)

    # φ_S algebraic: for dynamic networks, φ_S = ψ'(θ)/ψ'(1) still holds
    # because it represents the probability a random active neighbor is susceptible
    phi_S_expr = Symbolics.simplify(ψ_prime_θ / ψ_prime_1)

    # Edge hazard (from active edges only)
    edge_hazard = Symbolics.simplify(sum(
        stage.transmission_rate * phi[stage.name] for stage in prog.stages
    ))

    # Excess hazard through active edges
    excess_hazard = Symbolics.simplify(edge_hazard * ψ_double_θ / ψ_prime_θ)

    # Edge formation and breaking rates
    η₁ = model.η₁
    η₂ = model.η₂

    eqs = Equation[]

    # φ_S algebraic
    push!(eqs, phi_S ~ phi_S_expr)

    # θ ODE: active edges that transmit OR break
    # dθ/dt = -edge_hazard - η₂·(φ_S + Σ φ_stage) + η₁·φ_D
    # When an active edge breaks, it becomes dormant (leaves θ).
    # When a dormant edge forms, it becomes active (enters θ).
    active_phi_sum = phi_S + sum(phi[s.name] for s in prog.stages)
    push!(eqs, D(θ) ~ Symbolics.simplify(-edge_hazard - η₂ * active_phi_sum + η₁ * phi_D))

    # φ_D ODE: dormant edges
    # dφ_D/dt = η₂·(φ_S + Σ φ_stage) - η₁·φ_D
    push!(eqs, D(phi_D) ~ Symbolics.simplify(η₂ * active_phi_sum - η₁ * phi_D))

    incidence = Symbolics.simplify(edge_hazard * ψ_prime_θ)

    # φ ODEs for each disease stage
    for stage in prog.stages
        φ_var = phi[stage.name]

        inflow_terms = Any[]
        if stage.name == prog.entry
            push!(inflow_terms, excess_hazard * phi_S)
        end
        for tr in incoming[stage.name]
            push!(inflow_terms, tr.rate * phi[tr.source])
        end
        push!(inflow_terms, η₁ * phi_D * pop[stage.name])
        inflow = isempty(inflow_terms) ? 0 : foldl(+, inflow_terms)

        # Outflow: transmission + progression + edge breaking
        outflow_terms = Any[stage.transmission_rate * φ_var]
        for tr in outgoing[stage.name]
            push!(outflow_terms, tr.rate * φ_var)
        end
        push!(outflow_terms, η₂ * φ_var)  # Edge breaking moves to dormant
        outflow = foldl(+, outflow_terms)

        # Inflow from dormant: when a dormant edge forms to a node in this stage
        # The probability a dormant stub connects to stage m is proportional to
        # the population fraction in stage m. For SIR, this is handled by η₁.
        # In the simple model, newly formed edges connect to a random node,
        # so the fraction in each state matches the population proportions.

        push!(eqs, D(φ_var) ~ Symbolics.simplify(inflow - outflow))
    end

    append!(eqs, _population_stage_equations(prog, pop, incidence, incoming, outgoing, D))
    push!(eqs, S_pop ~ ψ_θ)
    push!(eqs, I_pop ~ _sum_stage_populations(pop, infected))

    sys = System(eqs, t; name = name)
    simplified = mtkcompile(sys)

    variables = Dict{Symbol, Any}(:θ => θ, :φ_D => phi_D)
    merge!(variables, Dict(Symbol("φ_", k) => v for (k, v) in phi))
    merge!(variables, Dict(Symbol("pop_", k) => v for (k, v) in pop))
    if length(recovered) == 1
        variables[:R] = pop[only(recovered)]
    end

    observables = Dict{Symbol, Any}(
        :S => S_pop,
        :I => I_pop,
        :φ_S => phi_S,
        :edge_hazard => edge_hazard,
        :excess_hazard => excess_hazard,
    )

    metadata = _default_seed_metadata(pop[prog.entry], ψ_θ)
    metadata[:edge_seed_groups] = Any[
        (; entry = phi[prog.entry], theta = θ, phi_S_expr = phi_S_expr),
    ]
    return EdgeModelSystem(simplified, variables, observables, metadata)
end

# ==========================================================================
# Multi-type configuration model
# ==========================================================================

struct MultiTypeConfigurationModel
    types::Vector{Symbol}
    pgfs::Dict{Symbol, MultivariatePGF}
    progression::DiseaseProgression
    contact_matrix::Dict{Tuple{Symbol,Symbol}, Any}
end

function MultiTypeConfigurationModel(;
    types::Vector{Symbol},
    pgfs::Dict{Symbol, MultivariatePGF},
    progression::DiseaseProgression,
    contact_matrix::Dict = Dict{Tuple{Symbol,Symbol}, Any}(),
)
    for type in types
        haskey(pgfs, type) || throw(ArgumentError("missing PGF for type $type"))
        Set(pgfs[type].types) == Set(types) ||
            throw(ArgumentError("PGF for type $type must have variables for all types: $types"))
    end
    # Fill missing contact matrix entries with 1 (homogeneous mixing)
    filled = Dict{Tuple{Symbol,Symbol}, Any}()
    for j in types, l in types
        filled[(j, l)] = get(contact_matrix, (j, l), 1)
    end
    return MultiTypeConfigurationModel(types, pgfs, progression, filled)
end

function build_edge_system(model::MultiTypeConfigurationModel;
                           name::Symbol = :multitype_ebm)
    return _build_multitype_expanded(model; name = name)
end

function _build_multitype_expanded(model::MultiTypeConfigurationModel; name::Symbol)
    prog = model.progression
    types = model.types
    K = length(types)
    t = t_nounits
    D = D_nounits

    incoming, outgoing = _transition_maps(prog)
    recovered = _recovered_stages(prog, outgoing)
    infected = [stage.name for stage in prog.stages if !(stage.name in recovered)]

    # --- Create symbolic variables ---
    # θ_{jl}(t) for each type pair: prob edge from l to j hasn't transmitted
    theta = Dict{Tuple{Symbol,Symbol}, Any}()
    for j in types, l in types
        vname = Symbol("θ_", j, "_", l)
        theta[(j, l)] = only(@variables $(vname)(t))
    end

    # φ_{stage,jl}(t) for each stage and type pair
    phi = Dict{Tuple{Symbol,Symbol,Symbol}, Any}()
    for stage in prog.stages, j in types, l in types
        vname = Symbol("φ_", stage.name, "_", j, "_", l)
        phi[(stage.name, j, l)] = only(@variables $(vname)(t))
    end

    # φ_S_{jl}(t) for susceptible (algebraic, but need a symbol for the equation)
    phi_S = Dict{Tuple{Symbol,Symbol}, Any}()
    for j in types, l in types
        vname = Symbol("φ_S_", j, "_", l)
        phi_S[(j, l)] = only(@variables $(vname)(t))
    end

    # Population-level variables per type
    S_pop = Dict{Symbol, Any}()
    I_pop = Dict{Symbol, Any}()
    pop = Dict{Tuple{Symbol, Symbol}, Any}()
    for l in types
        S_pop[l] = only(@variables $(Symbol("S_", l))(t))
        I_pop[l] = only(@variables $(Symbol("I_", l))(t))
        for stage in prog.stages
            pop[(stage.name, l)] = only(@variables $(Symbol("pop_", stage.name, "_", l))(t))
        end
    end

    eqs = Equation[]
    susceptible_partial = Dict{Tuple{Symbol, Symbol}, Any}()
    phi_S_expr = Dict{Tuple{Symbol, Symbol}, Any}()

    # --- PGF evaluations ---
    # For each type j (the neighbor), substitute θ_{k,j} for all k into ψ_j
    # θ_vec_j maps type k → θ_{kj}
    ψ_at_theta = Dict{Symbol, Any}()  # ψ_j(θ_vec_j)
    for j in types
        sub = Dict{Symbol, Any}(k => theta[(k, j)] for k in types)
        ψ_at_theta[j] = eval_multivariate_pgf(model.pgfs[j], sub)
    end

    # --- φ_S algebraic equations ---
    # φ_{S,jl} = ∂ψ_j/∂x_l(θ_vec_j) / ∂ψ_j/∂x_l(1_vec)
    # The neighbor is type j, reached via a type-l edge → differentiate ψ_j w.r.t. x_l
    for j in types, l in types
        pgf_j = model.pgfs[j]

        # Numerator: ∂ψ_j/∂x_l evaluated at θ_vec_j
        deriv_expr = partial_derivative(pgf_j, l, 1)
        sub_theta = Dict{Any, Any}(
            pgf_j.variables[findfirst(==(k), pgf_j.types)] => theta[(k, j)]
            for k in types
        )
        numerator = _cleanup_exp_zero(Symbolics.simplify(Symbolics.substitute(deriv_expr, sub_theta)))
        susceptible_partial[(j, l)] = numerator

        # Denominator: ∂ψ_j/∂x_l evaluated at 1
        sub_ones = Dict{Any, Any}(v => 1 for v in pgf_j.variables)
        denominator = _cleanup_exp_zero(Symbolics.simplify(Symbolics.substitute(deriv_expr, sub_ones)))

        push!(eqs, phi_S[(j, l)] ~ Symbolics.simplify(numerator / denominator))
        phi_S_expr[(j, l)] = Symbolics.simplify(numerator / denominator)
    end

    # --- Edge hazard and excess hazard per type pair ---
    # edge_hazard_{jl} = Σ_m β_{m,j} · contact[(j,l)] · φ_{I_m,jl}
    # This is the rate at which edge (j→l) transmits disease from j to l
    edge_hazard = Dict{Tuple{Symbol,Symbol}, Any}()
    for j in types, l in types
        h = sum(
            stage.transmission_rate * model.contact_matrix[(j, l)] * phi[(stage.name, j, l)]
            for stage in prog.stages;
            init = 0
        )
        edge_hazard[(j, l)] = Symbolics.simplify(h)
    end

    # Excess hazard for neighbor j, reached via l-edge:
    # Rate at which the type-j neighbor gets infected through its OTHER edges.
    # excess_hazard_{jl} = Σ_k edge_hazard_{kj} · ∂²ψ_j/(∂x_l ∂x_k)(θ_vec_j) / ∂ψ_j/∂x_l(θ_vec_j)
    excess_hazard = Dict{Tuple{Symbol,Symbol}, Any}()
    for j in types, l in types
        pgf_j = model.pgfs[j]
        sub_theta = Dict{Any, Any}(
            pgf_j.variables[findfirst(==(k), pgf_j.types)] => theta[(k, j)]
            for k in types
        )

        # ∂ψ_j/∂x_l at θ
        deriv_l = partial_derivative(pgf_j, l, 1)
        denom = _cleanup_exp_zero(Symbolics.simplify(Symbolics.substitute(deriv_l, sub_theta)))

        eh = 0
        for k in types
            # ∂²ψ_j/(∂x_l ∂x_k) at θ
            mixed = mixed_partial(pgf_j, l, k)
            numer_k = _cleanup_exp_zero(Symbolics.simplify(Symbolics.substitute(mixed, sub_theta)))

            # edge_hazard_{kj}: hazard from type-k stubs of the j-neighbor
            # These stubs connect j to k, so the hazard is from k infecting j
            h_kj = sum(
                stage.transmission_rate * model.contact_matrix[(k, j)] * phi[(stage.name, k, j)]
                for stage in prog.stages;
                init = 0
            )
            eh += h_kj * numer_k
        end
        excess_hazard[(j, l)] = Symbolics.simplify(eh / denom)
    end

    incidence = Dict{Symbol, Any}()
    for l in types
        incidence_terms = Any[]
        for j in types
            push!(incidence_terms, edge_hazard[(j, l)] * susceptible_partial[(l, j)])
        end
        incidence[l] = Symbolics.simplify(_sum_expr(incidence_terms))
    end

    # --- θ ODEs ---
    # dθ_{jl}/dt = -edge_hazard_{jl}
    for j in types, l in types
        push!(eqs, D(theta[(j, l)]) ~ Symbolics.simplify(-edge_hazard[(j, l)]))
    end

    # --- φ ODEs for each disease stage and type pair ---
    for stage in prog.stages, j in types, l in types
        φ_var = phi[(stage.name, j, l)]

        # Inflow
        inflow_terms = Any[]
        if stage.name == prog.entry
            # Infection of the j-neighbor through its OTHER edges
            push!(inflow_terms, excess_hazard[(j, l)] * phi_S[(j, l)])
        end
        for tr in incoming[stage.name]
            push!(inflow_terms, tr.rate * phi[(tr.source, j, l)])
        end
        inflow = isempty(inflow_terms) ? 0 : foldl(+, inflow_terms)

        # Outflow: transmission through this edge + progression
        outflow_terms = Any[stage.transmission_rate * model.contact_matrix[(j, l)] * φ_var]
        for tr in outgoing[stage.name]
            push!(outflow_terms, tr.rate * φ_var)
        end
        outflow = foldl(+, outflow_terms)

        push!(eqs, D(φ_var) ~ Symbolics.simplify(inflow - outflow))
    end

    # --- Population-level equations per type ---
    for l in types
        for stage in prog.stages
            pop_var = pop[(stage.name, l)]

            inflow_terms = Any[]
            if stage.name == prog.entry
                push!(inflow_terms, incidence[l])
            end
            for tr in incoming[stage.name]
                push!(inflow_terms, tr.rate * pop[(tr.source, l)])
            end
            inflow = _sum_expr(inflow_terms)

            outflow_terms = Any[]
            for tr in outgoing[stage.name]
                push!(outflow_terms, tr.rate * pop_var)
            end
            outflow = _sum_expr(outflow_terms)

            push!(eqs, D(pop_var) ~ Symbolics.simplify(inflow - outflow))
        end
        push!(eqs, S_pop[l] ~ ψ_at_theta[l])
        push!(eqs, I_pop[l] ~ _sum_stage_populations(pop, [(stage, l) for stage in infected]))
    end

    # --- Build and compile system ---
    sys = System(eqs, t; name = name)
    simplified = mtkcompile(sys)

    # Collect variables and observables
    variables = Dict{Symbol, Any}()
    for j in types, l in types
        variables[Symbol("θ_", j, "_", l)] = theta[(j, l)]
    end
    for stage in prog.stages, j in types, l in types
        variables[Symbol("φ_", stage.name, "_", j, "_", l)] = phi[(stage.name, j, l)]
    end
    for stage in prog.stages, l in types
        variables[Symbol("pop_", stage.name, "_", l)] = pop[(stage.name, l)]
    end
    if length(recovered) == 1
        recovered_stage = only(recovered)
        for l in types
            variables[Symbol("R_", l)] = pop[(recovered_stage, l)]
        end
    end

    observables = Dict{Symbol, Any}()
    for j in types, l in types
        observables[Symbol("φ_S_", j, "_", l)] = phi_S[(j, l)]
        observables[Symbol("edge_hazard_", j, "_", l)] = edge_hazard[(j, l)]
        observables[Symbol("excess_hazard_", j, "_", l)] = excess_hazard[(j, l)]
    end
    for l in types
        observables[Symbol("S_", l)] = S_pop[l]
        observables[Symbol("I_", l)] = I_pop[l]
    end

    metadata = Dict{Symbol, Any}(
        :seed_groups => Any[
            (; entry = pop[(prog.entry, l)], susceptible_expr = ψ_at_theta[l]) for l in types
        ],
        :edge_seed_groups => Any[
            (; entry = phi[(prog.entry, j, l)], phi_S_expr = phi_S_expr[(j, l)])
            for j in types for l in types
        ],
    )
    return EdgeModelSystem(simplified, variables, observables, metadata)
end

# ==========================================================================
# Clustered configuration model (single-edges + triangles)
# ==========================================================================
# Following Volz (2011) "Effects of heterogeneous and clustered contact patterns"
# and Miller (2009) "Spread of infectious disease through clustered populations"
#
# Key variables:
#   θ₂(t) = P(haven't been infected through a single-edge partner)
#   θ₃(t) = P(haven't been infected through a triangle-edge partner)

struct ClusteredConfigurationModel
    pgf::ClusteredPGF
    progression::DiseaseProgression
end

function build_edge_system(model::ClusteredConfigurationModel;
                           name::Symbol = :clustered_ebm)
    return _build_clustered_expanded(model; name = name)
end

function _build_clustered_expanded(model::ClusteredConfigurationModel; name::Symbol)
    prog = model.progression
    t = t_nounits
    D = D_nounits

    incoming, outgoing = _transition_maps(prog)
    recovered = _recovered_stages(prog, outgoing)
    infected = [stage.name for stage in prog.stages if !(stage.name in recovered)]

    # θ₂ = single-edge survivor, θ₃ = triangle-edge survivor
    θ₂ = only(@variables θ₂(t))
    θ₃ = only(@variables θ₃(t))

    # φ variables for single-edges (subscript 2) and triangle-edges (subscript 3)
    phi2 = Dict{Symbol, Any}()
    phi3 = Dict{Symbol, Any}()
    for stage in prog.stages
        v2 = Symbol("φ2_", stage.name)
        v3 = Symbol("φ3_", stage.name)
        phi2[stage.name] = only(@variables $(v2)(t))
        phi3[stage.name] = only(@variables $(v3)(t))
    end

    # φ_S for each edge type (algebraic)
    φ2_S = only(@variables φ2_S(t))
    φ3_S = only(@variables φ3_S(t))

    # Population-level
    S_pop = only(@variables S(t))
    I_pop = only(@variables I(t))
    pop = Dict{Symbol, Any}()
    for stage in prog.stages
        pop[stage.name] = only(@variables $(Symbol("pop_", stage.name))(t))
    end

    # PGF evaluations
    # S(t) = g(θ₂, θ₃²) — the θ₃² accounts for both triangle partners
    g_at_theta = _eval_clustered(model.pgf, θ₂, θ₃^2)

    # φ2_S = g_x(θ₂, θ₃²) / g_x(1, 1) — excess degree for single edges
    gx_theta = _eval_clustered_deriv(model.pgf, :single, 1, θ₂, θ₃^2)
    gx_1 = _eval_clustered_deriv(model.pgf, :single, 1, 1, 1)
    phi2_S_expr = Symbolics.simplify(gx_theta / gx_1)

    # φ3_S = g_y(θ₂, θ₃²) · θ₃ / g_y(1, 1) — excess degree for triangle edges
    # (chain rule: d/dθ₃ g(θ₂, θ₃²) = 2θ₃ g_y(θ₂, θ₃²))
    gy_theta = _eval_clustered_deriv(model.pgf, :triangle, 1, θ₂, θ₃^2)
    gy_1 = _eval_clustered_deriv(model.pgf, :triangle, 1, 1, 1)
    phi3_S_expr = Symbolics.simplify(gy_theta * θ₃ / gy_1)

    # Edge hazards
    edge_hazard2 = Symbolics.simplify(sum(
        stage.transmission_rate * phi2[stage.name] for stage in prog.stages))
    edge_hazard3 = Symbolics.simplify(sum(
        stage.transmission_rate * phi3[stage.name] for stage in prog.stages))

    # Excess hazard for single edges (infection through OTHER edges of partner)
    gxx_theta = _eval_clustered_deriv(model.pgf, :single, 2, θ₂, θ₃^2)

    # Mixed partial g_xy at (θ₂, θ₃²)
    gxy_expr = clustered_pgf_derivative(model.pgf, :single, 1)
    Dy = Differential(model.pgf.triangle_var)
    gxy_full = Symbolics.expand_derivatives(Dy(gxy_expr))
    gxy_theta = Symbolics.simplify(Symbolics.substitute(gxy_full,
        Dict(model.pgf.single_var => θ₂, model.pgf.triangle_var => θ₃^2)))

    excess2 = Symbolics.simplify(
        (edge_hazard2 * gxx_theta + edge_hazard3 * gxy_theta * 2θ₃) / gx_theta)

    # Excess hazard for triangle edges
    gyy_theta = _eval_clustered_deriv(model.pgf, :triangle, 2, θ₂, θ₃^2)

    # g_yx at (θ₂, θ₃²)
    gyx_expr = clustered_pgf_derivative(model.pgf, :triangle, 1)
    Dx = Differential(model.pgf.single_var)
    gyx_full = Symbolics.expand_derivatives(Dx(gyx_expr))
    gyx_theta = Symbolics.simplify(Symbolics.substitute(gyx_full,
        Dict(model.pgf.single_var => θ₂, model.pgf.triangle_var => θ₃^2)))

    # Within-triangle transmission: the other triangle partner can infect through
    # the third edge of the triangle. The 2*gy term keeps the chain-rule
    # normalization for S(θ₂, θ₃) = g(θ₂, θ₃²) inside the same fraction.
    excess3 = Symbolics.simplify(
        (
            edge_hazard2 * gyx_theta * 2θ₃ +
            edge_hazard3 * (2 * gy_theta + 4 * θ₃^2 * gyy_theta)
        ) / (gy_theta * 2θ₃),
    )

    incidence = Symbolics.simplify(gx_theta * edge_hazard2 + 2 * θ₃ * gy_theta * edge_hazard3)

    eqs = Equation[]

    # Algebraic: φ_S
    push!(eqs, φ2_S ~ phi2_S_expr)
    push!(eqs, φ3_S ~ phi3_S_expr)

    # θ ODEs
    push!(eqs, D(θ₂) ~ Symbolics.simplify(-edge_hazard2))
    push!(eqs, D(θ₃) ~ Symbolics.simplify(-edge_hazard3))

    # φ₂ ODEs (single-edge)
    for stage in prog.stages
        φ_var = phi2[stage.name]
        inflow_terms = Any[]
        if stage.name == prog.entry
            push!(inflow_terms, excess2 * φ2_S)
        end
        for tr in incoming[stage.name]
            push!(inflow_terms, tr.rate * phi2[tr.source])
        end
        inflow = isempty(inflow_terms) ? 0 : foldl(+, inflow_terms)
        outflow_terms = Any[stage.transmission_rate * φ_var]
        for tr in outgoing[stage.name]
            push!(outflow_terms, tr.rate * φ_var)
        end
        outflow = foldl(+, outflow_terms)
        push!(eqs, D(φ_var) ~ Symbolics.simplify(inflow - outflow))
    end

    # φ₃ ODEs (triangle-edge)
    for stage in prog.stages
        φ_var = phi3[stage.name]
        inflow_terms = Any[]
        if stage.name == prog.entry
            push!(inflow_terms, excess3 * φ3_S)
        end
        for tr in incoming[stage.name]
            push!(inflow_terms, tr.rate * phi3[tr.source])
        end
        inflow = isempty(inflow_terms) ? 0 : foldl(+, inflow_terms)
        outflow_terms = Any[stage.transmission_rate * φ_var]
        for tr in outgoing[stage.name]
            push!(outflow_terms, tr.rate * φ_var)
        end
        outflow = foldl(+, outflow_terms)
        push!(eqs, D(φ_var) ~ Symbolics.simplify(inflow - outflow))
    end

    append!(eqs, _population_stage_equations(prog, pop, incidence, incoming, outgoing, D))
    push!(eqs, S_pop ~ g_at_theta)
    push!(eqs, I_pop ~ _sum_stage_populations(pop, infected))

    sys = System(eqs, t; name = name)
    simplified = mtkcompile(sys)

    variables = Dict{Symbol, Any}(:θ₂ => θ₂, :θ₃ => θ₃)
    merge!(variables, Dict(Symbol("φ2_", k) => v for (k, v) in phi2))
    merge!(variables, Dict(Symbol("φ3_", k) => v for (k, v) in phi3))
    merge!(variables, Dict(Symbol("pop_", k) => v for (k, v) in pop))
    if length(recovered) == 1
        variables[:R] = pop[only(recovered)]
    end

    observables = Dict{Symbol, Any}(
        :S => S_pop, :I => I_pop, :φ2_S => φ2_S, :φ3_S => φ3_S,
        :edge_hazard2 => edge_hazard2, :edge_hazard3 => edge_hazard3,
    )

    metadata = _default_seed_metadata(pop[prog.entry], g_at_theta)
    metadata[:edge_seed_groups] = Any[
        (; entry = phi2[prog.entry], theta = θ₂, phi_S_expr = phi2_S_expr),
        (; entry = phi3[prog.entry], theta = θ₃, phi_S_expr = phi3_S_expr),
    ]
    return EdgeModelSystem(simplified, variables, observables, metadata)
end

function build_clustered_sir(pgf::ClusteredPGF, β, γ; name::Symbol = :clustered_sir)
    progression = DiseaseProgression(
        [DiseaseStage(:I; transmission_rate = β), DiseaseStage(:R; transmission_rate = 0)],
        [DiseaseTransition(:I, :R, γ)]; entry = :I)
    build_edge_system(ClusteredConfigurationModel(pgf, progression); name = name)
end

function build_clustered_seir(pgf::ClusteredPGF, σ, β, γ; name::Symbol = :clustered_seir)
    progression = DiseaseProgression(
        [DiseaseStage(:E; transmission_rate = 0),
         DiseaseStage(:I; transmission_rate = β),
         DiseaseStage(:R; transmission_rate = 0)],
        [DiseaseTransition(:E, :I, σ), DiseaseTransition(:I, :R, γ)]; entry = :E)
    build_edge_system(ClusteredConfigurationModel(pgf, progression); name = name)
end

# R₀ for clustered networks
function basic_reproduction_number(model::ClusteredConfigurationModel)
    prog = model.progression
    pgf = model.pgf

    # Compute transmissibility T
    infectious_stages = [s for s in prog.stages if !_is_zero_rate(s.transmission_rate)]
    if length(infectious_stages) == 1
        stage = only(infectious_stages)
        β_val = stage.transmission_rate
        outgoing_rate = sum(tr.rate for tr in prog.transitions if tr.source == stage.name; init = 0)
        T = Symbolics.simplify(β_val / (β_val + outgoing_rate))
    else
        T = _compute_multistage_transmissibility(prog)
    end

    # For clustered networks: R₀ = T · [excess_single + 2·excess_triangle·(1 + T)]
    # The (1+T) factor accounts for within-triangle transmission
    gx_1 = _eval_clustered_deriv(pgf, :single, 1, 1, 1)
    gxx_1 = _eval_clustered_deriv(pgf, :single, 2, 1, 1)
    gy_1 = _eval_clustered_deriv(pgf, :triangle, 1, 1, 1)

    # excess single degree
    excess_s = Symbolics.simplify(gxx_1 / gx_1)
    # mean triangle degree from a single-edge neighbor
    mean_tri = Symbolics.simplify(2 * gy_1 / gx_1)

    # R₀ with triangle correction
    Symbolics.simplify(T * excess_s + T * mean_tri * (1 + T))
end
