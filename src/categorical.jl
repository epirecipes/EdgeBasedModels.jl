# ==========================================================================
# Categorical composition framework for edge-based compartmental models
# ==========================================================================
#
# Provides open systems (OpenEBCM) with typed boundary ports, composition
# combinators (compose, tensor, stratify), natural transformations between
# model levels, and a functor F : Network → ODE.

using ModelingToolkit: Equation, System, mtkcompile
using OrdinaryDiffEqDefault: ODEProblem, solve, ReturnCode

# ============================================================
# §1  Open systems with typed boundary ports
# ============================================================

"""
    Port(name, type)

A typed boundary port on an open EBCM system.
`type` is one of `:susceptible`, `:infectious`, `:latent`, `:recovered`.
"""
struct Port
    name::Symbol
    type::Symbol
end

"""
    OpenEBCM(name, model, ports)
    OpenEBCM(name, model)          # auto-generates ports from DiseaseProgression

An open edge-based compartmental model with named boundary ports
that can be wired to other open systems via composition.
"""
struct OpenEBCM
    name::Symbol
    model::Any
    ports::Vector{Port}
end

# Helper to extract DiseaseProgression from any supported model type
_get_progression(m::StaticConfigurationModel)   = m.progression
_get_progression(m::DynamicConfigurationModel)  = m.progression
_get_progression(m::ClusteredConfigurationModel) = m.progression
_get_progression(m::MultiTypeConfigurationModel) = m.progression

function _stage_port_type(stage::DiseaseStage, recovered::Set{Symbol})
    if !_is_zero_rate(stage.transmission_rate)
        return :infectious
    elseif stage.name in recovered
        return :recovered
    end
    return :latent
end

function OpenEBCM(name::Symbol, model)
    prog = _get_progression(model)
    _, outgoing = _transition_maps(prog)
    recovered = Set(_recovered_stages(prog, outgoing))
    ports = Port[Port(prog.susceptible, :susceptible)]
    for stage in prog.stages
        ptype = _stage_port_type(stage, recovered)
        push!(ports, Port(stage.name, ptype))
    end
    return OpenEBCM(name, model, ports)
end

"""
    open_sir(pgf, β, γ; name=:sir)

Convenience constructor for an open SIR model on a configuration-model network.
"""
function open_sir(pgf::DegreePGF, β, γ; name::Symbol = :sir)
    prog = DiseaseProgression(
        [DiseaseStage(:I; transmission_rate = β),
         DiseaseStage(:R; transmission_rate = 0)],
        [DiseaseTransition(:I, :R, γ)]; entry = :I)
    OpenEBCM(name, StaticConfigurationModel(pgf, prog))
end

"""
    open_seir(pgf, σ, β, γ; name=:seir)

Convenience constructor for an open SEIR model on a configuration-model network.
"""
function open_seir(pgf::DegreePGF, σ, β, γ; name::Symbol = :seir)
    prog = DiseaseProgression(
        [DiseaseStage(:E; transmission_rate = 0),
         DiseaseStage(:I; transmission_rate = β),
         DiseaseStage(:R; transmission_rate = 0)],
        [DiseaseTransition(:E, :I, σ),
         DiseaseTransition(:I, :R, γ)]; entry = :E)
    OpenEBCM(name, StaticConfigurationModel(pgf, prog))
end

# ============================================================
# §2  Internal model types for composition results
# ============================================================

struct TensorModel
    components::Vector{Tuple{Symbol, Any}}
end

struct ComposedModel
    name1::Symbol
    model1::Any
    name2::Symbol
    model2::Any
    wiring::Vector{Pair{Symbol,Symbol}}
end

struct StratifiedModel
    base_pgf::DegreePGF
    progression::DiseaseProgression
    strata::Vector{Symbol}
    mixing::Matrix{Float64}
end

_get_progression(m::StratifiedModel) = m.progression

# ============================================================
# §3  Helper — build prefixed EBCM equations (before mtkcompile)
# ============================================================

"""
    _build_subsystem_equations(model, prefix)

Build the expanded EBCM equations for a `StaticConfigurationModel` with all
symbolic variables prefixed by `prefix` to avoid name collisions when multiple
subsystems are combined.  Returns a named tuple of equations, variable dicts,
and key symbolic references needed for coupling.
"""
function _build_subsystem_equations(model::StaticConfigurationModel, prefix::Symbol)
    prog = model.progression
    t = t_nounits
    D = D_nounits

    # Per-subsystem seed-fraction parameter ρ_<prefix>; susceptible-side
    # algebraic relations get a (1-ρ) factor (Miller 2011 Option B).
    ρ = only(@parameters $(Symbol(:ρ_, prefix)))
    q = 1 - ρ

    # θ variable — named θ_<prefix> so default_initial_conditions recognises it
    θ = only(@variables $(Symbol(:θ_, prefix))(t))

    # φ variables for each disease stage
    phi = Dict{Symbol, Any}()
    for stage in prog.stages
        varname = Symbol(:φ_, stage.name, :_, prefix)
        phi[stage.name] = only(@variables $(varname)(t))
    end

    # Susceptible φ (algebraic)
    phi_S = only(@variables $(Symbol(:φ_S_, prefix))(t))

    # PGF evaluations at θ
    ψ_θ        = _eval_pgf(model.pgf, θ)
    ψ_prime_θ  = _eval_pgf_deriv(model.pgf, 1, θ)
    ψ_prime_1  = _eval_pgf_deriv(model.pgf, 1, 1)
    ψ_double_θ = _eval_pgf_deriv(model.pgf, 2, θ)

    phi_S_expr = Symbolics.simplify(q * ψ_prime_θ / ψ_prime_1)

    edge_hazard = Symbolics.simplify(sum(
        stage.transmission_rate * phi[stage.name] for stage in prog.stages))

    excess_hazard = Symbolics.simplify(edge_hazard * ψ_double_θ / ψ_prime_θ)

    # Population-level observables
    S_pop = only(@variables $(Symbol(:S_, prefix))(t))
    I_pop = only(@variables $(Symbol(:I_, prefix))(t))
    pop = Dict{Symbol, Any}()
    for stage in prog.stages
        pop[stage.name] = only(@variables $(Symbol(:pop_, stage.name, :_, prefix))(t))
    end

    incoming, outgoing = _transition_maps(prog)
    recovered = _recovered_stages(prog, outgoing)
    infected = [stage.name for stage in prog.stages if !(stage.name in recovered)]
    incidence = Symbolics.simplify(q * edge_hazard * ψ_prime_θ)

    # ---- Build equations (same logic as _build_expanded) ----
    eqs = Equation[]

    # 1. φ_S algebraic
    push!(eqs, phi_S ~ phi_S_expr)

    # 2. θ ODE  (index 2 — used by compose for coupling)
    theta_rhs = Symbolics.simplify(-edge_hazard)
    push!(eqs, D(θ) ~ theta_rhs)

    # 3+ φ stage ODEs
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
    push!(eqs, S_pop ~ q * ψ_θ)
    push!(eqs, I_pop ~ _sum_stage_populations(pop, infected))

    # ---- Collect variable / observable dicts ----
    variables = Dict{Symbol, Any}()
    variables[Symbol(:θ_, prefix)] = θ
    for (k, v) in phi
        variables[Symbol(:φ_, k, :_, prefix)] = v
    end
    for (k, v) in pop
        variables[Symbol(:pop_, k, :_, prefix)] = v
    end
    if length(recovered) == 1
        variables[Symbol(:R_, prefix)] = pop[only(recovered)]
    end

    observables = Dict{Symbol, Any}()
    observables[Symbol(:S_, prefix)] = S_pop
    observables[Symbol(:I_, prefix)] = I_pop
    observables[Symbol(:φ_S_, prefix)] = phi_S

    return (
        equations   = eqs,
        variables   = variables,
        observables = observables,
        theta       = θ,
        phi         = phi,
        phi_S       = phi_S,
        edge_hazard = edge_hazard,
        theta_rhs   = theta_rhs,
        ψ_θ         = ψ_θ,
        S_pop       = S_pop,
        I_pop       = I_pop,
        progression = prog,
        rho         = ρ,
        seed_groups = Any[(; entry = pop[prog.entry], susceptible_expr = ψ_θ)],
        edge_seed_groups = Any[
            (; entry = phi[prog.entry], theta = θ, phi_S_expr = phi_S_expr),
        ],
    )
end

# ============================================================
# §4  build_edge_system methods for composed model types
# ============================================================

function build_edge_system(model::TensorModel; name::Symbol = :tensor_ebm)
    t = t_nounits
    all_eqs  = Equation[]
    all_vars = Dict{Symbol, Any}()
    all_obs  = Dict{Symbol, Any}()
    seed_groups = Any[]
    edge_seed_groups = Any[]
    rho_params = Any[]

    for (prefix, submodel) in model.components
        sub = _build_subsystem_equations(submodel, prefix)
        append!(all_eqs, sub.equations)
        merge!(all_vars, sub.variables)
        merge!(all_obs,  sub.observables)
        append!(seed_groups, sub.seed_groups)
        append!(edge_seed_groups, sub.edge_seed_groups)
        push!(rho_params, sub.rho)
    end

    sys      = System(all_eqs, t; name = name)
    compiled = mtkcompile(sys)
    metadata = Dict{Symbol, Any}(
        :rho_params => rho_params,
        :seed_groups => seed_groups,
        :edge_seed_groups => edge_seed_groups,
    )
    return EdgeModelSystem(compiled, all_vars, all_obs, metadata)
end

function build_edge_system(model::ComposedModel; name::Symbol = :composed_ebm)
    isempty(model.wiring) || throw(ArgumentError(
        "cross-system wiring is not yet supported by build_edge_system; " *
        "use tensor(...) for independent composition or stratify/multi-type models " *
        "for coupled populations",
    ))

    t = t_nounits
    D = D_nounits

    sub1 = _build_subsystem_equations(model.model1, model.name1)
    sub2 = _build_subsystem_equations(model.model2, model.name2)

    eqs1 = copy(sub1.equations)
    eqs2 = copy(sub2.equations)

    # The θ ODE is always at index 2 in the equation list produced by
    # _build_subsystem_equations (index 1 is the φ_S algebraic constraint).

    for (p1, p2) in model.wiring
        # m1 → m2 coupling: if p1 is an infectious stage in m1,
        # add its infection pressure to m2's θ equation.
        prog1 = sub1.progression
        idx1 = findfirst(s -> s.name == p1, prog1.stages)
        if !isnothing(idx1) && !_is_zero_rate(prog1.stages[idx1].transmission_rate)
            β_cross = prog1.stages[idx1].transmission_rate
            φ_cross = sub1.phi[p1]
            eqs2[2] = D(sub2.theta) ~ eqs2[2].rhs - β_cross * φ_cross
        end

        # m2 → m1 coupling (reverse direction of the same wire)
        prog2 = sub2.progression
        idx2 = findfirst(s -> s.name == p2, prog2.stages)
        if !isnothing(idx2) && !_is_zero_rate(prog2.stages[idx2].transmission_rate)
            β_cross2 = prog2.stages[idx2].transmission_rate
            φ_cross2 = sub2.phi[p2]
            eqs1[2] = D(sub1.theta) ~ eqs1[2].rhs - β_cross2 * φ_cross2
        end
    end

    all_eqs  = vcat(eqs1, eqs2)
    sys      = System(all_eqs, t; name = name)
    compiled = mtkcompile(sys)

    all_vars = merge(sub1.variables, sub2.variables)
    all_obs  = merge(sub1.observables, sub2.observables)
    metadata = Dict{Symbol, Any}(
        :rho_params => Any[sub1.rho, sub2.rho],
        :seed_groups => vcat(sub1.seed_groups, sub2.seed_groups),
        :edge_seed_groups => vcat(sub1.edge_seed_groups, sub2.edge_seed_groups),
    )
    return EdgeModelSystem(compiled, all_vars, all_obs, metadata)
end

function build_edge_system(model::StratifiedModel; name::Symbol = :stratified_ebm)
    K = length(model.strata)

    # Compute mean degree of the base network (numerically)
    ψ_prime_fn = _build_pgf_deriv_fn(model.base_pgf, 1)
    base_mean  = ψ_prime_fn(1.0)

    pgfs = Dict{Symbol, MultivariatePGF}()
    for (i, s) in enumerate(model.strata)
        contacts = Dict{Symbol, Any}()
        for (j, s2) in enumerate(model.strata)
            contacts[s2] = model.mixing[i, j] * base_mean
        end
        pgfs[s] = multivariate_poisson_pgf(model.strata, contacts)
    end

    mt = MultiTypeConfigurationModel(
        types = model.strata,
        pgfs  = pgfs,
        progression = model.progression,
    )
    return build_edge_system(mt; name = name)
end

# ============================================================
# §5  Composition combinators
# ============================================================

"""
    compose(m1, m2, wiring)

Compose two open EBCM systems by connecting matching ports.
`wiring` is a vector of `port_m1 => port_m2` pairs. Tensor products are
implemented, but explicit epidemic coupling between distinct open systems is
not yet compiled to an ODE system; use `stratify` or a multi-type model for
coupled populations.
"""
function compose(m1::OpenEBCM, m2::OpenEBCM, wiring::Vector{Pair{Symbol,Symbol}})
    model = ComposedModel(m1.name, m1.model, m2.name, m2.model, wiring)

    wired_m1 = Set(first(w) for w in wiring)
    wired_m2 = Set(last(w)  for w in wiring)
    remaining = Port[]
    for p in m1.ports
        p.name ∉ wired_m1 && push!(remaining, Port(Symbol(m1.name, :_, p.name), p.type))
    end
    for p in m2.ports
        p.name ∉ wired_m2 && push!(remaining, Port(Symbol(m2.name, :_, p.name), p.type))
    end
    return OpenEBCM(Symbol(m1.name, :_, m2.name), model, remaining)
end

"""
    tensor(m1, m2)

Tensor product: independent parallel composition with no interaction
(block-diagonal dynamics).  All ports from both systems are preserved.
"""
function tensor(m1::OpenEBCM, m2::OpenEBCM)
    model = TensorModel([(m1.name, m1.model), (m2.name, m2.model)])
    all_ports = Port[]
    for p in m1.ports
        push!(all_ports, Port(Symbol(m1.name, :_, p.name), p.type))
    end
    for p in m2.ports
        push!(all_ports, Port(Symbol(m2.name, :_, p.name), p.type))
    end
    return OpenEBCM(Symbol(m1.name, :_tensor_, m2.name), model, all_ports)
end

"""
    stratify(base, strata, mixing)

Cross a base model with a population structure.  For `K` strata, creates `K`
copies of the base model with cross-stratum coupling governed by the row-stochastic
`mixing` matrix (`mixing[i,j]` = fraction of contacts from stratum `i` directed
at stratum `j`).
"""
function stratify(base::OpenEBCM, strata::Vector{Symbol}, mixing::Matrix{Float64})
    K = length(strata)
    size(mixing) == (K, K) ||
        throw(ArgumentError("mixing matrix must be $K × $K, got $(size(mixing))"))

    base_model = base.model
    base_pgf   = base_model isa StaticConfigurationModel ? base_model.pgf :
                 error("stratify requires a StaticConfigurationModel base")
    prog = _get_progression(base_model)

    model = StratifiedModel(base_pgf, prog, strata, mixing)

    ports = Port[]
    _, outgoing = _transition_maps(prog)
    recovered = Set(_recovered_stages(prog, outgoing))
    for s in strata
        push!(ports, Port(Symbol(s, :_, prog.susceptible), :susceptible))
        for stage in prog.stages
            ptype = _stage_port_type(stage, recovered)
            push!(ports, Port(Symbol(s, :_, stage.name), ptype))
        end
    end
    return OpenEBCM(Symbol(base.name, :_stratified), model, ports)
end

# ============================================================
# §6  Natural transformations between model levels
# ============================================================

"""
    NaturalTransformation(name, source_type, target_type, description)

Metadata for a natural transformation between two model categories.
"""
struct NaturalTransformation
    name::Symbol
    source_type::Type
    target_type::Type
    description::String
end

function _pgf_excess_degree_ratio(pgf::DegreePGF)
    ψ_prime_1 = _eval_pgf_deriv(pgf, 1, 1)
    ψ_double_1 = _eval_pgf_deriv(pgf, 2, 1)
    return Symbolics.simplify(ψ_double_1 / ψ_prime_1)
end

"""
    to_mass_action(model::StaticConfigurationModel)

Transform an EBCM on a network to a mass-action approximation by matching the
edge-based excess-degree factor `ψ''(1)/ψ'(1)`. This is exact for Poisson
networks, where the excess degree ratio equals the mean degree.

Returns `(β_eff, γ)` where `β_eff = β · ψ''(1)/ψ'(1)`.
"""
function to_mass_action(model::StaticConfigurationModel)
    prog = model.progression
    excess_degree = _pgf_excess_degree_ratio(model.pgf)

    infectious_stages = [s for s in prog.stages if !_is_zero_rate(s.transmission_rate)]
    isempty(infectious_stages) && throw(ArgumentError("no infectious stages found"))

    β_total = sum(s.transmission_rate for s in infectious_stages)
    β_eff   = Symbolics.simplify(β_total * excess_degree)

    γ_total = sum(
        tr.rate for tr in prog.transitions
        if any(s.name == tr.source && !_is_zero_rate(s.transmission_rate)
               for s in prog.stages);
        init = 0)

    return (β_eff = β_eff, γ = γ_total)
end

"""
    compare_models(model; tspan, ε)

Solve both the EBCM and its mass-action approximation over `tspan`.
Requires numeric (non-symbolic) parameters.
Returns a named tuple `(ebcm, mass_action, β_eff, γ)`.
"""
function compare_models(model::StaticConfigurationModel;
                        tspan = (0.0, 100.0), ε = 1e-3)
    prog = model.progression
    _require_compact_form_supported(prog)

    # Numeric excess degree ratio; for Poisson networks this equals the mean degree.
    ψ_prime_fn = _build_pgf_deriv_fn(model.pgf, 1)
    ψ_double_fn = _build_pgf_deriv_fn(model.pgf, 2)
    excess_degree = ψ_double_fn(1.0) / ψ_prime_fn(1.0)

    infectious = [s for s in prog.stages if !_is_zero_rate(s.transmission_rate)]
    β_num  = sum(_to_float64(s.transmission_rate) for s in infectious)
    β_eff  = β_num * excess_degree

    γ_num  = sum(
        _to_float64(tr.rate) for tr in prog.transitions
        if any(s.name == tr.source && !_is_zero_rate(s.transmission_rate)
               for s in prog.stages);
        init = 0.0)

    # --- Solve EBCM (compact form self-seeds the epidemic from θ < 1) ---
    ebcm_sys = build_edge_system(model; form = :compact)
    ic_ebcm  = default_initial_conditions(ebcm_sys; ε = ε)
    prob_ebcm = ODEProblem(ebcm_sys.system, ic_ebcm, tspan)
    sol_ebcm  = solve(prob_ebcm; abstol = 1e-8, reltol = 1e-8)

    # --- Solve mass-action SIR ---
    t = t_nounits
    D = D_nounits
    @variables S_ma(t) I_ma(t) R_ma(t)

    eqs_ma = [
        D(S_ma) ~ -β_eff * S_ma * I_ma,
        D(I_ma) ~  β_eff * S_ma * I_ma - γ_num * I_ma,
        D(R_ma) ~  γ_num * I_ma,
    ]

    sys_ma      = System(eqs_ma, t; name = :mass_action_sir)
    compiled_ma = mtkcompile(sys_ma)
    ic_ma       = Dict(S_ma => 1.0 - ε, I_ma => ε, R_ma => 0.0)
    prob_ma     = ODEProblem(compiled_ma, ic_ma, tspan)
    sol_ma      = solve(prob_ma; abstol = 1e-8, reltol = 1e-8)

    return (ebcm = sol_ebcm, ebcm_system = ebcm_sys,
            mass_action = sol_ma, ma_system = compiled_ma,
            ma_vars = (S = S_ma, I = I_ma, R = R_ma),
            β_eff = β_eff, γ = γ_num)
end

# ============================================================
# §7  Functor  F : Network → ODE
# ============================================================

"""
    EBCMFunctor(name)

A functor that maps an `OpenEBCM` (in the network category) to an
`EdgeModelSystem` (in the ODE category) via `build_edge_system`.
"""
struct EBCMFunctor
    name::Symbol
end

function (F::EBCMFunctor)(open::OpenEBCM; kwargs...)
    return build_edge_system(open.model; kwargs...)
end

"""
    verify_functoriality(m1, m2, wiring; tspan, atol)

Verify that `F(compose(m1, m2, wiring))` gives the same trajectories
as composing the individual ODE systems.

For empty `wiring` (tensor product), this checks that each component
of `F(m1 ⊗ m2)` matches the standalone `F(m1)` and `F(m2)`.

Returns a named tuple with solutions, retcodes, trajectory differences,
and a boolean `is_functorial`.
"""
function verify_functoriality(m1::OpenEBCM, m2::OpenEBCM, wiring;
                               tspan = (0.0, 100.0), atol = 1e-4)
    F = EBCMFunctor(:F)

    # Path 1: compose in the model category, then apply functor
    composed = isempty(wiring) ? tensor(m1, m2) : compose(m1, m2, wiring)
    sys_composed = F(composed)
    ic_composed  = default_initial_conditions(sys_composed)
    prob_composed = ODEProblem(sys_composed.system, ic_composed, tspan)
    sol_composed  = solve(prob_composed; abstol = 1e-8, reltol = 1e-8)

    # Path 2: apply functor individually
    sys1 = F(m1)
    sys2 = F(m2)
    ic1  = default_initial_conditions(sys1)
    ic2  = default_initial_conditions(sys2)
    prob1 = ODEProblem(sys1.system, ic1, tspan)
    prob2 = ODEProblem(sys2.system, ic2, tspan)
    sol1  = solve(prob1; abstol = 1e-8, reltol = 1e-8)
    sol2  = solve(prob2; abstol = 1e-8, reltol = 1e-8)

    # Compare trajectories (for tensor products the components are independent)
    max_diff = 0.0
    if isempty(wiring)
        ts = range(tspan[1], tspan[2]; length = 50)
        θ1_comp = sys_composed.variables[Symbol(:θ_, m1.name)]
        θ2_comp = sys_composed.variables[Symbol(:θ_, m2.name)]
        θ1_solo = sys1.variables[:θ]
        θ2_solo = sys2.variables[:θ]
        for t_val in ts
            d1 = abs(sol_composed(t_val, idxs = θ1_comp) -
                     sol1(t_val, idxs = θ1_solo))
            d2 = abs(sol_composed(t_val, idxs = θ2_comp) -
                     sol2(t_val, idxs = θ2_solo))
            max_diff = max(max_diff, d1, d2)
        end
    end

    return (
        composed_solution    = sol_composed,
        individual_solutions = (sol1, sol2),
        max_difference       = max_diff,
        is_functorial        = max_diff < atol,
        composed_retcode     = sol_composed.retcode,
        individual_retcodes  = (sol1.retcode, sol2.retcode),
    )
end
