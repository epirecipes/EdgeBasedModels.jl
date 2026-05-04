# --- Numeric helpers ---
# Shared scalar conversion lives in builders.jl so analysis and initialization
# use the same symbolic-to-numeric semantics.

"""
    _build_pgf_fn(pgf::DegreePGF)

Compile the PGF expression into a callable `Float64 → Float64` function.
"""
function _build_pgf_fn(pgf::DegreePGF)
    Symbolics.build_function(pgf.expression, pgf.variable; expression = Val{false})
end

"""
    _build_pgf_deriv_fn(pgf::DegreePGF, order::Integer)

Compile the `order`-th derivative of the PGF into a callable `Float64 → Float64` function.
"""
function _build_pgf_deriv_fn(pgf::DegreePGF, order::Integer)
    deriv = pgf_derivative(pgf, order)
    Symbolics.build_function(deriv, pgf.variable; expression = Val{false})
end

"""
    _compute_transmissibility(prog::DiseaseProgression)

Compute the scalar transmissibility T from the disease progression.
For SIR: T = β/(β+γ). For multi-stage: T = 1 - ∏(γ_m/(β_m+γ_m)).
"""
function _compute_transmissibility(prog::DiseaseProgression)
    infectious_stages = [s for s in prog.stages if !_is_zero_rate(s.transmission_rate)]
    isempty(infectious_stages) && throw(ArgumentError(
        "DiseaseProgression has no infectious stages with a non-zero transmission rate; " *
        "cannot compute transmissibility"))

    if length(infectious_stages) == 1
        stage = only(infectious_stages)
        β = _to_float64(stage.transmission_rate)
        outgoing_rate = sum(
            _to_float64(tr.rate) for tr in prog.transitions if tr.source == stage.name;
            init = 0.0,
        )
        return β / (β + outgoing_rate)
    else
        outgoing = Dict(s.name => DiseaseTransition[] for s in prog.stages)
        for tr in prog.transitions
            push!(outgoing[tr.source], tr)
        end
        survival = 1.0
        for stage in prog.stages
            _is_zero_rate(stage.transmission_rate) && continue
            β_val = _to_float64(stage.transmission_rate)
            γ_val = sum(_to_float64(tr.rate) for tr in outgoing[stage.name]; init = 0.0)
            survival *= γ_val / (β_val + γ_val)
        end
        return 1.0 - survival
    end
end

# --- Analysis functions ---

"""
    final_size(model::StaticConfigurationModel; tol=1e-12, maxiter=1000)

Compute the epidemic final size R(∞) = 1 - ψ(θ∞) where θ∞ is the
fixed-point of θ = 1 - T + T·ψ'(θ)/ψ'(1).

Returns a named tuple `(R_infinity, θ_infinity)`.
For sub-threshold epidemics (R₀ ≤ 1), returns `(R_infinity=0.0, θ_infinity=1.0)`.
"""
function final_size(model::StaticConfigurationModel; tol = 1e-12, maxiter = 1000)
    pgf = model.pgf

    T_val = _compute_transmissibility(model.progression)
    ψ_fn = _build_pgf_fn(pgf)
    ψ′_fn = _build_pgf_deriv_fn(pgf, 1)

    ψ_prime_1 = ψ′_fn(1.0)

    # Fixed-point iteration: θ_{n+1} = 1 - T + T · ψ'(θ_n)/ψ'(1)
    θ = 1.0 - 1e-6
    for _ in 1:maxiter
        θ_new = 1.0 - T_val + T_val * ψ′_fn(θ) / ψ_prime_1
        if abs(θ_new - θ) < tol
            θ = θ_new
            break
        end
        θ = θ_new
    end

    if θ > 1.0 - tol
        return (R_infinity = 0.0, θ_infinity = 1.0)
    end

    R_inf = 1.0 - ψ_fn(θ)
    return (R_infinity = R_inf, θ_infinity = θ)
end

"""
    epidemic_probability(model::StaticConfigurationModel; tol=1e-12, maxiter=1000)

Compute the probability that a single infected individual causes a major epidemic.

Returns `P(major epidemic) = 1 - ψ(1 - T + T·q)` where `q` is the extinction
probability of the branching process, satisfying `q = ψ'(1-T+Tq)/ψ'(1)`.
For sub-threshold epidemics (R₀ ≤ 1), returns `0.0`.
"""
function epidemic_probability(model::StaticConfigurationModel; tol = 1e-12, maxiter = 1000)
    pgf = model.pgf

    T_val = _compute_transmissibility(model.progression)
    ψ_fn = _build_pgf_fn(pgf)
    ψ′_fn = _build_pgf_deriv_fn(pgf, 1)
    ψ″_fn = _build_pgf_deriv_fn(pgf, 2)

    ψ_prime_1 = ψ′_fn(1.0)
    R0 = T_val * ψ″_fn(1.0) / ψ_prime_1
    if R0 <= 1.0
        return 0.0
    end

    # Offspring PGF: G₁(x) = ψ'(1-T+Tx)/ψ'(1)
    # Fixed-point: q = G₁(q) where q is extinction probability
    q = 0.5
    for _ in 1:maxiter
        arg = 1.0 - T_val + T_val * q
        q_new = ψ′_fn(arg) / ψ_prime_1
        if abs(q_new - q) < tol
            q = q_new
            break
        end
        q = q_new
    end

    arg = 1.0 - T_val + T_val * q
    return 1.0 - ψ_fn(arg)
end

"""
    confidence_bands(model::StaticConfigurationModel, N::Int; level=0.95)

Compute CLT-based confidence bands for the final epidemic size in a
population of size N. Returns a named tuple `(lower, mean, upper, variance, std_error)`
as fractions.

Based on Ball (2021) "Central limit theorems for SIR epidemics and percolation
on configuration model random graphs."
"""
function confidence_bands(model::StaticConfigurationModel, N::Int; level = 0.95)
    fs = final_size(model)
    z = fs.R_infinity
    θ∞ = fs.θ_infinity

    if z < 1e-10
        return (lower = 0.0, mean = 0.0, upper = 0.0, variance = 0.0, std_error = 0.0)
    end

    pgf = model.pgf
    T_val = _compute_transmissibility(model.progression)

    ψ′_fn = _build_pgf_deriv_fn(pgf, 1)
    ψ″_fn = _build_pgf_deriv_fn(pgf, 2)

    ψ_prime_1 = ψ′_fn(1.0)
    ψ_prime_θ = ψ′_fn(θ∞)
    ψ_double_θ = ψ″_fn(θ∞)

    # Derivative of the fixed-point map at θ∞
    # h(θ) = 1 - T + T·ψ'(θ)/ψ'(1), so h'(θ) = T·ψ''(θ)/ψ'(1)
    h_prime = T_val * ψ_double_θ / ψ_prime_1

    # Ball's variance: σ² = z(1-z) + z·T·ψ'(θ∞)·(1-θ∞) / (ψ'(1)·(1-h')²)
    denom = (1 - h_prime)^2
    if denom < 1e-15
        # Near critical: fall back to binomial approximation
        σ² = z * (1 - z)
    else
        network_correction = z * T_val * ψ_prime_θ * (1 - θ∞) / (ψ_prime_1 * denom)
        σ² = z * (1 - z) + network_correction
    end

    α = 1 - level
    z_quantile = _normal_quantile(1 - α / 2)

    se = sqrt(max(0.0, σ²) / N)
    lower = max(0.0, z - z_quantile * se)
    upper = min(1.0, z + z_quantile * se)

    return (lower = lower, mean = z, upper = upper, variance = σ², std_error = se)
end

"""
    basic_reproduction_number(cpgf::CorrelatedPGF, T::Real)

Compatibility overload: forwards to [`correlated_R0`](@ref).
"""
basic_reproduction_number(cpgf::CorrelatedPGF, T::Real) = correlated_R0(cpgf, T)

"""
    disease_free_equilibrium(model::StaticConfigurationModel)

Return the analytical disease-free equilibrium (DFE) as a `Dict{Symbol,Float64}`
with all probability mass concentrated in the susceptible compartment:
`S = 1.0`, all other stage populations = `0.0`, `θ = 1.0`, and each `φ_X = 0.0`.

This is exact rather than the near-DFE numerical seed returned by
`default_initial_conditions`.
"""
function disease_free_equilibrium(model::StaticConfigurationModel)
    dfe = Dict{Symbol,Float64}(:S => 1.0, :θ => 1.0)
    for stage in model.progression.stages
        dfe[stage.name] = 0.0
        dfe[Symbol("φ_", stage.name)] = 0.0
    end
    return dfe
end

"""
    epidemic_threshold(model::StaticConfigurationModel)

Return the critical transmission rate `β_c` at which `R₀ = 1`.

For a single infectious stage with combined exit rate `γ_total`:
`R₀ = (β / (β + γ_total)) · κ = 1`  ⟹  `β_c = γ_total / (κ - 1)`,
where `κ = ψ''(1)/ψ'(1)` is the excess-degree ratio. The result is symbolic
when `γ_total` is symbolic and numeric otherwise.

Throws `ArgumentError` when `κ` is numerically `≤ 1` (no positive threshold) or
when the progression has more than one infectious stage (multi-stage analytic
solution not yet implemented).
"""
function epidemic_threshold(model::StaticConfigurationModel)
    prog = model.progression
    infectious = [s for s in prog.stages if !_is_zero_rate(s.transmission_rate)]
    isempty(infectious) && throw(ArgumentError("model has no infectious stages"))

    ψ_prime_1  = _eval_pgf_deriv(model.pgf, 1, 1)
    ψ_double_1 = _eval_pgf_deriv(model.pgf, 2, 1)
    κ_sym = Symbolics.simplify(ψ_double_1 / ψ_prime_1)
    # Only check κ > 1 when κ is fully numeric.
    κ_val = try _to_float64(κ_sym) catch; nothing end
    if κ_val !== nothing && κ_val <= 1
        throw(ArgumentError(
            "excess degree ratio κ = $(κ_val) ≤ 1; no positive epidemic threshold exists"))
    end

    if length(infectious) == 1
        stage = only(infectious)
        γ_total = sum(tr.rate for tr in prog.transitions if tr.source == stage.name; init = 0)
        return Symbolics.simplify(γ_total / (κ_sym - 1))
    end

    throw(ArgumentError(
        "epidemic_threshold for multi-stage progressions is not yet implemented; " *
        "use basic_reproduction_number and root-find numerically"))
end

# --- Bidirectional API parity aliases (additive, non-breaking) ---
# Mirror NodeBasedModels' `generate_*` naming so users can call either spelling.

"""
    generate_edge_system(args...; kwargs...)

Alias for [`build_edge_system`](@ref). Provided for naming parity with
NodeBasedModels.jl's `generate_pairwise` / `generate_individual_based`.
"""
generate_edge_system(args...; kwargs...) = build_edge_system(args...; kwargs...)

const generate_sir = build_sir
const generate_seir = build_seir
const generate_sis = build_sis
const generate_clustered_sir = build_clustered_sir
const generate_clustered_seir = build_clustered_seir

# Rational approximation to the standard normal quantile (Abramowitz & Stegun 26.2.23).
# Accurate to ~1e-4 for p ∈ (0, 1).
function _normal_quantile(p)
    if p < 0.5
        return -_normal_quantile(1 - p)
    end
    t = sqrt(-2 * log(1 - p))
    c0, c1, c2 = 2.515517, 0.802853, 0.010328
    d1, d2, d3 = 1.432788, 0.189269, 0.001308
    t - (c0 + c1 * t + c2 * t^2) / (1 + d1 * t + d2 * t^2 + d3 * t^3)
end
