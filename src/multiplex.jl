# ==========================================================================
# Multiplex / multi-layer network support
# ==========================================================================

"""
    NetworkLayer(name, pgf, progression)

A single layer of a multiplex network, with its own degree distribution
(PGF) and disease transmission dynamics.

Each layer represents an independent contact network (e.g., household,
workplace, community) through which disease can spread.
"""
struct NetworkLayer
    name::Symbol
    pgf::DegreePGF
    progression::DiseaseProgression
end

"""
    MultiplexModel(layers)

A multiplex network model composed of multiple independent layers.
Each layer has its own PGF and disease dynamics. A node's total
infection hazard is the sum across all layers.

The model generates one θ variable per layer, and S(t) = ∏ᵢ ψᵢ(θᵢ(t)).
"""
struct MultiplexModel
    layers::Vector{NetworkLayer}
end

"""
    build_multiplex_sir(layers; tspan=(0.0, 100.0))

Build a multiplex SIR model from a vector of `(name, pgf, β, γ)` tuples.
Each layer gets its own `θᵢ` variable following the Miller compact EBCM, plus
a shared recovery variable `R`.

Per-layer compact EBCM (Miller 2011):
- `dθᵢ/dt = -βᵢ·θᵢ + βᵢ·ψ'ᵢ(θᵢ)/ψ'ᵢ(1) + γᵢ·(1 - θᵢ)`

Population level:
- `S(t) = ∏ᵢ ψᵢ(θᵢ(t))`
- `dR/dt = γ·(1 - S - R)` with a common recovery rate `γ` shared by every layer

Returns `(system, u0, tspan, params)` suitable for `ODEProblem`.
"""
function _same_recovery_parameter(a, b)
    if a isa Number && b isa Number
        return isapprox(a, b)
    end
    return isequal(a, b)
end

function _shared_layer_recovery(layers)
    isempty(layers) && throw(ArgumentError("layers must not be empty"))
    γ_shared = layers[1][4]
    for layer in layers[2:end]
        _same_recovery_parameter(layer[4], γ_shared) ||
            throw(ArgumentError("multiplex SIR requires the same recovery rate on every layer"))
    end
    return γ_shared
end

function build_multiplex_sir(layers::Vector; tspan=(0.0, 100.0))
    n = length(layers)
    γ_shared = _shared_layer_recovery(layers)

    t = t_nounits
    D = D_nounits

    # Create per-layer θ variables
    θ = [only(@variables $(Symbol("θ_$(l[1])"))(t)) for l in layers]

    # Population-level recovery
    R_var = only(@variables R(t))

    # Per-layer parameters
    β_params = [only(@parameters $(Symbol("β_$(l[1])"))) for l in layers]
    γ_params = [only(@parameters $(Symbol("γ_$(l[1])"))) for l in layers]

    # Extract PGFs and numeric values
    pgfs = [l[2] for l in layers]
    βs = [l[3] for l in layers]
    γs = [l[4] for l in layers]

    # Build equations using compact EBCM per layer
    eqs = Equation[]

    for i in 1:n
        ψ_prime_θ = _eval_pgf_deriv(pgfs[i], 1, θ[i])
        ψ_prime_1 = _eval_pgf_deriv(pgfs[i], 1, 1)

        # Miller compact: dθ/dt = -β·θ + β·ψ'(θ)/ψ'(1) + γ·(1 - θ)
        θ_dot = Symbolics.simplify(
            -β_params[i] * θ[i] + β_params[i] * (ψ_prime_θ / ψ_prime_1) + γ_params[i] * (1 - θ[i])
        )
        push!(eqs, D(θ[i]) ~ θ_dot)
    end

    # S(t) = ∏ψᵢ(θᵢ)
    S_expr = Symbolics.simplify(prod(_eval_pgf(pgfs[i], θ[i]) for i in 1:n))

    # dR/dt = γ·(1 - S - R) with a shared recovery rate across layers
    γ_recovery = γ_params[1]
    push!(eqs, D(R_var) ~ Symbolics.simplify(γ_recovery * (1 - S_expr - R_var)))

    sys = System(eqs, t; name = :multiplex_sir)
    sys = mtkcompile(sys)

    # Initial conditions
    ε = 1e-6
    u0 = Dict{Any,Float64}()
    for i in 1:n
        u0[θ[i]] = 1.0 - ε
    end
    u0[R_var] = 0.0

    p = Dict{Any,Float64}()
    for i in 1:n
        p[β_params[i]] = Float64(βs[i])
        p[γ_params[i]] = Float64(γ_shared)
    end

    return (sys, u0, tspan, p)
end

"""
    multiplex_R0(layers)

Compute R₀ for a multiplex SIR model. For independent layers,
R₀ = Σᵢ Tᵢ · (excess degree)ᵢ, since a susceptible node can be
infected through any layer.

Each element of `layers` is a `(name, pgf, β, γ)` tuple.
"""
function multiplex_R0(layers)
    _shared_layer_recovery(layers)
    total = 0.0
    for (name, pgf, β, γ) in layers
        T = β / (β + γ)
        ψ1 = _build_pgf_deriv_fn(pgf, 1)
        ψ2 = _build_pgf_deriv_fn(pgf, 2)
        mean_k = ψ1(1.0)
        mean_k2_k = ψ2(1.0)
        excess = mean_k2_k / mean_k
        total += T * excess
    end
    return total
end

"""
    basic_reproduction_number(layers::AbstractVector{<:Tuple})

Compatibility overload for multiplex SIR models: accepts a vector of
`(name, pgf, β, γ)` tuples and forwards to [`multiplex_R0`](@ref).
"""
basic_reproduction_number(layers::AbstractVector{<:Tuple}) = multiplex_R0(layers)

"""
    susceptible_fraction(pgfs, θ_values)

Compute `S(t) = ∏ᵢ ψᵢ(θᵢ(t))` for a multiplex model.
"""
function susceptible_fraction(pgfs::Vector, θ_values::Vector)
    fns = [_build_pgf_fn(pgf) for pgf in pgfs]
    prod(fns[i](θ_values[i]) for i in eachindex(pgfs))
end
