_cleanup_exp_zero(expr) = Symbolics.substitute(
    expr,
    Dict(exp(Symbolics.Num(0)) => 1, exp(Symbolics.Num(0.0)) => 1),
)

struct DegreePGF
    variable
    expression
end

function polynomial_pgf(probabilities::AbstractVector; varname::Symbol = :z)
    isempty(probabilities) && throw(ArgumentError("probabilities must not be empty"))

    total_probability = sum(probabilities)
    isapprox(total_probability, one(total_probability); atol = 1e-8) ||
        throw(ArgumentError("probabilities must sum to 1, got $(total_probability)"))

    variable = only(@variables $(varname))
    expression = zero(variable)

    for (index, probability) in pairs(probabilities)
        degree = index - 1
        expression += probability * variable^degree
    end

    return DegreePGF(variable, Symbolics.simplify(expression))
end

function poisson_pgf(mean_contacts; varname::Symbol = :z)
    variable = only(@variables $(varname))
    expression = exp(mean_contacts * (variable - 1))
    return DegreePGF(variable, expression)
end

function pgf_derivative(pgf::DegreePGF, order::Integer = 1)
    order < 0 && throw(ArgumentError("order must be non-negative"))

    expression = pgf.expression
    derivative_operator = Differential(pgf.variable)

    for _ in 1:order
        expression = Symbolics.expand_derivatives(derivative_operator(expression))
    end

    return Symbolics.simplify(expression)
end

function mean_degree(pgf::DegreePGF)
    first_derivative = pgf_derivative(pgf, 1)
    return Symbolics.simplify(Symbolics.substitute(first_derivative, Dict(pgf.variable => 1)))
end

# --- Multivariate PGFs for multi-type networks ---

struct MultivariatePGF
    types::Vector{Symbol}
    variables::Vector   # Symbolic variables, one per type
    expression          # ψ(x₁, x₂, ..., x_K)
end

function partial_derivative(pgf::MultivariatePGF, type::Symbol, order::Integer = 1)
    order < 0 && throw(ArgumentError("order must be non-negative"))
    idx = findfirst(==(type), pgf.types)
    isnothing(idx) && throw(ArgumentError("type $type not found in PGF types $(pgf.types)"))

    expression = pgf.expression
    D = Differential(pgf.variables[idx])
    for _ in 1:order
        expression = Symbolics.expand_derivatives(D(expression))
    end
    return Symbolics.simplify(expression)
end

function mixed_partial(pgf::MultivariatePGF, type1::Symbol, type2::Symbol)
    idx1 = findfirst(==(type1), pgf.types)
    idx2 = findfirst(==(type2), pgf.types)
    isnothing(idx1) && throw(ArgumentError("type $type1 not found in PGF types"))
    isnothing(idx2) && throw(ArgumentError("type $type2 not found in PGF types"))

    D1 = Differential(pgf.variables[idx1])
    D2 = Differential(pgf.variables[idx2])
    expr = Symbolics.expand_derivatives(D1(pgf.expression))
    expr = Symbolics.expand_derivatives(D2(expr))
    return Symbolics.simplify(expr)
end

function eval_multivariate_pgf(pgf::MultivariatePGF, substitutions::Dict)
    sub_dict = Dict{Any, Any}()
    for (type, val) in substitutions
        idx = findfirst(==(type), pgf.types)
        isnothing(idx) && throw(ArgumentError("type $type not found in PGF types"))
        sub_dict[pgf.variables[idx]] = val
    end
    return _cleanup_exp_zero(Symbolics.simplify(Symbolics.substitute(pgf.expression, sub_dict)))
end

function multivariate_poisson_pgf(types::Vector{Symbol}, mean_contacts::Dict)
    K = length(types)
    variables = []
    for type in types
        varname = Symbol("z_", type)
        push!(variables, only(@variables $(varname)))
    end

    expression = zero(first(variables))
    for (i, type) in enumerate(types)
        κ = get(mean_contacts, type, 0)
        expression += κ * (variables[i] - 1)
    end
    expression = exp(expression)

    return MultivariatePGF(types, variables, expression)
end

function independent_pgf(type_pgf_pairs::Pair{Symbol, DegreePGF}...)
    types = Symbol[]
    variables = []
    product_expr = 1

    for (type, univariate) in type_pgf_pairs
        push!(types, type)
        new_var = only(@variables $(Symbol("z_", type)))
        push!(variables, new_var)
        # Substitute the univariate variable with the new type-specific variable
        renamed = Symbolics.substitute(univariate.expression, Dict(univariate.variable => new_var))
        product_expr = product_expr * renamed
    end

    return MultivariatePGF(types, variables, Symbolics.simplify(product_expr))
end

function mean_degree(pgf::MultivariatePGF, type::Symbol)
    deriv = partial_derivative(pgf, type, 1)
    ones_dict = Dict{Any, Any}(v => 1 for v in pgf.variables)
    return _cleanup_exp_zero(Symbolics.simplify(Symbolics.substitute(deriv, ones_dict)))
end

# ==========================================================================
# Clustered (bivariate) PGF: g(x,y) = Σ p_{s,t} x^s y^t
# where s = single-edge stubs and t = triangle-edge stubs
# ==========================================================================

struct ClusteredPGF
    single_var    # symbolic variable x (single-edge stubs)
    triangle_var  # symbolic variable y (triangle-edge stubs)
    expression    # g(x,y) = Σ p_{s,t} x^s y^t
end

function clustered_pgf(joint_probs::AbstractMatrix;
                       single_var::Symbol = :x, triangle_var::Symbol = :y)
    # joint_probs[s+1, t+1] = P(s single-stubs, t triangle-stubs)
    total = sum(joint_probs)
    isapprox(total, 1.0; atol=1e-8) || throw(ArgumentError("joint probabilities must sum to 1, got $total"))

    xvar = only(@variables $(single_var))
    yvar = only(@variables $(triangle_var))
    expr = zero(xvar)
    for s in axes(joint_probs, 1), t in axes(joint_probs, 2)
        p = joint_probs[s, t]
        if !iszero(p)
            expr += p * xvar^(s-1) * yvar^(t-1)
        end
    end
    ClusteredPGF(xvar, yvar, Symbolics.simplify(expr))
end

function clustered_poisson_pgf(κ_single, κ_triangle;
                                single_var::Symbol = :x, triangle_var::Symbol = :y)
    xvar = only(@variables $(single_var))
    yvar = only(@variables $(triangle_var))
    expr = exp(κ_single * (xvar - 1) + κ_triangle * (yvar - 1))
    ClusteredPGF(xvar, yvar, expr)
end

function mean_single_degree(pgf::ClusteredPGF)
    D = Differential(pgf.single_var)
    deriv = Symbolics.expand_derivatives(D(pgf.expression))
    Symbolics.simplify(Symbolics.substitute(deriv, Dict(pgf.single_var => 1, pgf.triangle_var => 1)))
end

function mean_triangle_degree(pgf::ClusteredPGF)
    D = Differential(pgf.triangle_var)
    deriv = Symbolics.expand_derivatives(D(pgf.expression))
    Symbolics.simplify(Symbolics.substitute(deriv, Dict(pgf.single_var => 1, pgf.triangle_var => 1)))
end

# C = 2⟨t⟩/(2⟨t⟩ + ⟨s⟩) where s=singles, t=triangles
function clustering_coefficient(pgf::ClusteredPGF)
    s = mean_single_degree(pgf)
    t = mean_triangle_degree(pgf)
    Symbolics.simplify(2t / (2t + s))
end

function clustered_pgf_derivative(pgf::ClusteredPGF, wrt::Symbol, order::Integer = 1)
    var = wrt == :single ? pgf.single_var : pgf.triangle_var
    expr = pgf.expression
    D = Differential(var)
    for _ in 1:order
        expr = Symbolics.expand_derivatives(D(expr))
    end
    Symbolics.simplify(expr)
end

function _eval_clustered(pgf::ClusteredPGF, x_val, y_val)
    Symbolics.simplify(Symbolics.substitute(pgf.expression,
        Dict(pgf.single_var => x_val, pgf.triangle_var => y_val)))
end

function _eval_clustered_deriv(pgf::ClusteredPGF, wrt::Symbol, order::Integer, x_val, y_val)
    deriv = clustered_pgf_derivative(pgf, wrt, order)
    Symbolics.simplify(Symbolics.substitute(deriv,
        Dict(pgf.single_var => x_val, pgf.triangle_var => y_val)))
end

# --- Degree-correlated networks (Wang et al 2019) ---

"""
    CorrelatedPGF(base_pgf, max_degree, degree_probs, mixing_matrix)

A degree-correlated network described by a base PGF ψ(z) and a mixing matrix Q
where Q[k,l] = P(neighbor has degree l | ego has degree k).

For neutral (uncorrelated) mixing: Q[k,l] = l·p_l/⟨k⟩.
"""
struct CorrelatedPGF
    base_pgf::DegreePGF
    max_degree::Int
    degree_probs::Vector{Float64}
    mixing_matrix::Matrix{Float64}
end

"""
    correlated_pgf(degree_probs, mixing_matrix)

Construct a `CorrelatedPGF` from a degree distribution and a row-stochastic mixing matrix
Q where Q[k+1, l+1] = P(neighbor has degree l | ego has degree k).
"""
function correlated_pgf(degree_probs::AbstractVector, mixing_matrix::AbstractMatrix)
    K = length(degree_probs) - 1
    size(mixing_matrix) == (K+1, K+1) || throw(ArgumentError(
        "mixing matrix must be $(K+1)×$(K+1), got $(size(mixing_matrix))"))

    for k in 1:K+1
        s = sum(mixing_matrix[k, :])
        isapprox(s, 1.0; atol=1e-8) || throw(ArgumentError(
            "mixing matrix row $k sums to $s, not 1"))
    end

    base = polynomial_pgf(degree_probs)
    CorrelatedPGF(base, K, collect(Float64, degree_probs), collect(Float64, mixing_matrix))
end

"""
    neutral_correlated_pgf(degree_probs)

Create a `CorrelatedPGF` with neutral (uncorrelated) mixing: Q(l|k) = l·p_l/⟨k⟩.
"""
function neutral_correlated_pgf(degree_probs::AbstractVector)
    K = length(degree_probs) - 1
    mean_k = sum((k-1) * degree_probs[k] for k in 1:K+1)
    mean_k > 0 || throw(ArgumentError("degree distribution must have positive mean degree"))
    Q = zeros(K+1, K+1)
    for k in 1:K+1, l in 1:K+1
        Q[k, l] = (l - 1) * degree_probs[l] / mean_k
    end
    for k in 1:K+1
        s = sum(Q[k, :])
        if s < 1e-12
            Q[k, :] .= degree_probs
        else
            Q[k, :] ./= s
        end
    end
    correlated_pgf(degree_probs, Q)
end

"""
    assortative_correlated_pgf(degree_probs, r)

Create a `CorrelatedPGF` with Newman-style assortativity parameter r ∈ [0,1].
r=0 is neutral, r=1 is perfectly assortative (same-degree neighbors).
Q_r(l|k) = r·δ(k,l) + (1-r)·Q_neutral(l|k)
"""
function assortative_correlated_pgf(degree_probs::AbstractVector, r::Real)
    0 ≤ r ≤ 1 || throw(ArgumentError("assortativity r must be in [0,1], got $r"))
    K = length(degree_probs) - 1
    neutral = neutral_correlated_pgf(degree_probs)
    Q = copy(neutral.mixing_matrix)
    for k in 1:K+1, l in 1:K+1
        Q[k, l] = r * (k == l ? 1.0 : 0.0) + (1 - r) * neutral.mixing_matrix[k, l]
    end
    for k in 1:K+1
        s = sum(Q[k, :])
        if s > 1e-12
            Q[k, :] ./= s
        end
    end
    correlated_pgf(degree_probs, Q)
end

"""
    correlated_R0(cpgf::CorrelatedPGF, T::Real)

R₀ for a degree-correlated network: T · ρ(C) where C[k,l] = (k-1) · Q(l|k)
is the next-generation matrix (excess degree) and ρ is its spectral radius.
"""
function correlated_R0(cpgf::CorrelatedPGF, T::Real)
    K = cpgf.max_degree
    C = zeros(K+1, K+1)
    for k in 0:K, l in 0:K
        C[k+1, l+1] = max(k - 1, 0) * cpgf.mixing_matrix[k+1, l+1]
    end
    spectral_radius = maximum(abs.(eigvals(C)))
    return T * spectral_radius
end
