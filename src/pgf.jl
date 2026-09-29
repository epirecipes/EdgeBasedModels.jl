_cleanup_exp_zero(expr) = Symbolics.substitute(
    expr,
    Dict(exp(Symbolics.Num(0)) => 1, exp(Symbolics.Num(0.0)) => 1),
)

"""
    DegreePGF(variable, expression[, distribution])
    DegreePGF(d::DegreeDistribution; varname = :z)

The legacy (0.1) symbolic degree PGF ψ(z) = `expression` in the Symbolics variable `variable`. It
is a `NetworkEpiCore.DegreeDistribution`, so it can be wrapped in a `ConfigurationNetwork` and
passed to [`edge_based`](@ref) and the factories.

`distribution` is optional provenance: the NetworkEpiCore degree distribution the PGF was built
from (`poisson_pgf` and `polynomial_pgf` set it, as does `DegreePGF(d::DegreeDistribution)`), or
`nothing`. With provenance, `canonical_text`, `rand` and `degree_probabilities` forward to it,
so NetworkOutbreaks can sample graphs and scenarios can hash networks built from factory PGFs.

`DegreePGF(d)` builds the symbolic PGF of a NetworkEpiCore distribution (the closed form of
`pgf(d, z)`; `PoissonDegree` and finite supports give exactly the expressions of `poisson_pgf`
and `polynomial_pgf`); `DegreePGF(::DegreePGF)` is the identity.
"""
struct DegreePGF <: DegreeDistribution
    variable
    expression
    distribution::Union{Nothing,DegreeDistribution}
end

DegreePGF(variable, expression) = DegreePGF(variable, expression, nothing)
DegreePGF(d::DegreePGF) = d
DegreePGF(d::PoissonDegree; varname::Symbol = :z) = poisson_pgf(d.mean; varname)
DegreePGF(d::EmpiricalDegree; varname::Symbol = :z) = polynomial_pgf(d.p; varname)
DegreePGF(d::PowerLawDegree; varname::Symbol = :z) =
    _with_distribution(polynomial_pgf(degree_probabilities(d); varname), d)
DegreePGF(d::RegularDegree; varname::Symbol = :z) =
    _with_distribution(polynomial_pgf([k == d.k ? 1.0 : 0.0 for k in 0:(d.k)]; varname), d)
function DegreePGF(d::DegreeDistribution; varname::Symbol = :z)
    variable = only(@variables $(varname))
    return DegreePGF(variable, pgf(d, variable), d)
end

_with_distribution(p::DegreePGF, d::DegreeDistribution) = DegreePGF(p.variable, p.expression, d)

function Base.show(io::IO, p::DegreePGF)
    print(io, "DegreePGF(", p.variable, " ↦ ", p.expression)
    p.distribution === nothing || print(io, "; from ", p.distribution)
    print(io, ")")
end

# Provenance of the legacy constructors. A distribution is recorded only when it is a valid
# NetworkEpiCore distribution; otherwise (a negative or non-real mean, symbolic probabilities)
# the PGF keeps working symbolically without provenance.
_is_numeric_value(x) = x isa Real && !(x isa Symbolics.Num)
function _poisson_provenance(μ)
    μ isa Real || return nothing
    _is_numeric_value(μ) && !(isfinite(μ) && μ >= 0) && return nothing
    return PoissonDegree(μ)
end
function _empirical_provenance(probabilities)
    all(p -> _is_numeric_value(p) && isfinite(p) && p >= 0, probabilities) || return nothing
    any(p -> p > 0, probabilities) || return nothing
    return EmpiricalDegree(collect(Float64, probabilities))
end

"""
    polynomial_pgf(probabilities; varname = :z) -> DegreePGF

The PGF ψ(z) = Σₖ pₖ zᵏ of a finite degree distribution with `probabilities[k+1] = pₖ` (they must
sum to 1). Numeric probabilities record the provenance `EmpiricalDegree(probabilities)`.
"""
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

    return DegreePGF(variable, Symbolics.simplify(expression), _empirical_provenance(probabilities))
end

"""
    poisson_pgf(mean_contacts; varname = :z) -> DegreePGF

The Poisson PGF ψ(z) = exp(μ(z − 1)); `μ` may be symbolic. It records the provenance
`PoissonDegree(μ)`.
"""
function poisson_pgf(mean_contacts; varname::Symbol = :z)
    variable = only(@variables $(varname))
    expression = exp(mean_contacts * (variable - 1))
    return DegreePGF(variable, expression, _poisson_provenance(mean_contacts))
end

# --- NetworkEpiCore degree-distribution interface ---------------------------------------------

# A symbolic value with no free variables becomes a Float64; anything else stays symbolic.
function _numeric_or_symbolic(x)
    x isa Symbolics.Num || return x
    v = _maybe_to_float64(x)
    return v === nothing ? x : v
end

"""
    pgf(p::DegreePGF, x)

ψ(x), by substituting `x` for the PGF variable: a `Float64` when the result has no free symbols,
else a symbolic expression.
"""
pgf(p::DegreePGF, x) =
    _numeric_or_symbolic(_cleanup_exp_zero(Symbolics.substitute(p.expression, Dict(p.variable => x))))

"""
    pgf_derivative(p::DegreePGF, x, n::Integer)

ψ⁽ⁿ⁾(x) of a legacy PGF (symbolic differentiation, then substitution of `x`); compare the legacy
two-argument form `pgf_derivative(p, n)`, which returns the derivative as an expression in the
PGF variable.
"""
function pgf_derivative(p::DegreePGF, x, n::Integer)
    n >= 0 || throw(ArgumentError("the derivative order must be ≥ 0; got $n"))
    expression = n == 0 ? p.expression : pgf_derivative(p, n)
    return _numeric_or_symbolic(_cleanup_exp_zero(Symbolics.substitute(expression, Dict(p.variable => x))))
end

function _require_distribution(p::DegreePGF, what::AbstractString)
    p.distribution === nothing && throw(ArgumentError(
        "$what needs the degree distribution of the PGF, but this DegreePGF has no provenance " *
        "(it was not built by poisson_pgf, polynomial_pgf or DegreePGF(::DegreeDistribution)); " *
        "use a NetworkEpiCore degree distribution such as PoissonDegree or EmpiricalDegree"))
    return p.distribution
end

"""
    canonical_text(io::IO, p::DegreePGF)

The canonical text of the provenance distribution (so `ConfigurationNetwork(poisson_pgf(5.0))`
and `ConfigurationNetwork(PoissonDegree(5.0))` hash alike); an error without provenance.
"""
canonical_text(io::IO, p::DegreePGF) = canonical_text(io, _require_distribution(p, "canonical_text"))

"""
    rand([rng,] p::DegreePGF[, n])

Degrees drawn from the provenance distribution of `p` (an error without provenance).
"""
Random.rand(rng::Random.AbstractRNG, p::DegreePGF) = rand(rng, _require_distribution(p, "rand"))
Random.rand(rng::Random.AbstractRNG, p::DegreePGF, n::Integer) =
    rand(rng, _require_distribution(p, "rand"), n)

"""
    degree_probabilities(p::DegreePGF; kw...)

The probabilities of the provenance distribution of `p` (an error without provenance).
"""
degree_probabilities(p::DegreePGF; kw...) =
    degree_probabilities(_require_distribution(p, "degree_probabilities"); kw...)

"""
    is_poisson_type(p::DegreePGF)

The Poisson-type test of the provenance distribution; without provenance, NetworkEpiCore's
numeric test on the symbolic PGF (numeric parameters only).
"""
is_poisson_type(p::DegreePGF) = p.distribution === nothing ?
    invoke(is_poisson_type, Tuple{DegreeDistribution}, p) : is_poisson_type(p.distribution)

"""
    pgf_derivative(pgf::DegreePGF, order = 1)

The `order`-th derivative of the legacy PGF as a symbolic expression in `pgf.variable`.
"""
function pgf_derivative(pgf::DegreePGF, order::Integer = 1)
    order < 0 && throw(ArgumentError("order must be non-negative"))

    expression = pgf.expression
    derivative_operator = Differential(pgf.variable)

    for _ in 1:order
        expression = Symbolics.expand_derivatives(derivative_operator(expression))
    end

    return Symbolics.simplify(expression)
end

"""
    mean_degree(pgf::DegreePGF)

The mean degree ψ'(1) of a legacy PGF: a `Float64` when the PGF is numeric, else a (simplified)
symbolic expression (for example `κ` for `poisson_pgf(κ)`).
"""
function mean_degree(pgf::DegreePGF)
    first_derivative = pgf_derivative(pgf, 1)
    return _numeric_or_symbolic(Symbolics.simplify(Symbolics.substitute(first_derivative, Dict(pgf.variable => 1))))
end

# --- Multivariate PGFs for multi-type networks ---

"""
    MultivariatePGF(types, variables, expression[, distribution])

The legacy multivariate degree PGF ψ(x₁, …, x_K) of a node of one type in a multitype
configuration network: `variables[i]` counts the edges to partners of type `types[i]`.

`distribution` is optional provenance, as for [`DegreePGF`](@ref): the NetworkEpiCore
`MultivariateDegree` the PGF was built from, or `nothing`. [`multivariate_poisson_pgf`](@ref)
records `IndependentDegrees(b => PoissonDegree(κ_b), …)` and [`independent_pgf`](@ref) records
`IndependentDegrees(b => d_b, …)`. The legacy `MultiTypeConfigurationModel` is lowered onto a
NetworkEpiCore `MultitypeNetwork` built from these distributions, so a PGF without provenance
cannot be lowered (build it with one of those two constructors).
"""
struct MultivariatePGF
    types::Vector{Symbol}
    variables::Vector   # Symbolic variables, one per type
    expression          # ψ(x₁, x₂, ..., x_K)
    distribution::Union{Nothing,MultivariateDegree}
end

MultivariatePGF(types, variables, expression) = MultivariatePGF(types, variables, expression, nothing)

"""
    partial_derivative(pgf::MultivariatePGF, type, order = 1)

The `order`-th partial derivative of `pgf` in the variable of partner type `type`.
"""
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

"""
    mixed_partial(pgf::MultivariatePGF, type1, type2)

The mixed second partial derivative ∂²ψ/∂x_{type1}∂x_{type2}.
"""
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

"""
    eval_multivariate_pgf(pgf::MultivariatePGF, substitutions::Dict)

Substitute values for the variables of `pgf`, given as `type => value`.
"""
function eval_multivariate_pgf(pgf::MultivariatePGF, substitutions::Dict)
    sub_dict = Dict{Any, Any}()
    for (type, val) in substitutions
        idx = findfirst(==(type), pgf.types)
        isnothing(idx) && throw(ArgumentError("type $type not found in PGF types"))
        sub_dict[pgf.variables[idx]] = val
    end
    return _cleanup_exp_zero(Symbolics.simplify(Symbolics.substitute(pgf.expression, sub_dict)))
end

"""
    multivariate_poisson_pgf(types, mean_contacts::Dict)

Independent Poisson numbers of edges to each partner type: ψ(x) = exp(Σ_b κ_b (x_b − 1)),
with `mean_contacts[b] = κ_b` (0 when absent).
"""
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

    parts = Pair{Symbol,DegreeDistribution}[]
    for type in types
        κ = get(mean_contacts, type, 0)
        (_is_numeric_value(κ) && iszero(κ)) && continue
        d = _poisson_provenance(κ)
        d === nothing && return MultivariatePGF(types, variables, expression)
        push!(parts, type => d)
    end
    return MultivariatePGF(types, variables, expression, IndependentDegrees(parts))
end

"""
    independent_pgf(type => pgf, ...)

The product of independent univariate PGFs, one per partner type.
"""
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

    provenance = IndependentDegrees(Pair{Symbol,DegreeDistribution}[
        type => something(univariate.distribution, univariate) for (type, univariate) in type_pgf_pairs])
    return MultivariatePGF(types, variables, Symbolics.simplify(product_expr), provenance)
end

"""
    mean_degree(pgf::MultivariatePGF, type)

The mean number of edges to partners of type `type`, ∂ψ/∂x_type at x = 1.
"""
function mean_degree(pgf::MultivariatePGF, type::Symbol)
    deriv = partial_derivative(pgf, type, 1)
    ones_dict = Dict{Any, Any}(v => 1 for v in pgf.variables)
    return _cleanup_exp_zero(Symbolics.simplify(Symbolics.substitute(deriv, ones_dict)))
end

# ==========================================================================
# Clustered (bivariate) PGF: g(x,y) = Σ p_{s,t} x^s y^t
# where s = single-edge stubs and t = triangle-edge stubs
# ==========================================================================

"""
    ClusteredPGF(single_var, triangle_var, expression[, joint])

The legacy bivariate PGF g(x, y) = Σ p_{s,t} xˢ yᵗ of clustered (triangle) degrees: s single
edges and t triangles per node. `joint` is optional provenance, the NetworkEpiCore
`ClusteredDegree` it was built from (set by `clustered_pgf` and `clustered_poisson_pgf`), which
`ClusteredNetwork(g)` needs.
"""
struct ClusteredPGF
    single_var    # symbolic variable x (single-edge stubs)
    triangle_var  # symbolic variable y (triangle-edge stubs)
    expression    # g(x,y) = Σ p_{s,t} x^s y^t
    joint::Union{Nothing,ClusteredDegree}
end

ClusteredPGF(single_var, triangle_var, expression) =
    ClusteredPGF(single_var, triangle_var, expression, nothing)

function _clustered_matrix_provenance(P)
    all(p -> _is_numeric_value(p) && isfinite(p) && p >= 0, P) || return nothing
    any(p -> p > 0, P) || return nothing
    return ClusteredDegree(Matrix{Float64}(P))
end
function _clustered_poisson_provenance(κs, κt)
    s, t = _poisson_provenance(κs), _poisson_provenance(κt)
    return (s === nothing || t === nothing) ? nothing : ClusteredDegree(s, t)
end

"""
    clustered_pgf(joint_probs::AbstractMatrix; single_var = :x, triangle_var = :y) -> ClusteredPGF

g(x, y) = Σ p_{s,t} xˢ yᵗ with `joint_probs[s+1, t+1]` = P(s single edges, t triangles); the
probabilities must sum to 1. Numeric probabilities record the provenance
`ClusteredDegree(joint_probs)`.
"""
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
    ClusteredPGF(xvar, yvar, Symbolics.simplify(expr), _clustered_matrix_provenance(joint_probs))
end

"""
    clustered_poisson_pgf(κ_single, κ_triangle; single_var = :x, triangle_var = :y) -> ClusteredPGF

Independent Poisson numbers of single edges (mean `κ_single`) and triangles (mean
`κ_triangle`): g(x, y) = exp(κ_s(x − 1) + κ_t(y − 1)). It records the provenance
`ClusteredDegree(PoissonDegree(κ_single), PoissonDegree(κ_triangle))`.
"""
function clustered_poisson_pgf(κ_single, κ_triangle;
                                single_var::Symbol = :x, triangle_var::Symbol = :y)
    xvar = only(@variables $(single_var))
    yvar = only(@variables $(triangle_var))
    expr = exp(κ_single * (xvar - 1) + κ_triangle * (yvar - 1))
    ClusteredPGF(xvar, yvar, expr, _clustered_poisson_provenance(κ_single, κ_triangle))
end

"""
    mean_single_degree(pgf::ClusteredPGF)

The mean number of single (non-triangle) edges per node, ∂g/∂x at (1, 1).
"""
function mean_single_degree(pgf::ClusteredPGF)
    D = Differential(pgf.single_var)
    deriv = Symbolics.expand_derivatives(D(pgf.expression))
    Symbolics.simplify(Symbolics.substitute(deriv, Dict(pgf.single_var => 1, pgf.triangle_var => 1)))
end

"""
    mean_triangle_degree(pgf::ClusteredPGF)

The mean number of triangles per node, ∂g/∂y at (1, 1).
"""
function mean_triangle_degree(pgf::ClusteredPGF)
    D = Differential(pgf.triangle_var)
    deriv = Symbolics.expand_derivatives(D(pgf.expression))
    Symbolics.simplify(Symbolics.substitute(deriv, Dict(pgf.single_var => 1, pgf.triangle_var => 1)))
end

"""
    clustering_coefficient(pgf::ClusteredPGF)

The clustering coefficient (transitivity) of the clustered configuration network of `pgf`: the
fraction of connected triples that are closed, 2E[t]/E[k(k − 1)] with k = s + 2t, i.e.

    C = 2 g_y(1, 1) / G''(1),   G''(1) = g_xx + 4 g_xy + 4 g_yy + 2 g_y   (at (1, 1)),

where G(z) = g(z, z²) is the PGF of the total degree; 0 when the network has no triangles. This is
NetworkEpiCore's `clustering_coefficient(ClusteredNetwork(...))` (2/27 for
`clustered_poisson_pgf(3, 1)`), as a symbolic expression for a symbolic PGF. EdgeBasedModels 0.1
returned 2⟨t⟩/(2⟨t⟩ + ⟨s⟩), the fraction of edges in triangles (0.4 there; verified issue E03), which
is [`triangle_edge_fraction`](@ref)`(pgf)`.
"""
function clustering_coefficient(pgf::ClusteredPGF)
    t = mean_triangle_degree(pgf)
    v = Symbolics.value(t)
    (v isa Number && iszero(v)) && return 0.0
    x, y = pgf.single_var, pgf.triangle_var
    at1(e) = Symbolics.substitute(e, Dict(x => 1, y => 1))
    d(e, v) = Symbolics.expand_derivatives(Differential(v)(e))
    g = pgf.expression
    gy = d(g, y)
    G2 = at1(d(d(g, x), x)) + 4 * at1(d(gy, x)) + 4 * at1(d(gy, y)) + 2 * at1(gy)
    return _numeric_or_symbolic(_cleanup_exp_zero(Symbolics.simplify(2 * at1(gy) / G2)))
end

"""
    triangle_edge_fraction(pgf::ClusteredPGF)

The fraction of edges that lie in triangles, 2⟨t⟩/(⟨s⟩ + 2⟨t⟩) with ⟨s⟩ = ∂g/∂x and
⟨t⟩ = ∂g/∂y at (1, 1) (Volz's p_t), as a symbolic expression (a number for a numeric PGF): the
method of NetworkEpiCore's `triangle_edge_fraction` for the legacy clustered PGF, equal to
`triangle_edge_fraction(ClusteredNetwork(pgf))` when the PGF records its `ClusteredDegree`. It
is not the clustering coefficient (verified issue E03). It is 0 when the network has no
triangles.
"""
function NetworkEpiCore.triangle_edge_fraction(pgf::ClusteredPGF)
    t = mean_triangle_degree(pgf)
    v = Symbolics.value(t)
    (v isa Number && iszero(v)) && return 0.0
    return Symbolics.simplify(2t / (2t + mean_single_degree(pgf)))
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
