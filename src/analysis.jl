# Owner: WP19 (DESIGN_NetworkEpiCore.md §A.2 generics table, §A.3, §E.2; work package in §G.2).
#
# Threshold quantities, final size, the probability of a major outbreak and final-size
# fluctuations of edge-based models, for the legacy `StaticConfigurationModel` and for lowered
# systems (`EdgeModelSystem`). Verified issues addressed (VERIFIED_ISSUES.md, corrected fixes):
#
# - E14: the per-edge transmissibility of an arbitrary Markov progression is an absorbing-chain
#   solve, T = w_entry with (β_m + out_m) w_m − Σ_n r_{m→n} w_n = β_m (branching, bypasses,
#   cycles; `_edge_transmissibility`); `epidemic_threshold` uses the probability of reaching the
#   infectious stage and its effective exit rate.
# - E15: `epidemic_probability` is the infector-side branching-process formula. An infector's
#   transmissions along its edges are independent only given its path, so the offspring law is
#   the mixed binomial Bin(D̃ − 1, 1 − W), W = e^{−Λ}, Λ = ∫β_{X(t)}dt; the moments
#   φ(j) = E[W^j] come from one linear solve each (`_laplace`).
# - E16: `confidence_bands` is Ball (2021, Ann. Appl. Probab. 31:2091, Theorem 2.2): NSW (iid
#   degrees, the default) or MR (a prescribed degree sequence), with q_I = φ(1) and
#   q_I⁽²⁾ = φ(2).
# - E17: the SIR-type functions refuse progressions that return nodes to the susceptible class
#   (SIS, SIRS, and their `with_reinfection_counting` lifts).
# - E18: every fixed point is found by bracketing (Brent's method) with explicit threshold
#   tests: exactly 0 at or below threshold, no unconverged value is ever returned.
# - E31(i): `final_size(model; seed_fraction = ρ)` (Miller 2014 eqs (3)-(4) with φ_S(0) = 1 − ρ).
# - E12: `basic_reproduction_number(sys)` is ρ(K) of the next-generation matrix of the lifted
#   field (for a multiplex, never the sum of the layer R₀'s).
#
# Methods on `EdgeModelSystem` (the 0.2 API; the NetworkEpiCore generics with keyword `p`, as
# `solve_epidemic(sys; p)`):
#
# - `next_generation_matrix`, `basic_reproduction_number`, `transmissibility` and
#   `early_growth_rate` are computed from the lifted vector field itself (`symbolic_ode(sys)`,
#   linearised at the disease-free state), symbolically where a closed form exists: an
#   independent check of NetworkEpiCore's numeric next-generation matrix;
# - `final_size` uses NetworkEpiCore's fixed-point equations where they exist and integrates the
#   ODE otherwise (exits, several entry states, neighbour exchange);
# - `epidemic_probability` and `confidence_bands` evaluate the formulas above for the model and
#   network the system was lifted from.

# =============================================================================================
# Compiled PGFs (also used by the legacy categorical and multiplex code)
# =============================================================================================

"""
    _build_pgf_fn(pgf::DegreePGF)

Compile the PGF expression into a callable `Float64 → Float64` function (it also accepts complex
arguments when the expression is analytic).
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

# =============================================================================================
# Small numerical tools
# =============================================================================================

# Brent's method (van Wijngaarden–Dekker–Brent) on a bracket [a, b] with f(a)·f(b) ≤ 0, to an
# absolute tolerance `xtol` in x. Throws (never returns an unconverged value, E18).
function _brent_root(f, a::Float64, b::Float64, fa::Float64, fb::Float64;
                     xtol::Float64 = 1e-15, maxiter::Int = 300, what::AbstractString)
    (isfinite(fa) && isfinite(fb)) || throw(ArgumentError(
        "$(what): the equation is not finite at the ends of the bracket [$a, $b]"))
    fa == 0 && return a
    fb == 0 && return b
    sign(fa) == sign(fb) && throw(ArgumentError(
        "$(what): the root is not bracketed by [$a, $b] (values $fa and $fb)"))
    c, fc = b, fb
    d = e = b - a
    for _ in 1:maxiter
        if sign(fb) == sign(fc)
            c, fc = a, fa
            d = e = b - a
        end
        if abs(fc) < abs(fb)
            a, b, c = b, c, b
            fa, fb, fc = fb, fc, fb
        end
        tol1 = 2 * eps(Float64) * abs(b) + xtol / 2
        xm = (c - b) / 2
        (abs(xm) <= tol1 || fb == 0) && return b
        if abs(e) >= tol1 && abs(fa) > abs(fb)
            s = fb / fa
            if a == c
                p = 2 * xm * s
                q = 1 - s
            else
                q = fa / fc
                r = fb / fc
                p = s * (2 * xm * q * (q - r) - (b - a) * (r - 1))
                q = (q - 1) * (r - 1) * (s - 1)
            end
            p > 0 ? (q = -q) : (p = -p)
            if 2p < min(3 * xm * q - abs(tol1 * q), abs(e * q))
                e = d
                d = p / q
            else
                d = xm
                e = d
            end
        else
            d = xm
            e = d
        end
        a, fa = b, fb
        b += abs(d) > tol1 ? d : copysign(tol1, xm)
        fb = f(b)
        isfinite(fb) || throw(ArgumentError("$(what): the equation is not finite at x = $b"))
    end
    throw(ErrorException("$(what): no convergence in $maxiter Brent steps"))
end

# The least root in [0, 1) of a convex function g on [0, 1] with g(0) ≥ 0 and g(1) = 0 whose
# slope at 1 is positive (a supercritical fixed-point equation x = G(x) with G a PGF-like
# function): 0 if g(0) ≤ 0; otherwise the root is bracketed by halving the distance to 1 until
# g < 0. Returns 1.0 when g stays ≥ 0 down to a distance 1e-15 from 1 (numerically at the
# threshold, where the root and 1 coincide).
function _least_root(g; what::AbstractString, xtol::Real = 1e-16, maxiter::Integer = 300)
    g0 = g(0.0)
    g0 <= 0 && return 0.0
    δ = 0.5
    ghi = g(1 - δ)
    while ghi >= 0
        δ /= 2
        δ < 1e-15 && return 1.0
        ghi = g(1 - δ)
    end
    lo = δ == 0.5 ? 0.0 : 1 - 2δ
    glo = lo == 0.0 ? g0 : g(lo)
    return _brent_root(g, lo, 1 - δ, glo, ghi; xtol = Float64(xtol), maxiter = Int(maxiter), what)
end

# The states reachable from `from` along transitions (from, to, rate) with a nonzero rate.
function _reachable(transitions, from::Symbol)
    reach = Set{Symbol}([from])
    changed = true
    while changed
        changed = false
        for (a, b, r) in transitions
            (a in reach && b !== nothing && !(b in reach) && !_is_zero_rate(r)) || continue
            push!(reach, b)
            changed = true
        end
    end
    return reach
end

_iszero_symbolic(x::Symbolics.Num) = (v = Symbolics.value(x); v isa Number && iszero(v))
_iszero_symbolic(x::Number) = iszero(x)
_iszero_symbolic(x) = false

# Solve A X = B by Gaussian elimination without pivoting. Used for symbolic entries: every matrix
# solved here is a nonsingular M-matrix (a positive diagonal of exit rates, non-positive
# off-diagonal transition rates, diagonally dominant), whose pivots stay positive (E14).
function _solve_nopivot(A::AbstractMatrix, B::AbstractMatrix)
    n = size(A, 1)
    M = Matrix{Any}(A)
    X = Matrix{Any}(B)
    for k in 1:n
        piv = M[k, k]
        _iszero_symbolic(piv) && throw(LinearAlgebra.SingularException(k))
        for i in (k + 1):n
            _iszero_symbolic(M[i, k]) && continue
            f = M[i, k] / piv
            for j in (k + 1):n
                M[i, j] -= f * M[k, j]
            end
            for j in axes(X, 2)
                X[i, j] -= f * X[k, j]
            end
            M[i, k] = 0
        end
    end
    for i in n:-1:1, j in axes(X, 2)
        s = X[i, j]
        for k in (i + 1):n
            _iszero_symbolic(M[i, k]) || (s -= M[i, k] * X[k, j])
        end
        X[i, j] = s / M[i, i]
    end
    return X
end

_is_symbolic(x) = x isa Symbolics.Num || x isa Symbolics.SymbolicUtils.BasicSymbolic

# Symbolics.simplify, falling back to simplification without fraction cancellation where the
# polynomial gcd of the fraction simplifier fails (a DivideError in MultivariatePolynomials for some
# rational functions with Float64 coefficients, e.g. R₀ of five Erlang stages). The result is the
# same function either way.
function _simplify(x)
    _is_symbolic(x) || return x
    try
        return Symbolics.simplify(Symbolics.Num(x))
    catch err
        err isa Union{DivideError,InexactError} || rethrow()
        return Symbolics.simplify(Symbolics.Num(x); simplify_fractions = false)
    end
end

# A Float64, or nothing for a symbolic value with free variables. (`Symbolics.value` gives the
# number held by a symbolic constant; a constant expression such as an unfolded exp(0.0) is
# evaluated.)
function _float_or_nothing(x)
    if _is_symbolic(x)
        v = Symbolics.value(x)
        v isa Real && !_is_symbolic(v) && return Float64(v)
        isempty(Symbolics.get_variables(x)) || return nothing
        return _maybe_to_float64(Symbolics.Num(x))
    end
    x isa Real && return Float64(x)
    return nothing
end

# =============================================================================================
# The infector's Markov chain
# =============================================================================================

# The stage process of one infected node, seen from one of its edges: the transient states
# (those the start state can reach and from which a transmitting state is reachable), the
# per-edge transmission hazard β of each (the sum of the per-contact rates of its contacts with a
# susceptible partner), the transition rates R[m, n] between transient states and the total exit
# rate `out` of each (to transient or absorbing states). `start` is the index of the state the
# node enters (0 when it can never transmit). The cumulative hazard Λ = ∫β_{X(t)}dt of the path
# decides everything an infector does to its edges: each edge transmits with probability
# 1 − e^{−Λ}, independently given the path.
struct _InfectorChain{T}
    names::Vector{Symbol}
    β::Vector{T}
    R::Matrix{T}
    out::Vector{T}
    start::Int
end

# `stages`: the states of the chain; `β`: state => hazard; `transitions`: (from, to, rate), `to`
# `nothing` for an absorbing exit (a removal); `from`: the state entered.
function _infector_chain(stages::AbstractVector{Symbol}, β::AbstractDict, transitions, from::Symbol)
    from in stages || throw(ArgumentError("the state $(from) is not a state of the infection chain"))
    transitions = [(a, b, r) for (a, b, r) in transitions if a in stages]
    pred = Dict{Symbol,Vector{Symbol}}(s => Symbol[] for s in stages)
    for (a, b, r) in transitions
        (_is_zero_rate(r) || b === nothing || !(b in stages)) && continue
        push!(pred[b], a)
    end
    reach = _reachable(transitions, from)
    hazard = Set{Symbol}(s for s in stages if !_is_zero_rate(get(β, s, 0)))
    live = copy(hazard)
    stack = collect(hazard)
    while !isempty(stack)
        for a in pred[pop!(stack)]
            a in live || (push!(live, a); push!(stack, a))
        end
    end
    names = Symbol[s for s in stages if s in reach && s in live]
    idx = Dict(s => i for (i, s) in enumerate(names))
    rates = Any[get(β, s, 0) for s in names]
    for (_, _, r) in transitions
        push!(rates, r)
    end
    T = any(_is_symbolic, rates) ? Symbolics.Num : Float64
    n = length(names)
    βv = T[get(β, s, 0) for s in names]
    R = zeros(T, n, n)
    out = zeros(T, n)
    for (a, b, r) in transitions
        (haskey(idx, a) && !_is_zero_rate(r)) || continue
        out[idx[a]] += r
        b !== nothing && haskey(idx, b) && (R[idx[a], idx[b]] += r)
    end
    return _InfectorChain{T}(names, βv, R, out, get(idx, from, 0))
end

_chain_solve(chain::_InfectorChain{Float64}, A, b) = A \ b
_chain_solve(chain::_InfectorChain, A, b) = vec(_solve_nopivot(A, reshape(b, :, 1)))

# T = P(an infected node transmits along one given edge) = E[1 − e^{−Λ}]: the absorbing-chain
# solve (β_m + out_m) w_m − Σ_n R[m,n] w_n = β_m, T = w_start (E14, corrected fix).
function _transmissibility(chain::_InfectorChain)
    chain.start == 0 && return zero(eltype(chain.β))
    A = LinearAlgebra.Diagonal(chain.β .+ chain.out) - chain.R
    w = _chain_solve(chain, Matrix(A), chain.β)
    return _simplify(w[chain.start])
end

# φ(s) = E[e^{−sΛ}] for real s ≥ 0: (out_m + sβ_m) φ_m − Σ_n R[m,n] φ_n = out_m − Σ_n R[m,n]
# (the rate of absorption), φ = 1 on absorbing states (E15). Numeric chains only.
function _laplace(chain::_InfectorChain{Float64}, s::Real)
    (chain.start == 0 || s == 0) && return 1.0
    A = LinearAlgebra.Diagonal(chain.out .+ s .* chain.β) - chain.R
    b = chain.out .- vec(sum(chain.R; dims = 2))
    return clamp((Matrix(A) \ b)[chain.start], 0.0, 1.0)
end

# E[Λ]: out_m Λ_m − Σ_n R[m,n] Λ_n = β_m.
function _mean_hazard(chain::_InfectorChain{Float64})
    chain.start == 0 && return 0.0
    A = LinearAlgebra.Diagonal(chain.out) - chain.R
    return (Matrix(A) \ chain.β)[chain.start]
end

# ---- the chain of a legacy DiseaseProgression -------------------------------------------------

# Symbol and Expr rates of a legacy progression become symbolic parameters (as in the builders).
_legacy_rate(r::Union{Symbol,Expr}) = _lift_rate(r)
_legacy_rate(r) = r

function _infector_chain(prog::DiseaseProgression; from::Symbol = prog.entry)
    stages = Symbol[s.name for s in prog.stages]
    β = Dict{Symbol,Any}(s.name => _legacy_rate(s.transmission_rate) for s in prog.stages)
    trans = [(tr.source, tr.target, _legacy_rate(tr.rate)) for tr in prog.transitions]
    return _infector_chain(stages, β, trans, from)
end

function _numeric_chain(chain::_InfectorChain, fname::AbstractString)
    chain isa _InfectorChain{Float64} && return chain
    vals = [_float_or_nothing(x) for x in vcat(chain.β, vec(chain.R), chain.out)]
    any(isnothing, vals) && throw(ArgumentError(
        "$(fname) needs numeric rates; the progression has symbolic rates (substitute values first, " *
        "or lift the model with edge_based and pass p)"))
    f(x) = Float64(_float_or_nothing(x))
    return _InfectorChain{Float64}(chain.names, f.(chain.β), f.(chain.R), f.(chain.out), chain.start)
end

"""
    _edge_transmissibility(prog::DiseaseProgression; from = prog.entry)

The per-edge transmissibility T of a legacy progression (verified issue E14): the probability
that a node entering `from` transmits along one given edge before its infectious period ends,
for any Markov progression (branching, bypasses, cycles, unreachable stages). With
w = 0 on stages that can no longer transmit, T = w_from where

    (β_m + out_m) w_m − Σ_n r_{m→n} w_n = β_m,

i.e. T = βᵀ(V + B)⁻¹e_from, the expanded edge-based ODE's next-generation matrix divided by
ψ''(1)/ψ'(1). Symbolic rates give a symbolic T (Gaussian elimination without pivoting, valid for
this M-matrix). For SIR T = β/(β + γ); for a linear chain T = 1 − ∏_m out_m/(β_m + out_m).
"""
function _edge_transmissibility(prog::DiseaseProgression; from::Symbol = prog.entry)
    _require_sir_type_analysis(prog, "the transmissibility")
    return _transmissibility(_infector_chain(prog; from))
end

"""
    _compute_transmissibility(prog::DiseaseProgression) -> Float64

The numeric per-edge transmissibility T of a legacy progression ([`_edge_transmissibility`](@ref)).
Throws an `ArgumentError` when the progression has no transmitting stage.
"""
function _compute_transmissibility(prog::DiseaseProgression)
    _require_transmitting(prog)
    return Float64(_float_or_nothing(_numeric_transmissibility(prog, "the transmissibility")))
end

_numeric_transmissibility(prog::DiseaseProgression, fname) =
    (_require_sir_type_analysis(prog, fname);
     _transmissibility(_numeric_chain(_infector_chain(prog), fname)))

function _require_transmitting(prog::DiseaseProgression)
    any(s -> !_is_zero_rate(s.transmission_rate), prog.stages) || throw(ArgumentError(
        "DiseaseProgression has no infectious stages with a non-zero transmission rate; " *
        "cannot compute transmissibility"))
    return nothing
end

"""
    _require_sir_type_analysis(prog::DiseaseProgression, fname)

Throw an `ArgumentError` when `prog` returns nodes to the susceptible class (verified issue E17,
corrected fix): a transition into `prog.susceptible` (SIS, SIRS), or into a non-transmitting
stage `S_p` of the same base compartment as the susceptible class (the lifts of
`with_reinfection_counting`, whose `I_p → S_p` transitions re-susceptibilise). The one-shot SIR
quantities (T, R₀ = Tκ, the percolation final size, P(major) and τ_c = γ/(κ − 1)) do not apply
there: re-susceptibilisation lowers the SIS threshold to γ/κ on the pairwise model.
"""
function _require_sir_type_analysis(prog::DiseaseProgression, fname::AbstractString)
    sus_base = base_compartment_of(prog.susceptible)
    zero_tx = Set(s.name for s in prog.stages if _is_zero_rate(s.transmission_rate))
    offending = [tr for tr in prog.transitions if tr.target == prog.susceptible ||
                 (tr.target in zero_tx && infection_count_of(tr.target) !== nothing &&
                  base_compartment_of(tr.target) == sus_base)]
    isempty(offending) && return nothing
    labels = join(("$(tr.source)→$(tr.target)" for tr in offending), ", ")
    throw(ArgumentError(
        "$(fname) assumes SIR-type dynamics (a one-shot transmissibility T = β/(β+γ)); this " *
        "progression re-susceptibilises ($(labels)), so R₀ = T·κ, the percolation final size, " *
        "P(major) and β_c = γ/(κ-1) do not apply (the SIS threshold is γ/κ on the pairwise " *
        "model). Use NodeBasedModels (node_based(sis_model(), net)) for SIS/SIRS thresholds, or " *
        "NetworkOutbreaks.simulate"))
end

# =============================================================================================
# Degree distributions: PGF functions and probabilities
# =============================================================================================

# ψ, ψ', ψ'' as Float64 functions and the mean degree ψ'(1), for a numeric degree distribution.
# A legacy PGF with a numeric provenance uses its distribution's closed forms (compiling the
# symbolic expression of a wide polynomial takes a minute); otherwise the expression is compiled.
function _pgf_functions(pgf::DegreePGF, fname::AbstractString)
    d = pgf.distribution
    d !== nothing && _float_or_nothing(mean_degree(d)) !== nothing && return _pgf_functions(d, fname)
    f0, f1, f2 = _build_pgf_fn(pgf), _build_pgf_deriv_fn(pgf, 1), _build_pgf_deriv_fn(pgf, 2)
    μ = _float_or_nothing(f1(1.0))
    (μ === nothing || !isfinite(μ)) && throw(ArgumentError(
        "$(fname) needs a numeric degree distribution; the PGF $(pgf.expression) has free parameters"))
    ψ(x) = Float64(_float_or_nothing(f0(x)))
    ψ1(x) = Float64(_float_or_nothing(f1(x)))
    ψ2(x) = Float64(_float_or_nothing(f2(x)))
    return ψ, ψ1, ψ2, μ
end

function _pgf_functions(d::DegreeDistribution, fname::AbstractString)
    μ = _float_or_nothing(mean_degree(d))
    (μ === nothing || !isfinite(μ)) && throw(ArgumentError(
        "$(fname) needs a numeric degree distribution; $(d) has symbolic parameters"))
    ψ(x) = Float64(_float_or_nothing(pgf(d, x)))
    ψ1(x) = Float64(_float_or_nothing(pgf_derivative(d, x, 1)))
    ψ2(x) = Float64(_float_or_nothing(pgf_derivative(d, x, 2)))
    return ψ, ψ1, ψ2, μ
end

# The degree probabilities p[k+1] = P(D = k), checked against the mean degree: the moment check
# of the E15 corrected fix (truncation or DFT aliasing preserves Σp_k but not Σk·p_k).
function _degree_coefficients(d::DegreeDistribution, μ::Float64, fname::AbstractString)
    p = if d isa DegreePGF
        d.distribution === nothing ? _pgf_coefficients_dft(d, μ, fname) :
        _degree_coefficients(d.distribution, μ, fname)
    else
        Float64.(degree_probabilities(d; tol = 1e-14))
    end
    _check_degree_coefficients(p, μ, fname)
    return p
end

function _check_degree_coefficients(p::Vector{Float64}, μ::Float64, fname::AbstractString)
    m = sum((k - 1) * p[k] for k in eachindex(p); init = 0.0)
    (abs(sum(p) - 1) <= 1e-9 && abs(m - μ) <= 1e-9 * max(1.0, μ)) || throw(ArgumentError(
        "$(fname): the degree probabilities do not reproduce the distribution (Σp_k = $(sum(p)), " *
        "Σk·p_k = $(m), ψ'(1) = $(μ)); the support is too wide or the PGF is not analytic on the " *
        "unit disc"))
    return nothing
end

# p_k of a legacy PGF without provenance, by a DFT of ψ on the unit circle, M doubling from 1024
# while the moment check fails (E15 corrected fix); a support too wide for M = 2^16, or an
# expression that is not a power series on the unit disc (e.g. one written with abs(z)), is an
# ArgumentError instead of a silently wrong number.
function _pgf_coefficients_dft(pgf::DegreePGF, μ::Float64, fname::AbstractString)
    f0 = _build_pgf_fn(pgf)
    M = 1024
    while true
        vals = ComplexF64[ComplexF64(f0(cis(2π * m / M))) for m in 0:(M - 1)]
        c = _fft(vals) ./ M
        p = [real(c[k + 1]) for k in 0:(M ÷ 2 - 1)]
        if all(x -> x >= -1e-12, p)
            p = max.(p, 0.0)
            K = findlast(>(1e-18), p)
            p = K === nothing ? p : p[1:K]
            m = sum((k - 1) * p[k] for k in eachindex(p); init = 0.0)
            abs(m - μ) <= 1e-9 * max(1.0, μ) && abs(sum(p) - 1) <= 1e-9 && return p
        end
        M *= 2
        M > 2^16 && throw(ArgumentError(
            "$(fname): cannot recover the degree probabilities from the PGF $(pgf.expression) " *
            "(support too wide or expression not analytic on the unit disc); build it with " *
            "poisson_pgf, polynomial_pgf or DegreePGF(::DegreeDistribution)"))
    end
end

# Radix-2 FFT, Σ_m x_m e^{−2πikm/M} (length a power of 2).
function _fft(x::Vector{ComplexF64})
    n = length(x)
    n == 1 && return copy(x)
    ev = _fft(x[1:2:end])
    od = _fft(x[2:2:end])
    out = similar(x)
    h = n ÷ 2
    for k in 1:h
        t = cis(-2π * (k - 1) / n) * od[k]
        out[k] = ev[k] + t
        out[k + h] = ev[k] - t
    end
    return out
end

# =============================================================================================
# Kernels: final size, probability of a major outbreak, Ball's variance
# =============================================================================================

# θ∞ of θ = 1 − T + T(1 − ρ)ψ'(θ)/ψ'(1) (seeds ρ in the entry state, Miller 2014 eqs (3)-(4)).
# ρ = 0 gives the large-outbreak limit: exactly 1 at or below threshold, R₀ = Tψ''(1)/ψ'(1) ≤ 1.
function _theta_infinity(T::Float64, ρ::Float64, ψ1, μ::Float64, R0::Float64; what::AbstractString,
                         xtol::Real = 1e-16, maxiter::Integer = 300)
    (T <= 0 || μ <= 0) && return 1.0
    g(θ) = 1 - T + T * (1 - ρ) * ψ1(θ) / μ - θ
    if ρ > 0
        g0 = g(0.0)
        g0 <= 0 && return 0.0
        return _brent_root(g, 0.0, 1.0, g0, g(1.0); xtol = Float64(xtol), maxiter = Int(maxiter), what)
    end
    R0 <= 1 && return 1.0
    return _least_root(g; what, xtol, maxiter)
end

# P(major) on a configuration network from one seed in the entry state (E15): with φ[j+1] =
# E[W^j] (j = 0…K), ξ = E[ψ'(ξ + (1−ξ)W)]/ψ'(1) (least root) and P = 1 − E[ψ(ξ + (1−ξ)W)],
# where E[(x + (1−x)W)^n] = Σ_j Bin(n, 1−x)_j φ(j), accumulated with the binomial recursion
# (a convex combination at every step: no cancellation, no overflow).
function _pmajor_configuration(p::Vector{Float64}, μ::Float64, φ::Vector{Float64};
                               what::AbstractString, xtol::Real = 1e-16, maxiter::Integer = 300)
    K = length(p) - 1
    μ <= 0 && return 0.0
    T = 1 - φ[2]
    R0 = T * sum((k - 1) * (k - 2) * p[k] for k in 3:length(p); init = 0.0) / μ
    R0 <= 1 && return 0.0
    b = zeros(K + 1)
    A = zeros(K + 1)
    function moments!(ξ)            # A[n+1] = E[(ξ + (1−ξ)W)^n], n = 0…K
        y = 1 - ξ
        fill!(b, 0.0)
        b[1] = 1.0
        A[1] = 1.0
        for n in 1:K
            for j in (n + 1):-1:2
                b[j] = ξ * b[j] + y * b[j - 1]
            end
            b[1] *= ξ
            s = 0.0
            for j in 1:(n + 1)
                s += b[j] * φ[j]
            end
            A[n + 1] = s
        end
        return A
    end
    function g(ξ)
        moments!(ξ)
        return sum(k * p[k + 1] * A[k] for k in 1:K; init = 0.0) / μ - ξ
    end
    ξ = _least_root(g; what, xtol, maxiter)
    ξ >= 1 && return 0.0
    moments!(ξ)
    return clamp(1 - sum(p[k + 1] * A[k + 1] for k in 0:K), 0.0, 1.0)
end

# P(major) with fleeting contacts (WellMixed(κ)) from one seed: offspring Poisson(κΛ) given the
# path, so the extinction probability solves q = E[e^{−κ(1−q)Λ}] = φ(κ(1 − q)).
function _pmajor_fleeting(κ::Float64, chain::_InfectorChain{Float64}; what::AbstractString)
    κ * _mean_hazard(chain) <= 1 && return 0.0
    q = _least_root(x -> _laplace(chain, κ * (1 - x)) - x; what)
    return clamp(1 - q, 0.0, 1.0)
end

# Ball (2021) Theorem 2.2 (O(1) initial infectives, conditioned on a major outbreak): n·Var of
# the final-size fraction, eqs (2.4)-(2.5) (MR, f_{Dε} → f_D) and (2.6)-(2.7) with ε = 0 (NSW),
# z from (2.9). pI = T, qI = φ(1) = 1 − T, q2 = φ(2) = E[e^{−2Λ}].
function _ball_variance(ψ, ψ1, ψ2, μ::Float64, z::Float64, pI::Float64, q2::Float64, graph::Symbol)
    qI = 1 - pI
    ρ = 1 - ψ(z)
    den = 1 - pI * ψ2(z) / μ
    den <= sqrt(eps(Float64)) && return Inf         # at the threshold the variance diverges
    h = (qI - z) / (pI * den)
    ip = (q2 - qI^2) * h^2 * (ψ2(1.0) - ψ2(z))
    if graph === :NSW
        ED2 = ψ2(1.0) + μ                           # σ_D² + μ_D² = E[D²]
        return ρ * (1 - ρ) - h * (z - qI) * μ +
               h^2 * ((pI * qI - 2z * (z - qI)) * μ + (z - qI)^2 * ED2) + ip
    end
    z2 = z^2
    return h^2 * ((pI * qI + 2 * (z - qI)^2) * μ - pI^2 * (ψ1(z2) + z2 * ψ2(z2))) +
           h * (2pI * z * ψ1(z2) - (z - qI) * μ) + 1 - ρ - ψ(z2) + ip
end

function _check_graph(graph::Symbol)
    graph in (:NSW, :MR) || throw(ArgumentError(
        "confidence_bands: graph must be :NSW (iid degrees, Newman–Strogatz–Watts) or :MR (a " *
        "prescribed degree sequence, Molloy–Reed); got :$(graph)"))
    return graph
end

function _check_band(N::Integer, level::Real)
    (0 < level < 1) || throw(ArgumentError("confidence_bands: level must be in (0, 1); got $(level)"))
    N >= 1 || throw(ArgumentError("confidence_bands: N must be ≥ 1; got $(N)"))
    return nothing
end

function _band(mean::Float64, σ²::Float64, N::Integer, level::Real)
    zq = _normal_quantile(1 - (1 - level) / 2)
    se = sqrt(max(0.0, σ²) / N)
    return (lower = max(0.0, mean - zq * se), mean = mean, upper = min(1.0, mean + zq * se),
            variance = σ², std_error = se)
end

const _ZERO_BAND = (lower = 0.0, mean = 0.0, upper = 0.0, variance = 0.0, std_error = 0.0)

# =============================================================================================
# Legacy StaticConfigurationModel
# =============================================================================================

"""
    final_size(model::StaticConfigurationModel; seed_fraction = 0.0, tol = 1e-15, maxiter = 300)

The final size R(∞), the fraction of nodes ever infected (seeds included), of an SIR-type model
on a configuration network: R∞ = 1 − (1 − ρ)ψ(θ∞) with θ∞ the least root in [0, 1] of

    θ = 1 − T + T(1 − ρ)ψ'(θ)/ψ'(1),

where T is the per-edge transmissibility of the progression (any Markov progression: branching,
bypasses and cycles, verified issue E14) and ρ = `seed_fraction` is the fraction seeded
uniformly at random in the entry stage, as `default_initial_conditions(sys; seed_fraction)`
seeds the ODE (Miller 2014 eqs (3)-(4) with φ_S(0) = 1 − ρ, verified issue E31(i)); R∞ is then
the limit of the ODE's recovered fraction. With `seed_fraction = 0` (the default) it is the
large-outbreak limit of a vanishing seed, `(R_infinity = 0.0, θ_infinity = 1.0)` exactly when
R₀ = Tψ''(1)/ψ'(1) ≤ 1.

The root is bracketed and refined by Brent's method to an absolute tolerance `tol` in θ (verified
issue E18: the old fixed-point iteration stopped after `maxiter` steps unconverged, up to 150×
too small just above threshold). Returns `(R_infinity, θ_infinity)`. Progressions that return
nodes to the susceptible class (SIS, SIRS) are refused (E17).
"""
function final_size(model::StaticConfigurationModel; seed_fraction::Real = 0.0, tol::Real = 1e-15,
                    maxiter::Integer = 300)
    fname = "final_size"
    prog = model.progression
    _require_transmitting(prog)
    ρ = Float64(seed_fraction)
    (0 <= ρ <= 1) || throw(ArgumentError("final_size: seed_fraction must be in [0, 1]; got $(ρ)"))
    T = Float64(_numeric_transmissibility(prog, fname))
    ψ, ψ1, ψ2, μ = _pgf_functions(model.pgf, fname)
    R0 = μ > 0 ? T * ψ2(1.0) / μ : 0.0
    θ = _theta_infinity(T, ρ, ψ1, μ, R0; what = "final_size: the final-size equation", xtol = tol,
                        maxiter)
    (ρ == 0 && θ == 1) && return (R_infinity = 0.0, θ_infinity = 1.0)
    return (R_infinity = clamp(1 - (1 - ρ) * ψ(θ), 0.0, 1.0), θ_infinity = θ)
end

"""
    epidemic_probability(model::StaticConfigurationModel; tol = 1e-15, maxiter = 300) -> Float64

The probability that one infected node, seeded uniformly at random in the entry stage, starts a
major epidemic: the survival probability of the infector-side branching process (verified issue
E15). An infector's transmissions along its edges are independent only given its infectious
path, so the offspring law is the mixed binomial Bin(D̃ − 1, 1 − W) with W = e^{−Λ} and
Λ = ∫β_{X(t)}dt the cumulative per-edge hazard of the path (Ball 2021, §2.4; Kenah & Robins
2007). With φ(j) = E[W^j] from one linear solve per j,

    ξ = E[ψ'(ξ + (1 − ξ)W)]/ψ'(1)   (least root),   P = 1 − E[ψ(ξ + (1 − ξ)W)].

For SIR, φ(j) = γ/(γ + jβ), and P is smaller than the final size unless the infectious period is
constant: 0.6094 against R∞ = 0.7968 for τ = 1/6, γ = 1/4 on Poisson(5). Returns 0.0 when
R₀ ≤ 1. The degree probabilities come from the PGF's provenance (or a DFT with a moment check)
and ξ is bracketed and refined by Brent's method (E18). SIS/SIRS progressions are refused (E17).
"""
function epidemic_probability(model::StaticConfigurationModel; tol::Real = 1e-15,
                              maxiter::Integer = 300)
    fname = "epidemic_probability"
    prog = model.progression
    _require_transmitting(prog)
    _require_sir_type_analysis(prog, fname)
    chain = _numeric_chain(_infector_chain(prog), fname)
    _, _, _, μ = _pgf_functions(model.pgf, fname)
    return _pmajor(model.pgf, μ, chain, fname; xtol = tol, maxiter)
end

function _pmajor(d::DegreeDistribution, μ::Float64, chain::_InfectorChain{Float64}, fname;
                 xtol::Real = 1e-16, maxiter::Integer = 300)
    μ <= 0 && return 0.0
    p = _degree_coefficients(d, μ, fname)
    length(p) < 2 && return 0.0
    φ = [_laplace(chain, j) for j in 0:(length(p) - 1)]
    return _pmajor_configuration(p, μ, φ; what = "$(fname): the extinction equation", xtol, maxiter)
end

"""
    confidence_bands(model::StaticConfigurationModel, N::Integer; level = 0.95, graph = :NSW)

Central-limit confidence band for the final size of a major outbreak started by O(1) infectives
in a population of `N` nodes: Ball (2021, Ann. Appl. Probab. 31:2091-2142), Theorem 2.2,
conditioned on a major outbreak (verified issue E16). `graph = :NSW` (the default) is the
configuration model with iid degrees (eqs (2.6)-(2.7) with ε = 0), `:MR` a prescribed degree
sequence (eqs (2.4)-(2.5)); σ²_NSW ≥ σ²_MR. With z = θ∞ and ρ = R∞ from [`final_size`](@ref),
p_I = T, q_I = 1 − T and q_I⁽²⁾ = E[e^{−2Λ}] (the probability that an infector fails to infect
two given neighbours; γ/(γ + 2β) for SIR, (q_I)² for a constant infectious period):

    h = (q_I − z)/(p_I(1 − p_I ψ''(z)/μ)),
    σ²_NSW = ρ(1 − ρ) − h(z − q_I)μ + h²{[p_I q_I − 2z(z − q_I)]μ + (z − q_I)²E[D²]}
             + (q_I⁽²⁾ − q_I²)h²[ψ''(1) − ψ''(z)].

Returns `(lower, mean, upper, variance, std_error)` as fractions: `mean` = ρ, `variance` = σ²
(N·Var of the final-size fraction), `std_error` = σ/√N and the band mean ± z_{(1+level)/2}·SE,
clipped to [0, 1]. All zeros when R₀ ≤ 1; `variance = Inf` (band [0, 1]) where the variance
diverges at the threshold. q_I⁽²⁾ is computed for any Markov progression (the path's Laplace
transform), which covers Erlang and branching progressions; SIS/SIRS are refused (E17).
"""
function confidence_bands(model::StaticConfigurationModel, N::Integer; level::Real = 0.95,
                          graph::Symbol = :NSW)
    fname = "confidence_bands"
    _check_graph(graph)
    prog = model.progression
    _require_transmitting(prog)
    _require_sir_type_analysis(prog, fname)
    chain = _numeric_chain(_infector_chain(prog), fname)
    return _confidence_bands(chain, _pgf_functions(model.pgf, fname)..., N, level, graph, fname)
end

function _confidence_bands(chain::_InfectorChain{Float64}, ψ, ψ1, ψ2, μ::Float64, N::Integer,
                           level::Real, graph::Symbol, fname)
    _check_band(N, level)
    μ > 0 || return _ZERO_BAND
    pI = 1 - _laplace(chain, 1)
    R0 = pI * ψ2(1.0) / μ
    R0 <= 1 && return _ZERO_BAND
    z = _theta_infinity(pI, 0.0, ψ1, μ, R0; what = "$(fname): the final-size equation")
    z >= 1 && return _ZERO_BAND
    σ² = _ball_variance(ψ, ψ1, ψ2, μ, z, pI, _laplace(chain, 2), graph)
    return _band(1 - ψ(z), σ², N, level)
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
`default_initial_conditions`. For a lowered system use `disease_free_equilibrium(sys)`, which
is keyed by the system's own variables.
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

The critical per-edge transmission rate `β_c` at which `R₀ = 1`, for a progression with one
transmitting stage m that the entry stage reaches (verified issue E14, corrected fix). With
π = P(reach m from the entry stage) and the effective exit rate γ_eff = out_m − Σ_{n≠m} r_{m→n}h_n
(h_n = P(return to m from n)), so that the total time in m is Exp(γ_eff) even when m is revisited,
T(β) = π·β/(β + γ_eff) and

    R₀ = κ·π·β/(β + γ_eff) = 1   ⟹   β_c = γ_eff/(π·κ − 1),

where `κ = ψ''(1)/ψ'(1)` is the excess-degree ratio (for SIR and SEIR β_c = γ/(κ − 1)). The result
is symbolic when the rates or κ are symbolic and numeric otherwise.

Throws an `ArgumentError` when κ (or π·κ) is numerically ≤ 1 (R₀ < 1 for every β), when several
transmitting stages are reachable (solve R₀ = 1 numerically, e.g. with
`epidemic_threshold(edge_based(model, net); vary)`), and for progressions that return nodes to
the susceptible class (E17; the SIS pairwise threshold is γ/κ, see NodeBasedModels).
"""
function epidemic_threshold(model::StaticConfigurationModel)
    prog = model.progression
    _require_sir_type_analysis(prog, "epidemic_threshold")
    infectious = [s for s in prog.stages if !_is_zero_rate(s.transmission_rate)]
    isempty(infectious) && throw(ArgumentError("model has no infectious stages"))

    ψ_prime_1 = _eval_pgf_deriv(model.pgf, 1, 1)
    ψ_double_1 = _eval_pgf_deriv(model.pgf, 2, 1)
    κ_sym = Symbolics.simplify(ψ_double_1 / ψ_prime_1)
    # Only check κ > 1 when κ is fully numeric.
    κ_val = try _to_float64(κ_sym) catch; nothing end
    if κ_val !== nothing && κ_val <= 1
        throw(ArgumentError(
            "excess degree ratio κ = $(κ_val) ≤ 1; no positive epidemic threshold exists"))
    end

    # The transmitting stages the entry stage can reach.
    stages = Symbol[s.name for s in prog.stages]
    trans = [(tr.source, tr.target, _legacy_rate(tr.rate)) for tr in prog.transitions]
    reach = _reachable(trans, prog.entry)
    reachable_infectious = [s for s in infectious if s.name in reach]
    isempty(reachable_infectious) && throw(ArgumentError(
        "epidemic_threshold: no transmitting stage is reachable from the entry stage $(prog.entry)"))
    length(reachable_infectious) == 1 || throw(ArgumentError(
        "epidemic_threshold for progressions with several reachable transmitting stages " *
        "($(join((s.name for s in reachable_infectious), ", "))) has no closed form; solve R₀ = 1 " *
        "numerically, e.g. epidemic_threshold(edge_based(model_or_contact_model, net); p, vary)"))
    m = only(reachable_infectious).name
    π_m, γ_eff = _hitting(stages, trans, prog.entry, m)
    if κ_val !== nothing
        πv = _float_or_nothing(π_m)
        πv !== nothing && πv * κ_val <= 1 && throw(ArgumentError(
            "epidemic_threshold: the entry stage reaches the transmitting stage $(m) with " *
            "probability $(πv), and π·κ = $(πv * κ_val) ≤ 1, so R₀ < 1 for every β"))
    end
    βc = _simplify(γ_eff / (π_m * κ_sym - 1))
    v = _float_or_nothing(βc)
    return v === nothing ? βc : v
end

# π = P(reach m from `from`) and γ_eff = out_m − Σ_{n≠m} r_{m→n} h_n, where h_n = P(reach m | n):
# out_n h_n − Σ_{k≠m} r_{n→k} h_k = r_{n→m} for the states n ≠ m that can reach m.
function _hitting(stages, trans, from::Symbol, m::Symbol)
    # the states that can reach m (reverse reachability)
    can = Set{Symbol}([m])
    changed = true
    while changed
        changed = false
        for (a, b, r) in trans
            (_is_zero_rate(r) || b === nothing) && continue
            if b in can && !(a in can)
                push!(can, a)
                changed = true
            end
        end
    end
    U = Symbol[s for s in stages if s in can && s !== m]
    idx = Dict(s => i for (i, s) in enumerate(U))
    rates = Any[r for (_, _, r) in trans]
    T = any(_is_symbolic, rates) ? Symbolics.Num : Float64
    n = length(U)
    A = zeros(T, n, n)
    rhs = zeros(T, n)
    out_m = zero(T)
    back = zero(T)
    for (a, b, r) in trans
        _is_zero_rate(r) && continue
        if haskey(idx, a)
            A[idx[a], idx[a]] += r
            b !== nothing && haskey(idx, b) && (A[idx[a], idx[b]] -= r)
            b === m && (rhs[idx[a]] += r)
        end
    end
    h = n == 0 ? T[] : (T === Float64 ? A \ rhs : vec(_solve_nopivot(A, reshape(rhs, :, 1))))
    for (a, b, r) in trans
        (a === m && !_is_zero_rate(r)) || continue
        out_m += r
        b !== nothing && haskey(idx, b) && (back += r * h[idx[b]])
    end
    π_m = from === m ? one(T) : (haskey(idx, from) ? h[idx[from]] : zero(T))
    return _simplify(π_m), _simplify(out_m - back)
end

# =============================================================================================
# Lowered systems (EdgeModelSystem): the 0.2 API
# =============================================================================================

# The closures whose fields are linear in the initially susceptible fractions q (every gain of
# a contact carries its recipient's qξ, and a node's infected edges are its φ coordinates), so
# that the linearisation at the disease-free state splits as J(q = 1) = F − V with V = −J(q = 0).
# The heterogeneous-susceptibility field (lift/heterogeneous.jl) is of this form too: every gain
# of a contact carries n_a q_a ξ_a of the recipient's class. The neighbour-exchange (:dynamic),
# dormant-contact, clustered and mean-field social heterogeneity (:mfsh) fields are not (their
# used-edge, dormant-stub, triangle and fleeting-contact coordinates); they use NetworkEpiCore's
# numeric methods or their lift file's `_numeric_threshold` method.
const _LINEARISABLE_CLOSURES = (:configuration, :well_mixed, :multitype, :multiplex, :degree_correlated,
                                :heterogeneous)

# The closure of a lowered system (`metadata[:closure]` of assembled systems).
_system_closure(sys::EdgeModelSystem) = get(sys.metadata, :closure, :unknown)
_linearisable(sys::EdgeModelSystem) = _system_closure(sys) in _LINEARISABLE_CLOSURES

"""
    _numeric_threshold(::Val{closure}, f, sys, vals; kw...)

The threshold quantity `f` (`basic_reproduction_number`, `next_generation_matrix`,
`transmissibility` or `early_growth_rate`) of a lowered system whose closure is not linearised
here (`_LINEARISABLE_CLOSURES`), with the numeric parameter values `vals`. The
default is NetworkEpiCore's numeric method `f(model, network, vals; kw...)` on the model and
network the system was lifted from (for `DynamicNetwork`, the neighbour-exchange next-generation
matrix of Miller–Slim–Volz). The lift file of a closure may add a more specific method (e.g. for
`Val{:clustered}`) by dispatch, without editing this file (design §G.1).
"""
_numeric_threshold(::Val, f, sys::EdgeModelSystem, vals; kw...) =
    f(_system_model(sys, string(nameof(f)))..., vals; kw...)

_fallback_threshold(f, sys::EdgeModelSystem, p; kw...) =
    _numeric_threshold(Val(_system_closure(sys)), f, sys, _parameter_values(sys, p); kw...)

function _system_model(sys::EdgeModelSystem, fname::AbstractString)
    md = sys.metadata
    cm = get(md, :model, nothing)
    net = get(md, :network, nothing)
    (cm isa ContactModel && net isa NetworkDescriptor) || throw(ArgumentError(
        "$(fname): this edge-based system records no model and network (it was not built by " *
        "edge_based); lift the model with edge_based(model, net) instead"))
    return cm, net
end

# Parameter values by name: the system's parameter defaults, overridden by `p` (a Dict keyed by
# Symbol or symbolic parameter, or a NamedTuple).
function _parameter_values(sys::EdgeModelSystem, p)
    vals = Dict{Symbol,Float64}(parameter_defaults(sys))
    p === nothing && return vals
    for (k, v) in pairs(p)
        vals[_pname(k)] = Float64(v)
    end
    return vals
end

# The states that matter for transmission: reachable from an entry state and able to reach an
# infector through node transitions (the recovered and the sinks are not).
function _transmission_chain(cm::ContactModel)
    Σ = Set(susceptible_species(cm))
    succ = Dict{Symbol,Vector{Symbol}}()
    pred = Dict{Symbol,Vector{Symbol}}()
    for t in node_transitions(cm)
        (t.to === nothing || t.from in Σ) && continue
        push!(get!(succ, t.from, Symbol[]), t.to)
        push!(get!(pred, t.to, Symbol[]), t.from)
    end
    reach = Set{Symbol}(entry_species(cm))
    stack = collect(reach)
    while !isempty(stack)
        for b in get(succ, pop!(stack), Symbol[])
            b in reach || (push!(reach, b); push!(stack, b))
        end
    end
    live = Set{Symbol}(c.infector for c in contacts(cm) if c.recipient in Σ)
    stack = collect(live)
    while !isempty(stack)
        for a in get(pred, pop!(stack), Symbol[])
            a in live || (push!(live, a); push!(stack, a))
        end
    end
    return intersect(reach, live)
end

# The linearisation of the lifted field at the disease-free state (θ = ξ = 1, every φ and pop
# 0) over the infection-chain coordinates: F (new infections) and V (transitions, and the
# transmission that uses up an edge), with J(q = 1) = F − V.
struct _EBLinearisation
    names::Vector{Symbol}
    species::Vector{Symbol}
    F::Matrix{Symbolics.Num}
    V::Matrix{Symbolics.Num}
    entries::Vector{Int}
    hazard::Union{Nothing,Vector{Symbolics.Num}}
end

function _eb_linearisation(sys::EdgeModelSystem, fname::AbstractString)
    cm, net = _system_model(sys, fname)
    md = sys.metadata
    table = md[:contributions]
    raw = md[:raw]
    info = table.coordinate_info
    chain = _transmission_chain(cm)
    role = any(x -> x.role === :φ, info) ? :φ : :pop
    states = collect(raw.states)
    rhs = collect(raw.rhs)
    dfe = Dict{Any,Any}()
    idx = Int[]
    names = Symbol[]
    species = Symbol[]
    θidx = Int[]
    for (i, s) in enumerate(states)
        k = findfirst(x -> isequal(x.var, s), info)
        k === nothing && throw(ArgumentError("$(fname): the state $(s) is not an edge-based coordinate"))
        x = info[k]
        if x.role in (:θ, :ξ)
            dfe[s] = 1
            x.role === :θ && push!(θidx, i)
        else
            dfe[s] = 0
            if x.role === role && x.species in chain
                push!(idx, i)
                push!(names, x.name)
                push!(species, x.species)
            end
        end
    end
    isempty(idx) && throw(ArgumentError(
        "$(fname): the model :$(cm.name) has no state from which a transmission can follow"))
    qs = [last(sq) for sq in table.seed_factors]
    at(e, qv) = _simplify(Symbolics.substitute(e, merge(dfe, Dict{Any,Any}(q => qv for q in qs));
                                               fold = Val(true)))
    J = Symbolics.jacobian(rhs[idx], states[idx])
    J1 = at.(J, 1)
    J0 = at.(J, 0)
    F = Symbolics.Num.(_simplify.(J1 .- J0))
    V = Symbolics.Num.(_simplify.(-J0))
    # the coordinates of the entry states, the only rows of F that new infections reach
    entry = Set(entry_species(cm))
    entries = [i for i in eachindex(species) if species[i] in entry]
    hazard = nothing
    if table.closure === :configuration && length(θidx) == 1
        Jθ = Symbolics.jacobian(rhs[θidx], states[idx])
        hazard = Symbolics.Num[-at(Jθ[1, j], 1) for j in eachindex(idx)]
    end
    return _EBLinearisation(names, species, F, V, entries, hazard)
end

# Evaluate symbolic entries with parameter values by name (missing names are an error).
function _evaluate(x::AbstractArray, vals::AbstractDict{Symbol}, fname::AbstractString)
    vars = Dict{Any,Float64}()
    missing_ = Symbol[]
    for e in x, v in Symbolics.get_variables(e)
        n = _pname(v)
        haskey(vals, n) ? (vars[v] = vals[n]) : (n in missing_ || push!(missing_, n))
    end
    isempty(missing_) || throw(ArgumentError(
        "$(fname): missing parameter values for $(join(sort!(missing_), ", ")) (pass them in p)"))
    return map(x) do e
        v = _float_or_nothing(Symbolics.substitute(e, vars; fold = Val(true)))
        v === nothing && throw(ArgumentError("$(fname): could not evaluate $(e) numerically"))
        Float64(v)
    end
end

_numeric_or_num(x) = (v = _float_or_nothing(x); v === nothing ? _simplify(x) : v)

"""
    next_generation_matrix(sys::EdgeModelSystem; p = nothing) -> Matrix

The next-generation matrix of an edge-based system, from its own vector field
(`symbolic_ode(sys)`) linearised at the disease-free state (θ = ξ = 1, every φ_X and pop_X zero):
over the edge coordinates φ_X of the states from which transmission can follow (the population
coordinates pop_X on `WellMixed`), J = F − V, where F holds the new infections (the terms
proportional to the susceptible fractions q) and V the transitions and the transmission that
uses up an edge. The matrix returned is K = (F V⁻¹) restricted to the coordinates of the entry
states (the rows of F that are not zero), which has the nonzero spectrum of F V⁻¹; R₀ = ρ(K).

With `p = nothing` K is symbolic in the model's rate parameters (a `Float64` matrix when every rate
is numeric); with `p` (a `Dict` by name, or a `NamedTuple`) it is evaluated numerically, the
parameters `p` does not give taking their [`parameter_defaults`](@ref)`(sys)`. For an untyped
configuration network K_{X←Y} = κ_ex Σ_{r: entry X} T_r(Y) and on `WellMixed(κ)`
K_{X←Y} = κ Σ_r τ_r[V⁻¹e_Y]_{J_r}, as NetworkEpiCore's numeric
`next_generation_matrix(cm, net, p)` (whose indexing by (edge kind, entry state) may order the
rows differently; the spectra agree). The exit factor ξ is taken at 1 (the start of the epidemic).

A system whose closure is not linearised here (neighbour exchange, the clustered lift, the legacy
builders) gets NetworkEpiCore's numeric matrix for its model and network (see
`_numeric_threshold`), so `p` (or the parameter defaults) must then give every rate.
"""
function NetworkEpiCore.next_generation_matrix(sys::EdgeModelSystem; p = nothing)
    fname = "next_generation_matrix"
    _linearisable(sys) || return _fallback_threshold(next_generation_matrix, sys, p)
    L = _eb_linearisation(sys, fname)
    ent = L.entries
    n = length(L.names)
    E = zeros(Int, n, length(ent))
    for (c, i) in enumerate(ent)
        E[i, c] = 1
    end
    if p === nothing
        X = _solve_nopivot(L.V, E)
        K = [_numeric_or_num(sum(L.F[i, k] * X[k, c] for k in 1:n)) for i in ent, c in eachindex(ent)]
        return all(x -> x isa Float64, K) ? Float64.(K) : Symbolics.Num.(K)
    end
    vals = _parameter_values(sys, p)
    Fn = _evaluate(L.F, vals, fname)
    Vn = _evaluate(L.V, vals, fname)
    return Fn[ent, :] * (Vn \ Float64.(E))
end

"""
    basic_reproduction_number(sys::EdgeModelSystem; p = nothing)

R₀ = ρ(K), the spectral radius of the [`next_generation_matrix`](@ref)`(sys; p)` of the lifted
field (for a multiplex, over layers and entry states; never the sum of the layer R₀s, verified
issue E12). Symbolic when `p = nothing` and K has a closed-form Perron root (one entry
coordinate: R₀ = K₁₁, e.g. 5τ/(τ + γ) for SIR on Poisson(5); two: (a + d)/2 + √(((a − d)/2)² + bc));
numeric with `p`, or when every rate is numeric. A larger symbolic K (a typed network) needs `p`.
Systems whose closure is not linearised here use NetworkEpiCore's numeric R₀ (e.g. the
neighbour-exchange R₀ of a `DynamicNetwork`).
"""
function basic_reproduction_number(sys::EdgeModelSystem; p = nothing)
    fname = "basic_reproduction_number"
    _linearisable(sys) || return Float64(_fallback_threshold(basic_reproduction_number, sys, p))
    K = NetworkEpiCore.next_generation_matrix(sys; p)
    isempty(K) && return 0.0
    K isa Matrix{Float64} && return Float64(maximum(abs, LinearAlgebra.eigvals(K)))
    n = size(K, 1)
    n == 1 && return _simplify(K[1, 1])
    if n == 2
        a, b, c, d = K[1, 1], K[1, 2], K[2, 1], K[2, 2]
        return _simplify((a + d) / 2 + sqrt(((a - d) / 2)^2 + b * c))
    end
    throw(ArgumentError(
        "$(fname): the next-generation matrix of this system is $(n)×$(n) and symbolic, so its " *
        "spectral radius has no closed form; pass numeric parameter values p (e.g. " *
        "p = parameter_defaults(sys))"))
end

"""
    transmissibility(sys::EdgeModelSystem; p = nothing, from = nothing)

The per-edge transmissibility of a system lifted on an untyped `ConfigurationNetwork`: the
probability that a node entering state `from` (default: the unique entry state of the model)
eventually transmits across one given edge, T(Y) = hᵀV⁻¹e_Y with h = −∂θ̇/∂φ the edge hazard of the
lifted field and V as in [`next_generation_matrix`](@ref) (so B, the use of an edge by
transmission, is included). For SIR T = τ/(τ + γ), for n Erlang stages
T_n = 1 − (nγ/(τ + nγ))ⁿ, with a bypass E → R at probability 1 − p, T = pτ/(τ + γ) (E14).
Symbolic when `p = nothing`, numeric with `p`. Systems whose closure is not linearised here use
NetworkEpiCore's numeric `transmissibility(model, net, p; from)`.
"""
function NetworkEpiCore.transmissibility(sys::EdgeModelSystem; p = nothing,
                                         from::Union{Nothing,Symbol} = nothing)
    fname = "transmissibility"
    cm, _ = _system_model(sys, fname)
    _linearisable(sys) || return _fallback_threshold(transmissibility, sys, p;
                                                    (from === nothing ? (;) : (; from))...)
    _system_closure(sys) === :heterogeneous && throw(ArgumentError(
        "$(fname): with heterogeneous susceptibility the per-edge transmissibility depends on the class of " *
        "the recipient, so there is no single T; use next_generation_matrix(sys; p) (its entries are " *
        "κ_ex n_a T_a for SIR) or basic_reproduction_number(sys; p)"))
    L = _eb_linearisation(sys, fname)
    L.hazard === nothing && throw(ArgumentError(
        "$(fname): defined for systems lifted on an untyped ConfigurationNetwork (one θ); use " *
        "NetworkEpiCore's transmissibility(model, net, p; …) for typed or layered networks"))
    Y = something(from, default_seed_state(cm))
    Y in species_names(cm) || throw(ArgumentError(
        "$(fname): $(Y) is not a species of the model :$(cm.name) (species: " *
        "$(join(species_names(cm), ", ")))"))
    j = findfirst(==(Symbol(:φ_, Y)), L.names)
    j === nothing && return 0.0          # a state from which no transmission can follow
    n = length(L.names)
    e = zeros(Int, n, 1)
    e[j, 1] = 1
    if p === nothing
        x = _solve_nopivot(L.V, e)
        return _numeric_or_num(sum(L.hazard[k] * x[k, 1] for k in 1:n))
    end
    vals = _parameter_values(sys, p)
    return Float64(dot(_evaluate(L.hazard, vals, fname), _evaluate(L.V, vals, fname) \ vec(Float64.(e))))
end

"""
    early_growth_rate(sys::EdgeModelSystem; p = nothing) -> Float64

The initial exponential growth rate r of the lifted field: the leading eigenvalue of its
linearisation F − V at the disease-free state (see [`next_generation_matrix`](@ref)), with the
parameter values `p` over [`parameter_defaults`](@ref)`(sys)`. sign(r) = sign(R₀ − 1); for SIR on a
configuration network r = τ(κ_ex − 1) − γ. Systems whose closure is not linearised here use
NetworkEpiCore's numeric `early_growth_rate(model, net, p)`.
"""
function NetworkEpiCore.early_growth_rate(sys::EdgeModelSystem; p = nothing)
    fname = "early_growth_rate"
    _linearisable(sys) || return Float64(_fallback_threshold(early_growth_rate, sys, p))
    L = _eb_linearisation(sys, fname)
    vals = _parameter_values(sys, p)
    J = _evaluate(L.F, vals, fname) .- _evaluate(L.V, vals, fname)
    return Float64(maximum(real, LinearAlgebra.eigvals(J)))
end

# Whether NetworkEpiCore's fixed-point final size applies: no exits from the susceptible class,
# one entry state per node type, a descriptor with fixed-point equations.
function _fixed_point_final_size(cm::ContactModel, net::NetworkDescriptor)
    Σ = Set(susceptible_species(cm))
    any(t -> t.from in Σ, node_transitions(cm)) && return false
    labels = species_labels(cm)
    stratum(s) = haskey(labels, s) ? labels[s].stratum : :all
    # shared (unlabelled) species on a typed network: heterogeneous susceptibility, which
    # NetworkEpiCore's fixed point does not model (it assigns every species to one node type)
    net isa MultitypeNetwork && any(X -> stratum(X) === :all, species_names(cm)) && return false
    prods = Dict{Symbol,Set{Symbol}}()
    for c in contacts(cm)
        c.recipient in Σ && push!(get!(prods, stratum(c.recipient), Set{Symbol}()), c.product)
    end
    all(s -> length(s) <= 1, values(prods)) || return false
    return net isa Union{ConfigurationNetwork,WellMixed,MultitypeNetwork,MultiplexNetwork,
                         MFSHNetwork,DegreeCorrelatedNetwork}
end

"""
    final_size(sys::EdgeModelSystem; p = nothing, initial = nothing, N = nothing, method = :auto,
               reltol = 1e-10, abstol = 1e-12, tmax = 1e6) -> Float64

The final size of a lowered system: the fraction of nodes ever infected, seeds included (§E.2),
the limit of its `:cumulative` observable, with the parameter values `p` (over
[`parameter_defaults`](@ref)`(sys)`) and the seeding `initial` (a `SeedSpec`).

- `method = :fixed_point`: NetworkEpiCore's `final_size(model, net, p; initial, N)`, the
  fixed-point equations of the model on the network (configuration, well-mixed, multitype,
  multiplex, …). With `initial = nothing` it is the large-outbreak limit of a vanishing seed
  (exactly 0 at or below threshold).
- `method = :ode`: the lifted ODE integrated until the infection chain is empty (the population
  in states from which transmission can follow is below `abstol`), doubling the horizon up to
  `tmax`; needs `initial`. This is the route for models without a fixed-point equation: exits
  from the susceptible class (vaccination, whose final size depends on the course of the
  epidemic through ξ(t)), several entry states (two strains), neighbour exchange and
  heterogeneous susceptibility (shared species on `unstructured(net, st)`).
- `method = :auto` (the default) takes the fixed point where it exists and the ODE otherwise.
"""
function final_size(sys::EdgeModelSystem; p = nothing, initial::Union{Nothing,SeedSpec} = nothing,
                    N::Union{Nothing,Integer} = nothing, method::Symbol = :auto,
                    reltol::Real = 1e-10, abstol::Real = 1e-12, tmax::Real = 1e6)
    fname = "final_size"
    method in (:auto, :fixed_point, :ode) || throw(ArgumentError(
        "$(fname): method must be :auto, :fixed_point or :ode; got :$(method)"))
    cm, net = _system_model(sys, fname)
    vals = _parameter_values(sys, p)
    fixed = method === :fixed_point || (method === :auto && _fixed_point_final_size(cm, net))
    fixed && return Float64(final_size(cm, net, vals; initial, N))
    initial === nothing && throw(ArgumentError(
        "$(fname): the model :$(cm.name) on $(nameof(typeof(net))) has no fixed-point final-size " *
        "equation, so the final size is computed from the ODE, which needs a seeding: pass " *
        "initial (e.g. SeedFraction(:I => 0.01))"))
    return _final_size_ode(sys, cm, p, initial, N; reltol, abstol, tmax, fname)
end

# `p` goes to solve_epidemic as given (it fills the parameter defaults itself).
function _final_size_ode(sys::EdgeModelSystem, cm::ContactModel, p, initial, N;
                         reltol, abstol, tmax, fname)
    chain = [X for X in _transmission_chain(cm) if haskey(sys.variables, Symbol(:pop_, X))]
    acc = get(sys.variables, :cumulative, get(sys.observables, :cumulative, nothing))
    Svar = get(sys.observables, :S, nothing)
    (acc === nothing && Svar === nothing) && throw(ArgumentError(
        "$(fname): the system has no cumulative-incidence observable"))
    init = N === nothing ? default_initial_conditions(sys; initial) :
           default_initial_conditions(sys; initial, N)
    T = 100.0
    while true
        sol = solve_epidemic(sys; p, init, tspan = (0.0, T), save_everystep = false, reltol, abstol)
        SciMLBase.successful_retcode(sol) || throw(ErrorException(
            "$(fname): the ODE solve failed (retcode $(sol.retcode))"))
        active = sum((sol[sys.variables[Symbol(:pop_, X)]][end] for X in chain); init = 0.0)
        if active <= abstol
            return clamp(acc === nothing ? 1 - sol[Svar][end] : sol[acc][end], 0.0, 1.0)
        end
        T >= tmax && throw(ErrorException(
            "$(fname): the infection has not died out by t = $(T) (population in the infection " *
            "chain $(active)); raise tmax"))
        T = min(2T, Float64(tmax))
    end
end

# The infector chain of a ContactModel with numeric per-contact rates, on a network whose
# susceptible nodes are one class: the hazard of a state is the sum of the per-contact rates of
# its contacts with a susceptible partner. Every such contact must produce the same entry state
# (the scalar branching process; several products need a multitype process).
function _contact_chain(cm::ContactModel, net::NetworkDescriptor, vals, fname; from = nothing)
    Σ = susceptible_species(cm)
    length(Σ) == 1 || throw(ArgumentError(
        "$(fname): defined for models with one susceptible class; :$(cm.name) has $(join(Σ, ", "))"))
    any(t -> t.from in Σ, node_transitions(cm)) && throw(ArgumentError(
        "$(fname): the model :$(cm.name) has exits from the susceptible class, so the early epidemic " *
        "is not a time-homogeneous branching process"))
    inst = instantiate(cm, vals)
    τ = per_contact_rates(inst, net)
    entry = entry_species(inst)
    length(entry) == 1 || throw(ArgumentError(
        "$(fname): the model :$(cm.name) has several entry states ($(join(entry, ", "))); the " *
        "scalar branching process needs one"))
    β = Dict{Symbol,Any}()
    for (c, r) in zip(contacts(inst), τ)
        c.recipient in Σ || continue
        β[c.infector] = get(β, c.infector, 0.0) + Float64(_float_or_nothing(r))
    end
    stages = Symbol[X for X in species_names(inst) if !(X in Σ)]
    trans = [(t.from, t.to, Float64(_float_or_nothing(t.rate))) for t in node_transitions(inst)]
    return _numeric_chain(_infector_chain(stages, β, trans, something(from, only(entry))), fname)
end

"""
    epidemic_probability(sys::EdgeModelSystem; p = nothing, from = nothing) -> Float64

The probability that one infected node, seeded uniformly at random in state `from` (default: the
unique entry state), starts a major epidemic, for the model and network the system was lifted
from, with the parameter values `p` (over [`parameter_defaults`](@ref)`(sys)`): the infector-side
branching-process formula of `epidemic_probability(::StaticConfigurationModel)` (verified issue
E15) on a `ConfigurationNetwork`, and on `WellMixed(κ)` 1 − q with q = E[e^{−κ(1−q)Λ}] (for SIR,
1 − γ/(κτ) = 1 − 1/R₀). Several infectors are allowed (SEAIR); models with exits, several
entry states or several susceptible classes are refused (their early epidemic is not a scalar
time-homogeneous branching process), as are other descriptors.
"""
function epidemic_probability(sys::EdgeModelSystem; p = nothing, from::Union{Nothing,Symbol} = nothing)
    fname = "epidemic_probability"
    cm, net = _system_model(sys, fname)
    vals = _parameter_values(sys, p)
    if net isa ConfigurationNetwork
        chain = _contact_chain(cm, net, vals, fname; from)
        _, _, _, μ = _pgf_functions(net.degrees, fname)
        return _pmajor(net.degrees, μ, chain, fname)
    elseif net isa WellMixed
        κ = _float_or_nothing(net.κ)
        κ === nothing && throw(ArgumentError("$(fname) needs a numeric κ; got $(net.κ)"))
        chain = _contact_chain(cm, net, vals, fname; from)
        return _pmajor_fleeting(κ, chain; what = "$(fname): the extinction equation")
    end
    throw(ArgumentError(
        "$(fname): the infector-side branching process is implemented for ConfigurationNetwork and " *
        "WellMixed; for $(nameof(typeof(net))) estimate P(major) with NetworkOutbreaks " *
        "(epidemic_probability(ensemble))"))
end

"""
    confidence_bands(sys::EdgeModelSystem, N::Integer; p = nothing, level = 0.95, graph = :NSW)

Ball's (2021) central-limit band for the final size of a major outbreak in a population of `N`
nodes (see `confidence_bands(::StaticConfigurationModel, N)`), for the model and
`ConfigurationNetwork` the system was lifted from, with the parameter values `p`. The model must
have one susceptible class, one entry state and no exits.
"""
function confidence_bands(sys::EdgeModelSystem, N::Integer; p = nothing, level::Real = 0.95,
                          graph::Symbol = :NSW)
    fname = "confidence_bands"
    _check_graph(graph)
    cm, net = _system_model(sys, fname)
    net isa ConfigurationNetwork || throw(ArgumentError(
        "$(fname): Ball's central limit theorem is for configuration networks; got $(nameof(typeof(net)))"))
    chain = _contact_chain(cm, net, _parameter_values(sys, p), fname)
    return _confidence_bands(chain, _pgf_functions(net.degrees, fname)..., N, level, graph, fname)
end

"""
    epidemic_threshold(sys::EdgeModelSystem; p = nothing, vary = :τ) -> Float64

The value of the rate parameter `vary` at which R₀ = 1, the other parameters taken from `p` (over
[`parameter_defaults`](@ref)`(sys)`): NetworkEpiCore's `calibrate(model, net, p; target = :R0 => 1,
vary)` on the model and network the system was lifted from (a bracketing search and Brent's
method). For SIR on a configuration network τ_c = γ/(κ_ex − 1). For the closures whose R₀
NetworkEpiCore does not compute (heterogeneous susceptibility, the clustered and dormant-contact
lifts), the root of `basic_reproduction_number(sys; p) = 1` in `vary` is bracketed (by doubling or
halving the starting value) and refined by Brent's method.
"""
function epidemic_threshold(sys::EdgeModelSystem; p = nothing, vary::Symbol = :τ)
    fname = "epidemic_threshold"
    cm, net = _system_model(sys, fname)
    vals = _parameter_values(sys, p)
    _system_closure(sys) in _OWN_R0_CLOSURES || return calibrate(cm, net, vals; target = :R0 => 1.0, vary)[vary]
    haskey(vals, vary) || throw(ArgumentError(
        "$(fname): no value for the parameter $(vary) to start from; pass it in p"))
    g(x) = Float64(basic_reproduction_number(sys; p = merge(vals, Dict(vary => x)))) - 1
    x0 = vals[vary]
    (isfinite(x0) && x0 > 0) || throw(ArgumentError(
        "$(fname): the starting value $(vary) = $(x0) must be finite and positive"))
    lo, hi = x0, x0
    glo = ghi = g(x0)
    for _ in 1:200
        sign(glo) != sign(ghi) && break
        # R₀ grows or falls with the rate: move the end that has the same sign as the start
        if glo > 0
            lo /= 2
            glo = g(lo)
        else
            hi *= 2
            ghi = g(hi)
        end
        (isfinite(glo) && isfinite(ghi)) || break
    end
    glo == 0 && return lo
    ghi == 0 && return hi
    sign(glo) == sign(ghi) && throw(ArgumentError(
        "$(fname): R₀ = 1 is not attained by varying $(vary) from $(x0) (R₀ − 1 = $(glo) at " *
        "$(vary) = $(lo) and $(ghi) at $(hi))"))
    return _brent_root(g, lo, hi, glo, ghi; xtol = 1e-14 * max(1.0, hi),
                       what = "$(fname): R₀(sys; $(vary)) = 1")
end

# Closures whose R₀ comes from EdgeBasedModels itself, not from NetworkEpiCore's numeric methods,
# which refuse (or do not model) their networks: `epidemic_threshold` solves R₀ = 1 directly.
const _OWN_R0_CLOSURES = (:heterogeneous, :clustered, :dormant)

"""
    disease_free_equilibrium(sys::EdgeModelSystem)

The disease-free equilibrium of a lowered system in its own coordinates: the initial conditions
with no seed (θ = ξ = 1, every φ_X and pop_X zero, S = 1), keyed by the system's variables (and
seed parameters) like [`default_initial_conditions`](@ref), so it can be passed as `init` to
`solve_epidemic`.
"""
disease_free_equilibrium(sys::EdgeModelSystem) = default_initial_conditions(sys; initial = SeedFraction())

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

# The standard normal quantile Φ⁻¹(p) by Acklam's rational approximation (relative error below
# 1.15e-9 over (0, 1)); the previous Abramowitz & Stegun 26.2.23 form was accurate to 4.5e-4.
function _normal_quantile(p::Real)
    (0 < p < 1) || throw(DomainError(p, "the normal quantile needs 0 < p < 1"))
    a = (-3.969683028665376e+01, 2.209460984245205e+02, -2.759285104469687e+02,
         1.383577518672690e+02, -3.066479806614716e+01, 2.506628277459239e+00)
    b = (-5.447609879822406e+01, 1.615858368580409e+02, -1.556989798598866e+02,
         6.680131188771972e+01, -1.328068155288572e+01)
    c = (-7.784894002430293e-03, -3.223964580411365e-01, -2.400758277161838e+00,
         -2.549732539343734e+00, 4.374664141464968e+00, 2.938163982698783e+00)
    d = (7.784695709041462e-03, 3.224671290700398e-01, 2.445134137142996e+00,
         3.754408661907416e+00)
    plow = 0.02425
    if p < plow
        q = sqrt(-2 * log(p))
        return (((((c[1] * q + c[2]) * q + c[3]) * q + c[4]) * q + c[5]) * q + c[6]) /
               ((((d[1] * q + d[2]) * q + d[3]) * q + d[4]) * q + 1)
    elseif p <= 1 - plow
        q = p - 0.5
        r = q * q
        return (((((a[1] * r + a[2]) * r + a[3]) * r + a[4]) * r + a[5]) * r + a[6]) * q /
               (((((b[1] * r + b[2]) * r + b[3]) * r + b[4]) * r + b[5]) * r + 1)
    end
    q = sqrt(-2 * log1p(-p))
    return -(((((c[1] * q + c[2]) * q + c[3]) * q + c[4]) * q + c[5]) * q + c[6]) /
            ((((d[1] * q + d[2]) * q + d[3]) * q + d[4]) * q + 1)
end
