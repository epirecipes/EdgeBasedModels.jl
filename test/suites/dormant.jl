# WP36b: the edge-based lift on dormant contacts, DynamicNetwork(base, DormantContacts(η₁, η₂)) (Miller, Slim &
# Volz 2012, Part II §3.2.4, papers/1106.6319v1.md:175-201 and the PDF p. 10, which has the ratios π_X/π that the
# markdown rendering loses; Appendix D; DESIGN §C.3, §K WP36b; verified issue E07).
#
# Every expected value comes from an independent source:
# - a hand transcription, in this file, of MSV's dormant-contact (DC) equations in MSV's own variables (θ, φ_S, φ_I,
#   φ_D, ξ_R, π_R, R, with the explicit seed q = 1 − ρ: S = qψ(θ), ξ_S = q(θ − φ_D)ψ'(θ)/ψ'(1),
#   π_S = qφ_Dψ'(θ)/ψ'(1)), mapped onto the lift by a semiconjugacy that NetworkEpiCore's `verify` checks;
# - for SEIR, a transcription of the E07 verifier's general DC equations (VERIFIED_ISSUES.md E07, fix (2)), checked
#   the same way, and the verifier's printed values for its DC scenarios C and D (with its exact stub SSA);
# - the static configuration lift (η₂ = 0), the neighbour-exchange lift of lift/dynamic.jl (η₁ → ∞, MSV Appendix
#   D.1), the MFSH lift of lift/mfsh.jl with the per-contact rate τA (η₁ = η₂ → ∞, Appendix D.3) and a hand
#   transcription of MSV's dynamic variable-degree (DVD) equations (§3.1.3; η₁ → 0 with the degrees scaled by 1/A,
#   Appendix D.2);
# - a branching-process calculation written here, independent of the lift: the expected (discounted)
#   transmissions of a stub of a newly infected node over its active and dormant periods give R₀ (and a closed form
#   for SIR) and, through the Euler–Lotka equation, the early growth rate r;
# - exact simulation of the dormant-contact stub process in NetworkOutbreaks (WP36b, DormantContactProcess): the
#   scenarios' own ensembles (fresh stationary stub states per run from NetworkOutbreaks.stable_rng(base + r), the
#   run from stable_rng(base + 2³² + r), design §J.7; runs conditioned on a major outbreak, design §E.2),
#   summarised by NetworkOutbreaks' `summarise` and compared by NetworkEpiCore's `compare`.

using EdgeBasedModels
using NetworkEpiCore
using ModelingToolkit
using Symbolics
using LinearAlgebra
using Statistics
using Random
using OrdinaryDiffEq: ODEProblem, Vern9
import OrdinaryDiffEq
using Test

import NetworkOutbreaks as NO

const EBM = EdgeBasedModels
const TOL = (solver = Vern9(), reltol = 1e-11, abstol = 1e-13)

dc(d, η1, η2) = DynamicNetwork(d, DormantContacts(η1, η2))
dfd(d, η) = DynamicNetwork(d, NeighbourExchange(η))
curve(sys, sol, X) = compartment(sys, sol, X)
numval(e, at) = Float64(Symbolics.value(Symbolics.substitute(e, at; fold = Val(true))))

const MSV_DEGREES = EmpiricalDegree(2 => 0.5, 8 => 0.5)       # MSV Part II Fig. 5: ψ(x) = (x² + x⁸)/2
const REMOVAL = ContactModel(:rem; contacts = [Contact(:S, :I, :I, 1 / 6)], transitions = [NodeTransition(:I, nothing, 1 / 4)])

κ_excess(d) = pgf_derivative(d, 1.0, 2) / mean_degree(d)

# ---------------------------------------------------------------------------------------------
# MSV's dormant-contact equations, transcribed by hand (PDF p. 10; explicit seed q = q_S)
# ---------------------------------------------------------------------------------------------

# SIR: θ̇ = −τφ_I, φ̇_S = −τφ_Iφ_Sψ''/ψ' + η₁(π_S/π)φ_D − η₂φ_S, φ̇_I = τφ_Iφ_Sψ''/ψ' + η₁(π_I/π)φ_D −
# (η₂ + τ + γ)φ_I, φ̇_D = η₂(θ − φ_D) − η₁φ_D, ξ̇_R = −η₂ξ_R + η₁π_R + γξ_I, π̇_R = η₂ξ_R − η₁π_R + γπ_I,
# Ṙ = γI, with ξ = η₁/(η₁ + η₂), π = η₂/(η₁ + η₂), ξ_S = q(θ − φ_D)ψ'(θ)/ψ'(1), π_S = qφ_Dψ'(θ)/ψ'(1),
# ξ_I = ξ − ξ_S − ξ_R, π_I = π − π_S − π_R, S = qψ(θ), I = 1 − S − R. `η1`, `η2` are numbers or parameters.
# Negative controls: `:no_ratio` is the markdown rendering η₁π_Xφ_D (the division by π lost), `:no_q` drops the
# seed factor from S, ξ_S and π_S.
function msv_dc_sir(d, η1, η2; variant::Symbol = :msv)
    τ, γ, q = as_parameter(:τ), as_parameter(:γ), as_parameter(:q_S)
    qq = variant === :no_q ? 1 : q
    @variables t TH(t) PS(t) PI(t) PD(t) XR(t) PR(t) R(t)
    ψ(x) = pgf(d, x)
    ψ1(x) = pgf_derivative(d, x, 1)
    ψ2(x) = pgf_derivative(d, x, 2)
    k̄ = mean_degree(d)
    ξ, π = η1 / (η1 + η2), η2 / (η1 + η2)
    ξS = qq * (TH - PD) * ψ1(TH) / k̄
    πS = qq * PD * ψ1(TH) / k̄
    ξI, πI = ξ - ξS - XR, π - πS - PR
    new = τ * PI * PS * ψ2(TH) / ψ1(TH)
    activate(πX) = variant === :no_ratio ? η1 * πX * PD : η1 * (πX / π) * PD
    rhs = Any[-τ * PI,
              -new + activate(πS) - η2 * PS,
              new + activate(πI) - (η2 + τ + γ) * PI,
              η2 * (TH - PD) - η1 * PD,
              -η2 * XR + η1 * PR + γ * ξI,
              η2 * XR - η1 * PR + γ * πI,
              γ * (1 - qq * ψ(TH) - R)]
    params = Any[τ, γ, q]
    for η in (η1, η2)
        Symbolics.value(η) isa Real || push!(params, η)
    end
    ode = SymbolicODE(:msv_dc_sir; states = Any[TH, PS, PI, PD, XR, PR, R], rhs, parameters = params,
                      domain = Pair{Any,Tuple{Float64,Float64}}[TH => (0.3, 1.0)])
    return ode, (; TH, PS, PI, PD, XR, PR, R, ψ, ψ1, k̄, ξ, π, ξI, πI, q)
end

# MSV's system is the invariant set {θ = Aθ_A + Dθ_D, θ_A = φ_S + Σφ, α_S + Σα = 1, π_S + Σπ = 1, S + Σpop = 1} of
# the lift (whose coordinates are MSV's divided by the activity fractions: θ_A = (θ − φ_D)/ξ, θ_D = φ_D/π,
# φ_X = φ_X^MSV/ξ, α_X = ξ_X/ξ, π_X = π_X^MSV/π, and φ_S = ξχqψ'(θ)/ψ'(1)): a semiconjugacy MSV → lift.
function msv_inclusion(sys, d, η1, η2; kw...)
    ode, v = msv_dc_sir(d, η1, η2; kw...)
    c = sys.metadata[:coords]
    map = Pair{Any,Any}[c[:θ] => v.TH, c[:θ_A] => (v.TH - v.PD) / v.ξ, c[:θ_D] => v.PD / v.π,
                        c[:χ] => v.PS * v.k̄ / (v.ξ * v.q * v.ψ1(v.TH)), c[:φ_I] => v.PI / v.ξ,
                        c[:φ_R] => (v.TH - v.PS - v.PI - v.PD) / v.ξ, c[:α_I] => v.ξI / v.ξ, c[:α_R] => v.XR / v.ξ,
                        c[:π_I] => v.πI / v.π, c[:π_R] => v.PR / v.π, c[:pop_I] => 1 - v.q * v.ψ(v.TH) - v.R,
                        c[:pop_R] => v.R]
    return Semiconjugacy(:msv_dc_sir, ode, symbolic_ode(sys), map, Pair{Any,Any}[], :restriction, :exact,
                         [Evidence(:paper, "Miller, Slim & Volz 2012, Part II §3.2.4 (papers/1106.6319v1.pdf p. 10)")])
end

# SEIR in the E07 verifier's variables (VERIFIED_ISSUES.md E07, fix (2)): a, d the non-transmission of active and
# dormant stubs, f_X = φ_X/ξ, p_X and q_X the compositions of the dormant and of the active stubs, the entry class E
# taking the remainder: θ' = −ξh, a' = −h − η₂(a − d), d' = η₁(a − d), f_S' = −ξHf_S + η₂(dp_S − f_S),
# f_E' = ξHf_S − (σ + η₂)f_E + η₂dp_E, f_I' = σf_E − (γ + τ + η₂)f_I + η₂dp_I,
# p_X' = η₁(q_X − p_X) + (stage flow), q_X' = η₂(p_X − q_X) + (stage flow), h = τf_I, H = hψ''(θ)/ψ'(θ),
# p_S = qdψ'(θ)/ψ'(1), q_S = qaψ'(θ)/ψ'(1), and the node equations E' = qψ'(θ)ξh − σE, R' = γI.
function verifier_seir(d, η1, η2)
    τ, σ, γ, q = as_parameter(:τ), as_parameter(:σ), as_parameter(:γ), as_parameter(:q_S)
    @variables t TH(t) AA(t) DD(t) FS(t) FE(t) FI(t) PI(t) PR(t) QI(t) QR(t) EE(t) RR(t)
    ψ(x) = pgf(d, x)
    ψ1(x) = pgf_derivative(d, x, 1)
    ψ2(x) = pgf_derivative(d, x, 2)
    k̄ = mean_degree(d)
    ξ = η1 / (η1 + η2)
    h = τ * FI
    H = h * ψ2(TH) / ψ1(TH)
    pS, qS = q * DD * ψ1(TH) / k̄, q * AA * ψ1(TH) / k̄
    pE, qE = 1 - pS - PI - PR, 1 - qS - QI - QR
    rhs = Any[-ξ * h,
              -h - η2 * (AA - DD),
              η1 * (AA - DD),
              -ξ * H * FS + η2 * (DD * pS - FS),
              ξ * H * FS - (σ + η2) * FE + η2 * DD * pE,
              σ * FE - (γ + τ + η2) * FI + η2 * DD * PI,
              η1 * (QI - PI) + σ * pE - γ * PI,
              η1 * (QR - PR) + γ * PI,
              η2 * (PI - QI) + σ * qE - γ * QI,
              η2 * (PR - QR) + γ * QI,
              q * ψ1(TH) * ξ * h - σ * EE,
              γ * (1 - q * ψ(TH) - EE - RR)]
    ode = SymbolicODE(:verifier_dc_seir; states = Any[TH, AA, DD, FS, FE, FI, PI, PR, QI, QR, EE, RR], rhs,
                      parameters = Any[τ, σ, γ, q],
                      domain = Pair{Any,Tuple{Float64,Float64}}[TH => (0.3, 1.0), AA => (0.3, 1.0), DD => (0.3, 1.0)])
    return ode, (; TH, AA, DD, FS, FE, FI, PI, PR, QI, QR, EE, RR, ψ, ψ1, k̄, q, pE, qE)
end

function verifier_inclusion(sys, d, η1, η2)
    ode, v = verifier_seir(d, η1, η2)
    c = sys.metadata[:coords]
    map = Pair{Any,Any}[c[:θ] => v.TH, c[:θ_A] => v.AA, c[:θ_D] => v.DD, c[:χ] => v.FS * v.k̄ / (v.q * v.ψ1(v.TH)),
                        c[:φ_E] => v.FE, c[:φ_I] => v.FI, c[:φ_R] => v.AA - v.FS - v.FE - v.FI,
                        c[:α_E] => v.qE, c[:α_I] => v.QI, c[:α_R] => v.QR,
                        c[:π_E] => v.pE, c[:π_I] => v.PI, c[:π_R] => v.PR,
                        c[:pop_E] => v.EE, c[:pop_I] => 1 - v.q * v.ψ(v.TH) - v.EE - v.RR, c[:pop_R] => v.RR]
    return Semiconjugacy(:verifier_dc_seir, ode, symbolic_ode(sys), map, Pair{Any,Any}[], :restriction, :exact,
                         [Evidence(:paper, "VERIFIED_ISSUES.md E07, fix (2): the dormant-contact model for any stages")])
end

# MSV's DVD equations (§3.1.3, papers/1106.6319v1.md:119-121) with an explicit seed ρ in I, written out here and
# integrated independently of any EBM code: Θ̇ = −τΘ + τqΨ'(Θ)/Ψ'(1) + γ(1 − Θ) + η(1 − Θ − (τ/γ)Π_R),
# Π̇_R = γ(1 − qΨ'(Θ)/Ψ'(1) − Π_R), Ṙ = γ(1 − qΨ(Θ) − R), S = qΨ(Θ). Columns S, I, R on `grid`.
function dvd_curves(Ψ, Ψ1, τ, γ, η, ρ, grid)
    q = 1 - ρ
    Ψ11 = Ψ1(1.0)
    f(u, _, _) = [-τ * u[1] + τ * q * Ψ1(u[1]) / Ψ11 + γ * (1 - u[1]) + η * (1 - u[1] - τ / γ * u[2]),
                  γ * (1 - q * Ψ1(u[1]) / Ψ11 - u[2]),
                  γ * (1 - q * Ψ(u[1]) - u[3])]
    sol = OrdinaryDiffEq.solve(ODEProblem(f, [1.0, 0.0, 0.0], (grid[1], grid[end])), Vern9();
                               saveat = grid, reltol = 1e-12, abstol = 1e-14)
    S = [q * Ψ(u[1]) for u in sol.u]
    R = [u[3] for u in sol.u]
    return hcat(S, 1 .- S .- R, R)
end

# MFSH (MSV §3.2.2) with an explicit seed ρ in I, by hand: θ̇ = −τθ + τqθ²ψ'(θ)/ψ'(1) − γθ ln θ, Ṙ = γ(1 − qψ − R).
function mfsh_curves(d, τ, γ, ρ, grid)
    q = 1 - ρ
    k̄ = mean_degree(d)
    f(u, _, _) = [-τ * u[1] + τ * q * u[1]^2 * pgf_derivative(d, u[1], 1) / k̄ - γ * u[1] * log(u[1]),
                  γ * (1 - q * pgf(d, u[1]) - u[2])]
    sol = OrdinaryDiffEq.solve(ODEProblem(f, [1.0, 0.0], (grid[1], grid[end])), Vern9();
                               saveat = grid, reltol = 1e-12, abstol = 1e-14)
    S = [q * pgf(d, u[1]) for u in sol.u]
    R = [u[2] for u in sol.u]
    return hcat(S, 1 .- S .- R, R)
end

sir_curves(sys, sol) = hcat(curve(sys, sol, :S), curve(sys, sol, :pop_I), curve(sys, sol, :pop_R))

# The observables of a model on a lifted system: S, every pop_X and the fraction ever infected.
function node_curves(sys, sol, cm)
    Xs = vcat([:S, :cumulative], [Symbol(:pop_, Y) for Y in species_names(cm) if Y ∉ susceptible_species(cm)])
    haskey(sys.variables, :pop_removed) && push!(Xs, :pop_removed)
    return Xs, reduce(hcat, [curve(sys, sol, X) for X in Xs])
end

# Conservation along a solution: max_t of |S + Σpop − 1|, |θ − Aθ_A − Dθ_D|, |θ_A − φ_S − Σφ|, |α_S + Σα − 1|,
# |π_S + Σπ − 1|.
function conservation_errors(sys, sol, A)
    ks = collect(keys(sys.variables))
    total(prefix) = sum(curve(sys, sol, k) for k in ks if startswith(string(k), prefix))
    θ, θA, θD = curve(sys, sol, :θ), curve(sys, sol, :θ_A), curve(sys, sol, :θ_D)
    node = maximum(abs.(curve(sys, sol, :S) .+ total("pop_") .- 1))
    split = maximum(abs.(θ .- A .* θA .- (1 - A) .* θD))
    edge = maximum(abs.(θA .- curve(sys, sol, :φ_S) .- total("φ_")))
    active = maximum(abs.(curve(sys, sol, :α_S) .+ total("α_") .- 1))
    dormant = maximum(abs.(curve(sys, sol, :π_S) .+ total("π_") .- 1))
    return (; node, split, edge, active, dormant)
end

# ---------------------------------------------------------------------------------------------
# The stub branching process (R₀ and r without the lift)
# ---------------------------------------------------------------------------------------------

# The expected transmissions, discounted at rate r, of a stub of a node in stage X of the infection chain `stages`
# at the disease-free state: m_a (active, its partner susceptible and not yet infected by it), m_t (active, the
# partner already infected) and m_d (dormant). An active stub with a susceptible partner transmits at rate τ_X and
# its partnership is then used; an active edge breaks at rate η₂ (the stub becomes dormant); a dormant stub
# activates at rate η₁ with a fresh, susceptible partner; the node moves between stages at the model's rates (a
# transition out of the chain ends the count). `out` lists X => [(Y, rate), …].
function stub_offspring(stages, τX, out, η1, η2; r = 0.0)
    n = length(stages)
    ix = Dict(X => i for (i, X) in enumerate(stages))
    M = zeros(3n, 3n)
    b = zeros(3n)
    a_(i) = i
    t_(i) = n + i
    d_(i) = 2n + i
    for (i, X) in enumerate(stages)
        leave = sum((a for (_, a) in get(out, X, [])); init = 0.0)
        τ = get(τX, X, 0.0)
        M[a_(i), a_(i)] = τ + η2 + leave + r; M[a_(i), t_(i)] -= τ; M[a_(i), d_(i)] -= η2; b[a_(i)] = τ
        M[t_(i), t_(i)] = η2 + leave + r; M[t_(i), d_(i)] -= η2
        M[d_(i), d_(i)] = η1 + leave + r; M[d_(i), a_(i)] -= η1
        for (Y, a) in get(out, X, [])
            haskey(ix, Y) || continue
            j = ix[Y]
            M[a_(i), a_(j)] -= a; M[t_(i), t_(j)] -= a; M[d_(i), d_(j)] -= a
        end
    end
    m = M \ b
    return (a = m[1:n], t = m[(n + 1):2n], d = m[(2n + 1):3n], ix = ix)
end

# The (discounted) offspring of a node newly infected into `entry`: the stub it was infected through is in state t,
# and each of its κ_ex other stubs (in expectation) is active with a susceptible partner with probability A and
# dormant with probability D. R₀ = this at r = 0; the early growth rate solves it = 1 (Euler–Lotka).
function offspring(stages, τX, out, entry, η1, η2, κex; r = 0.0)
    A = η1 / (η1 + η2)
    m = stub_offspring(stages, τX, out, η1, η2; r)
    i = m.ix[entry]
    return m.t[i] + κex * (A * m.a[i] + (1 - A) * m.d[i])
end

# (only for R₀ > 1, so r > 0: the bracket starts at r = 0, where the discounted offspring is R₀ > 1; a negative r
# below minus the slowest decay rate of the stub process would make the discounted count diverge)
function euler_lotka(args...; lo = 0.0, hi = 10.0)
    f(r) = offspring(args...; r) - 1
    @assert f(lo) > 0 > f(hi)
    for _ in 1:200
        mid = (lo + hi) / 2
        f(mid) > 0 ? (lo = mid) : (hi = mid)
    end
    return (lo + hi) / 2
end

# The SIR closed form of `offspring` at r = 0 (solved by hand with sympy): R₀ = η₁τ(η₁η₂κ + η₁η₂ + η₁γκ + η₂²κ + η₂²
# + 2η₂γκ + γ²κ) / (γ(η₁ + η₂)(η₁ + η₂ + γ)(η₂ + γ + τ)), κ = κ_ex. η₂ = 0 gives τκ/(τ + γ) (static) and η₁ → ∞
# gives MSV's DFD value τ/(τ + η₂ + γ)·(η₂/γ + (η₂ + γ)κ/γ).
dc_R0(τ, γ, η1, η2, κ) = η1 * τ * (η1 * η2 * κ + η1 * η2 + η1 * γ * κ + η2^2 * κ + η2^2 + 2η2 * γ * κ + γ^2 * κ) /
                         (γ * (η1 + η2) * (η1 + η2 + γ) * (η2 + γ + τ))

# ---------------------------------------------------------------------------------------------
# NetworkOutbreaks ensembles
# ---------------------------------------------------------------------------------------------

const BASE = 20260927

# The comparison table of the EB curves with the reference summary of a scenario from NetworkOutbreaks' dormant-
# contact process (the scenario's own N, runs, seeds, grid, conditioning).
function against_process(sc)
    summary = NO.summarise(NO.scenario_ensemble(sc))
    sys = edge_based(sc)
    sol = solve_epidemic(sys, sc; TOL...)
    return compare(summary, model_curves(sys, sol; t = sc.tgrid, label = "edge-based")), sys, sol
end

# EB curves of `obs` against NetworkOutbreaks runs conditioned on a major outbreak.
function no_runs(cm, net, p, initial, grid; N, nsims, obs)
    ens = NO.simulate(cm, net; N, p, initial, tspan = (0.0, grid[end]), nsims, seed = BASE, tgrid = grid)
    nseed = sum(round(Int, v * N) for (_, v) in seed_fractions(initial))
    runs = Matrix{Float64}[]
    for tr in ens.trajectories
        NO.final_size(tr) * N - nseed >= 0.05 * N || continue
        ix = [tr.model.index_of[X] for X in obs]
        push!(runs, reduce(hcat, [NO.state_at(tr, t)[ix] ./ N for t in grid]))
    end
    return runs, length(ens.trajectories)
end

# D∞ = max over observables and time of |EB − mean of the runs|, with the SE of the mean there.
function discrepancy(eb::AbstractMatrix, runs)
    A = cat(runs...; dims = 3)
    μ = dropdims(mean(A; dims = 3); dims = 3)
    se = dropdims(std(A; dims = 3); dims = 3) ./ sqrt(length(runs))
    d = abs.(eb .- μ)
    k = argmax(d)
    return (D = d[k], se = se[k], at = k)
end

# ---------------------------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------------------------

@testset "lift: dormant contacts (MSV Part II §3.2.4)" begin
    @testset "structure: coordinates, seeds, observables, metadata, the process row" begin
        net = dc(MSV_DEGREES, 1.0, 1.0)
        cm = sir_model(; τ = 1.0, γ = 1.0)
        sys = edge_based(cm, net)
        @test Set(keys(sys.variables)) == Set([:θ, :θ_A, :θ_D, :χ, :φ_I, :φ_R, :α_I, :α_R, :π_I, :π_R, :pop_I, :pop_R,
                                              :cumulative, :R])
        @test Set(keys(sys.observables)) == Set([:S, :I, :infectious, :φ_S, :α_S, :π_S, :edge_hazard, :excess_hazard])
        md = sys.metadata
        @test md[:kind] === :assembled && md[:closure] === :dormant && md[:form] === :expanded
        @test md[:network] == net && md[:model] == cm && md[:entry] === :I
        @test Set(keys(md[:seed_params])) == Set([:I, :R])
        table = md[:contributions]
        @test table isa LiftContributions && table.closure === :dormant
        @test [r.type for r in table] == [:contact, :progress, :process]
        @test table[:dormant_contacts].type === :process && table[:dormant_contacts].flux == 0
        @test first.(table.coordinates) == [:θ, :θ_A, :θ_D, :χ, :ξ, :φ_I, :φ_R, :α_I, :α_R, :π_I, :π_R, :pop_I, :pop_R]
        @test :ξ ∉ state_names(symbolic_ode(sys))                     # nothing exits: ξ ≡ 1 is dropped
        # the table's field is the system's field, and so is lift_contributions'
        @test vector_fields_equal(symbolic_ode(table), symbolic_ode(sys))
        @test vector_fields_equal(symbolic_ode(lift_contributions(cm, net)), symbolic_ode(sys))
        # the rows at a probe point, against the formulas of the lift written out here (A = D = 1/2, ψ'(1) = 5)
        coord = Dict(table.coordinates)
        q = only(last.(table.seed_factors))
        pt = (θ = 0.8, θA = 0.85, θD = 0.75, χ = 0.7, φI = 0.1, φR = 0.05, αI = 0.12, αR = 0.06, πI = 0.09, πR = 0.07)
        at = Dict{Any,Any}(coord[:θ] => pt.θ, coord[:θ_A] => pt.θA, coord[:θ_D] => pt.θD, coord[:χ] => pt.χ,
                           coord[:ξ] => 1.0, coord[:φ_I] => pt.φI, coord[:φ_R] => pt.φR, coord[:α_I] => pt.αI,
                           coord[:α_R] => pt.αR, coord[:π_I] => pt.πI, coord[:π_R] => pt.πR, q => 0.97)
        ψ1, ψ2 = pgf_derivative(MSV_DEGREES, pt.θ, 1), pgf_derivative(MSV_DEGREES, pt.θ, 2)
        u = 1.0 * pt.φI
        h = 0.5 * u
        contact = Dict{Symbol,Float64}()
        for (k, v) in table[1].terms
            contact[k] = get(contact, k, 0.0) + numval(v, at)
        end
        @test contact[:θ] ≈ -h atol = 1e-15
        @test contact[:θ_A] ≈ -u atol = 1e-15
        @test contact[:φ_I] ≈ -u + h * pt.χ * 0.97 * ψ2 / 5 atol = 1e-15
        @test contact[:α_I] ≈ u * 0.97 * (ψ1 + 0.5 * pt.θA * ψ2) / 5 atol = 1e-15
        @test contact[:π_I] ≈ h * 0.97 * pt.θD * ψ2 / 5 atol = 1e-15
        @test contact[:pop_I] ≈ h * 0.97 * ψ1 atol = 1e-15
        process = Dict(k => numval(v, at) for (k, v) in table[:dormant_contacts].terms)
        @test process[:θ_A] ≈ pt.θD - pt.θA atol = 1e-15
        @test process[:θ_D] ≈ pt.θA - pt.θD atol = 1e-15
        @test process[:χ] ≈ pt.θD^2 - pt.χ atol = 1e-15
        @test process[:φ_I] ≈ pt.θD * pt.πI - pt.φI atol = 1e-15
        @test process[:α_R] ≈ pt.πR - pt.αR atol = 1e-15
        @test process[:π_R] ≈ pt.αR - pt.πR atol = 1e-15
        @test Set(keys(process)) == Set([:θ_A, :θ_D, :χ, :φ_I, :φ_R, :α_I, :α_R, :π_I, :π_R])
        # initial conditions: θ = θ_A = θ_D = χ = 1, φ = α = π = pop = ρ in the seeded class, S(0) = 1 − ρ
        c = md[:coords]
        ic = default_initial_conditions(sys; initial = SeedFraction(:I => 0.01))
        @test all(ic[c[X]] == 1 for X in (:θ, :θ_A, :θ_D, :χ))
        @test ic[c[:φ_I]] == ic[c[:α_I]] == ic[c[:π_I]] == ic[c[:pop_I]] == 0.01
        @test ic[c[:φ_R]] == ic[c[:α_R]] == ic[c[:π_R]] == ic[c[:pop_R]] == 0
        sol = solve_epidemic(sys; initial = SeedFraction(:I => 0.01), tspan = (0.0, 20.0), saveat = 0.0:0.5:20.0, TOL...)
        @test curve(sys, sol, :S)[1] ≈ 0.99 atol = 1e-14
        for X in (:φ_S, :α_S, :π_S)
            @test curve(sys, sol, X)[1] ≈ 0.99 atol = 1e-14
        end
        @test curve(sys, sol, :cumulative) ≈ 1 .- curve(sys, sol, :S) atol = 1e-10       # SIR: ever infected = 1 − S
        @test curve(sys, sol, :edge_hazard) ≈ 0.5 .* curve(sys, sol, :φ_I) atol = 1e-14   # τAφ_I
        # edge_hazard = −θ̇ along the solution (central differences of a dense solution: no saveat)
        dense = solve_epidemic(sys; initial = SeedFraction(:I => 0.01), tspan = (0.0, 20.0), TOL...)
        for t in (2.0, 5.0, 9.0)
            θdot = (dense(t + 1e-4; idxs = c[:θ]) - dense(t - 1e-4; idxs = c[:θ])) / 2e-4
            @test dense(t; idxs = sys.observables[:edge_hazard]) ≈ -θdot rtol = 1e-6
        end
        mc = model_curves(sys, sol; t = 0:1.0:20)
        @test mc.representation === :edge_based
        @test issubset([:S, :I, :R, :infectious, :cumulative], keys(mc.values))
        # the network's mean degree is Aψ'(1), the mean number of active contacts (NetworkEpiCore)
        @test mean_degree(net) ≈ 2.5
        @test mean_degree(dc(MSV_DEGREES, 1.0, 3.0)) ≈ 1.25
        # a latent class, exits and removals get their own coordinates
        seir = edge_based(seir_model(), net)
        @test issubset([:φ_E, :α_E, :π_E, :pop_E], keys(seir.variables)) && seir.metadata[:entry] === :E
        sirv = edge_based(sirv_model(), net)
        @test issubset([:ξ, :φ_V, :α_V, :π_V, :pop_V], keys(sirv.variables))
        rem = edge_based(REMOVAL, net)
        @test issubset([:φ_removed, :α_removed, :π_removed, :pop_removed], keys(rem.variables)) &&
              rem.metadata[:sinks] == [:removed]
        # Symbol rates are parameters; the scenario form lifts the scenario's model and network
        @test issubset(Set([:τ, :σ, :γ]), Set(Symbol(Symbolics.getname(x)) for x in symbolic_ode(seir).parameters))
        sc = scenario(:sir_dormant_msv)
        @test edge_based(sc).metadata[:network] == sc.network
        @test sc.expected[:mean_degree] ≈ 2.5
    end

    @testset "MSV Part II §3.2.4 (hand transcription) is the invariant set of the lift, four ψ, symbolic η" begin
        η1, η2 = as_parameter(:η₁), as_parameter(:η₂)
        # (the negative binomial ψ, whose symbolic form has a non-integer power, is checked with numeric η below: with
        # symbolic η₁, η₂ as well the symbolic simplification in `verify` does not finish in 15 minutes)
        for d in (MSV_DEGREES, PoissonDegree(3.0), RegularDegree(4))
            sys = edge_based(sir_model(), dc(d, η1, η2))
            r = verify(msv_inclusion(sys, d, η1, η2))
            @test r.ok
            @test r.max_residual < 1e-12
            # the markdown rendering (no division by π) and the missing seed factor are not MSV's model
            @test !verify(msv_inclusion(sys, d, η1, η2; variant = :no_ratio)).ok
            @test !verify(msv_inclusion(sys, d, η1, η2; variant = :no_q)).ok
        end
        # numeric rates: the same identity (the scenario's η₁ = η₂ = 1 and an asymmetric pair)
        for (a, b) in ((1.0, 1.0), (0.1, 1.0), (3.0, 0.5)), d in (MSV_DEGREES, NegBinDegree(4.0, 2 / 3))
            sys = edge_based(sir_model(), dc(d, a, b))
            @test verify(msv_inclusion(sys, d, a, b)).ok
        end
    end

    @testset "SEIR: the E07 verifier's general dormant-contact equations are the invariant set of the lift" begin
        η1, η2 = as_parameter(:η₁), as_parameter(:η₂)
        for d in (PoissonDegree(5.0), MSV_DEGREES)
            sys = edge_based(seir_model(), dc(d, η1, η2))
            r = verify(verifier_inclusion(sys, d, η1, η2))
            @test r.ok
            @test r.max_residual < 1e-12
        end
    end

    @testset "η₁ and η₂ both enter (E07: the legacy builder ignored η₁)" begin
        η1, η2 = as_parameter(:η₁), as_parameter(:η₂)
        sys = edge_based(sir_model(), dc(PoissonDegree(3.0), η1, η2))
        f = symbolic_ode(sys)
        @test issubset([:η₁, :η₂], Set(Symbol(Symbolics.getname(x)) for x in f.parameters))
        rng = Random.Xoshiro(362)
        at = Dict{Any,Any}(s => 0.2 + 0.6rand(rng) for s in f.states)
        for p in f.parameters
            at[p] = 0.3 + rand(rng)
        end
        for η in (η1, η2)
            ∂ = [numval(Symbolics.derivative(Num(e), η), at) for e in f.rhs]
            @test maximum(abs, ∂) > 1e-3
        end
        # E07, scenario C (MSV §3.3: Poisson(3), β = 2, γ = 1, η₂ = 0.5, 0.1% seeded). The verifier's exact stub SSA
        # (N = 2×10⁴, 40 runs): η₁ = 0.25 subcritical (0.011), η₁ = 1: 0.6264 ± 0.0011, η₁ = 5: 0.7992 ± 0.0005; its
        # DC ODE: 0.0089, 0.6258, 0.7993; the legacy builder: 0.8434 for all three.
        attack = Float64[]
        for (η₁, fix, ssa, se) in ((0.25, 0.0089, nothing, nothing), (1.0, 0.6258, 0.6264, 0.0011),
                                   (5.0, 0.7993, 0.7992, 0.0005))
            s = edge_based(sir_model(; τ = 2.0, γ = 1.0), dc(PoissonDegree(3.0), η₁, 0.5))
            so = solve_epidemic(s; initial = SeedFraction(:I => 1e-3), tspan = (0.0, 400.0), TOL...)
            a = 1 - curve(s, so, :S)[end]
            push!(attack, a)
            @test a ≈ fix atol = 1e-4
            if ssa === nothing
                @test basic_reproduction_number(s) < 1                  # subcritical (R₀ = 0.898)
            else
                @test abs(a - ssa) < 3se
                @test abs(0.8434 - ssa) > 10se                           # the legacy value is refuted
            end
        end
        @test issorted(attack) && allunique(attack)
        # η₂ alone matters as well (η₁ = 1): the final size at η₂ = 0.5, 1, 2 differs
        fs = map((0.5, 1.0, 2.0)) do b
            s = edge_based(sir_model(; τ = 2.0, γ = 1.0), dc(PoissonDegree(3.0), 1.0, b))
            final_size(s; initial = SeedFraction(:I => 1e-3))
        end
        @test minimum(abs, diff(collect(fs))) > 0.05
        # E07, scenario D (SEIR: τ = 0.4, σ = 0.5, γ = 0.25, Poisson(5), η₁ = 1, η₂ = 0.5, 0.1% in E): the verifier's
        # DC ODE gives attack / peak I / time of peak 0.9169 / 0.2441 / 22.89 (its SSA 0.9167 / 0.2446 / 23.2); the
        # legacy builder 0.8881 / 0.3238 / 6.15
        s = edge_based(seir_model(; τ = 0.4, σ = 0.5, γ = 0.25), dc(PoissonDegree(5.0), 1.0, 0.5))
        so = solve_epidemic(s; initial = SeedFraction(:E => 1e-3), tspan = (0.0, 400.0), saveat = 0.01, TOL...)
        I = curve(s, so, :pop_I)
        k = argmax(I)
        @test 1 - curve(s, so, :S)[end] ≈ 0.9169 atol = 1e-4
        @test I[k] ≈ 0.2441 atol = 1e-4
        @test so.t[k] ≈ 22.89 atol = 0.01
        @test abs(1 - curve(s, so, :S)[end] - 0.9167) < 2e-3
    end

    @testset "η₂ = 0 is the static configuration model; η₁ = 0 has no contacts" begin
        # With η₂ = 0 every stub is active (A = 1): χ ≡ 1, θ_A ≡ θ, and the θ, ξ, φ and pop equations are exactly those
        # of edge_based(cm, base) (symbolically, after χ = 1, θ_A = θ); trajectories agree to 1e-10.
        function static_part(sys)
            raw = symbolic_ode(sys)
            c = sys.metadata[:coords]
            keep = [i for (i, n) in enumerate(state_names(raw))
                    if n in (:θ, :ξ) || startswith(string(n), "φ_") || startswith(string(n), "pop_")]
            sub(e) = Symbolics.substitute(e, Dict{Any,Any}(c[:χ] => 1, c[:θ_A] => c[:θ]); fold = Val(true))
            return SymbolicODE(:dc_at_eta2_0; states = raw.states[keep], rhs = Any[sub(raw.rhs[i]) for i in keep],
                               parameters = :infer, domain = raw.domain)
        end
        models = (sir_model(), seir_model(), seair_model(), twostrain_model(), sirv_model(),
                  ContactModel(:rem; contacts = [Contact(:S, :I, :I, :τ)], transitions = [NodeTransition(:I, nothing, :γ)]))
        for cm in models, d in (RegularDegree(6), PoissonDegree(5.0), MSV_DEGREES)
            @test vector_fields_equal(static_part(edge_based(cm, dc(d, 1.0, 0.0))),
                                      symbolic_ode(edge_based(cm, ConfigurationNetwork(d))))
        end
        cases = ((sir_model(; τ = 1 / 6, γ = 1 / 4), SeedFraction(:I => 0.05)),
                 (seir_model(; τ = 1 / 6, σ = 1 / 5, γ = 1 / 4), SeedFraction(:E => 0.01)),
                 (sirv_model(; τ = 1 / 6, γ = 1 / 4, ν = 0.02), SeedFraction(:I => 0.01)))
        grid = 0.0:1.0:150.0
        for (cm, initial) in cases, d in (RegularDegree(6), PoissonDegree(5.0), MSV_DEGREES)
            dy = edge_based(cm, dc(d, 0.7, 0.0))
            st = edge_based(cm, ConfigurationNetwork(d))
            sd = solve_epidemic(dy; initial, tspan = (0.0, 150.0), saveat = grid, TOL...)
            ss = solve_epidemic(st; initial, tspan = (0.0, 150.0), saveat = grid, TOL...)
            Xs, x = node_curves(dy, sd, cm)
            @test maximum(abs.(x .- reduce(hcat, [curve(st, ss, X) for X in Xs]))) < 1e-10
            @test maximum(abs.(curve(dy, sd, :χ) .- 1)) < 1e-12
            @test maximum(abs.(curve(dy, sd, :θ_A) .- curve(dy, sd, :θ))) < 1e-12
        end
        # η₁ = 0: every stub is dormant (A = 0), nobody is ever infected (S stays 1 − ρ), and nothing is NaN
        s0 = edge_based(sir_model(; τ = 1.0, γ = 0.25), dc(MSV_DEGREES, 0.0, 1.0))
        so = solve_epidemic(s0; initial = SeedFraction(:I => 0.01), tspan = (0.0, 50.0), TOL...)
        @test all(isfinite, reduce(vcat, so.u))
        @test curve(s0, so, :S)[end] ≈ 0.99 atol = 1e-14
        @test curve(s0, so, :cumulative)[end] ≈ 0.01 atol = 1e-12
        @test basic_reproduction_number(s0) == 0
    end

    @testset "conservation: θ = Aθ_A + Dθ_D, θ_A = φ_S + Σφ, Σα = Σπ = 1, S + Σpop = 1 (every T_EB shape)" begin
        cases = ((sir_model(; τ = 1 / 6, γ = 1 / 4), SeedFraction(:I => 0.01)),
                 (seir_model(; τ = 1 / 6, σ = 1 / 5, γ = 1 / 4), SeedFraction(:E => 0.01)),
                 (seair_model(; τI = 1 / 6, τA = 1 / 12, σ = 1 / 5, p = 0.6, γ = 1 / 4), SeedFraction(:E => 0.01)),
                 (twostrain_model(; τ1 = 1 / 6, τ2 = 1 / 5, γ = 1 / 4), SeedFraction(:I1 => 0.005, :I2 => 0.005)),
                 (sirv_model(; τ = 1 / 6, γ = 1 / 4, ν = 0.02), SeedFraction(:I => 0.01)),
                 (REMOVAL, SeedFraction(:I => 0.01)))
        for (cm, initial) in cases, d in (RegularDegree(6), PoissonDegree(5.0), NegBinDegree(; mean = 4, var = 8)),
            (a, b) in ((0.3, 1.0), (2.0, 0.5))
            sys = edge_based(cm, dc(d, a, b))
            sol = solve_epidemic(sys; initial, tspan = (0.0, 150.0), saveat = 0.0:1.0:150.0, TOL...)
            e = conservation_errors(sys, sol, a / (a + b))
            @test e.node < 1e-9 && e.split < 1e-9 && e.edge < 1e-9 && e.active < 1e-9 && e.dormant < 1e-9
            @test all(>=(-1e-12), curve(sys, sol, :χ)) && all(<=(1 + 1e-12), curve(sys, sol, :χ))
            @test all(>=(-1e-12), curve(sys, sol, :cumulative))
        end
    end

    @testset "limits (MSV Appendix D): η₁ → ∞ is neighbour exchange at η = η₂" begin
        # the DFD lift of lift/dynamic.jl (WP21) at η = η₂; the error is O(D) = O(η₂/η₁)
        cases = ((sir_model(; τ = 1.0, γ = 1.0), SeedFraction(:I => 0.01), 20.0),
                 (seir_model(; τ = 1 / 6, σ = 1 / 5, γ = 1 / 4), SeedFraction(:E => 0.01), 150.0))
        for (cm, initial, T) in cases, d in (MSV_DEGREES, PoissonDegree(5.0))
            grid = 0.0:(T / 200):T
            ref_sys = edge_based(cm, dfd(d, 1.0))
            ref_sol = solve_epidemic(ref_sys; initial, tspan = (0.0, T), saveat = grid, TOL...)
            Xs, ref = node_curves(ref_sys, ref_sol, cm)
            errs = Float64[]
            for η₁ in (10.0, 100.0, 1000.0, 10_000.0)
                sys = edge_based(cm, dc(d, η₁, 1.0))
                sol = solve_epidemic(sys; initial, tspan = (0.0, T), saveat = grid, TOL...)
                push!(errs, maximum(abs.(reduce(hcat, [curve(sys, sol, X) for X in Xs]) .- ref)))
            end
            @info "WP36b η₁ → ∞: max |DC(η₁, 1) − DFD(1)| for η₁ = 10, 100, 1000, 10⁴" model = cm.name degrees = d errs = join(round.(errs; sigdigits = 3), ", ")
            @test issorted(errs; rev = true) && allunique(errs)
            @test errs[end] < 1e-3
            @test errs[end - 1] / errs[end] > 5                          # O(1/η₁): ratio ≈ 10
        end
    end

    @testset "limits (MSV Appendix D): η₁ = η₂ → ∞ is MFSH with the per-contact rate τA" begin
        # MSV Fig. 5 (bottom): ψ = (x² + x⁸)/2, β = γ = 1, η₁ = η₂: MFSH with βξ = 1/2. References: the MFSH lift of
        # lift/mfsh.jl (WP36c) and the MFSH ODE written out here.
        grid = 0.0:0.1:20.0
        cm = sir_model(; τ = 1.0, γ = 1.0)
        mf_sys = edge_based(sir_model(; τ = 0.5, γ = 1.0), MFSHNetwork(MSV_DEGREES))
        mf_sol = solve_epidemic(mf_sys; initial = SeedFraction(:I => 0.01), tspan = (0.0, 20.0), saveat = grid, TOL...)
        mf = sir_curves(mf_sys, mf_sol)
        @test maximum(abs.(mf .- mfsh_curves(MSV_DEGREES, 0.5, 1.0, 0.01, collect(grid)))) < 1e-9
        errs = Float64[]
        for η in (10.0, 100.0, 1000.0, 10_000.0)
            sys = edge_based(cm, dc(MSV_DEGREES, η, η))
            sol = solve_epidemic(sys; initial = SeedFraction(:I => 0.01), tspan = (0.0, 20.0), saveat = grid, TOL...)
            push!(errs, maximum(abs.(sir_curves(sys, sol) .- mf)))
        end
        @info "WP36b η₁ = η₂ → ∞: max |DC(η, η) − MFSH(τ/2)| for η = 10, 100, 1000, 10⁴" errs = join(round.(errs; sigdigits = 3), ", ")
        @test issorted(errs; rev = true) && allunique(errs)
        @test errs[end] < 1e-3
        @test errs[end - 1] / errs[end] > 5
        # the scenario pair: :sir_dormant_fast (η = 10) is between :sir_dormant_msv (η = 1) and :sir_mfsh_msv
        R∞ = map((:sir_dormant_msv, :sir_dormant_fast, :sir_mfsh_msv)) do id
            sc = scenario(id)
            sys = edge_based(sc)
            final_size(sys; p = sc.params, initial = sc.initial, method = :ode)
        end
        @info "WP36b R∞ of :sir_dormant_msv, :sir_dormant_fast, :sir_mfsh_msv" R∞
        @test R∞[1] < R∞[2] < R∞[3]
        # and the final-size gap to MFSH closes at O(1/η): η = 10 (the scenario) against η = 100
        R100 = final_size(edge_based(cm, dc(MSV_DEGREES, 100.0, 100.0)); initial = SeedFraction(:I => 0.01), method = :ode)
        @test R∞[2] < R100 < R∞[3]
        @test 5 < (R∞[3] - R∞[2]) / (R∞[3] - R100) < 20
    end

    @testset "limits (MSV Appendix D.2): η₁ → 0 with degrees scaled by 1/A is the DVD model" begin
        # MSV Fig. 5 (middle): β = γ = 1, η₂ = 1, ψ = (x^L + x^{4L})/2 with L = 1/A = (η₁ + η₂)/η₁, against the DVD
        # model with η = 1 and Ψ(x) = (e^{−(1−x)} + e^{−4(1−x)})/2, transcribed by hand above.
        Ψ(x) = (exp(-(1 - x)) + exp(-4 * (1 - x))) / 2
        Ψ1(x) = (exp(-(1 - x)) + 4 * exp(-4 * (1 - x))) / 2
        grid = collect(0.0:0.1:20.0)
        dv = dvd_curves(Ψ, Ψ1, 1.0, 1.0, 1.0, 0.01, grid)
        cm = sir_model(; τ = 1.0, γ = 1.0)
        errs = Float64[]
        for L in (3, 6, 11, 21, 41)
            sys = edge_based(cm, dc(EmpiricalDegree(L => 0.5, 4L => 0.5), 1 / (L - 1), 1.0))
            sol = solve_epidemic(sys; initial = SeedFraction(:I => 0.01), tspan = (0.0, 20.0), saveat = grid, TOL...)
            push!(errs, maximum(abs.(sir_curves(sys, sol) .- dv)))
        end
        @info "WP36b DC → DVD: max |DC − DVD| for L = 3, 6, 11, 21, 41" errs = join(round.(errs; sigdigits = 3), ", ") R∞_DVD = dv[end, 3]
        @test issorted(errs; rev = true) && allunique(errs)
        @test errs[end] < 0.01
        @test errs[1] / errs[end] > 5                                    # O(1/L)
        # the scenario :sir_dormant_dvd is the L = 11 member
        sc = scenario(:sir_dormant_dvd)
        @test sc.network == dc(EmpiricalDegree(11 => 0.5, 44 => 0.5), 0.1, 1.0)
    end

    @testset "R₀ and r: the stub branching process (closed form for SIR) and the growth of the lift itself" begin
        sir_stages(τ, γ) = ([:I], Dict(:I => τ), Dict(:I => [(:R, γ)]))
        for d in (PoissonDegree(3.0), MSV_DEGREES, RegularDegree(6)), (τ, γ) in ((2.0, 1.0), (1 / 6, 1 / 4)),
            (a, b) in ((0.25, 0.5), (1.0, 1.0), (5.0, 0.5), (0.1, 1.0))
            sys = edge_based(sir_model(; τ, γ), dc(d, a, b))
            κ = κ_excess(d)
            R0 = offspring(sir_stages(τ, γ)..., :I, a, b, κ)
            @test R0 ≈ dc_R0(τ, γ, a, b, κ) rtol = 1e-12
            @test basic_reproduction_number(sys) ≈ R0 rtol = 1e-10
            @test only(next_generation_matrix(sys)) ≈ R0 rtol = 1e-10
            if R0 > 1.05
                @test early_growth_rate(sys) ≈ euler_lotka(sir_stages(τ, γ)..., :I, a, b, κ) rtol = 1e-8
            end
        end
        # the limits of the closed form: static (η₂ = 0) and DFD (η₁ → ∞, MSV Part I's R₀)
        @test dc_R0(0.5, 1.0, 3.0, 0.0, 4.0) ≈ 0.5 * 4 / 1.5
        @test dc_R0(0.5, 1.0, 1e9, 0.7, 4.0) ≈ 0.5 / 2.2 * (0.7 + 1.7 * 4.0) rtol = 1e-8
        # the canonical scenarios
        for (id, R0) in ((:sir_dormant_msv, 92 / 45), (:sir_dormant_fast, nothing), (:sir_dormant_dvd, nothing))
            sc = scenario(id)
            d, p = sc.network.base.degrees, sc.network.process
            ref = dc_R0(1.0, 1.0, p.η_form, p.η_break, κ_excess(d))
            R0 === nothing || @test ref ≈ R0 rtol = 1e-14
            @test basic_reproduction_number(edge_based(sc); p = sc.params) ≈ ref rtol = 1e-10
        end
        # SEIR and SEAIR (two infectors) against the stub process of their stages
        seir = ([:E, :I], Dict(:I => 1 / 6), Dict(:E => [(:I, 1 / 5)], :I => [(:R, 1 / 4)]))
        seair = ([:E, :A, :I], Dict(:I => 1 / 6, :A => 1 / 12),
                 Dict(:E => [(:I, 0.6 / 5), (:A, 0.4 / 5)], :A => [(:R, 1 / 4)], :I => [(:R, 1 / 4)]))   # p = P(E → I)
        for (cm, st) in ((seir_model(; τ = 1 / 6, σ = 1 / 5, γ = 1 / 4), seir),
                         (seair_model(; τI = 1 / 6, τA = 1 / 12, σ = 1 / 5, p = 0.6, γ = 1 / 4), seair)),
            d in (PoissonDegree(5.0), MSV_DEGREES), (a, b) in ((1.0, 0.5), (0.3, 1.0))
            sys = edge_based(cm, dc(d, a, b))
            R0 = offspring(st..., :E, a, b, κ_excess(d))
            @test basic_reproduction_number(sys) ≈ R0 rtol = 1e-10
            R0 > 1.05 && @test early_growth_rate(sys) ≈ euler_lotka(st..., :E, a, b, κ_excess(d)) rtol = 1e-8
        end
        # two strains: a diagonal next-generation matrix, one entry per strain
        sys = edge_based(twostrain_model(; τ1 = 1 / 6, τ2 = 1 / 5, γ = 1 / 4), dc(PoissonDegree(5.0), 1.0, 0.5))
        K = next_generation_matrix(sys)
        R1 = offspring([:I1], Dict(:I1 => 1 / 6), Dict(:I1 => [(:R, 1 / 4)]), :I1, 1.0, 0.5, 5.0)
        R2 = offspring([:I2], Dict(:I2 => 1 / 5), Dict(:I2 => [(:R, 1 / 4)]), :I2, 1.0, 0.5, 5.0)
        @test size(K) == (2, 2) && abs(K[1, 2]) < 1e-12 && abs(K[2, 1]) < 1e-12
        @test sort(diag(K)) ≈ sort([R1, R2]) rtol = 1e-10
        # the lift's own growth: pop_I from a tiny seed grows like e^{rt}
        sys = edge_based(sir_model(; τ = 1.0, γ = 1.0), dc(MSV_DEGREES, 1.0, 1.0))
        r = early_growth_rate(sys)
        # (seed 1e-12 and the window [10, 14]: the transient has decayed and pop_I ≤ 1e-4 is still linear)
        sol = solve_epidemic(sys; initial = SeedFraction(:I => 1e-12), tspan = (0.0, 14.0), saveat = [10.0, 14.0], TOL...)
        I = curve(sys, sol, :pop_I)
        @test I[2] < 1e-4
        @test log(I[2] / I[1]) / 4 ≈ r rtol = 1e-4
        # the final size comes from the ODE (there is no fixed-point equation)
        @test final_size(sys; initial = SeedFraction(:I => 0.01)) ≈
              curve(sys, solve_epidemic(sys; initial = SeedFraction(:I => 0.01), tspan = (0.0, 200.0), TOL...),
                    :cumulative)[end] atol = 1e-8
    end

    @testset "symbolic η₁, η₂ and degree parameters" begin
        η1, η2, μ = as_parameter(:η₁), as_parameter(:η₂), as_parameter(:μ)
        sym = edge_based(sir_model(), dc(PoissonDegree(μ), η1, η2))
        num = edge_based(sir_model(; τ = 1 / 6, γ = 1 / 4), dc(PoissonDegree(5.0), 1.0, 0.5))
        grid = 0.0:1.0:100.0
        s1 = solve_epidemic(sym; p = Dict(:τ => 1 / 6, :γ => 1 / 4, :η₁ => 1.0, :η₂ => 0.5, :μ => 5.0),
                            initial = SeedFraction(:I => 0.01), tspan = (0.0, 100.0), saveat = grid, TOL...)
        s2 = solve_epidemic(num; initial = SeedFraction(:I => 0.01), tspan = (0.0, 100.0), saveat = grid, TOL...)
        for X in (:S, :pop_I, :cumulative, :φ_S, :α_S, :π_S)
            @test maximum(abs.(curve(sym, s1, X) .- curve(num, s2, X))) < 1e-10
        end
        @test basic_reproduction_number(sym; p = Dict(:τ => 1 / 6, :γ => 1 / 4, :η₁ => 1.0, :η₂ => 0.5, :μ => 5.0)) ≈
              basic_reproduction_number(num) rtol = 1e-10
        # mean degree 0: no stub, no contact; nothing is NaN (verified issues E11, E32)
        s0 = edge_based(sir_model(; τ = 1.0, γ = 0.25), dc(RegularDegree(0), 1.0, 1.0))
        so = solve_epidemic(s0; initial = SeedFraction(:I => 0.01), tspan = (0.0, 50.0), TOL...)
        @test all(isfinite, reduce(vcat, so.u))
        @test curve(s0, so, :S)[end] ≈ 0.99 atol = 1e-14
    end

    @testset "gluing: the reaction rows add, the stub process acts once (H1 with the process as a component)" begin
        net = dc(PoissonDegree(5.0), 1.0, 0.5)
        tr = open_model(ContactModel(:tr; contacts = [Contact(:S, :I, :E, :τ)]); legs = [[:S], [:E, :I]])
        pr = open_model(ContactModel(:pr; transitions = [NodeTransition(:E, :I, :σ), NodeTransition(:I, :R, :γ)]);
                        legs = [[:E, :I, :R]])
        glued = symbolic_ode(edge_based(glue(tr, pr; on = [:E, :I]), net))
        @test vector_fields_equal(glued, symbolic_ode(edge_based(seir_model(), net)))
        ta, tb = lift_contributions(tr, net), lift_contributions(pr, net)
        @test count(r -> r.type === :process, ta) == 1               # the part with θ carries the process
        @test count(r -> r.type === :process, tb) == 0               # a part without θ has none
        reactions(t) = LiftContributions(t.name, t.network, t.closure, t.coordinates, t.seed_factors,
                                         filter(r -> r.type !== :process, t.contributions), t.coordinate_info)
        s = sum_contributions(reactions(ta), reactions(tb))
        row = EBM._process_row(net, s.closure, s.coordinate_info)
        @test row isa ReactionContribution && row.type === :process && row.reaction === :dormant_contacts
        whole = LiftContributions(s.name, s.network, s.closure, s.coordinates, s.seed_factors,
                                  vcat(s.contributions, row), s.coordinate_info)
        @test vector_fields_equal(symbolic_ode(whole), glued)
        # sum_contributions itself keeps exactly one process row, rebuilt through `_process_row` for the coordinates of
        # the sum (so the stub process also acts on φ_R, α_R, π_R of the second part)
        @test vector_fields_equal(symbolic_ode(sum_contributions(ta, tb)), glued)
        @test count(r -> r.type === :process, sum_contributions(ta, tb)) == 1
        # the process row of another network is not this one
        @test EBM._process_row(dfd(PoissonDegree(5.0), 1.0), :dormant, s.coordinate_info) === nothing
        @test EBM._process_row(net, :dynamic, s.coordinate_info) === nothing
        # an injective relabel is the lift of the relabelled model
        f = Dict(:I => :J, :R => :Z)
        @test vector_fields_equal(symbolic_ode(relabel(lift_contributions(seir_model(), net), f)),
                                  symbolic_ode(edge_based(relabel(seir_model(), f), net)))
    end

    @testset "errors: inadmissible models, forms, transmissibility, names" begin
        net = dc(PoissonDegree(5.0), 1.0, 0.5)
        @test_throws AdmissibilityError edge_based(sis_model(), net)
        @test_throws AdmissibilityError edge_based(sirs_model(), net)
        err = try edge_based(sir_model(), net; form = :compact) catch e e end
        @test err isa ArgumentError && occursin("only the expanded form", sprint(showerror, err))
        sys = edge_based(sir_model(; τ = 1.0, γ = 1.0), net)
        err = try transmissibility(sys) catch e e end
        @test err isa ArgumentError && occursin("no single per-edge transmissibility", sprint(showerror, err))
        # two susceptible classes need a typed network
        @test_throws AdmissibilityError edge_based(stratify(sir_model(), [:a, :b]), net)
        # a parameter named like a generated coordinate or observable is refused (E26)
        for bad in (:θ_A, :α_I, :χ, :excess_hazard)
            cm = ContactModel(:bad; contacts = [Contact(:S, :I, :I, bad)], transitions = [NodeTransition(:I, :R, :γ)])
            @test_throws ArgumentError edge_based(cm, net)
        end
        # the descriptor refuses rates that cannot be a stub process (NetworkEpiCore)
        @test_throws ArgumentError DormantContacts(0, 0)
        @test_throws ArgumentError DormantContacts(-1, 1)
    end

    @testset "against NetworkOutbreaks' dormant-contact process: :sir_dormant_msv, _dvd and _fast" begin
        # Acceptance (design §K WP36b, §E.2; back ends declared :exact_limit): D∞ < 0.01 on the scenarios' own
        # ensembles (N = 10⁴, 200 runs, fresh stationary stub states per run, 1% seeded).
        for id in (:sir_dormant_msv, :sir_dormant_dvd, :sir_dormant_fast)
            sc = scenario(id)
            @test sc.backends[:edge_based] === :exact_limit
            tab, sys, sol = against_process(sc)
            @test tab.n == sc.sim.nsims                              # 100 seeds: every run is major
            rows = Dict(r.observable => r for r in tab)
            fmt(f) = join(("$X $(round(f(rows[X]); sigdigits = 3))" for X in (:S, :I, :R)), ", ")
            @info "WP36b EB vs NetworkOutbreaks (dormant contacts)" scenario = id N = sc.sim.N runs = tab.n D∞ = fmt(r -> r.D∞) SE∞ = fmt(r -> r.SE∞) z∞ = fmt(r -> r.z∞) ΔR∞ = rows[:I].ΔR∞ ΔR∞_ci = rows[:I].ΔR∞_ci R∞_EB = curve(sys, sol, :cumulative)[end]
            @test all(rows[X].D∞ < 0.01 for X in (:S, :I, :R, :cumulative))
            @test rows[:I].D∞ < 0.005                                # prevalence, the design's §E.2 criterion
            @test abs(rows[:I].ΔR∞) < 0.005
            @test rows[:I].ΔR∞_ci[1] < 0 < rows[:I].ΔR∞_ci[2]         # R∞ within its 95% interval
            @test all(rows[X].z∞ < 4 for X in (:S, :I, :R))
        end
    end

    @testset "against NetworkOutbreaks: SEIR, SIR + vaccination and removals with dormant contacts, N = 5000" begin
        # The general T_EB lift (latency, an exit out of S, the removal sink) on Poisson(5) maximum degrees with
        # η₁ = 1, η₂ = 0.5 (A = 2/3), 60 runs each, 5% seeded (ρN = 250: at ρN = 50 the slow epidemics carry a
        # finite-size bias of the mean of steep curves, as WP21 measured for neighbour exchange).
        N = 5000
        net = dc(PoissonDegree(5), 1.0, 0.5)
        cases = ((seir_model(), Dict(:τ => 1 / 6, :σ => 1 / 5, :γ => 1 / 4), SeedFraction(:E => 0.05), 120.0,
                  [:S, :E, :I, :R]),
                 (sirv_model(), Dict(:τ => 1 / 6, :γ => 1 / 4, :ν => 0.02), SeedFraction(:I => 0.05), 80.0,
                  [:S, :I, :R, :V]),
                 (ContactModel(:rem; contacts = [Contact(:S, :I, :I, :τ)], transitions = [NodeTransition(:I, nothing, :γ)]),
                  Dict(:τ => 1 / 6, :γ => 1 / 4), SeedFraction(:I => 0.05), 80.0, [:S, :I, :removed]))
        for (cm, p, initial, T, obs) in cases
            grid = collect(0.0:1.0:T)
            sys = edge_based(cm, net)
            sol = solve_epidemic(sys; p, initial, tspan = (0.0, T), saveat = grid, TOL...)
            eb = permutedims(reduce(hcat, [X === :S ? curve(sys, sol, :S) : curve(sys, sol, Symbol(:pop_, X)) for X in obs]))
            runs, n = no_runs(cm, net, p, initial, grid; N, nsims = 60, obs)
            @test length(runs) >= n - 2
            dd = discrepancy(eb, runs)
            @info "WP36b DC vs NetworkOutbreaks" model = cm.name N runs = n major = length(runs) D∞ = dd.D se_at_max = dd.se z∞ = dd.D / dd.se observable = obs[dd.at[1]] t = grid[dd.at[2]]
            @test dd.D < 0.01
            @test dd.D / dd.se < 4
        end
    end
end
