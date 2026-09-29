# WP20: the clustered edge-based lift, Volz, Miller, Galvani & Ancel Meyers (2011, PLoS Comput
# Biol 7:e1002042; papers/clustering1.md), with triangle pair states (src/lift/clustered.jl).
#
# Acceptance (DESIGN_NetworkEpiCore.md §G.2 WP20):
#   1. final size 0.7125 ± 10⁻³ for κ_s = 1, κ_t = 2, τ = 0.6, γ = 1, ρ = 10⁻³ (the w1 reference);
#   2. the invariant θ₃ = Σ φ3_XY holds to 1e-10;
#   3. D∞ < 0.005 against NetworkOutbreaks on :sir_clust_s2t2 (a local ensemble with the scenario's
#      N, runs, seeds and streams, since the committed summary does not exist yet);
#   4. other models error; SEIR (the stretch goal) is supported and validated the same way.
# Bug fixes with regression tests: E02 (the legacy clustered EBCM treated triangle partners as
# independent edges), E04 (the clustered R₀), E11 (phantom states of empty edge classes), E27
# (polynomial laws, pre-cancelled entry terms).
#
# References that are independent of the package: Volz et al.'s own (unordered) equations and
# their tree-of-triangles final-size relation (eq. 27), written here in plain Julia from the
# paper; the E02/E04 verifiers' exact simulations (VERIFIED_ISSUES.md); and exact stochastic
# simulation with NetworkOutbreaks on freshly drawn Newman–Miller graphs (design §E.2, §J.7).

using EdgeBasedModels
using NetworkEpiCore
using LinearAlgebra
using Markdown
using Statistics
using Symbolics
using Test
using ModelingToolkit: @parameters
using OrdinaryDiffEq: ODEProblem, Vern9, solve
import NetworkOutbreaks as NO

const EBM = EdgeBasedModels
const TOL = (solver = Vern9(), reltol = 1e-12, abstol = 1e-13)

# ---------------------------------------------------------------------------------------------
# Independent references
# ---------------------------------------------------------------------------------------------

# ∂ˣⁱ∂ʸʲ g for Poisson singles and triangles, and for a joint matrix P[s+1, t+1] (own code).
poisson_g(ks, kt) = (x, y, i, j) -> ks^i * kt^j * exp(ks * (x - 1) + kt * (y - 1))
function joint_g(P)
    ff(n, k) = prod(Float64(n - m) for m in 0:(k - 1); init = 1.0)
    return (x, y, i, j) -> sum(P[a, b] * ff(a - 1, i) * ff(b - 1, j) * x^(a - 1 - i) * y^(b - 1 - j)
                               for a in axes(P, 1), b in axes(P, 2) if P[a, b] != 0 && a - 1 >= i && b - 1 >= j;
                               init = 0.0)
end

# Volz et al. (2011), SIR, in the paper's unordered pair states, with the outside infection rate
# A = −d ln g_y/dt of a triangle partner (and h_L of a line partner):
#   u = [θ₂, θ₃, φ_I, φ_R, φ_SI, φ_SR, φ_II, φ_IR, φ_RR, I, R]
function volz_sir!(du, u, p, t)
    g, β, γ, q = p
    θ2, θ3, φI, φR, φSI, φSR, φII, φIR, φRR, I, R = u
    gx1, gy1 = g(1.0, 1.0, 1, 0), g(1.0, 1.0, 0, 1)
    dθ2 = -β * φI
    dθ3 = -β * (φSI + 2φII + φIR)
    du[1], du[2] = dθ2, dθ3
    if gx1 > 0
        hL = -(g(θ2, θ3, 2, 0) * dθ2 + g(θ2, θ3, 1, 1) * dθ3) / g(θ2, θ3, 1, 0)
        du[3] = hL * q * g(θ2, θ3, 1, 0) / gx1 - (β + γ) * φI
    else
        du[3] = 0.0
    end
    du[4] = γ * φI
    φSS = (q * g(θ2, θ3, 0, 1) / gy1)^2
    A = -(g(θ2, θ3, 1, 1) * dθ2 + g(θ2, θ3, 0, 2) * dθ3) / g(θ2, θ3, 0, 1)
    du[5] = 2A * φSS - (A + 2β + γ) * φSI
    du[6] = γ * φSI - A * φSR
    du[7] = (A + β) * φSI - 2(β + γ) * φII
    du[8] = A * φSR + 2γ * φII - (β + γ) * φIR
    du[9] = γ * φIR
    du[10] = -q * (g(θ2, θ3, 1, 0) * dθ2 + g(θ2, θ3, 0, 1) * dθ3) - γ * I
    du[11] = γ * I
end

function volz_sir(g, β, γ; ρ = 1e-3, T = 200.0, saveat = 0.5)
    q = 1 - ρ
    u0 = [1.0, 1.0, ρ, 0.0, 2ρ * q, 0.0, ρ^2, 0.0, 0.0, ρ, 0.0]
    return solve(ODEProblem(volz_sir!, u0, (0.0, T), (g, β, γ, q)), Vern9(); reltol = 1e-12,
                 abstol = 1e-13, saveat)
end

# SEIR in the same unordered, S-explicit style (derived here from the pair-state rules of the
# paper: an S partner is infected from outside at A, by an I partner at β, and enters E):
#   u = [θ₂, θ₃, φ_E, φ_I, φ_R, φ_SE, φ_SI, φ_SR, φ_EE, φ_EI, φ_ER, φ_II, φ_IR, φ_RR, E, I, R]
function volz_seir!(du, u, p, t)
    g, β, σ, γ, q = p
    θ2, θ3, φE, φI, φR, SE, SI, SR, EE, EI, ER, II, IR, RR, E, I, R = u
    gx1, gy1 = g(1.0, 1.0, 1, 0), g(1.0, 1.0, 0, 1)
    dθ2 = -β * φI
    dθ3 = -β * (SI + EI + 2II + IR)
    du[1], du[2] = dθ2, dθ3
    hL = -(g(θ2, θ3, 2, 0) * dθ2 + g(θ2, θ3, 1, 1) * dθ3) / g(θ2, θ3, 1, 0)
    du[3] = hL * q * g(θ2, θ3, 1, 0) / gx1 - σ * φE
    du[4] = σ * φE - (β + γ) * φI
    du[5] = γ * φI
    SS = (q * g(θ2, θ3, 0, 1) / gy1)^2
    A = -(g(θ2, θ3, 1, 1) * dθ2 + g(θ2, θ3, 0, 2) * dθ3) / g(θ2, θ3, 0, 1)
    du[6] = 2A * SS - (A + σ) * SE
    du[7] = σ * SE - (A + 2β + γ) * SI
    du[8] = γ * SI - A * SR
    du[9] = A * SE - 2σ * EE
    du[10] = (A + β) * SI + 2σ * EE - (σ + β + γ) * EI
    du[11] = A * SR + γ * EI - σ * ER
    du[12] = σ * EI - 2(β + γ) * II
    du[13] = σ * ER + 2γ * II - (β + γ) * IR
    du[14] = γ * IR
    du[15] = -q * (g(θ2, θ3, 1, 0) * dθ2 + g(θ2, θ3, 0, 1) * dθ3) - σ * E
    du[16] = σ * E - γ * I
    du[17] = γ * I
end

function volz_seir(g, β, σ, γ; ρ = 1e-3, T = 200.0, saveat = 0.5)
    q = 1 - ρ
    u0 = zeros(17)
    u0[1] = u0[2] = 1.0
    u0[3] = ρ
    u0[6] = 2ρ * q
    u0[9] = ρ^2
    u0[15] = ρ
    return solve(ODEProblem(volz_seir!, u0, (0.0, T), (g, β, σ, γ, q)), Vern9(); reltol = 1e-12,
                 abstol = 1e-13, saveat)
end

# The tree-of-triangles final size of Markov SIR on Poisson lines and triangles (Volz et al. 2011,
# eq. 27): the partner of a line escapes with 1 − T, a pair of triangle partners as enumerated.
function volz_final_size(ks, kt, β, γ; ρ = 1e-3)
    q = 1 - ρ
    q1 = γ / (β + γ)                 # P(an infective does not transmit to a given contact)
    q2 = γ / (γ + 2β)                # … to either of two given contacts
    θ2 = θ3 = 0.0
    for _ in 1:20_000
        s = q * exp(ks * (θ2 - 1) + kt * (θ3 - 1))
        θ2, θ3 = s + (1 - s) * q1, s^2 + 2s * (1 - s) * (q2 + (q1 - q2) * q1) + (1 - s)^2 * q1^2
    end
    return 1 - q * exp(ks * (θ2 - 1) + kt * (θ3 - 1))
end

# The subexpressions a/b (or a^−n) of `ex` whose denominator depends on one of `states`.
function state_divisions(ex, states)
    sv = Set(Symbolics.unwrap.(states))
    dep(x) = any(v -> Symbolics.unwrap(v) in sv, Symbolics.get_variables(x))
    bad = Any[]
    function walk(x)
        Symbolics.iscall(x) || return nothing
        op, args = Symbolics.operation(x), Symbolics.arguments(x)
        op === (/) && dep(args[2]) && push!(bad, x)
        op === (^) && args[2] isa Number && args[2] < 0 && dep(args[1]) && push!(bad, x)
        foreach(walk, args)
        return nothing
    end
    walk(Symbolics.unwrap(ex))
    return bad
end

lift(cm, net) = edge_based(cm, net)
solveρ(sys, ρ, X; T = 200.0, saveat = 0.5) =
    solve_epidemic(sys; initial = SeedFraction(X => ρ), tspan = (0.0, T), saveat, TOL...)
C(sys, sol, X) = compartment(sys, sol, X)

pois(ks, kt) = ClusteredNetwork(PoissonDegree(ks), PoissonDegree(kt))
binomv(n, p) = [binomial(n, k) * p^k * (1 - p)^(n - k) for k in 0:n]

# The pair states of a solved clustered system, and the invariant defects.
function invariants(sys, sol)
    names = sort!(collect(keys(sys.variables)))
    pair_vars = [n for n in names if startswith(string(n), "φ3_")]
    pair_obs = [n for n in keys(sys.observables) if startswith(string(n), "φ3_")]
    θ3 = C(sys, sol, :θ₃)
    Σφ3 = reduce(+, (C(sys, sol, n) for n in vcat(pair_vars, pair_obs)))
    φ2 = [n for n in names if startswith(string(n), "φ2_")]
    θ2 = haskey(sys.variables, :θ₂) ? C(sys, sol, :θ₂) .- C(sys, sol, :φ2_S) .-
                                       reduce(+, (C(sys, sol, n) for n in φ2)) : [0.0]
    pops = [n for n in names if startswith(string(n), "pop_")]
    node = C(sys, sol, :S) .+ reduce(+, (C(sys, sol, n) for n in pops)) .- 1
    return (θ3 = maximum(abs.(θ3 .- Σφ3)), θ2 = maximum(abs.(θ2)), node = maximum(abs.(node)))
end

@testset "clustered lift (Volz et al. 2011)" begin
    @testset "acceptance 1: the w1 reference, final size 0.7125 (E02)" begin
        sys = lift(sir_model(; τ = 0.6, γ = 1.0), pois(1.0, 2.0))
        sol = solveρ(sys, 1e-3, :I; T = 60.0)
        R∞ = C(sys, sol, :cumulative)[end]
        @test abs(R∞ - 0.7125) <= 1e-3
        @test R∞ ≈ 1 - C(sys, sol, :S)[end] atol = 1e-12
        # Volz's tree-of-triangles final-size relation (eq. 27), independent of any ODE
        @test R∞ ≈ volz_final_size(1.0, 2.0, 0.6, 1.0) atol = 1e-6
        # exact SSA on N = 2×10⁵ Newman–Miller graphs (E02: 150 runs 0.71213 ± 0.00017;
        # NetworkOutbreaks 0.71295 ± 0.00032): within 4 SE of the first
        @test abs(R∞ - 0.71213) <= 4 * 0.00017
        # the legacy independent-edge EBCM gave 0.72930 (S = g(θ₂, θ₃²)); regression
        @test abs(R∞ - 0.72930) > 0.015
    end

    @testset "exact against Volz et al.'s own equations" begin
        cases = [("Poisson (1, 2)", pois(1.0, 2.0), poisson_g(1.0, 2.0), 0.6, 1.0, 0.71250),
                 ("Poisson (0, 1.5), triangles only", pois(0.0, 1.5), poisson_g(0.0, 1.5), 1.0, 1.0, 0.52798),
                 ("Poisson (3, 1)", pois(3.0, 1.0), poisson_g(3.0, 1.0), 1 / 6, 0.25, 0.77028),
                 ("joint [0.1 0.2; 0.3 0.4]", ClusteredNetwork([0.1 0.2; 0.3 0.4]),
                  joint_g([0.1 0.2; 0.3 0.4]), 0.5, 0.1, 0.00757),
                 ("regular (2, 2)", ClusteredNetwork(RegularDegree(2), RegularDegree(2)),
                  joint_g([0 0 0; 0 0 0; 0 0 1.0]), 1 / 6, 0.25, nothing)]
        for (label, net, g, β, γ, ref) in cases
            @testset "$label" begin
                sys = lift(sir_model(; τ = β, γ = γ), net)
                T = 600.0
                sol = solveρ(sys, 1e-3, :I; T)
                v = volz_sir(g, β, γ; T)
                S_ref = [(1 - 1e-3) * g(u[1], u[2], 0, 0) for u in v.u]
                @test maximum(abs.(C(sys, sol, :S) .- S_ref)) < 1e-8
                @test maximum(abs.(C(sys, sol, :pop_I) .- getindex.(v.u, 10))) < 1e-8
                @test maximum(abs.(C(sys, sol, :θ₃) .- getindex.(v.u, 2))) < 1e-8
                # the pair states are Volz's (unordered): φ_SI, φ_SR, φ_II, φ_IR, φ_RR
                for (k, name) in ((5, :φ3_S_I), (6, :φ3_S_R), (7, :φ3_I_I), (8, :φ3_I_R), (9, :φ3_R_R))
                    @test maximum(abs.(C(sys, sol, name) .- getindex.(v.u, k))) < 1e-8
                end
                ref === nothing || @test C(sys, sol, :cumulative)[end] ≈ ref atol = 1e-5
            end
        end
        # E02 (non-Poisson): the test-suite joint law is subcritical on a tree of triangles
        # (SSA 0.00753 ± 0.00011, N = 2×10⁵); the legacy EBCM predicted a 63% epidemic
        sysj = lift(sir_model(; τ = 0.5, γ = 0.1), ClusteredNetwork([0.1 0.2; 0.3 0.4]))
        @test C(sysj, solveρ(sysj, 1e-3, :I; T = 600.0), :cumulative)[end] < 0.02
    end

    @testset "acceptance 2: θ₃ = Σφ3_XY, θ₂ = φ2_S + Σφ2_X, S + Σpop = 1 (to 1e-10)" begin
        for (cm, net, X) in ((sir_model(; τ = 0.6, γ = 1.0), pois(1.0, 2.0), :I),
                             (sir_model(; τ = 0.3, γ = 0.25), ClusteredNetwork(RegularDegree(2), RegularDegree(2)), :I),
                             (sir_model(; τ = 0.5, γ = 0.1), ClusteredNetwork([0.1 0.2; 0.3 0.4]), :I),
                             (seir_model(; τ = 1.2, σ = 0.5, γ = 1.0), pois(1.0, 2.0), :E),
                             (ContactModel(:sir_removal; contacts = [Contact(:S, :I, :I, 0.6)],
                                           transitions = [NodeTransition(:I, nothing, 1.0)]), pois(1.0, 2.0), :I))
            sys = lift(cm, net)
            sol = solveρ(sys, 0.01, X; T = 150.0)
            d = invariants(sys, sol)
            @test d.θ3 < 1e-10
            @test d.θ2 < 1e-10
            @test d.node < 1e-10
            @test all(x -> -1e-12 <= x <= 1 + 1e-12, C(sys, sol, :θ₃))
        end
        # a removal I → ∅ is lowered to the sink :removed (design §J.2) and equals SIR
        a = lift(sir_model(; τ = 0.6, γ = 1.0), pois(1.0, 2.0))
        b = lift(ContactModel(:sir_removal; contacts = [Contact(:S, :I, :I, 0.6)],
                              transitions = [NodeTransition(:I, nothing, 1.0)]), pois(1.0, 2.0))
        @test haskey(b.variables, :φ3_I_removed)
        @test C(a, solveρ(a, 0.01, :I; T = 30.0), :S) ≈ C(b, solveρ(b, 0.01, :I; T = 30.0), :S) rtol = 1e-10
    end

    @testset "empty blocks have no coordinates; the κ → 0 limit (E11)" begin
        # no triangles: the configuration-model lift of g(x, 1)
        s0 = lift(sir_model(; τ = 0.6, γ = 1.0), pois(5.0, 0.0))
        @test !haskey(s0.variables, :θ₃) && !any(n -> startswith(string(n), "φ3_") || startswith(string(n), "χ_"),
                                                  keys(s0.variables))
        c0 = lift(sir_model(; τ = 0.6, γ = 1.0), ConfigurationNetwork(PoissonDegree(5.0)))
        @test C(s0, solveρ(s0, 1e-3, :I; T = 30.0), :S) ≈ C(c0, solveρ(c0, 1e-3, :I; T = 30.0), :S) rtol = 1e-10
        # no single edges: no θ₂ (the legacy builder's phantom θ₂ drifted to −18.75 by t = 40)
        s1 = lift(sir_model(; τ = 1.0, γ = 1.0), pois(0.0, 1.5))
        @test !haskey(s1.variables, :θ₂) && !any(n -> startswith(string(n), "φ2_"), keys(s1.variables))
        @test haskey(s1.variables, :θ₃)
        # symbolic means that are 0 at solve time select the limit (no NaN, no phantom drift) and
        # agree with the numeric lifts, and with a tiny mean
        @parameters κs κt
        sk = lift(sir_model(; τ = 0.6, γ = 1.0), ClusteredNetwork(PoissonDegree(κs), PoissonDegree(κt)))
        for (a, b) in ((1.0, 2.0), (5.0, 0.0), (0.0, 1.5))
            sol = solve_epidemic(sk; p = Dict(:κs => a, :κt => b), initial = SeedFraction(:I => 1e-3),
                                 tspan = (0.0, 40.0), saveat = 0.5, TOL...)
            @test string(sol.retcode) == "Success"
            ref = lift(sir_model(; τ = 0.6, γ = 1.0), pois(a, b))
            @test C(sk, sol, :S) ≈ C(ref, solveρ(ref, 1e-3, :I; T = 40.0), :S) rtol = 1e-9
            @test all(x -> 0 <= x <= 1, C(sk, sol, :θ₂)) && all(x -> 0 <= x <= 1, C(sk, sol, :θ₃))
            tiny = lift(sir_model(; τ = 0.6, γ = 1.0), pois(max(a, 1e-9), max(b, 1e-9)))
            @test C(sk, sol, :S) ≈ C(tiny, solveρ(tiny, 1e-3, :I; T = 40.0), :S) atol = 1e-7
        end
    end

    @testset "polynomial laws: constant divisors only (E27)" begin
        # E27: Bin(8, ½) × Bin(4, 0.4) broke the legacy builder (Symbolics.simplify of a ratio of
        # Float64 polynomials); here the matrix law equals the closed-form independent binomials
        # and Volz's equations
        P = binomv(8, 0.5) * binomv(4, 0.4)'
        P ./= sum(P)
        sm = lift(sir_model(; τ = 0.3, γ = 0.1), ClusteredNetwork(P))
        sb = lift(sir_model(; τ = 0.3, γ = 0.1), ClusteredNetwork(BinomialDegree(8, 0.5), BinomialDegree(4, 0.4)))
        solm = solveρ(sm, 1e-3, :I; T = 80.0)
        @test string(solm.retcode) == "Success"
        @test C(sm, solm, :S) ≈ C(sb, solveρ(sb, 1e-3, :I; T = 80.0), :S) rtol = 1e-9
        v = volz_sir(joint_g(P), 0.3, 0.1; T = 80.0)
        @test maximum(abs.(C(sm, solm, :pop_I) .- getindex.(v.u, 10))) < 1e-8
        d = invariants(sm, solm)
        @test d.θ3 < 1e-10 && d.θ2 < 1e-10 && d.node < 1e-10
        # a large law (31 × 16 coefficients; the legacy builder ran 438 s and then threw) builds
        big = binomv(30, 0.1) * binomv(15, 0.1)'
        t = @elapsed sbig = lift(sir_model(; τ = 0.3, γ = 0.1), ClusteredNetwork(big))
        @test t < 120
        solbig = solveρ(sbig, 1e-3, :I; T = 40.0)
        ref = lift(sir_model(; τ = 0.3, γ = 0.1), ClusteredNetwork(BinomialDegree(30, 0.1), BinomialDegree(15, 0.1)))
        @test C(sbig, solbig, :S) ≈ C(ref, solveρ(ref, 1e-3, :I; T = 40.0), :S) rtol = 1e-9
        # the field divides only by the constant means g_x(1,1), g_y(1,1): no quotient (or negative
        # power) of an expression in the states anywhere in the right-hand sides
        for s in (sm, lift(sir_model(; τ = 0.6, γ = 1.0), pois(1.0, 2.0)),
                  lift(seir_model(; τ = 0.6, σ = 1.0, γ = 1.0), ClusteredNetwork(P)))
            ode = symbolic_ode(s)
            @test all(f -> isempty(state_divisions(f, ode.states)), ode.rhs)
            @test !isempty(state_divisions(ode.rhs[1] / (1 + ode.states[2]), ode.states))   # the check has power
        end
    end

    @testset "SEIR (stretch): Volz-style equations and the E02 verifiers" begin
        sys = lift(seir_model(; τ = 1.2, σ = 0.5, γ = 1.0), pois(1.0, 2.0))
        sol = solveρ(sys, 1e-3, :E; T = 200.0)
        v = volz_seir(poisson_g(1.0, 2.0), 1.2, 0.5, 1.0; T = 200.0)
        @test maximum(abs.(C(sys, sol, :pop_E) .- getindex.(v.u, 15))) < 1e-8
        @test maximum(abs.(C(sys, sol, :pop_I) .- getindex.(v.u, 16))) < 1e-8
        for (k, name) in ((6, :φ3_S_E), (7, :φ3_S_I), (9, :φ3_E_E), (10, :φ3_E_I), (12, :φ3_I_I), (13, :φ3_I_R))
            @test maximum(abs.(C(sys, sol, name) .- getindex.(v.u, k))) < 1e-8
        end
        R∞ = C(sys, sol, :cumulative)[end]
        # E02: the verifier's independent pair-state implementation gave 0.85686; exact SSAs on
        # N = 2×10⁵ Newman–Miller graphs 0.85714 ± 0.00020 and 0.85644 ± 0.00017 (30 runs each)
        @test R∞ ≈ 0.85686 atol = 2e-5
        @test abs(R∞ - 0.85714) <= 3 * 0.00020 && abs(R∞ - 0.85644) <= 3 * 0.00017
        @test abs(R∞ - 0.86321) > 0.005                       # the legacy EBCM
        # the factory is the same lift
        f = build_clustered_seir(pois(1.0, 2.0), 0.5, 1.2, 1.0)
        @test C(f, solveρ(f, 1e-3, :E; T = 200.0), :S) ≈ C(sys, sol, :S) rtol = 1e-12
    end

    @testset "acceptance 3: against NetworkOutbreaks on Newman–Miller graphs" begin
        # Protocol (design §E.2, §J.7): NO.simulate(sc) draws graph r from stable_rng(b + r) and
        # runs the SSA of run r from stable_rng(b + 2³² + r) (NextReaction), with exactly ρN seeds;
        # runs are conditioned on a major outbreak (infections, seeds excluded, ≥ 0.05 N by t_end).
        # D∞ = max_t |x_EB(t) − x̄(t)| on the scenario grid; SE at the argmax.
        function ensemble_check(id; obs, ebname)
            sc = scenario(id)
            N, nsims = sc.sim.N, sc.sim.nsims
            ens = NO.simulate(sc)
            ρ = sum(last.(seed_fractions(sc.initial)))
            infected = [X for X in obs if X !== :S]
            major = [r for r in ens.trajectories if sum(NO.compartment(r, X)[end] for X in infected) - ρ >= 0.05]
            sys = edge_based(sc)
            sol = solve_epidemic(sys, sc; TOL...)
            rows = Dict{Symbol,Any}()
            for X in obs
                M = reduce(hcat, [NO.compartment(r, X) for r in major])
                μ = vec(mean(M; dims = 2))
                se = vec(std(M; dims = 2)) ./ sqrt(size(M, 2))
                d = abs.(C(sys, sol, ebname[X]) .- μ)
                k = argmax(d)
                rows[X] = (D∞ = d[k], t = sc.tgrid[k], se = se[k], μ = μ)
            end
            fs = [sum(NO.compartment(r, X)[end] for X in infected) for r in major]
            ΔR∞ = C(sys, sol, :cumulative)[end] - mean(fs)
            @info "WP20 clustered lift vs NetworkOutbreaks :$id" N runs = nsims major = length(major) D∞ = join(("$X $(round(rows[X].D∞; sigdigits = 3)) (SE $(round(rows[X].se; sigdigits = 2)), t = $(rows[X].t))" for X in obs), "; ") ΔR∞ se_R∞ = std(fs) / sqrt(length(fs))
            return sc, rows, ΔR∞, length(major), nsims
        end
        sirmap = Dict(:S => :S, :I => :pop_I, :R => :pop_R)
        sc, rows, ΔR∞, nmajor, nsims = ensemble_check(:sir_clust_s2t2; obs = (:S, :I, :R), ebname = sirmap)
        @test nmajor >= 0.95 * nsims
        for X in (:S, :I, :R)
            @test rows[X].D∞ < 0.005
        end
        @test abs(ΔR∞) < 0.005
        # the test has power: the unclustered lift on the same degree sequence (6-regular) is far
        # from the simulations. It is exactly what the 0.1 clustered builder computed (verified issue
        # E02: every triangle rewired into two independent edges); that builder is removed (WP29).
        noclust = edge_based(sc.model, ConfigurationNetwork(RegularDegree(6)))
        for other in (noclust,)
            so = solve_epidemic(other; p = sc.params, initial = sc.initial, tspan = sc.tspan, saveat = sc.tgrid, TOL...)
            d = maximum(abs.(C(other, so, :I) .- rows[:I].μ))
            @test d > 5 * max(rows[:I].D∞, 0.002)
        end
        _, rows2, ΔR2, nm2, ns2 = ensemble_check(:sir_clust_pois12; obs = (:S, :I, :R), ebname = sirmap)
        @test nm2 >= 0.95 * ns2
        @test all(rows2[X].D∞ < 0.005 for X in (:S, :I, :R)) && abs(ΔR2) < 0.005
        # SEIR (stretch) on the graphs of :seir_clust_s2t2
        _, rows3, ΔR3, nm3, ns3 = ensemble_check(:seir_clust_s2t2; obs = (:S, :E, :I, :R),
                                                 ebname = Dict(:S => :S, :E => :pop_E, :I => :pop_I, :R => :pop_R))
        @test nm3 >= 0.95 * ns3
        @test all(rows3[X].D∞ < 0.005 for X in (:S, :E, :I, :R)) && abs(ΔR3) < 0.005
    end

    @testset "acceptance 4: other models go to the general clustered lift; SIS/SIRS error" begin
        net = pois(1.0, 2.0)
        # WP20 refused every model that is not SIR- or SEIR-shaped; WP36d (src/lift/clustered_general.jl)
        # opened the gate for every T_EB model with one susceptible class, with the same field. Its
        # numerical checks (an independent transcription of the pair-state rules, SIR equality with
        # this lift, and NetworkOutbreaks on :seir_clust_s2t2 / :seair_clust_s2t2) are in
        # test/suites/clustered_general.jl; here only that the gate is open and the field is clustered.
        for cm in (seair_model(), sirv_model(), twostrain_model(), erlang_stages(sir_model(), :I, 2),
                   ContactModel(:si2; contacts = [Contact(:S, :I, :I, :τ)],
                                transitions = [NodeTransition(:I, :J, :γ), NodeTransition(:J, :R, :γ)]))
            sys = edge_based(cm, net)
            @test sys isa EdgeModelSystem && sys.metadata[:closure] === :clustered
            @test lift_contributions(cm, net) isa LiftContributions
        end
        @test_throws AdmissibilityError edge_based(sis_model(), net)
        @test_throws AdmissibilityError edge_based(sirs_model(), net)
        @test_throws ArgumentError edge_based(sir_model(), net; form = :compact)
        # the clustered lift is lax under gluing (F2): tables of parts are not summed or relabelled
        tab = lift_contributions(sir_model(), net)
        @test tab.closure === :clustered
        @test_throws ArgumentError relabel(tab, Dict(:I => :J))
        pr = ContactModel(:pr; transitions = [NodeTransition(:I, :R, :γ)])
        @test_throws ArgumentError lift_contributions(pr, net)
    end

    @testset "R₀ on a tree of triangles (E04)" begin
        R0(cm, net; kw...) = EBM._clustered_reproduction_number(cm, net; kw...)
        R0p(ks, kt, T; kw...) = R0(sir_model(; τ = T / (1 - T), γ = 1.0), pois(ks, kt); kw...)
        # thresholds of Markov SIR on Poisson lines and triangles (Volz et al. 2011 final-size
        # bisection = the NGM = N = 10⁶ simulation; E04); the legacy R₀ gave 0.721, 2.029, 0.754, 1.041
        for (ks, kt, Tc) in [(3.0, 1.0, 0.190158), (0.5, 1.5, 0.253004), (2.0, 1.0, 0.233103), (1.0, 2.0, 0.181708)]
            for kind in (:generation, :clump)
                @test R0p(ks, kt, Tc; kind) ≈ 1.0 atol = 1e-3
                @test R0p(ks, kt, 0.97Tc; kind) < 1 < R0p(ks, kt, 1.03Tc; kind)
            end
        end
        @test R0p(0.5, 1.5, 0.5) ≈ (1.75 + sqrt(1.75^2 + 4 * (1 / 6) * 1.5)) / 2 atol = 1e-8   # 1.88278 (legacy 4.75)
        @test R0p(0.5, 1.5, 0.5; kind = :clump) ≈ 2.0 atol = 1e-8
        r = R0p(0.0, 2.0, 1 / 3)                                     # triangles only (legacy: Inf)
        @test isfinite(r)
        @test r ≈ (4 / 3 + sqrt((4 / 3)^2 + 4 * (1 / 6) * (4 / 3))) / 2 atol = 1e-8   # 1.48316
        @test R0p(0.0, 2.0, 0.219224) ≈ 1.0 atol = 1e-3
        P = zeros(5, 3)
        P[2, 3] = 0.5
        P[5, 1] = 0.5                                                # half (s=1, t=2), half (s=4, t=0)
        @test R0(sir_model(; τ = 0.30062 / (1 - 0.30062), γ = 1.0), ClusteredNetwork(P)) ≈ 1.0 atol = 1e-3   # legacy 1.034
        @test R0p(5.0, 0.0, 0.2) ≈ 0.2 * 5 atol = 1e-12             # no triangles: T κ
        @test R0p(3.0, 1.0, 2 / 3) < (2 / 3) * 27 / 5                # clustering lowers R₀ (same k = s + 2t)
        # SEIR: the entry state E always progresses, so R₀ is that of SIR
        @test R0(seir_model(; τ = 0.5, σ = 0.3, γ = 1.0), pois(1.0, 2.0)) ≈ R0(sir_model(; τ = 0.5, γ = 1.0), pois(1.0, 2.0)) rtol = 1e-12
        # p by name, and the system form
        sys = build_clustered_sir(pois(1.0, 2.0), :τ, :γ)
        @test EBM._clustered_reproduction_number(sys; p = Dict(:τ => 0.5, :γ => 1.0)) ≈ R0(sir_model(; τ = 0.5, γ = 1.0), pois(1.0, 2.0)) rtol = 1e-12
        # symbolic rates: closed forms equal the numeric values (E04 skeptic: no simplify around sqrt)
        @parameters τ γ
        for net in (pois(0.5, 1.5), pois(3.0, 1.0), pois(0.0, 2.0)), kind in (:generation, :clump)
            rs = R0(sir_model(; τ = τ, γ = γ), net; kind)
            for τv in (1 / 3, 1.0, 3.0)
                val = Symbolics.value(Symbolics.substitute(rs, Dict(τ => τv, γ => 1.0); fold = Val(true)))
                @test Float64(val) ≈ R0(sir_model(; τ = τv, γ = 1.0), net; kind) rtol = 1e-10
            end
        end
        # a non-rank-deficient law with symbolic rates: no silent switch to R_* (E04 skeptic)
        @test_throws ArgumentError R0(sir_model(; τ = τ, γ = γ), ClusteredNetwork(P))
        @test R0(sir_model(; τ = τ, γ = γ), ClusteredNetwork(P); kind = :clump) isa Symbolics.Num

        # the ODE and R₀ agree on the threshold: the growth rate of the lifted field at the
        # disease-free state changes sign where R₀ = 1 (the legacy ODE's own threshold did not
        # match its R₀, E04 item 6)
        function growth(ks, kt, T)
            s = lift(sir_model(; τ = T / (1 - T), γ = 1.0), pois(ks, kt))
            ode = symbolic_ode(s)
            names = [Symbol(Symbolics.getname(x)) for x in ode.states]
            infected = [i for (i, n) in enumerate(names) if n in (:φ2_I, :χ_I, :φ3_I_I, :φ3_I_R)]
            J = Symbolics.jacobian(ode.rhs[infected], ode.states[infected])
            dfe = Dict{Any,Any}(x => (n in (:θ₂, :θ₃) ? 1.0 : 0.0) for (x, n) in zip(ode.states, names))
            for p in ode.parameters
                Symbol(Symbolics.getname(p)) === :q_S && (dfe[p] = 1.0)
            end
            Jn = [Float64(Symbolics.value(Symbolics.substitute(x, dfe; fold = Val(true)))) for x in J]
            return maximum(real, eigvals(Jn))
        end
        for (ks, kt) in ((3.0, 1.0), (0.5, 1.5), (1.0, 2.0))
            lo, hi = 0.05, 0.6
            for _ in 1:40
                mid = (lo + hi) / 2
                growth(ks, kt, mid) > 0 ? (hi = mid) : (lo = mid)
            end
            @test R0p(ks, kt, (lo + hi) / 2) ≈ 1.0 atol = 1e-6
        end
    end

    @testset "API: parameters, factories, observables, metadata" begin
        net = pois(1.0, 2.0)
        sys = build_clustered_sir(net, :τ, :γ)
        @test sys.metadata[:kind] === :assembled && sys.metadata[:closure] === :clustered
        @test sys.metadata[:network] == net && sys.metadata[:entry] === :I
        sol = solve_epidemic(sys; p = Dict(:τ => 0.6, :γ => 1.0), initial = SeedFraction(:I => 1e-3),
                             tspan = (0.0, 60.0), saveat = 0.5, TOL...)
        ref = lift(sir_model(; τ = 0.6, γ = 1.0), net)
        @test C(sys, sol, :S) ≈ C(ref, solveρ(ref, 1e-3, :I; T = 60.0), :S) rtol = 1e-10
        @test C(sys, sol, :R) == C(sys, sol, :pop_R)
        # the legacy ClusteredPGF with provenance goes through the same lift
        leg = build_clustered_sir(clustered_poisson_pgf(1.0, 2.0), 0.6, 1.0)
        @test leg.metadata[:closure] === :clustered
        # model_curves: species, :infectious and :cumulative (= 1 − S for SIR)
        mc = model_curves(sys, sol)
        @test mc[:cumulative] ≈ 1 .- mc[:S] atol = 1e-10
        @test haskey(mc, :I) && haskey(mc, :R) && haskey(mc, :infectious)
        # symbolic_ode(sys) is the closed per-reaction table
        @test vector_fields_equal(symbolic_ode(sys), symbolic_ode(lift_contributions(sir_model(), net)))
        @test length(symbolic_ode(sys).states) == 11                 # θ₂ θ₃ φ2_I φ2_R pop_I pop_R χ_I χ_R φ3_II φ3_IR φ3_RR
        # a parameter named like a generated coordinate is refused (E26)
        @test_throws ArgumentError edge_based(sir_model(; τ = :χ_I, γ = 1.0), net)
        # the susceptible class need not be called S
        cm = ContactModel(:sirU; contacts = [Contact(:U, :I, :I, 0.6)], transitions = [NodeTransition(:I, :R, 1.0)])
        su = lift(cm, net)
        @test haskey(su.observables, :S) && haskey(su.observables, :χ_U) && haskey(su.observables, :φ3_U_I)
        @test C(su, solveρ(su, 1e-3, :I; T = 60.0), :S) ≈ C(ref, solveρ(ref, 1e-3, :I; T = 60.0), :S) rtol = 1e-10
        # the docstring example of edge_based on a ClusteredNetwork runs and prints what it claims
        codes = String[]
        walk(x) = x isa Markdown.Code ? push!(codes, x.code) :
                  hasproperty(x, :content) ? foreach(walk, x.content) : nothing
        walk(Base.Docs.doc(edge_based))
        code = only(filter(c -> occursin("ClusteredNetwork(PoissonDegree(1.0), PoissonDegree(2.0))", c), codes))
        m = Module(:ClusteredDocExample)
        Core.eval(m, :(using EdgeBasedModels))
        @test round(Base.include_string(m, code); digits = 4) == 0.7125
    end
end
