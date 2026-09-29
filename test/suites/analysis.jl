# Analysis of edge-based models (WP19, DESIGN_NetworkEpiCore.md §G.2): threshold quantities, final
# size, the probability of a major outbreak and Ball's central limit theorem, for the legacy
# StaticConfigurationModel and for lowered systems (EdgeModelSystem).
#
# Acceptance (§G.2 WP19): symbolic R₀ equals NetworkEpiCore's numeric NGM on the corpus; Erlang T_n;
# final_size with ρ equals the ODE to 1e-8; the infector-side epidemic_probability lies within the
# Wilson CI of NetworkOutbreaks' P(major) for :sir_pois5_1seed (the committed summary once WP30
# lands, before that a local 2000-run ensemble); multiplex R₀ = ρ(K); the EoN cross-validation.
# Regression tests for the verified issues E12, E14, E15, E16, E17, E18, E29 and E31(i)
# (VERIFIED_ISSUES.md; the corrected fixes are authoritative). The references are independent of
# the code under test: closed forms, the verifiers' scipy/mpmath values, quadratures written here,
# the lifted ODE, EoN 1.2 (test/golden/eon) and NetworkOutbreaks simulation.
#
# Stochastic protocol (§E.2, §J.7): NetworkOutbreaks.simulate with its stable_rng streams (graph r
# from stable_rng(b + r), run r from stable_rng(b + 2³² + r)), a fresh graph per run, runs
# conditioned on a major outbreak (ever infected minus seeds ≥ 0.05 N).

using EdgeBasedModels
using NetworkEpiCore
using ModelingToolkit
using Symbolics
using LinearAlgebra
using Statistics
using Test
using OrdinaryDiffEq: Vern9

import NetworkOutbreaks as NO
import TOML

const EBM = EdgeBasedModels
const SCM = StaticConfigurationModel
const TIGHT = (solver = Vern9(), reltol = 1e-12, abstol = 1e-14)
const EON = TOML.parsefile(joinpath(@__DIR__, "..", "golden", "eon", "eon_like_for_like.toml"))

# ---- legacy progressions, built field by field (no deprecated factories) ------------------------
sirp(β, γ) = DiseaseProgression([DiseaseStage(:I; transmission_rate = β), DiseaseStage(:R)],
                                [DiseaseTransition(:I, :R, γ)]; entry = :I)
seirp(σ, β, γ) = DiseaseProgression([DiseaseStage(:E), DiseaseStage(:I; transmission_rate = β), DiseaseStage(:R)],
                                    [DiseaseTransition(:E, :I, σ), DiseaseTransition(:I, :R, γ)]; entry = :E)
bypassp(p; β = 1.0) = DiseaseProgression(
    [DiseaseStage(:E), DiseaseStage(:I; transmission_rate = β), DiseaseStage(:R)],
    [DiseaseTransition(:E, :I, p), DiseaseTransition(:E, :R, 1 - p), DiseaseTransition(:I, :R, 1.0)]; entry = :E)
asymp(pA; βA = 1.0, βI = 1.0) = DiseaseProgression(
    [DiseaseStage(:E), DiseaseStage(:A; transmission_rate = βA), DiseaseStage(:I; transmission_rate = βI), DiseaseStage(:R)],
    [DiseaseTransition(:E, :A, pA), DiseaseTransition(:E, :I, 1 - pA), DiseaseTransition(:A, :R, 1.0),
     DiseaseTransition(:I, :R, 1.0)]; entry = :E)
sisp(β, γ) = DiseaseProgression([DiseaseStage(:I; transmission_rate = β)], [DiseaseTransition(:I, :S, γ)]; entry = :I)
sirsp(β, γ, ε) = DiseaseProgression([DiseaseStage(:I; transmission_rate = β), DiseaseStage(:R)],
                                    [DiseaseTransition(:I, :R, γ), DiseaseTransition(:R, :S, ε)]; entry = :I)

const POIS5 = poisson_pgf(5.0)
const BIM28 = polynomial_pgf([0, 0, 0.5, 0, 0, 0, 0, 0, 0.5])          # {2, 8}, E15
const REG4 = polynomial_pgf([0.0, 0.0, 0.0, 0.0, 1.0])

val(x) = Float64(Symbolics.value(x))

# A symbolic expression evaluated with parameter values by name (folding constant subexpressions).
symval(e, p) = Float64(Symbolics.value(Symbolics.substitute(
    Symbolics.Num(e), Dict(v => Float64(p[Symbol(Symbolics.getname(v))]) for v in Symbolics.get_variables(e));
    fold = Val(true))))
# The symbolic variables of an expression, by name, as Num.
symvars(e) = Dict(Symbol(Symbolics.getname(v)) => Symbolics.Num(v) for v in Symbolics.get_variables(e))
# Whether a symbolic expression simplifies to 0.
symzero(e) = (v = Symbolics.value(Symbolics.simplify(Symbolics.Num(e))); v isa Number && iszero(v))

# ---- independent references --------------------------------------------------------------------

# θ∞ = 1 − T + T(1 − ρ)ψ'(θ)/ψ'(1) by 200 BigFloat bisections (ψ'(θ)/ψ'(1) = `dψn(θ)`), and
# R∞ = 1 − (1 − ρ)ψ(θ∞) (Miller 2014 eqs (3)-(4)).
function ref_final_size(ψ, dψn, T, ρ)
    T, ρ = big(T), big(ρ)
    g(θ) = 1 - T + T * (1 - ρ) * dψn(θ) - θ
    lo, hi = big(0.0), ρ > 0 ? big(1.0) : big(1.0) - big(10.0)^-30
    for _ in 1:200
        mid = (lo + hi) / 2
        g(mid) > 0 ? (lo = mid) : (hi = mid)
    end
    return Float64(1 - (1 - ρ) * ψ(lo))
end
ref_final_size_pois(κ, T, ρ) = ref_final_size(θ -> exp(κ * (θ - 1)), θ -> exp(κ * (θ - 1)), T, ρ)

# Markov SIR on Poisson(κ): P(major) = 1 − ξ with ξ = E[exp(−κ(1 − ξ)(1 − W))], W = e^{−βI},
# I ~ Exp(γ), the expectation by composite Simpson over t ∈ [0, 60/γ] (independent of the package's
# moment method); ξ by bisection on the least root.
function ref_pmajor_pois_sir(κ, β, γ; n = 60_000)
    L = 60 / γ
    h = L / n
    t = range(0, L; length = n + 1)
    w = [(i == 1 || i == n + 1) ? 1.0 : (iseven(i) ? 4.0 : 2.0) for i in 1:(n + 1)] .* (h / 3)
    dens = γ .* exp.(-γ .* t)
    Wt = exp.(-β .* t)
    tail = exp(-γ * L)
    E(ξ) = sum(w .* dens .* exp.(-κ .* (1 - ξ) .* (1 .- Wt))) + tail * exp(-κ * (1 - ξ))
    g(ξ) = E(ξ) - ξ
    lo, hi = 0.0, 1.0 - 1e-6
    g(hi) >= 0 && return 0.0
    for _ in 1:80
        mid = (lo + hi) / 2
        g(mid) > 0 ? (lo = mid) : (hi = mid)
    end
    return 1 - (lo + hi) / 2
end

# The 95% Wilson interval of k successes in n trials.
function wilson(k, n; z = 1.959963984540054)
    p̂ = k / n
    c = (p̂ + z^2 / (2n)) / (1 + z^2 / n)
    h = z * sqrt(p̂ * (1 - p̂) / n + z^2 / (4n^2)) / (1 + z^2 / n)
    return (c - h, c + h)
end

# The lifted ODE's final state, solved directly (not through final_size's ODE route).
function ode_final(sys; init, p = nothing, T = 2000.0)
    sol = solve_epidemic(sys; p, init, tspan = (0.0, T), save_everystep = false, TIGHT...)
    @assert sol.retcode == ModelingToolkit.SciMLBase.ReturnCode.Success
    return sol
end

@testset "analysis" begin
    @testset "E14: transmissibility of Markov progressions (absorbing chain)" begin
        # bypass E → I (p), E → R (1 − p), β = γ = 1: T = p·β/(β + γ) (Volz 2008: T = E[1 − e^{−βI}], and
        # I = 0 with probability 1 − p)
        @test EBM._edge_transmissibility(bypassp(0.5)) ≈ 0.25 atol = 1e-14
        @test EBM._compute_transmissibility(bypassp(0.3)) ≈ 0.15 atol = 1e-14
        # A/I split with unequal hazards (pA = 0.3, βA = 0.5, βI = 2): T = 0.3·0.5/1.5 + 0.7·2/3
        @test EBM._compute_transmissibility(asymp(0.3; βA = 0.5, βI = 2.0)) ≈ 0.3 * 0.5 / 1.5 + 0.7 * 2 / 3 atol = 1e-14
        # linear chains are unchanged: two stages, T = 1 − ∏ out/(β + out)
        two = DiseaseProgression([DiseaseStage(:I1; transmission_rate = 0.1), DiseaseStage(:I2; transmission_rate = 0.2),
                                  DiseaseStage(:R)], [DiseaseTransition(:I1, :I2, 0.5), DiseaseTransition(:I2, :R, 0.3)]; entry = :I1)
        @test EBM._compute_transmissibility(two) ≈ 1 - (0.5 / 0.6) * (0.3 / 0.5) atol = 1e-14
        # symbolic rates: T = pβ/(β + γ) exactly
        @parameters β γ σ p κ
        symb = DiseaseProgression([DiseaseStage(:E), DiseaseStage(:I; transmission_rate = β), DiseaseStage(:R)],
                                  [DiseaseTransition(:E, :I, p * σ), DiseaseTransition(:E, :R, (1 - p) * σ),
                                   DiseaseTransition(:I, :R, γ)]; entry = :E)
        Ts = EBM._edge_transmissibility(symb)
        @test symzero(Ts - p * β / (β + γ))
        # final sizes on Poisson(5) (E14 verifier: the package ODE 0.371663 at ρ = 1e-4, EPN sim 0.3708 ± 0.0017)
        @test final_size(SCM(POIS5, bypassp(0.5))).R_infinity ≈ ref_final_size_pois(5, 0.25, 0.0) rtol = 1e-10
        @test final_size(SCM(POIS5, bypassp(0.5))).R_infinity ≈ 0.371370 atol = 1e-6            # was 0.892645
        @test final_size(SCM(POIS5, bypassp(0.3))) == (R_infinity = 0.0, θ_infinity = 1.0)     # R₀ = 0.75
        @test final_size(SCM(POIS5, asymp(0.5))).R_infinity ≈ ref_final_size_pois(5, 0.5, 0.0) rtol = 1e-10  # 0.892645
        # epidemic_threshold with a bypass: β_c = γ/(p·κ − 1) (was γ/(κ − 1) = 0.25)
        @test epidemic_threshold(SCM(POIS5, bypassp(0.5))) ≈ 2 / 3 atol = 1e-12
        thr = epidemic_threshold(SCM(poisson_pgf(κ), symb))
        @test symzero(thr - γ / (p * κ - 1))
        # a revisited stage (E → I 1, I → E 1, I → R 1): the time in I is Exp(γ_eff = 1), β_c = 1/(κ − 1)
        cyc = DiseaseProgression([DiseaseStage(:E), DiseaseStage(:I; transmission_rate = 1.0), DiseaseStage(:R)],
                                 [DiseaseTransition(:E, :I, 1.0), DiseaseTransition(:I, :E, 1.0), DiseaseTransition(:I, :R, 1.0)];
                                 entry = :E)
        @test epidemic_threshold(SCM(POIS5, cyc)) ≈ 0.25 atol = 1e-12                        # was 0.5
        @test EBM._compute_transmissibility(cyc) ≈ 0.5 atol = 1e-14                         # β/(β + γ_eff)
        cyc2 = DiseaseProgression([DiseaseStage(:E), DiseaseStage(:I; transmission_rate = 1.0), DiseaseStage(:R)],
                                  [DiseaseTransition(:E, :I, 1.0), DiseaseTransition(:I, :E, 1.0), DiseaseTransition(:I, :R, 1.0),
                                   DiseaseTransition(:E, :R, 0.5)]; entry = :E)
        @test epidemic_threshold(SCM(POIS5, cyc2)) ≈ 4 / 7 atol = 1e-12                      # E14 skeptic; was 6/7
        # R₀ at the threshold is 1, from the absorbing-chain T
        for m in (SCM(POIS5, bypassp(0.5)), SCM(POIS5, cyc2))
            βc = epidemic_threshold(m)
            prog = m.progression
            atc = DiseaseProgression([DiseaseStage(s.name; transmission_rate = EBM._is_zero_rate(s.transmission_rate) ? 0 : βc)
                                      for s in prog.stages], prog.transitions; entry = prog.entry)
            @test 5 * EBM._compute_transmissibility(atc) ≈ 1 atol = 1e-12
        end
        @test_throws ArgumentError epidemic_threshold(SCM(POIS5, asymp(0.5)))            # two transmitting stages
        @test_throws ArgumentError epidemic_threshold(SCM(POIS5, bypassp(0.1)))          # π·κ = 0.5 ≤ 1
        # The legacy basic_reproduction_number(::StaticConfigurationModel) (src/builders.jl) uses
        # the absorbing-chain transmissibility since WP29: 1.25, not the 0.1 shortcut's 2.5 (E14).
        @test val(basic_reproduction_number(SCM(POIS5, bypassp(0.5)))) ≈ 1.25
        # the lifted system gives the correct R₀ for the same progression
        @test basic_reproduction_number(build_edge_system(SCM(POIS5, bypassp(0.5)))) ≈ 1.25 atol = 1e-12
    end

    @testset "Erlang T_n" begin
        # NetworkEpiCore's erlang_stages uses n·γ per stage: T_n = 1 − (nγ/(τ + nγ))ⁿ
        for n in (1, 2, 3, 5)
            sys = edge_based(erlang_stages(sir_model(; τ = :τ, γ = :γ), :I, n), ConfigurationNetwork(PoissonDegree(5.0)))
            Tn = transmissibility(sys)
            @test Set(keys(symvars(Tn))) == Set([:τ, :γ])
            # the symbolic T_n is the closed form (compared at several parameter points)
            for (a, b) in ((1 / 6, 1 / 4), (0.7, 0.1), (2.0, 3.0), (0.05, 1.0))
                @test symval(Tn, Dict(:τ => a, :γ => b)) ≈ 1 - (n * b / (a + n * b))^n rtol = 1e-13
            end
            for (a, b) in ((1 / 6, 1 / 4), (0.2, 0.1))
                pv = Dict(:τ => a, :γ => b)
                @test transmissibility(sys; p = pv) ≈ 1 - (n * b / (a + n * b))^n atol = 1e-14
                @test basic_reproduction_number(sys; p = pv) ≈ 5 * (1 - (n * b / (a + n * b))^n) atol = 1e-12
                @test transmissibility(sys; p = pv) ≈ transmissibility(erlang_stages(sir_model(), :I, n),
                                                                     ConfigurationNetwork(PoissonDegree(5.0)), pv) atol = 1e-14
            end
        end
        # legacy ErlangStage: the user passes the stage exit rate n·γ (vignette 10; E30 corrected fix (c)):
        # mean sojourn 1/γ and R₀ = κ(1 − (nγ/(nγ + β))ⁿ) = 3.920 for n = 3, β = 0.2, γ = 0.1 on Poisson(5)
        n, g, b = 3, 0.1, 0.2
        erl = expand_erlang_stages([ErlangStage(:I, n, g; transmission_rate = b), DiseaseStage(:R)],
                                   [DiseaseTransition(:I, :R, n * g)]; entry = :I)
        @test all(tr -> tr.rate ≈ n * g, erl.transitions)
        @test sum(1 / tr.rate for tr in erl.transitions) ≈ 1 / g
        Tl = EBM._compute_transmissibility(erl)
        @test Tl ≈ 1 - (n * g / (n * g + b))^n atol = 1e-14
        @test 5 * Tl ≈ 3.92 atol = 1e-12
        @test val(basic_reproduction_number(SCM(POIS5, erl))) ≈ 5 * Tl atol = 1e-12        # linear chain (builders.jl)
        @test final_size(SCM(POIS5, erl)).R_infinity ≈ ref_final_size_pois(5, Tl, 0.0) rtol = 1e-10
    end

    @testset "Symbolic R₀ equals NetworkEpiCore's numeric NGM on the corpus" begin
        # every canonical scenario on a descriptor the lift linearises (configuration, well mixed,
        # multitype, multiplex, degree-correlated), deduplicated by (model, network, parameters)
        seen = Set{String}()
        n_checked = 0
        for id in scenario_ids()
            sc = scenario(id)
            sc.network isa Union{ConfigurationNetwork,WellMixed,MultitypeNetwork,MultiplexNetwork,
                                 DegreeCorrelatedNetwork} || continue
            is_admissible(sc.model, :edge_based; network = sc.network) || continue
            key = canonical_text(sc.model) * canonical_text(sc.network) * repr(sort!(collect(sc.params)))
            key in seen && continue
            push!(seen, key)
            sys = edge_based(sc)
            p = sc.params
            R0 = basic_reproduction_number(sc.model, sc.network, p)
            @testset "$id" begin
                @test basic_reproduction_number(sys; p) ≈ R0 rtol = 1e-10
                K = next_generation_matrix(sys; p)
                @test maximum(abs, eigvals(K)) ≈ R0 rtol = 1e-10
                @test early_growth_rate(sys; p) ≈ early_growth_rate(sc.model, sc.network, p) rtol = 1e-9 atol = 1e-12
                if haskey(sc.expected, :R0)
                    @test R0 ≈ sc.expected[:R0] rtol = 1e-10
                end
                if size(K, 1) <= 2          # a closed-form Perron root: the symbolic R₀
                    @test symval(basic_reproduction_number(sys), p) ≈ R0 rtol = 1e-10
                else
                    @test_throws ArgumentError basic_reproduction_number(sys)
                end
            end
            n_checked += 1
        end
        @test n_checked >= 15
        @info "WP19: symbolic/lifted R₀ checked against NetworkEpiCore's NGM" scenarios = n_checked

        # hand-built models with a known R₀ (E14 cases; symbolic R₀ = the closed form)
        net5 = ConfigurationNetwork(PoissonDegree(5.0))
        cases = [
            (ContactModel(:bypass; contacts = [Contact(:S, :I, :E, :τ)],
                          transitions = [NodeTransition(:E, :I, :(p * σ)), NodeTransition(:E, :R, :((1 - p) * σ)),
                                         NodeTransition(:I, :R, :γ)]),
             Dict(:τ => 1.0, :γ => 1.0, :σ => 1.0, :p => 0.5), 1.25),
            (ContactModel(:split; contacts = [Contact(:S, :A, :E, :τA), Contact(:S, :I, :E, :τI)],
                          transitions = [NodeTransition(:E, :A, :(pA * σ)), NodeTransition(:E, :I, :((1 - pA) * σ)),
                                         NodeTransition(:A, :R, :γ), NodeTransition(:I, :R, :γ)]),
             Dict(:τA => 0.5, :τI => 2.0, :γ => 1.0, :σ => 1.0, :pA => 0.3), 5 * (0.3 * 0.5 / 1.5 + 0.7 * 2 / 3)),
            (ContactModel(:cycle; contacts = [Contact(:S, :I, :E, :τ)],
                          transitions = [NodeTransition(:E, :I, 1.0), NodeTransition(:I, :E, 1.0), NodeTransition(:I, :R, 1.0)]),
             Dict(:τ => 1.0), 2.5),                                              # T = β/(β + γ_eff), γ_eff = 1
            (ContactModel(:removal; contacts = [Contact(:S, :I, :I, :τ)], transitions = [NodeTransition(:I, nothing, :γ)]),
             Dict(:τ => 1 / 6, :γ => 1 / 4), 2.0),                               # I → ∅ (the :removed sink)
            (ContactModel(:unreachable; contacts = [Contact(:S, :I, :I, :τ), Contact(:S, :X, :I, :τ)],
                          transitions = [NodeTransition(:I, :R, :γ), NodeTransition(:X, :R, :γ)]),
             Dict(:τ => 1.0, :γ => 1.0), 2.5),                                   # X is never entered
        ]
        for (cm, p, ref) in cases
            sys = edge_based(cm, net5)
            @test basic_reproduction_number(sys; p) ≈ ref rtol = 1e-12
            @test basic_reproduction_number(cm, net5, p) ≈ ref rtol = 1e-12
            @test symval(basic_reproduction_number(sys), p) ≈ ref rtol = 1e-12
        end
        byp = edge_based(cases[1][1], net5)
        Tb = transmissibility(byp)
        v = symvars(Tb)
        @test symzero(Tb - v[:p] * v[:τ] / (v[:τ] + v[:γ]))
        # a symbolic mean degree: R₀ = κτ/(τ + γ)
        @parameters κs
        sysκ = edge_based(sir_model(), ConfigurationNetwork(PoissonDegree(κs)))
        R0κ = basic_reproduction_number(sysκ)
        v = symvars(R0κ)
        @test symzero(R0κ - v[:κs] * v[:τ] / (v[:τ] + v[:γ]))
        # every rate numeric: a number
        @test basic_reproduction_number(edge_based(sir_model(; τ = 0.3, γ = 0.1), net5)) ≈ 3.75 atol = 1e-12
        # a typed network's 4×4 matrix has no closed-form Perron root: p is required
        @test_throws ArgumentError basic_reproduction_number(edge_based(scenario(:sir_sbm2)))
    end

    @testset "early growth rate against the lifted ODE" begin
        # the slope of log φ_I at tiny prevalence (linear regime) equals the leading eigenvalue
        for id in (:sir_pois5, :seir_pois5, :sir_bim)
            sc = scenario(id)
            sys = edge_based(sc)
            r = early_growth_rate(sys; p = sc.params)
            X = only(entry_species(sc.model))
            init = default_initial_conditions(sys; initial = SeedFraction(X => 1e-12))
            sol = solve_epidemic(sys; p = sc.params, init, tspan = (0.0, 40.0), saveat = [25.0, 35.0],
                                 solver = Vern9(), reltol = 1e-12, abstol = 1e-30)
            y = sol[sys.variables[:φ_I]]
            @test log(y[2] / y[1]) / 10 ≈ r rtol = 1e-4
        end
    end

    @testset "E12: multiplex R₀ = ρ(K)" begin
        mpx = ContactModel(:mpx2; contacts = [Contact(:S, :I, :I, :τa; layer = :a), Contact(:S, :I, :I, :τb; layer = :b)],
                           transitions = [NodeTransition(:I, :R, :γ)])
        # K = diag(T)·M, M_ii = ψ_i''(1)/ψ_i'(1), M_ij = ψ_j'(1) (E12; Jacobsen et al. 2018, App. A.1)
        function ρK(d, T)
            k = [Float64(pgf_derivative(x, 1.0, 1)) for x in d]
            κx = [Float64(pgf_derivative(x, 1.0, 2)) / k[i] for (i, x) in enumerate(d)]
            K = [T[i] * (i == j ? κx[i] : k[j]) for i in 1:2, j in 1:2]
            return maximum(abs, eigvals(K))
        end
        bim17 = EmpiricalDegree([0, 0.5, 0, 0, 0, 0, 0, 0.5])
        for (d, T, ref, additive) in (((RegularDegree(3), RegularDegree(3)), (0.22, 0.22), 1.1, 0.88),
                                      ((RegularDegree(4), RegularDegree(3)), (0.3, 0.3), 1.8, 1.5),
                                      ((bim17, bim17), (0.1, 0.1), 0.925, 1.05),
                                      ((PoissonDegree(3.0), PoissonDegree(2.0)), (0.75, 2 / 3), 3.5833333333333335, 3.5833333333333335))
            net = MultiplexNetwork(:a => d[1], :b => d[2])
            p = Dict(:τa => T[1] / (1 - T[1]), :τb => T[2] / (1 - T[2]), :γ => 1.0)
            @test ρK(d, T) ≈ ref rtol = 1e-12
            @test basic_reproduction_number(mpx, net, p) ≈ ref rtol = 1e-12
            sys = edge_based(mpx, net)
            @test basic_reproduction_number(sys; p) ≈ ref rtol = 1e-12
            @test symval(basic_reproduction_number(sys), p) ≈ ref rtol = 1e-12   # 2 × 2: symbolic Perron root
            # the sum of the layer R₀'s is right only when det K = 0 (Poisson layers)
            @test (ref ≈ additive) == (d[1] isa PoissonDegree)
            # sign(r) = sign(R₀ − 1): the bimodal pair is subcritical although the sum exceeds 1
            @test sign(early_growth_rate(sys; p)) == sign(ref - 1)
        end
    end

    @testset "final_size with ρ equals the ODE to 1e-8 (E31(i))" begin
        # legacy: final_size(model; seed_fraction = ρ) against the lifted ODE seeded with ρ in the entry stage
        for (label, model) in (("SIR Poisson(5)", SCM(POIS5, sirp(1 / 6, 1 / 4))),
                               ("SIR bimodal {2, 8}", SCM(BIM28, sirp(1 / 6, 1 / 4))),
                               ("SEIR Poisson(5)", SCM(POIS5, seirp(1 / 5, 1 / 6, 1 / 4))),
                               ("bypass Poisson(5)", SCM(POIS5, bypassp(0.8))))
            sys = build_edge_system(model)
            for ρ in (0.01, 0.2)
                sol = ode_final(sys; init = default_initial_conditions(sys; seed_fraction = ρ))
                fs = final_size(model; seed_fraction = ρ)
                @test fs.R_infinity ≈ 1 - sol[sys.observables[:S]][end] atol = 1e-8
                @test fs.R_infinity ≈ sol[sys.variables[:cumulative]][end] atol = 1e-8
                @test fs.R_infinity >= ρ
            end
            @test final_size(model; seed_fraction = 0.0) == final_size(model)
        end
        # the finite seed matters (E31: ρ → 0 under-predicts by 0.0034 at ρ = 0.01, 0.046 at ρ = 0.2)
        m = SCM(POIS5, sirp(1 / 6, 1 / 4))
        @test final_size(m; seed_fraction = 0.01).R_infinity - final_size(m).R_infinity > 0.003
        @test_throws ArgumentError final_size(m; seed_fraction = 1.5)
        # lowered systems: NetworkEpiCore's fixed point and the ODE route both equal the solved ODE
        for id in (:sir_pois5, :seir_pois5, :seair_pois5, :sir_bim, :sir_wm5, :sir_sbm2, :sir_mpx)
            sc = scenario(id)
            sys = edge_based(sc)
            init = default_initial_conditions(sys; initial = sc.initial)
            ode = ode_final(sys; init, p = sc.params)[sys.variables[:cumulative]][end]
            @test final_size(sys; p = sc.params, initial = sc.initial) ≈ ode atol = 1e-8
            @test final_size(sys; p = sc.params, initial = sc.initial, method = :ode) ≈ ode atol = 1e-8
            haskey(sc.expected, :final_size) && @test sc.expected[:final_size] ≈ ode atol = 1e-8
        end
        # no fixed-point equation: exits (vaccination) and two strains take the ODE route
        for id in (:sir_vax_pois5, :twostrain_pois5)
            sc = scenario(id)
            sys = edge_based(sc)
            init = default_initial_conditions(sys; initial = sc.initial)
            ode = ode_final(sys; init, p = sc.params)[sys.variables[:cumulative]][end]
            @test final_size(sys; p = sc.params, initial = sc.initial) ≈ ode atol = 1e-8
            @test_throws ArgumentError final_size(sys; p = sc.params)                  # the ODE needs a seed
            @test_throws ArgumentError final_size(sys; p = sc.params, initial = sc.initial, method = :fixed_point)
        end
        @test_throws ArgumentError final_size(edge_based(scenario(:sir_pois5)); method = :other)
    end

    @testset "E29: EoN cross-validation of the final size" begin
        # EoN 1.2 Attack_rate_cts_time (test/golden/eon/eon_like_for_like.toml, generate_eon.py): exact
        # Poisson(5) with rho = None and rho = 0.01, and the ER(1000, seed 42) degree distribution at rho = 0.01
        ar = EON["attack_rate"]
        τ, γ, ρ = EON["setup"]["tau"], EON["setup"]["gamma"], EON["setup"]["rho"]
        m = SCM(POIS5, sirp(τ, γ))
        @test final_size(m).R_infinity ≈ ar["poisson5_rho_to_0"] atol = 1e-12                 # 0.7968121
        @test final_size(m; seed_fraction = ρ).R_infinity ≈ ar["poisson5_rho_001"] atol = 1e-12 # 0.8002040
        er = SCM(polynomial_pgf(Float64.(EON["sir_er1000_seed42"]["pk"])), sirp(τ, γ))
        @test final_size(er; seed_fraction = ρ).R_infinity ≈ ar["er1000_seed42_rho_001"] atol = 1e-12  # 0.7987353
        # the EBCM trajectory reaches the ρ = 0.01 attack rate (R(40) = 0.7985035, EoN like for like)
        sys = build_edge_system(m)
        sol = ode_final(sys; init = default_initial_conditions(sys; seed_fraction = ρ), T = 40.0)
        @test compartment(sys, sol, :R)[end] ≈ EON["sir_poisson5"]["R40"] atol = 5e-8     # EoN solved at scipy tolerances
        @test sol[sys.variables[:cumulative]][end] < final_size(m; seed_fraction = ρ).R_infinity
    end

    @testset "E18: final size and P(major) near the threshold" begin
        mk(R0) = (T = R0 / 5; SCM(POIS5, sirp(T / (1 - T), 1.0)))
        # R∞ solves R = 1 − exp(−R₀R) on Poisson(5); references from scipy brentq and 60-digit mpmath (E18)
        for (R0, Rref) in ((1.001, 1.997336441e-3), (1.005, 9.933720086e-3), (1.01, 1.973641044e-2))
            fs = final_size(mk(R0))
            @test fs.R_infinity ≈ Rref rtol = 1e-9
            @test fs.R_infinity ≈ 1 - exp(-R0 * fs.R_infinity) rtol = 1e-9
            @test fs.R_infinity ≈ ref_final_size_pois(5, R0 / 5, 0.0) rtol = 1e-9
            # the Markov P(major) (E15) from an independent quadrature; far below R∞ near threshold
            T = R0 / 5
            @test epidemic_probability(mk(R0)) ≈ ref_pmajor_pois_sir(5.0, T / (1 - T), 1.0) rtol = 1e-6
        end
        for R0 in (0.5, 0.6, 0.9, 0.99, 0.999, 1.0)          # exactly (0, 1) when R₀ ≤ 1
            @test final_size(mk(R0)) == (R_infinity = 0.0, θ_infinity = 1.0)
            @test epidemic_probability(mk(R0)) == 0.0
            @test confidence_bands(mk(R0), 10_000).variance == 0.0
        end
        # 2-regular graph (κ = 1): never supercritical
        @test final_size(SCM(polynomial_pgf([0.0, 0.0, 1.0]), sirp(1000.0, 1.0))).R_infinity == 0.0
        # no degree-1 nodes and T ≈ 1 (degrees 0 and 3): θ∞ ≈ 0 and R∞ = 1 − p₀
        @test final_size(SCM(polynomial_pgf([0.1, 0.0, 0.0, 0.9]), sirp(1e15, 1.0))).R_infinity ≈ 0.9 atol = 1e-12
    end

    @testset "E15: epidemic_probability is the infector-side formula" begin
        # references: Poisson β = γ closed form κy(1 − y) = 1 − e^{−κy}; the others from the E15 verifier's
        # scipy quadrature (ref.py) and the skeptic's independent Gauss–Legendre code (agree to 1e-13)
        m = SCM(POIS5, sirp(1.0, 1.0))
        h(y) = 5y * (1 - y) - (1 - exp(-5y))             # κy(1 − y) = 1 − e^{−κy}, root in (0.5, 0.9)
        lo, hi = 0.5, 0.9
        for _ in 1:100
            mid = (lo + hi) / 2
            h(mid) > 0 ? (lo = mid) : (hi = mid)
        end
        @test epidemic_probability(m) ≈ (lo + hi) / 2 atol = 1e-10
        @test epidemic_probability(m) ≈ 0.73468666 atol = 1e-8                              # was 0.892645
        @test epidemic_probability(m) < final_size(m).R_infinity - 0.1                       # was identical
        @test epidemic_probability(SCM(BIM28, sirp(1.0, 1.0))) ≈ 0.70309771 atol = 1e-8        # was 0.836099
        @test epidemic_probability(SCM(POIS5, sirp(1 / 6, 1 / 4))) ≈ 0.60940835 atol = 1e-8     # was 0.796812
        @test epidemic_probability(SCM(POIS5, sirp(0.3, 0.1))) ≈ 0.90522357 atol = 1e-8        # was 0.974082
        @test epidemic_probability(SCM(POIS5, sirp(1 / 6, 1 / 4))) ≈ ref_pmajor_pois_sir(5.0, 1 / 6, 1 / 4) rtol = 1e-9
        # a latent period does not change P
        @test epidemic_probability(SCM(POIS5, seirp(1.0, 1.0, 1.0))) ≈ 0.73468666 atol = 1e-8
        # Erlang-2 infectious period (two stages at rate 2, β = 1): E[W^j] = (2/(2 + j))²
        erl2 = DiseaseProgression([DiseaseStage(:I1; transmission_rate = 1.0), DiseaseStage(:I2; transmission_rate = 1.0),
                                   DiseaseStage(:R)], [DiseaseTransition(:I1, :I2, 2.0), DiseaseTransition(:I2, :R, 2.0)]; entry = :I1)
        @test epidemic_probability(SCM(POIS5, erl2)) ≈ 0.84890273 atol = 1e-8                # was 0.922994
        @test epidemic_probability(SCM(POIS5, sirp(0.01, 1.0))) == 0.0
        # the E14 bypass case: 0.1420 exact (skeptic's branching process), NOT R∞ = 0.3714
        @test epidemic_probability(SCM(POIS5, bypassp(0.5))) ≈ 0.1420 atol = 1e-4
        # moment guard (E15 skeptic): a power law with support up to 800 (> 512) is exact, 0.11693271
        K = 800
        w = [k == 0 ? 0.0 : k^-2.2 for k in 0:K]
        @test epidemic_probability(SCM(polynomial_pgf(w ./ sum(w)), sirp(0.2, 1.0))) ≈ 0.11693271 atol = 1e-8
        # a PGF without provenance: the DFT route, and a non-analytic expression is an error, not a number
        @variables z
        @test epidemic_probability(SCM(DegreePGF(z, exp(5.0 * (z - 1))), sirp(1.0, 1.0))) ≈ 0.73468666 atol = 1e-8
        @test_throws ArgumentError epidemic_probability(SCM(DegreePGF(z, exp(5.0 * (abs(z) - 1))), sirp(1.0, 1.0)))
        # lowered systems give the same numbers; WellMixed(κ): 1 − 1/R₀ for SIR and SEIR
        sc = scenario(:sir_pois5)
        @test epidemic_probability(edge_based(sc); p = sc.params) ≈ epidemic_probability(SCM(POIS5, sirp(1 / 6, 1 / 4))) atol = 1e-12
        sc = scenario(:seair_pois5)
        sys = edge_based(sc)
        P = epidemic_probability(sys; p = sc.params)
        @test 0 < P < final_size(sys; p = sc.params)
        @test epidemic_probability(sys; p = sc.params, from = :I) != P
        wm = edge_based(scenario(:sir_wm5))
        @test epidemic_probability(wm; p = scenario(:sir_wm5).params) ≈ 1 - 1 / 2 atol = 1e-12
        wms = edge_based(seir_model(; σ = 0.3, τ = 0.1, γ = 1 / 4), WellMixed(5))
        @test epidemic_probability(wms) ≈ 1 - 1 / 2 atol = 1e-12
        for (id, why) in ((:sir_sbm2, "a typed network"), (:sir_vax_pois5, "exits"), (:twostrain_pois5, "entry states"))
            s = scenario(id)
            err = try epidemic_probability(edge_based(s); p = s.params) catch e; e end
            @test err isa ArgumentError
        end
    end

    @testset "P(major) against NetworkOutbreaks (:sir_pois5_1seed)" begin
        sc = scenario(:sir_pois5_1seed)
        P = epidemic_probability(edge_based(sc); p = sc.params)
        @test P ≈ 0.60940835 atol = 1e-8
        bond = final_size(sc.model, sc.network, sc.params)                 # the old (bond-percolation) value
        N = sc.sim.N
        dir = joinpath(pkgdir(NO), "data", "scenarios")
        base = summary_basename(sc.id, scenario_hash(sc))
        k, n, ci, source = if isfile(joinpath(dir, base * ".toml"))
            s = load_summary(dir, sc.id, scenario_hash(sc); algorithm_revision = NO.ALGORITHM_REVISION)
            s.n_major, s.nsims, s.p_major_ci, "committed summary $(base)"
        else
            ens = NO.simulate(sc)                                         # 2000 runs, the scenario's streams
            seeds = round(Int, only(last.(seed_fractions(sc.initial))) * N)
            ever = [NO.final_size(t) * N for t in ens.trajectories]
            k = count(x -> x - seeds >= 0.05N, ever)
            k, length(ever), wilson(k, length(ever)), "local ensemble (N = $(N), $(length(ever)) runs)"
        end
        se = sqrt(k / n * (1 - k / n) / n)
        @info "WP19: P(major) for :sir_pois5_1seed" source major = k runs = n p_major = k / n se ci infector_side = P bond_percolation = bond
        @test n >= 2000
        @test ci[1] <= P <= ci[2]
        @test !(ci[1] <= bond <= ci[2])
    end

    @testset "E16: confidence_bands is Ball (2021) Theorem 2.2" begin
        m1 = SCM(POIS5, sirp(1.0, 1.0))
        cb = confidence_bands(m1, 10_000)
        @test cb.variance ≈ 0.19763 rtol = 1e-4                        # NSW; sim 0.2006 ± 0.0036 (E16); was 0.13578
        @test confidence_bands(m1, 10_000; graph = :MR).variance ≈ 0.16831 rtol = 1e-4
        @test confidence_bands(SCM(POIS5, sirp(0.3, 0.1)), 10_000).variance ≈ 0.030388 rtol = 1e-4   # was 0.04222
        # a regular graph: NSW == MR (Ball Remark 2.5)
        c4 = SCM(REG4, sirp(1.0, 1.0))
        @test confidence_bands(c4, 10_000).variance ≈ 0.76977 rtol = 1e-4
        @test confidence_bands(c4, 10_000).variance ≈ confidence_bands(c4, 10_000; graph = :MR).variance rtol = 1e-10
        # NSW ≥ MR, and a constant infectious period (q2 = q_I²) gives less variance than the Markov one
        @test cb.variance > confidence_bands(m1, 10_000; graph = :MR).variance
        # Erlang-3 infectious period at T = 1/2 (q_I⁽²⁾ = 0.28484): 0.174332 (E16 skeptic)
        βe = 3 * (2^(1 / 3) - 1)
        erl3 = DiseaseProgression([DiseaseStage(:I1; transmission_rate = βe), DiseaseStage(:I2; transmission_rate = βe),
                                   DiseaseStage(:I3; transmission_rate = βe), DiseaseStage(:R)],
                                  [DiseaseTransition(:I1, :I2, 3.0), DiseaseTransition(:I2, :I3, 3.0), DiseaseTransition(:I3, :R, 3.0)];
                                  entry = :I1)
        @test EBM._compute_transmissibility(erl3) ≈ 0.5 atol = 1e-12
        @test confidence_bands(SCM(POIS5, erl3), 10_000).variance ≈ 0.174332 rtol = 1e-5
        @test cb.std_error ≈ sqrt(cb.variance / 10_000)
        @test cb.mean ≈ final_size(m1).R_infinity
        @test cb.lower < cb.mean < cb.upper
        @test cb.upper - cb.mean ≈ 1.959963984540054 * cb.std_error rtol = 1e-8
        # the variance blows up at the threshold (R₀ = 1.05: Ball 59.25; was 0.2348)
        Tc = 1.05 / 5
        @test confidence_bands(SCM(POIS5, sirp(Tc / (1 - Tc), 1.0)), 10_000).variance ≈ 59.25 rtol = 1e-3
        @test confidence_bands(SCM(POIS5, sirp(0.01, 1.0)), 10_000) ==
              (lower = 0.0, mean = 0.0, upper = 0.0, variance = 0.0, std_error = 0.0)
        @test_throws ArgumentError confidence_bands(m1, 10_000; graph = :other)
        @test_throws ArgumentError confidence_bands(m1, 10_000; level = 1.0)
        # lowered systems give the same band
        sc = scenario(:sir_pois5)
        cbs = confidence_bands(edge_based(sc), 10_000; p = sc.params)
        cbl = confidence_bands(SCM(POIS5, sirp(1 / 6, 1 / 4)), 10_000)
        @test all(isapprox(getfield(cbs, f), getfield(cbl, f); rtol = 1e-12) for f in keys(cbl))
        @test cbl.variance ≈ 0.55997 rtol = 1e-4                       # vignette parameters (E16); was 0.2205
        # simulation: n·Var(final size | major) from NetworkOutbreaks, Poisson(5) degrees, β = γ = 1, one
        # seed. Ball's NSW graph has iid degrees, so the graphs are erased configuration graphs with iid
        # Poisson(5) degrees (an EmpiricalDegree; NetworkOutbreaks samples PoissonDegree as Erdős–Rényi
        # G(N, p), whose edge count varies twice as much, so its variance is not σ²_NSW).
        N, runs = 10_000, 600
        p5 = degree_probabilities(PoissonDegree(5.0); tol = 1e-15)
        nsw = ConfigurationNetwork(EmpiricalDegree(p5 ./ sum(p5)))
        ens = NO.simulate(sir_model(; τ = 1.0, γ = 1.0), nsw; N,
                          initial = SeedFraction(:I => 1 / N), tspan = (0.0, 60.0), nsims = runs, seed = 20260927)
        sizes = [NO.final_size(t) for t in ens.trajectories]
        major = [x for x in sizes if x - 1 / N >= 0.05]
        kk = length(major)
        v = var(major)
        m4 = mean((major .- mean(major)) .^ 4)
        se_v = N * sqrt(max(m4 - v^2 * (kk - 3) / (kk - 1), 0.0) / kk)
        @info "WP19: Ball (2021) NSW variance vs NetworkOutbreaks" N runs major = kk nvar = N * v se = se_v ball = cb.variance old_formula = 0.13578
        @test abs(N * v - cb.variance) < 3 * se_v
        @test abs(N * v - 0.13578) > 3 * se_v
        @test abs(mean(major) - cb.mean) < 3 * std(major) / sqrt(kk)
    end

    @testset "E17: SIR-type analysis refuses re-susceptibilising progressions" begin
        sis = SCM(POIS5, sisp(0.22, 1.0))
        sirs = SCM(POIS5, sirsp(0.24, 1.0, 2.0))
        # the 0.1 with_reinfection_counting(::DiseaseProgression, L) lift (an error since WP29, which
        # deleted it) produced these progressions: stages I_p, S_p (p = 1..L), recoveries I_p → S_p,
        # susceptible S_0 and entry I_1. The guard must still refuse them.
        counted(β, γ, L) = DiseaseProgression(
            vcat([DiseaseStage(Symbol(:I_, p); transmission_rate = β) for p in 1:L],
                 [DiseaseStage(Symbol(:S_, p)) for p in 1:L]),
            [DiseaseTransition(Symbol(:I_, p), Symbol(:S_, p), γ) for p in 1:L]; susceptible = :S_0, entry = :I_1)
        @test_throws ErrorException with_reinfection_counting(sisp(0.22, 1.0), 1)
        lifted = [SCM(POIS5, counted(0.22, 1.0, L)) for L in (1, 2)]
        for m in vcat([sis, sirs], lifted)
            @test_throws ArgumentError final_size(m)
            @test_throws ArgumentError epidemic_probability(m)
            @test_throws ArgumentError confidence_bands(m, 10_000)
            @test_throws ArgumentError epidemic_threshold(m)
            @test_throws ArgumentError EBM._compute_transmissibility(m.progression)
        end
        err = try final_size(sis) catch e; e end
        @test occursin("re-susceptibilises (I→S)", sprint(showerror, err))
        @test occursin("NodeBasedModels", sprint(showerror, err))
        # the SIR controls are accepted (no false positive on user-named stages I_1, I_2)
        sir = SCM(POIS5, sirp(0.22, 1.0))
        @test val(basic_reproduction_number(sir)) ≈ 5 * 0.22 / 1.22
        @test epidemic_threshold(sir) ≈ 0.25
        chain = DiseaseProgression([DiseaseStage(:I_1; transmission_rate = 0.3), DiseaseStage(:I_2; transmission_rate = 0.3),
                                    DiseaseStage(:R)], [DiseaseTransition(:I_1, :I_2, 1.0), DiseaseTransition(:I_2, :R, 1.0)];
                                   entry = :I_1)
        @test final_size(SCM(POIS5, chain)).R_infinity > 0
        # The legacy R₀ of builders.jl refuses SIS since WP29 (E17):
        @test_throws ArgumentError basic_reproduction_number(sis)
        # an SIS model cannot be lifted at all
        @test_throws AdmissibilityError edge_based(sis_model(), ConfigurationNetwork(PoissonDegree(5.0)))
    end

    @testset "lowered systems: thresholds, equilibria and errors" begin
        sc = scenario(:sir_pois5)
        sys = edge_based(sc)
        @test epidemic_threshold(sys; p = sc.params) ≈ (1 / 4) / (5 - 1) rtol = 1e-10
        @test basic_reproduction_number(sys; p = Dict(:τ => epidemic_threshold(sys; p = sc.params), :γ => 1 / 4)) ≈ 1 rtol = 1e-10
        sl = epidemic_threshold(sys; p = sc.params, vary = :γ)
        @test basic_reproduction_number(sys; p = Dict(:τ => 1 / 6, :γ => sl)) ≈ 1 rtol = 1e-10
        # the disease-free equilibrium stays disease free: nobody is ever infected (and, without exits,
        # it is an exact fixed point: S = 1 throughout)
        for id in (:sir_pois5, :sir_vax_pois5, :sir_sbm2)
            sc_ = scenario(id)
            s = edge_based(sc_)
            dfe = disease_free_equilibrium(s)
            sol = solve_epidemic(s; p = sc_.params, init = dfe, tspan = (0.0, 50.0), saveat = [0.0, 50.0])
            infected = [k for k in keys(s.variables) if startswith(string(k), "pop_I") || k === :cumulative]
            @test !isempty(infected)
            @test all(all(iszero, sol[s.variables[k]]) for k in infected)
            id === :sir_vax_pois5 || @test all(==(1.0), compartment(s, sol, :S))
        end
        @test disease_free_equilibrium(sys)[sys.variables[:θ]] == 1.0
        # numeric evaluation needs every parameter
        @test_throws ArgumentError basic_reproduction_number(edge_based(sir_model(), ConfigurationNetwork(PoissonDegree(5.0))); p = Dict(:τ => 0.1))
        # descriptors whose lifted field is not linearised here (neighbour exchange, MFSH) fall back to
        # NetworkEpiCore's numeric R₀ and r (the lifts belong to WP21 and WP36c)
        for id in (:sir_ne_reg6_eta1, :sir_mfsh_pois5)
            sc_ = scenario(id)
            s = try edge_based(sc_) catch err; err isa ArgumentError ? nothing : rethrow() end
            if s === nothing
                @test_broken false         # the lift of this descriptor is not available
            else
                @test EBM._system_closure(s) ∉ EBM._LINEARISABLE_CLOSURES
                @test basic_reproduction_number(s; p = sc_.params) ≈ basic_reproduction_number(sc_.model, sc_.network, sc_.params)
                @test early_growth_rate(s; p = sc_.params) ≈ early_growth_rate(sc_.model, sc_.network, sc_.params)
                @test_throws ArgumentError epidemic_probability(s; p = sc_.params)
            end
        end
    end

    @testset "numerical tools" begin
        # Acklam's normal quantile (the old A&S 26.2.23 was accurate to 4.5e-4)
        for (p, q) in ((0.975, 1.959963984540054), (0.995, 2.5758293035489004), (0.9, 1.2815515655446004),
                       (0.01, -2.3263478740408408), (0.5, 0.0), (1e-6, -4.753424308822899))
            @test EBM._normal_quantile(p) ≈ q rtol = 2e-9 atol = 1e-15
        end
        @test_throws DomainError EBM._normal_quantile(1.0)
        # Brent's method refuses an unbracketed root and never returns an unconverged value
        @test EBM._brent_root(x -> x^3 - 2, 0.0, 2.0, -2.0, 6.0; what = "cube root") ≈ cbrt(2) atol = 1e-15
        @test_throws ArgumentError EBM._brent_root(x -> x^2 + 1, 0.0, 2.0, 1.0, 5.0; what = "no root")
        # no-pivot elimination on an M-matrix, symbolic and numeric
        @parameters a b c
        A = [a+b -b; -c c+1]
        X = EBM._solve_nopivot(A, reshape([1, 0], 2, 1))
        sub = Dict(a => 0.7, b => 0.3, c => 0.2)
        An = [1.0 -0.3; -0.2 1.2]
        @test [val(Symbolics.substitute(Symbolics.Num(X[i, 1]), sub; fold = Val(true))) for i in 1:2] ≈ An \ [1.0, 0.0] atol = 1e-14
    end
end
