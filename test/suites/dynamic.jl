# WP21: the edge-based lift on dynamic fixed-degree networks, DynamicNetwork(base,
# NeighbourExchange(η)) (Miller, Slim & Volz 2012, Part I §3.2, papers/1106.6320v1.md:190-222, and
# Part II §3.2.3; DESIGN §C.3, §D.5 Λ3, §G.2 WP21; verified issues E05, E06, E07).
#
# Every expected value comes from an independent source:
# - a hand transcription, in this file, of the MSV DFD equations in MSV's own variables
#   (θ, φ_S, φ_I, π_R, R, with the explicit seed q = 1 − ρ: S = qψ(θ), π_S = qθψ'(θ)/ψ'(1)),
#   mapped onto the lift by a semiconjugacy that NetworkEpiCore's `verify` checks symbolically;
# - the static configuration lift of lift/configuration.jl (η = 0);
# - mass action through the well-mixed unit M1, and the MFSH ODE written out in this file (Λ3);
# - NetworkEpiCore's next-generation engine (WP11) and MSV's closed-form R₀;
# - the independent ODEs and exact simulations of the verifiers of E05, E06 and E07
#   (VERIFIED_ISSUES.md), whose printed values are quoted where they are used;
# - exact simulation of the neighbour-exchange process in NetworkOutbreaks (WP26): a fresh graph
#   per run (graph r from NetworkOutbreaks.stable_rng(base + r), the run from
#   stable_rng(base + 2³² + r), design §J.7), NextReaction, exactly ρN seeds, runs conditioned on a
#   major outbreak (ever infected minus seeds ≥ 0.05 N, design §E.2).

using EdgeBasedModels
using NetworkEpiCore
using ModelingToolkit
using Symbolics
using LinearAlgebra
using Statistics
using OrdinaryDiffEq: ODEProblem, Vern9
import OrdinaryDiffEq
using Test

import NetworkOutbreaks as NO

const EBM = EdgeBasedModels
const TOL = (solver = Vern9(), reltol = 1e-11, abstol = 1e-13)

dfd(d, η) = DynamicNetwork(d, NeighbourExchange(η))
curve(sys, sol, X) = compartment(sys, sol, X)
numval(e, at) = Float64(Symbolics.value(Symbolics.substitute(e, at; fold = Val(true))))

const BIMODAL = EmpiricalDegree(Dict(2 => 0.5, 8 => 0.5))       # the E06 skeptic's non-Poisson case
const SIR_BIM = EmpiricalDegree(Dict(2 => 5 / 6, 10 => 1 / 6))  # :sir_bim (excess degree 5)

# ---------------------------------------------------------------------------------------------
# The MSV DFD equations, transcribed by hand in MSV's variables (explicit seed q = q_S)
# ---------------------------------------------------------------------------------------------

# SIR (papers/1106.6320v1.md:210-218): θ̇ = −τφ_I, φ̇_S = −τφ_Iφ_Sψ''/ψ' + ηθπ_S − ηφ_S,
# φ̇_I = τφ_Iφ_Sψ''/ψ' + ηθπ_I − (τ + γ + η)φ_I, π̇_R = γπ_I, Ṙ = γI, with π_S = qθψ'(θ)/ψ'(1),
# π_I = 1 − π_R − π_S, S = qψ(θ), I = 1 − S − R. `typo = true` is the printed Volz–Meyers (2007)
# swap target ψ'(θ)/ψ'(1) of the legacy builder (E05); `q = false` drops the seed factor (E06).
function msv_sir(d; typo::Bool = false, q::Bool = true)
    τ, γ, η = as_parameter(:τ), as_parameter(:γ), as_parameter(:η)
    qS = q ? as_parameter(:q_S) : 1
    @variables t TH(t) PS(t) PI(t) PR(t) R(t)
    ψ(x) = pgf(d, x)
    ψ1(x) = pgf_derivative(d, x, 1)
    ψ2(x) = pgf_derivative(d, x, 2)
    k̄ = mean_degree(d)
    πS = qS * TH * ψ1(TH) / k̄
    πI = 1 - PR - πS
    target = typo ? ψ1(TH) / k̄ : πS
    rhs = Any[-τ * PI,
              -τ * PI * PS * ψ2(TH) / ψ1(TH) + η * TH * target - η * PS,
              τ * PI * PS * ψ2(TH) / ψ1(TH) + η * TH * πI - (τ + γ + η) * PI,
              γ * πI,
              γ * (1 - qS * ψ(TH) - R)]
    ode = SymbolicODE(:msv_dfd_sir; states = Any[TH, PS, PI, PR, R], rhs,
                      parameters = Any[τ, γ, η, as_parameter(:q_S)],
                      domain = Pair{Any,Tuple{Float64,Float64}}[TH => (0.3, 1.0)])
    return ode, (; TH, PS, PI, PR, R, ψ, ψ1, k̄)
end

# SEIR, the same construction with a latent class (the DFD of MSV Part II §3.2.3 extended to SEIR,
# as in the E07 verification): φ̇_E = τφ_Iφ_Sψ''/ψ' − σφ_E + ηθπ_E − ηφ_E, φ̇_I = σφ_E −
# (τ + γ + η)φ_I + ηθπ_I, π̇_I = σπ_E − γπ_I, π̇_R = γπ_I, π_E = 1 − π_S − π_I − π_R,
# Ė = τφ_I qψ'(θ) − σE, Ṙ = γI, I = 1 − S − E − R.
function msv_seir(d)
    τ, σ, γ, η, q = as_parameter(:τ), as_parameter(:σ), as_parameter(:γ), as_parameter(:η), as_parameter(:q_S)
    @variables t TH(t) PS(t) PE(t) PI(t) QI(t) QR(t) E(t) R(t)
    ψ(x) = pgf(d, x)
    ψ1(x) = pgf_derivative(d, x, 1)
    ψ2(x) = pgf_derivative(d, x, 2)
    k̄ = mean_degree(d)
    πS = q * TH * ψ1(TH) / k̄
    πE = 1 - πS - QI - QR
    new = τ * PI * PS * ψ2(TH) / ψ1(TH)
    rhs = Any[-τ * PI,
              -new + η * TH * πS - η * PS,
              new - σ * PE + η * TH * πE - η * PE,
              σ * PE - (τ + γ + η) * PI + η * TH * QI,
              σ * πE - γ * QI,
              γ * QI,
              τ * PI * q * ψ1(TH) - σ * E,
              γ * (1 - q * ψ(TH) - E - R)]
    ode = SymbolicODE(:msv_dfd_seir; states = Any[TH, PS, PE, PI, QI, QR, E, R], rhs, parameters = :infer,
                      domain = Pair{Any,Tuple{Float64,Float64}}[TH => (0.3, 1.0)])
    return ode, (; TH, PS, PE, PI, QI, QR, E, R, ψ, ψ1, k̄, q)
end

# The inclusion of MSV's system as the invariant set {θ = φ_S + Σφ, Σπ = 1, S + Σpop = 1} of the
# lift (φ_S = χ q ψ'(θ)/ψ'(1)): a semiconjugacy MSV → lift (kind :restriction).
function msv_sir_inclusion(sys, d; kw...)
    ode, v = msv_sir(d; kw...)
    c = sys.metadata[:coords]
    q = as_parameter(:q_S)
    map = Pair{Any,Any}[c[:θ] => v.TH, c[:χ] => v.PS * v.k̄ / (q * v.ψ1(v.TH)), c[:φ_I] => v.PI,
                        c[:φ_R] => v.TH - v.PS - v.PI, c[:π_I] => 1 - v.PR - q * v.TH * v.ψ1(v.TH) / v.k̄,
                        c[:π_R] => v.PR, c[:pop_I] => 1 - q * v.ψ(v.TH) - v.R, c[:pop_R] => v.R]
    return Semiconjugacy(:msv_dfd_sir, ode, symbolic_ode(sys), map, Pair{Any,Any}[], :restriction, :exact,
                         [Evidence(:paper, "Miller, Slim & Volz 2012, Part I §3.2 (papers/1106.6320v1.md:210-218)")])
end

function msv_seir_inclusion(sys, d)
    ode, v = msv_seir(d)
    c = sys.metadata[:coords]
    q = v.q
    πS = q * v.TH * v.ψ1(v.TH) / v.k̄
    map = Pair{Any,Any}[c[:θ] => v.TH, c[:χ] => v.PS * v.k̄ / (q * v.ψ1(v.TH)), c[:φ_E] => v.PE,
                        c[:φ_I] => v.PI, c[:φ_R] => v.TH - v.PS - v.PE - v.PI, c[:π_E] => 1 - πS - v.QI - v.QR,
                        c[:π_I] => v.QI, c[:π_R] => v.QR, c[:pop_E] => v.E,
                        c[:pop_I] => 1 - q * v.ψ(v.TH) - v.E - v.R, c[:pop_R] => v.R]
    return Semiconjugacy(:msv_dfd_seir, ode, symbolic_ode(sys), map, Pair{Any,Any}[], :restriction, :exact,
                         Evidence[])
end

# ---------------------------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------------------------

# Conservation along a solution: max_t of |S + Σpop − 1|, |θ − φ_S − Σφ| and |π_S + Σπ − 1|.
function conservation_errors(sys, sol)
    ks = collect(keys(sys.variables))
    pops = [k for k in ks if startswith(string(k), "pop_")]
    φs = [k for k in ks if startswith(string(k), "φ_")]
    πs = [k for k in ks if startswith(string(k), "π_")]
    node = maximum(abs.(curve(sys, sol, :S) .+ sum(curve(sys, sol, k) for k in pops) .- 1))
    edge = maximum(abs.(curve(sys, sol, :θ) .- curve(sys, sol, :φ_S) .- sum(curve(sys, sol, k) for k in φs)))
    stub = maximum(abs.(curve(sys, sol, :π_S) .+ sum(curve(sys, sol, k) for k in πs) .- 1))
    return (; node, edge, stub)
end

# The lift at η = 0 restricted to the coordinates of the static lift (θ, ξ, φ_X, pop_X), with χ = 1.
function static_part(sys)
    raw = symbolic_ode(sys)
    χ = sys.metadata[:coords][:χ]
    keep = [i for (i, n) in enumerate(state_names(raw))
            if n in (:θ, :ξ) || startswith(string(n), "φ_") || startswith(string(n), "pop_")]
    sub(e) = Symbolics.substitute(e, Dict{Any,Any}(χ => 1); fold = Val(true))
    return SymbolicODE(:dfd_at_eta0; states = raw.states[keep], rhs = Any[sub(raw.rhs[i]) for i in keep],
                       parameters = :infer, domain = raw.domain)
end

# The disease-free linearisation of a DFD lift: the Jacobian J of its field at θ = ξ = χ = 1, q = 1,
# every φ, π and pop 0, whose infected block (φ_X, π_X for X infected) decouples from θ and χ there,
# so its spectral abscissa is the early growth rate r; and the next-generation matrix FV⁻¹ on that
# block, with F derived by hand here: a contact r infects along the edges at rate τ_r per φ_{J_r},
# and at the disease-free state its entry into φ_{X_r} is τ_r κ_ex (κ_ex = ψ''(1)/ψ'(1)) and into
# π_{X_r} is τ_r E[k²]/E[k] = τ_r (1 + κ_ex).
function dfe_linearisation(sys, cm, d, p::AbstractDict{Symbol})
    raw = symbolic_ode(sys)
    names = state_names(raw)
    at = Dict{Any,Any}()
    for (x, n) in zip(raw.states, names)
        at[x] = n in (:θ, :ξ, :χ) ? 1.0 : 0.0
    end
    for q in raw.parameters
        n = Symbol(Symbolics.getname(q))
        at[q] = n === :q_S ? 1.0 : p[n]
    end
    J = [numval(Jij, at) for Jij in Symbolics.jacobian(Num.(raw.rhs), Num.(raw.states))]
    inf = sys.metadata[:infected]
    idx = [i for (i, n) in enumerate(names)
           if any(X -> n === Symbol(:φ_, X) || n === Symbol(:π_, X), inf)]
    κex = pgf_derivative(d, 1.0, 2) / mean_degree(d)
    F = zeros(length(idx), length(idx))
    pos(n) = findfirst(i -> names[i] === n, idx)
    for c in contacts(cm)
        τ = c.rate isa Symbol ? p[c.rate] : c.rate
        j = pos(Symbol(:φ_, c.infector))
        F[pos(Symbol(:φ_, c.product)), j] += τ * κex
        F[pos(Symbol(:π_, c.product)), j] += τ * (1 + κex)
    end
    V = F .- J[idx, idx]
    return (; J, R0 = maximum(abs.(eigvals(F / V))), r = maximum(real.(eigvals(J[idx, idx]))))
end

# MSV's closed form (papers/1106.6320v1.md:224): R₀ = τ/(τ + η + γ)·(η/γ + (η + γ)/γ · κ_ex).
msv_R0(τ, γ, η, κex) = τ / (τ + η + γ) * (η / γ + (η + γ) / γ * κex)

# The MFSH ODE with an explicit seed ρ in I (the η → ∞ limit of DFD, MSV Part II §3.2.2 and
# Appendix C.1, with φ_I → θπ_I and π_R = −(γ/τ) ln θ): θ̇ = −τθ + τqθ²ψ'(θ)/ψ'(1) − γθ ln θ,
# Ṙ = γ(1 − qψ(θ) − R), S = qψ(θ). Written out here, independently of any EBM code.
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

# NetworkOutbreaks ensemble of `cm` on `net` (a fresh graph per run, design §J.7), conditioned on a
# major outbreak; `obs` are the compartments recorded (fractions of N on `grid`). Returns the
# retained runs as observables × time matrices and the number of runs.
const BASE = 20260926
function no_ensemble(cm, net, p, initial, grid; N, nsims, obs)
    ens = NO.simulate(cm, net; N, p, initial, tspan = (0.0, grid[end]), nsims, seed = BASE,
                      tgrid = grid)
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

@testset "lift: dynamic fixed degree (neighbour exchange)" begin
    @testset "structure: coordinates, seeds, metadata, the process row" begin
        net = dfd(RegularDegree(6), 1.0)
        sys = edge_based(sir_model(; τ = 1 / 12, γ = 1 / 4), net)
        @test Set(keys(sys.variables)) ==
              Set([:θ, :χ, :φ_I, :φ_R, :π_I, :π_R, :pop_I, :pop_R, :cumulative, :R])
        @test issubset([:S, :I, :infectious, :φ_S, :π_S, :edge_hazard, :excess_hazard], keys(sys.observables))
        md = sys.metadata
        @test md[:kind] === :assembled && md[:closure] === :dynamic && md[:network] == net
        @test Set(keys(md[:seed_params])) == Set([:I, :R])
        table = md[:contributions]
        @test [r.type for r in table] == [:contact, :progress, :process]
        @test table[:neighbour_exchange].type === :process
        # the table's field is the system's field
        @test vector_fields_equal(symbolic_ode(table), symbolic_ode(sys))
        @test vector_fields_equal(symbolic_ode(lift_contributions(sir_model(; τ = 1 / 12, γ = 1 / 4), net)),
                                  symbolic_ode(sys))
        # initial conditions: θ = χ = 1, φ = π = pop = ρ in the seeded class, S(0) = 1 − ρ (E06)
        ic = default_initial_conditions(sys; initial = SeedFraction(:I => 0.01))
        c = md[:coords]
        @test ic[c[:θ]] == 1 && ic[c[:χ]] == 1
        @test ic[c[:φ_I]] == ic[c[:π_I]] == ic[c[:pop_I]] == 0.01
        @test ic[c[:φ_R]] == ic[c[:π_R]] == 0
        sol = solve_epidemic(sys; initial = SeedFraction(:I => 0.01), tspan = (0.0, 100.0), TOL...)
        @test curve(sys, sol, :S)[1] ≈ 0.99 atol = 1e-14
        mc = model_curves(sys, sol; t = 0:1.0:100)
        @test issubset([:S, :I, :R, :infectious, :cumulative], keys(mc.values))
        # a latent class gets its own coordinates and parameters (E07: SEIR is not SIR)
        seir = edge_based(seir_model(), net)
        @test issubset([:φ_E, :π_E, :pop_E], keys(seir.variables))
        @test issubset(Set([:τ, :σ, :γ]), Set(Symbol(Symbolics.getname(x)) for x in symbolic_ode(seir).parameters))
        @test seir.metadata[:entry] === :E
    end

    @testset "the MSV DFD equations (hand transcription) are the invariant set: SIR, SEIR, four ψ" begin
        η = as_parameter(:η)
        for d in (RegularDegree(6), PoissonDegree(3.0), NegBinDegree(4.0, 2 / 3), BIMODAL)
            sys = edge_based(sir_model(), dfd(d, η))
            m = msv_sir_inclusion(sys, d)
            r = verify(m; method = :symbolic)
            @test r.ok
            @test r.method === :symbolic && r.max_residual == 0
            # the legacy defects fail: the printed swap target ψ'(θ)/ψ'(1) (E05) and no seed factor (E06)
            @test !verify(msv_sir_inclusion(sys, d; typo = true)).ok
            @test !verify(msv_sir_inclusion(sys, d; q = false)).ok
        end
        for d in (RegularDegree(6), PoissonDegree(5.0))
            sys = edge_based(seir_model(), dfd(d, η))
            r = verify(msv_seir_inclusion(sys, d); method = :symbolic)
            @test r.ok && r.method === :symbolic
        end
    end

    @testset "η = 0 is the static model (symbolic, and trajectories to 1e-10)" begin
        for cm in (sir_model(), seir_model(), seair_model(), twostrain_model(), sirv_model(),
                   ContactModel(:rem; contacts = [Contact(:S, :I, :I, :τ)], transitions = [NodeTransition(:I, nothing, :γ)])),
            d in (RegularDegree(6), PoissonDegree(5.0), SIR_BIM)
            dyn = edge_based(cm, dfd(d, 0.0))
            st = edge_based(cm, ConfigurationNetwork(d))
            @test vector_fields_equal(static_part(dyn), symbolic_ode(st))
        end
        cases = ((sir_model(; τ = 1 / 6, γ = 1 / 4), SeedFraction(:I => 0.05)),
                 (seir_model(; τ = 1 / 6, σ = 1 / 5, γ = 1 / 4), SeedFraction(:E => 0.01)),
                 (sirv_model(; τ = 1 / 6, γ = 1 / 4, ν = 0.02), SeedFraction(:I => 0.01)))
        for (cm, initial) in cases, d in (RegularDegree(6), PoissonDegree(5.0), SIR_BIM)
            dyn = edge_based(cm, dfd(d, 0.0))
            st = edge_based(cm, ConfigurationNetwork(d))
            grid = 0.0:1.0:150.0
            sd = solve_epidemic(dyn; initial, tspan = (0.0, 150.0), saveat = grid, TOL...)
            ss = solve_epidemic(st; initial, tspan = (0.0, 150.0), saveat = grid, TOL...)
            for X in vcat([:S, :cumulative], [Symbol(:pop_, Y) for Y in species_names(cm) if Y !== :S])
                @test maximum(abs.(curve(dyn, sd, X) .- curve(st, ss, X))) < 1e-10
            end
            @test maximum(abs.(curve(dyn, sd, :χ) .- 1)) < 1e-12
        end
        # E06 regression (static limit at a 5% seed): R∞ = 0.813193 (static EBCM; NE-SSA N = 10⁵, 40
        # runs: 0.81306 ± 0.00036); the legacy dynamic builder gave 0.853361 (S + I + R = 1 + ρ).
        sys = edge_based(sir_model(; τ = 1 / 6, γ = 1 / 4), dfd(PoissonDegree(5.0), 0.0))
        sol = solve_epidemic(sys; initial = SeedFraction(:I => 0.05), tspan = (0.0, 400.0), TOL...)
        @test curve(sys, sol, :cumulative)[end] ≈ 0.813193 atol = 1e-6
    end

    @testset "conservation: θ = φ_S + Σφ, Σπ = 1, S + Σpop = 1 (SIR, SEIR, SEAIR, strains, exits, removals)" begin
        cases = ((sir_model(; τ = 1 / 12, γ = 1 / 4), SeedFraction(:I => 0.01)),
                 (seir_model(; τ = 1 / 6, σ = 1 / 5, γ = 1 / 4), SeedFraction(:E => 0.01)),
                 (seair_model(; τI = 1 / 6, τA = 1 / 12, σ = 1 / 5, p = 0.6, γ = 1 / 4), SeedFraction(:E => 0.01)),
                 (twostrain_model(; τ1 = 1 / 6, τ2 = 1 / 5, γ = 1 / 4), SeedFraction(:I1 => 0.005, :I2 => 0.005)),
                 (sirv_model(; τ = 1 / 6, γ = 1 / 4, ν = 0.02), SeedFraction(:I => 0.01)),
                 (ContactModel(:rem; contacts = [Contact(:S, :I, :I, 1 / 6)], transitions = [NodeTransition(:I, nothing, 1 / 4)]),
                  SeedFraction(:I => 0.01)))
        for (cm, initial) in cases, d in (RegularDegree(6), PoissonDegree(5.0), NegBinDegree(; mean = 4, var = 8)),
            η in (0.3, 3.0)
            sys = edge_based(cm, dfd(d, η))
            sol = solve_epidemic(sys; initial, tspan = (0.0, 150.0), saveat = 0.0:1.0:150.0, TOL...)
            e = conservation_errors(sys, sol)
            @test e.node < 1e-9 && e.edge < 1e-9 && e.stub < 1e-9
            @test all(>=(-1e-12), curve(sys, sol, :χ)) && all(<=(1 + 1e-12), curve(sys, sol, :χ))
        end
    end

    @testset "E05/E06: final sizes of the verified Miller–Slim–Volz DFD references" begin
        # Values of the verifiers' hand-coded MSV DFD ODEs (explicit q = 1 − ρ), each confirmed by an
        # exact neighbour-exchange SSA (VERIFIED_ISSUES.md E05, E06), and what the legacy builder gave.
        refs = [
            # (τ, γ, degrees, η, ρ, DFD R∞, SSA mean ± se, legacy builder)
            (0.6, 1.0, PoissonDegree(3.0), 1.0, 1e-3, 0.473831, (0.47380, 0.00054), 0.501817),
            (1.25, 1.0, NegBinDegree(4.0, 2 / 3), 0.5, 1e-3, 0.473348, (0.47341, 0.00031), 0.497726),
            (1 / 6, 1 / 4, PoissonDegree(5.0), 0.5, 0.01, 0.859871, (0.85999, 0.00015), 0.880127),
            (1 / 6, 1 / 4, PoissonDegree(5.0), 1.0, 0.05, 0.884758, (0.88480, 0.00022), 0.944545),
            (1 / 6, 1 / 4, PoissonDegree(5.0), 1.0, 0.1, 0.892446, (0.89254, 0.00024), 1.004667),
            (1 / 6, 1 / 4, PoissonDegree(5.0), 1.0, 1e-3, 0.876926, (0.87697, 0.00020), 0.883664),
            (1 / 6, 1 / 4, BIMODAL, 1.0, 0.05, 0.834951, (0.83486, 0.00023), 0.892585),
            (1 / 6, 1 / 4, BIMODAL, 1.0, 1e-3, 0.824443, (0.82444, 0.00027), 0.830534),
        ]
        for (τ, γ, d, η, ρ, ref, (ssa, se), legacy) in refs
            sys = edge_based(sir_model(; τ, γ), dfd(d, η))
            sol = solve_epidemic(sys; initial = SeedFraction(:I => ρ), tspan = (0.0, 500.0), TOL...)
            R = curve(sys, sol, :cumulative)[end]
            @test R ≈ ref atol = 2e-6
            @test abs(R - ssa) < 3 * se
            @test abs(legacy - ssa) > 10 * se                      # the legacy value is refuted
            @test 1 - curve(sys, sol, :S)[end] ≈ R atol = 1e-8
            @test curve(sys, sol, :pop_R)[end] ≈ R atol = 1e-6
        end
        # fast mixing: the swap target is M_S = π_S = qθψ'(θ)/ψ'(1), so φ_S → θπ_S (E05: the ratio is
        # 1.00016 with the corrected target, 1.0853 = 1/θ with the printed one)
        sys = edge_based(sir_model(; τ = 0.6, γ = 1.0), dfd(PoissonDegree(3.0), 1000.0))
        sol = solve_epidemic(sys; initial = SeedFraction(:I => 1e-3), tspan = (0.0, 10.0), TOL...)
        θ, φS, πS = (sol(4.0; idxs = v) for v in (sys.variables[:θ], sys.observables[:φ_S], sys.observables[:π_S]))
        @test φS / (θ * πS) ≈ 1 atol = 1e-3
        @test πS ≈ (1 - 1e-3) * θ * exp(3 * (θ - 1)) rtol = 1e-12
    end

    @testset "E07: SEIR is lifted as SEIR (no model silently becomes SIR)" begin
        # E07 scenario: τ = 0.2, σ = 0.5, γ = 0.25, Poisson(5), 0.1% seeded in E. The verifier's and
        # the skeptic's independent DFD-SEIR ODEs give attack / peak I / time of peak 0.8484 / 0.1659 /
        # 32.05 at η = 0 (NO NextReaction 0.8469 ± 0.0006) and 0.8815 / 0.2060 / 26.71 at η = 0.3
        # (exact SSA 0.8812 ± 0.0005 / 0.2073 ± 0.0005 / 26.9 ± 0.2, and 0.8809 ± 0.0006); with γ = 0.1
        # and 0.5 at η = 0.3, 0.9786 and 0.6088 (SSA 0.9784 ± 0.0002 at γ = 0.1). The legacy builder gave
        # 0.5339 at η = 0 and 0.6165 at η = 0.3 for every γ.
        function seir_run(η, γ)
            sys = edge_based(seir_model(; τ = 0.2, σ = 0.5, γ), dfd(PoissonDegree(5.0), η))
            sol = solve_epidemic(sys; initial = SeedFraction(:E => 1e-3), tspan = (0.0, 400.0), saveat = 0.01, TOL...)
            I = curve(sys, sol, :pop_I)
            k = argmax(I)
            return (attack = 1 - curve(sys, sol, :S)[end], peak = I[k], tpeak = sol.t[k])
        end
        a = seir_run(0.0, 0.25)
        @test a.attack ≈ 0.8484 atol = 1e-4
        @test a.peak ≈ 0.1659 atol = 1e-4
        @test a.tpeak ≈ 32.05 atol = 0.01
        b = seir_run(0.3, 0.25)
        @test b.attack ≈ 0.8815 atol = 1e-4
        @test b.peak ≈ 0.2060 atol = 1e-4
        @test b.tpeak ≈ 26.71 atol = 0.01
        @test abs(b.attack - 0.8812) < 3 * 0.0005
        @test seir_run(0.3, 0.1).attack ≈ 0.9786 atol = 1e-4
        @test seir_run(0.3, 0.5).attack ≈ 0.6088 atol = 1e-4
        # an SEIR model and the SIR model with the latent rate as recovery rate (the legacy bug) differ
        sys = edge_based(sir_model(; τ = 0.2, γ = 0.5), dfd(PoissonDegree(5.0), 0.3))
        sol = solve_epidemic(sys; initial = SeedFraction(:I => 1e-3), tspan = (0.0, 400.0), TOL...)
        @test abs(1 - curve(sys, sol, :S)[end] - b.attack) > 0.1
    end

    @testset "R₀ and r of the linearised lift: NetworkEpiCore's engine and MSV's closed form" begin
        for d in (RegularDegree(6), PoissonDegree(5.0), NegBinDegree(; mean = 4, var = 8)), η in (0.1, 1.0, 10.0)
            κex = pgf_derivative(d, 1.0, 2) / mean_degree(d)
            p = Dict(:τ => 1 / 12, :γ => 1 / 4)
            net = dfd(d, η)
            lin = dfe_linearisation(edge_based(sir_model(), net), sir_model(), d, p)
            @test lin.R0 ≈ msv_R0(1 / 12, 1 / 4, η, κex) rtol = 1e-10
            @test lin.R0 ≈ basic_reproduction_number(sir_model(), net, p) rtol = 1e-10
            @test lin.r ≈ early_growth_rate(sir_model(), net, p) rtol = 1e-8
        end
        # the canonical sweep :sir_ne_reg6_eta{01,1,10} (R₀ = 1.4231, 1.8125, 1.9758; WP11/WP12)
        for (η, R0) in ((0.1, 1.4230769230769231), (1.0, 1.8125), (10.0, 1.9758064516129032))
            lin = dfe_linearisation(edge_based(sir_model(), dfd(RegularDegree(6), η)), sir_model(),
                                    RegularDegree(6), Dict(:τ => 1 / 12, :γ => 1 / 4))
            @test lin.R0 ≈ R0 rtol = 1e-12
        end
        # SEIR and SEAIR (branching, two infectors) against the engine
        for (cm, p) in ((seir_model(), Dict(:τ => 1 / 6, :σ => 1 / 5, :γ => 1 / 4)),
                        (seair_model(), Dict(:τI => 1 / 6, :τA => 1 / 12, :σ => 1 / 5, :p => 0.6, :γ => 1 / 4))),
            d in (PoissonDegree(5.0), SIR_BIM), η in (0.1, 1.0)
            net = dfd(d, η)
            lin = dfe_linearisation(edge_based(cm, net), cm, d, p)
            @test lin.R0 ≈ basic_reproduction_number(cm, net, p) rtol = 1e-10
            @test lin.r ≈ early_growth_rate(cm, net, p) rtol = 1e-8
        end
    end

    @testset "Λ3 on a Regular(6) base: the error against mass_action(cm; κ = 6) decreases in η" begin
        # :sir_ne_reg6_eta* parameters (τ = 1/12, γ = 1/4, 1% seeded). Mass action is taken through the
        # well-mixed unit M1 (verified here): edge_based(cm, WellMixed(6)) is conjugate to
        # mass_action(cm; κ = 6), MA(1/2, 1/4) = :sir_wm5 with R∞ = 0.8002.
        cm = sir_model(; τ = 1 / 12, γ = 1 / 4)
        grid = collect(0.0:0.25:100.0)
        wm = edge_based(cm, WellMixed(6.0))
        @test verify(EBM._well_mixed_unit(wm)).ok
        swm = solve_epidemic(wm; initial = SeedFraction(:I => 0.01), tspan = (0.0, 100.0), saveat = grid, TOL...)
        ma = sir_curves(wm, swm)
        errs = Float64[]
        for η in (0.0, 0.1, 1.0, 10.0, 100.0, 1000.0)
            sys = edge_based(cm, dfd(RegularDegree(6), η))
            sol = solve_epidemic(sys; initial = SeedFraction(:I => 0.01), tspan = (0.0, 100.0), saveat = grid, TOL...)
            push!(errs, maximum(abs.(sir_curves(sys, sol) .- ma)))
        end
        @info "WP21 Λ3, Regular(6): max |DFD − MA(6τ)| for η = 0, 0.1, 1, 10, 100, 1000" errs
        @test issorted(errs; rev = true) && allunique(errs)
        @test errs[end] < 1e-3                                   # O(1/η): 2.1e-3 at η = 100, 2.1e-4 at 1000
        @test errs[end - 1] / errs[end] > 5
    end

    @testset "Λ3 on a Poisson(5) base: the model approaches MFSH, not mass action" begin
        # Design §D.5 Λ3: with τ = 1/6, γ = 1/4 the η → ∞ limit is MFSH with the base's degrees
        # (R₀ = τE[k²]/(γE[k]) = 4, attack rate 0.905), not MA(5τ) (R₀ = 3.33, attack rate 0.960).
        τ, γ, ρ = 1 / 6, 1 / 4, 0.01
        cm = sir_model(; τ, γ)
        grid = collect(0.0:0.25:100.0)
        mf = mfsh_curves(PoissonDegree(5.0), τ, γ, ρ, grid)
        wm = edge_based(cm, WellMixed(5.0))
        swm = solve_epidemic(wm; initial = SeedFraction(:I => ρ), tspan = (0.0, 100.0), saveat = grid, TOL...)
        ma = sir_curves(wm, swm)
        @test mf[end, 3] ≈ 0.905 atol = 1e-3
        @test ma[end, 3] ≈ 0.960 atol = 1e-3
        dmf, dma = Float64[], Float64[]
        for η in (1.0, 10.0, 100.0, 1000.0)
            sys = edge_based(cm, dfd(PoissonDegree(5.0), η))
            sol = solve_epidemic(sys; initial = SeedFraction(:I => ρ), tspan = (0.0, 100.0), saveat = grid, TOL...)
            x = sir_curves(sys, sol)
            push!(dmf, maximum(abs.(x .- mf)))
            push!(dma, maximum(abs.(x .- ma)))
        end
        @info "WP21 Λ3, Poisson(5): max |DFD − MFSH| and max |DFD − MA(5τ)| for η = 1, 10, 100, 1000" dmf dma
        @test issorted(dmf; rev = true) && allunique(dmf)
        @test dmf[end] < 1e-3                                    # O(1/η): 3.1e-4 at η = 1000
        @test all(>(0.08), dma)                                  # MA stays ≈ 0.12 away
        @test dma[end] ≈ maximum(abs.(mf .- ma)) atol = 2e-3
    end

    @testset "symbolic η, Symbol rates, and the process table under an injective relabel" begin
        η = as_parameter(:η)
        sym = edge_based(sir_model(), dfd(RegularDegree(6), η))
        num = edge_based(sir_model(; τ = 1 / 12, γ = 1 / 4), dfd(RegularDegree(6), 1.0))
        grid = 0.0:1.0:100.0
        s1 = solve_epidemic(sym; p = Dict(:τ => 1 / 12, :γ => 1 / 4, :η => 1.0), initial = SeedFraction(:I => 0.01),
                            tspan = (0.0, 100.0), saveat = grid, TOL...)
        s2 = solve_epidemic(num; initial = SeedFraction(:I => 0.01), tspan = (0.0, 100.0), saveat = grid, TOL...)
        @test maximum(abs.(curve(sym, s1, :pop_I) .- curve(num, s2, :pop_I))) < 1e-10
        @test curve(num, s2, :cumulative)[end] ≈ 0.74694 atol = 1e-4   # NO's DFD reference for :sir_ne_reg6_eta1
        # pushing a table along an injective species map is the lift of the relabelled model
        net = dfd(PoissonDegree(5.0), 1.0)
        f = Dict(:I => :J, :R => :Z)
        @test vector_fields_equal(symbolic_ode(relabel(lift_contributions(seir_model(), net), f)),
                                  symbolic_ode(edge_based(relabel(seir_model(), f), net)))
    end

    @testset "gluing: the reaction rows add, the exchange acts once (H1 with the process as a component)" begin
        net = dfd(PoissonDegree(5.0), 1.0)
        tr = open_model(ContactModel(:tr; contacts = [Contact(:S, :I, :E, :τ)]); legs = [[:S], [:E, :I]])
        pr = open_model(ContactModel(:pr; transitions = [NodeTransition(:E, :I, :σ), NodeTransition(:I, :R, :γ)]);
                        legs = [[:E, :I, :R]])
        glued = symbolic_ode(edge_based(glue(tr, pr; on = [:E, :I]), net))
        ta, tb = lift_contributions(tr, net), lift_contributions(pr, net)
        @test count(r -> r.type === :process, ta) == 1               # the part with θ carries the process
        @test count(r -> r.type === :process, tb) == 0               # a part without θ has none
        reactions(t) = LiftContributions(t.name, t.network, t.closure, t.coordinates, t.seed_factors,
                                         filter(r -> r.type !== :process, t.contributions), t.coordinate_info)
        s = sum_contributions(reactions(ta), reactions(tb))
        row = EBM._process_row(net, s.closure, s.coordinate_info)
        @test row isa ReactionContribution && row.type === :process
        whole = LiftContributions(s.name, s.network, s.closure, s.coordinates, s.seed_factors,
                                  vcat(s.contributions, row), s.coordinate_info)
        @test vector_fields_equal(symbolic_ode(whole), glued)
        # sum_contributions keeps exactly one process row, so the sum of the parts is the lift of the
        # gluing (H1 with the process as a component)
        @test vector_fields_equal(symbolic_ode(sum_contributions(ta, tb)), glued)
        @test EBM._process_row(ConfigurationNetwork(PoissonDegree(5.0)), :configuration, s.coordinate_info) === nothing
    end

    @testset "errors: inadmissible models, forms, other processes" begin
        net = dfd(RegularDegree(6), 1.0)
        @test_throws AdmissibilityError edge_based(sis_model(), net)
        @test_throws AdmissibilityError edge_based(sirs_model(), net)
        err = try edge_based(sir_model(), net; form = :compact) catch e e end
        @test err isa ArgumentError && occursin("only the expanded form", sprint(showerror, err))
        # DormantContacts is lifted by its own method (src/lift/dormant.jl, WP36b), not refused
        @test edge_based(sir_model(), DynamicNetwork(RegularDegree(6), DormantContacts(1.0, 0.5))) isa EdgeModelSystem
        # a parameter named like a generated coordinate is refused (E26)
        bad = ContactModel(:bad; contacts = [Contact(:S, :I, :I, :χ)], transitions = [NodeTransition(:I, :R, :γ)])
        @test_throws ArgumentError edge_based(bad, net)
    end

    @testset "against NetworkOutbreaks' neighbour-exchange process: :sir_ne_reg6_eta01 and _eta1, N = 5000" begin
        # Acceptance: D∞ < 0.01 at η ∈ {0.1, 1}. Observables S, I, R; 100 runs each (the scenarios'
        # nsims), fresh 6-regular graph per run.
        N = 5000
        for (id, η) in ((:sir_ne_reg6_eta01, 0.1), (:sir_ne_reg6_eta1, 1.0))
            sc = scenario(id)
            @test sc.network == dfd(RegularDegree(6), η)
            grid = collect(0.0:1.0:100.0)
            sys = edge_based(sc)
            sol = solve_epidemic(sys; p = sc.params, initial = sc.initial, tspan = (0.0, 100.0), saveat = grid, TOL...)
            eb = permutedims(sir_curves(sys, sol))
            runs, n = no_ensemble(sc.model, sc.network, sc.params, sc.initial, grid; N, nsims = 100, obs = [:S, :I, :R])
            @test length(runs) >= n - 2
            dd = discrepancy(eb, runs)
            fs = [r[3, end] for r in runs]
            seR = std(fs) / sqrt(length(fs))
            @info "WP21 DFD vs NetworkOutbreaks" scenario = id η N runs = n major = length(runs) D∞ = dd.D se_at_max = dd.se z∞ = dd.D / dd.se observable = (:S, :I, :R)[dd.at[1]] t = grid[dd.at[2]] R∞_EB = eb[3, end] R∞_sim = mean(fs) se_R∞ = seR
            @test dd.D < 0.01
            @test dd.D / dd.se < 4                                   # within Monte Carlo error
            @test abs(eb[3, end] - mean(fs)) < max(0.005, 3 * seR)
        end
    end

    @testset "against NetworkOutbreaks: SEIR, SEAIR and SIR + vaccination on Poisson(5), η = 1, N = 5000" begin
        # The general T_EB lift (latency, branching with two infectors, an exit out of S), 60 runs each,
        # with 5% seeded (ρN = 250). With 1% seeded (ρN = 50) at N = 5000 the slow SEIR epidemics
        # carry a finite-size bias of the mean: random early time shifts of variance O(1/(ρN)) bias
        # the mean of steep curves at O(1/(ρN)), and WP21 measured D∞ = 0.021 (SE 0.008) for SEIR and
        # 0.014 (SE 0.007) for SEAIR there, but 0.0055 (SE 0.004) and 0.0038 (SE 0.004) at N = 2×10⁴
        # with 1% seeded (40 runs), and 0.0036 and 0.0016 at N = 5000 with 5% seeded: the discrepancy
        # vanishes as ρN grows, as for an exact limit.
        N = 5000
        net = dfd(PoissonDegree(5), 1.0)
        cases = ((seir_model(), Dict(:τ => 1 / 6, :σ => 1 / 5, :γ => 1 / 4), SeedFraction(:E => 0.05), 150.0,
                  [:S, :E, :I, :R]),
                 (seair_model(), Dict(:τI => 1 / 6, :τA => 1 / 12, :σ => 1 / 5, :p => 0.6, :γ => 1 / 4),
                  SeedFraction(:E => 0.05), 200.0, [:S, :E, :A, :I, :R]),
                 (sirv_model(), Dict(:τ => 1 / 6, :γ => 1 / 4, :ν => 0.02), SeedFraction(:I => 0.05), 60.0,
                  [:S, :I, :R, :V]))
        for (cm, p, initial, T, obs) in cases
            grid = collect(0.0:1.0:T)
            sys = edge_based(cm, net)
            sol = solve_epidemic(sys; p, initial, tspan = (0.0, T), saveat = grid, TOL...)
            eb = permutedims(reduce(hcat, [X === :S ? curve(sys, sol, :S) : curve(sys, sol, Symbol(:pop_, X)) for X in obs]))
            runs, n = no_ensemble(cm, net, p, initial, grid; N, nsims = 60, obs)
            @test length(runs) >= n - 2
            dd = discrepancy(eb, runs)
            @info "WP21 DFD vs NetworkOutbreaks" model = cm.name η = 1.0 N runs = n major = length(runs) D∞ = dd.D se_at_max = dd.se z∞ = dd.D / dd.se observable = obs[dd.at[1]] t = grid[dd.at[2]]
            @test dd.D < 0.01
            @test dd.D / dd.se < 4
        end
    end
end
