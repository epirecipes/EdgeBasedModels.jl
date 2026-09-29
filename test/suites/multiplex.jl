# WP22: the multiplex edge-based lift through the per-reaction assembler (DESIGN §C.2, §C.3, §D.4,
# §D.6 H6, §G.2 WP22; verified issues E12 and E13).
#
# Every expected value comes from an independent computation:
# - the single-layer configuration lift (6-regular for two 3-regular layers; any one layer);
# - Miller & Volz (2013, PLoS ONE 8:e69162) eq. (13) for their three-mode example of §2.2.4, and
#   Jacobsen, Burch, Tien & Rempała (2018, J. Biol. Dyn. 12:746–788) eq. (13) with the seed
#   α_S = 1 − ρ, both transcribed by hand below as plain Float64 ODEs;
# - NetworkEpiCore's next-generation matrix over (layer, entry) blocks, its growth rate and its
#   final-size fixed point, the closed-form 2 × 2 spectral radius, and the NGM of the lifted ODE
#   linearised at the disease-free state (R₀ = ρ(K), E12);
# - exact stochastic simulation (NetworkOutbreaks, NextReaction) on the canonical scenario
#   :sir_mpx: N = 10⁴, 200 runs, a fresh multiplex graph per run, stable_rng streams, runs
#   conditioned on a major outbreak (DESIGN §E.2, §J.7).

using EdgeBasedModels
using NetworkEpiCore
using ModelingToolkit
using Symbolics
using LinearAlgebra
using Statistics
using Test
import OrdinaryDiffEq
using OrdinaryDiffEq: Vern9

import NetworkOutbreaks as NO

const EBM = EdgeBasedModels
const TOL = (solver = Vern9(), reltol = 1e-12, abstol = 1e-14)

curve(sys, sol, X) = compartment(sys, sol, X)
maxdiff(a, b) = maximum(abs.(a .- b))

# SIR with one contact S + I → 2I per layer (`ℓ => τ`; `:all` acts on every layer).
layered_sir(τs::Pair...; γ = 1 / 4, name = :layered_sir) =
    ContactModel(name; contacts = [Contact(:S, :I, :I, τ; layer = ℓ) for (ℓ, τ) in τs],
                 transitions = [NodeTransition(:I, :R, γ)])

solve_mpx(sys; ρ = 0.01, T = 80.0, saveat = 1.0, X = :I) =
    solve_epidemic(sys; initial = SeedFraction(X => ρ), tspan = (0.0, T), saveat, TOL...)

# Node conservation S + Σ pop − 1 and, on every layer ℓ, edge conservation θ_ℓ − φ_S_ℓ − Σ_X φ_X_ℓ.
function conservation_errors(sys, sol, layers)
    pops = [k for k in keys(sys.variables) if startswith(string(k), "pop_")]
    node = maximum(abs.(curve(sys, sol, :S) .+ sum(curve(sys, sol, k) for k in pops) .- 1))
    edge = 0.0
    for ℓ in layers
        φs = [k for k in keys(sys.variables) if startswith(string(k), "φ_") && endswith(string(k), "_$(ℓ)")]
        e = curve(sys, sol, Symbol(:θ_, ℓ)) .- curve(sys, sol, Symbol(:φ_S_, ℓ)) .- sum(curve(sys, sol, k) for k in φs)
        edge = max(edge, maximum(abs.(e)))
    end
    return node, edge
end

# The next-generation matrix of the lifted SIR ODE at the disease-free state (θ = 1, φ = 0,
# q = 1): its φ_I block is F − V with V = diag(τ_ℓ + γ) (the φ_{I,ℓ} losses: transmission along
# the edge and recovery of the partner), so R₀ = ρ(F V⁻¹); the growth rate is the leading
# eigenvalue of the block.
function lifted_ngm(sys, γ, τ::AbstractDict)
    raw = symbolic_ode(sys)
    names = [Symbol(Symbolics.getname(x)) for x in raw.states]
    idx = [i for (i, n) in enumerate(names) if startswith(string(n), "φ_I_")]
    dfe = Dict{Any,Any}(x => (startswith(string(n), "θ") || n === :ξ ? 1.0 : 0.0)
                        for (x, n) in zip(raw.states, names))
    for p in raw.parameters
        Symbolics.getname(p) === :q_S && (dfe[p] = 1.0)
    end
    J = Symbolics.jacobian(raw.rhs[idx], raw.states[idx])
    Jn = Float64[Float64(Symbolics.value(Symbolics.substitute(J[i, j], dfe; fold = Val(true))))
                 for i in axes(J, 1), j in axes(J, 2)]
    lays = [Symbol(replace(string(names[i]), "φ_I_" => "")) for i in idx]
    V = Diagonal([τ[ℓ] + γ for ℓ in lays])
    return maximum(abs, eigvals((Jn + V) * inv(V))), maximum(real, eigvals(Jn))
end

reg3() = polynomial_pgf([0.0, 0.0, 0.0, 1.0])

@testset "WP22: multiplex edge-based lift" begin
    @testset "acceptance 1: two identical 3-regular layers = the 6-regular network (1e-10)" begin
        τ, γ = 1 / 6, 1 / 4
        mpx = MultiplexNetwork(:a => RegularDegree(3), :b => RegularDegree(3))
        reg6 = ConfigurationNetwork(RegularDegree(6))
        s6 = edge_based(sir_model(; τ, γ), reg6)
        b = solve_mpx(s6)
        for (label, cm) in (("one contact per layer", layered_sir(:a => τ, :b => τ; γ)),
                            ("one contact on :all", layered_sir(:all => τ; γ)))
            sys = edge_based(cm, mpx)
            a = solve_mpx(sys)
            for X in (:S, :pop_I, :pop_R, :cumulative, :I)
                @test maxdiff(curve(sys, a, X), curve(s6, b, X)) < 1e-10
            end
            for ℓ in (:a, :b)      # by symmetry θ_ℓ = θ and φ_I_ℓ = φ_I of the 6-regular lift
                @test maxdiff(curve(sys, a, Symbol(:θ_, ℓ)), curve(s6, b, :θ)) < 1e-10
                @test maxdiff(curve(sys, a, Symbol(:φ_I_, ℓ)), curve(s6, b, :φ_I)) < 1e-10
                @test maxdiff(curve(sys, a, Symbol(:φ_S_, ℓ)), curve(s6, b, :φ_S)) < 1e-10
            end
            # the compact form (Jacobsen et al. eq. (13)) too
            sc = edge_based(cm, mpx; form = :compact)
            c = solve_mpx(sc)
            @test maxdiff(curve(sc, c, :S), curve(s6, b, :S)) < 1e-10
            @test maxdiff(curve(sc, c, :R), curve(s6, b, :R)) < 1e-10
        end
        # the factory, legacy PGFs through the 0.1 tuple form, and SEIR with layered contacts
        f = build_multiplex_sir([(:a, reg3(), τ, γ), (:b, reg3(), τ, γ)])
        @test maxdiff(curve(f, solve_mpx(f), :S), curve(s6, b, :S)) < 1e-10
        seir = ContactModel(:seir_mpx; contacts = [Contact(:S, :I, :E, τ; layer = :a), Contact(:S, :I, :E, τ; layer = :b)],
                            transitions = [NodeTransition(:E, :I, 1 / 5), NodeTransition(:I, :R, γ)])
        se = edge_based(seir, mpx)
        se6 = edge_based(seir_model(; τ, σ = 1 / 5, γ), reg6)
        x, y = solve_mpx(se; X = :E, T = 150.0), solve_mpx(se6; X = :E, T = 150.0)
        for X in (:S, :pop_E, :pop_I, :pop_R, :cumulative)
            @test maxdiff(curve(se, x, X), curve(se6, y, X)) < 1e-10
        end
    end

    @testset "acceptance 2a: conservation on every layer (exits, removals, branching, :all)" begin
        net3 = MultiplexNetwork(:home => RegularDegree(3), :comm => PoissonDegree(5),
                                :work => NegBinDegree(; mean = 4, var = 8))
        cases = [
            ("SIR on three layers", layered_sir(:home => 0.2, :comm => 0.05, :work => 0.1), :I, 80.0),
            ("SIR + vaccination (exit)",
             ContactModel(:sirv; contacts = [Contact(:S, :I, :I, 0.2; layer = :home), Contact(:S, :I, :I, 0.05)],
                          transitions = [NodeTransition(:I, :R, 0.25), NodeTransition(:S, :V, 0.02)]), :I, 80.0),
            ("SIR with a removal I → ∅ (sink)",
             ContactModel(:sir0; contacts = [Contact(:S, :I, :I, 0.2; layer = :home), Contact(:S, :I, :I, 0.08; layer = :work)],
                          transitions = [NodeTransition(:I, nothing, 0.25)]), :I, 80.0),
            ("SEAIR: branching, two infectors on different layers",
             ContactModel(:seair; contacts = [Contact(:S, :I, :E, 0.15; layer = :home), Contact(:S, :A, :E, 0.05),
                                              Contact(:S, :I, :E, 0.04; layer = :comm)],
                          transitions = [NodeTransition(:E, :I, 0.6 * 0.2), NodeTransition(:E, :A, 0.4 * 0.2),
                                         NodeTransition(:I, :R, 0.25), NodeTransition(:A, :R, 0.25)]), :E, 200.0),
        ]
        for (label, cm, X, T) in cases
            sys = edge_based(cm, net3)
            sol = solve_mpx(sys; X, T)
            node, edge = conservation_errors(sys, sol, layer_names(net3))
            @test node < 1e-10
            @test edge < 1e-10
            for ℓ in layer_names(net3)         # θ_ℓ never increases (E13: it did in 0.1)
                @test all(diff(curve(sys, sol, Symbol(:θ_, ℓ))) .<= 1e-13)
            end
            @test curve(sys, sol, :S)[1] ≈ 0.99
            # the lifted final size agrees with NetworkEpiCore's fixed point where it has one
            if label == "SIR on three layers"
                long = solve_mpx(sys; T = 2000.0, saveat = 2000.0)
                @test curve(sys, long, :cumulative)[end] ≈
                      final_size(cm, net3, Dict{Symbol,Float64}(); initial = SeedFraction(:I => 0.01)) atol = 1e-8
            end
        end
        # the exit is lifted with the survival factor ξ: V gains from the edge-S of every layer
        sirv = cases[2][2]
        sys = edge_based(sirv, net3)
        @test haskey(sys.variables, :ξ) && haskey(sys.variables, :pop_V)
        @test all(haskey(sys.variables, Symbol(:φ_V_, ℓ)) for ℓ in layer_names(net3))
        @test haskey(edge_based(cases[3][2], net3).variables, :pop_removed)
    end

    @testset "acceptance 2b: R₀ = ρ(K), not the sum of the layer R₀s (E12)" begin
        # E12 regression (verified issue, corrected fix): two 3-regular layers at T = 0.22, γ = 1
        γ, T = 1.0, 0.22
        β = T * γ / (1 - T)
        r3 = reg3()
        layers = [(:a, r3, β, γ), (:b, r3, β, γ)]
        @test multiplex_R0(layers) ≈ 5T                     # 0.1 gave 4T = 0.88
        @test multiplex_R0(layers) > 1
        @test basic_reproduction_number(layers) ≈ 5T
        # the multiplex ODE equals the single 6-regular layer (guards the equivalence)
        m = build_multiplex_sir(layers)
        sol = solve_epidemic(m; initial = SeedFraction(:I => 1e-6), tspan = (0.0, 4000.0), saveat = 4000.0, TOL...)
        r6 = polynomial_pgf([0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1.0])
        @test curve(m, sol, :cumulative)[end] ≈
              final_size(sir_model(; τ = β, γ), ConfigurationNetwork(RegularDegree(6)), Dict{Symbol,Float64}()) atol = 1e-4
        @test curve(m, sol, :cumulative)[end] ≈ 0.254041 atol = 1e-4        # E12 verifier and skeptic
        # 4-regular + 3-regular at T = 0.3: ρ([[0.9, 0.9], [1.2, 0.6]]) = 1.8 (the sum gives 1.5)
        β3 = 0.3 / 0.7
        @test multiplex_R0([(:a, polynomial_pgf([0, 0, 0, 0, 1.0]), β3, 1.0), (:b, r3, β3, 1.0)]) ≈ 1.8
        # over-dispersed layers: the sum over-states R₀ (1.05); the true value is 0.925
        bim = polynomial_pgf([0, 0.5, 0, 0, 0, 0, 0, 0.5])
        @test multiplex_R0([(:a, bim, 0.1 / 0.9, 1.0), (:b, bim, 0.1 / 0.9, 1.0)]) ≈ 0.925
        # Poisson layers: ρ(K) equals the sum (det K = 0), as in 0.1
        @test multiplex_R0([(:home, poisson_pgf(3.0), 0.3, 0.1), (:work, poisson_pgf(2.0), 0.2, 0.1)]) ≈ 0.75 * 3 + (2 / 3) * 2
        # a heterogeneous-T case of the E12 skeptic: 0.1 gave exactly 1.000, ρ(K) = 1.1782
        @test multiplex_R0([(:a, r3, 0.3 / 0.7, 1.0), (:b, polynomial_pgf([0, 0, 0, 0, 0, 1.0]), 0.1 / 0.9, 1.0)]) ≈ 1.1782 atol = 1e-4
        # symbolic rates: the two-layer closed form (0.1 accepted symbolic β; the corrected fix keeps it)
        @parameters βs
        Rsym = multiplex_R0([(:a, r3, βs, γ), (:b, r3, βs, γ)])
        @test Rsym isa Symbolics.Num
        @test Symbolics.value(Symbolics.substitute(Rsym, Dict(βs => β); fold = Val(true))) ≈ 5T
        @test_throws ArgumentError multiplex_R0([(:a, r3, βs, γ), (:b, r3, βs, γ), (:c, r3, βs, γ)])
        @test_throws ArgumentError multiplex_R0([(:a, r3, 0.1, 1.0), (:b, r3, 0.1, 0.5)])      # one γ

        # NetworkEpiCore's (layer, entry) NGM, the closed form, and the NGM of the lifted ODE
        net = MultiplexNetwork(:home => RegularDegree(3), :comm => PoissonDegree(5))
        τh, τc, γ2 = 0.15, 0.05, 1 / 4
        cm = layered_sir(:home => τh, :comm => τc; γ = γ2)
        Th, Tc = τh / (τh + γ2), τc / (τc + γ2)
        K = [Th * 2 Th * 5; Tc * 3 Tc * 5]              # K_ii = T_iψ_i''(1)/ψ_i'(1), K_ij = T_iψ_j'(1)
        ρK = (K[1, 1] + K[2, 2]) / 2 + sqrt(((K[1, 1] - K[2, 2]) / 2)^2 + K[1, 2] * K[2, 1])
        @test basic_reproduction_number(cm, net, Dict{Symbol,Float64}()) ≈ ρK rtol = 1e-12
        @test multiplex_R0([(:home, reg3(), τh, γ2), (:comm, poisson_pgf(5.0), τc, γ2)]) ≈ ρK rtol = 1e-12
        @test ρK > Th * 2 + Tc * 5 + 0.1                  # the 0.1 sum (1.5833) is far off (1.7608)
        R0lift, λlift = lifted_ngm(edge_based(cm, net), γ2, Dict(:home => τh, :comm => τc))
        @test R0lift ≈ ρK rtol = 1e-10
        @test λlift ≈ early_growth_rate(cm, net, Dict{Symbol,Float64}()) rtol = 1e-10
        # three layers, one of them negative binomial, and a contact on :all
        net3 = MultiplexNetwork(:home => RegularDegree(3), :comm => PoissonDegree(5),
                                :work => NegBinDegree(; mean = 4, var = 8))
        cm3 = ContactModel(:three; contacts = [Contact(:S, :I, :I, 0.12; layer = :home), Contact(:S, :I, :I, 0.03),
                                               Contact(:S, :I, :I, 0.05; layer = :work)],
                           transitions = [NodeTransition(:I, :R, γ2)])
        R0l3, λl3 = lifted_ngm(edge_based(cm3, net3), γ2, Dict(:home => 0.15, :comm => 0.03, :work => 0.08))
        @test R0l3 ≈ basic_reproduction_number(cm3, net3, Dict{Symbol,Float64}()) rtol = 1e-10
        @test λl3 ≈ early_growth_rate(cm3, net3, Dict{Symbol,Float64}()) rtol = 1e-10

        # the threshold of the lifted ODE sits at ρ(K) = 1, not at the sum = 1 (E12 verifier)
        for (Tb, major) in ((0.10, false), (0.13, true))       # ρ(K) = 0.925 and 1.2025; sums 1.05 and 1.365
            βb = Tb / (1 - Tb)
            lb = [(:a, bim, βb, 1.0), (:b, bim, βb, 1.0)]
            mb = build_multiplex_sir(lb)
            sb = solve_epidemic(mb; initial = SeedFraction(:I => 1e-6), tspan = (0.0, 4000.0), saveat = 4000.0, TOL...)
            zb = curve(mb, sb, :cumulative)[end]
            cmb, netb = mb.metadata[:model], mb.metadata[:network]
            λb = early_growth_rate(cmb, netb, Dict{Symbol,Float64}())
            @test (λb > 0) == major == (multiplex_R0(lb) > 1)
            @test (2 * Tb * (0.5 * 42) / 4 > 1)                # the additive R₀ claims an epidemic in both
            if major
                @test zb ≈ 0.2647 atol = 5e-4                   # E12: 36 major SSA runs, mean 0.2655 ± 0.0015
                @test zb ≈ final_size(cmb, netb, Dict{Symbol,Float64}()) atol = 1e-4
            else
                @test zb < 1e-4                                 # only the seeds' chains: ≈ 1e-6/(1 − 0.925)
                @test final_size(cmb, netb, Dict{Symbol,Float64}()) == 0
            end
        end

        # the canonical scenario is calibrated to ρ(K) = 2; the additive R₀ would be 1.80
        sc = scenario(:sir_mpx)
        c = sc.params[:c]
        tuples = [(:home, RegularDegree(3), 3c, sc.params[:γ]), (:comm, PoissonDegree(5), c, sc.params[:γ])]
        @test multiplex_R0(tuples) ≈ 2 rtol = 1e-8
        @test sc.expected[:R0_additive] < 1.85
    end

    @testset "acceptance 3: D∞ < 0.005 against NetworkOutbreaks on :sir_mpx" begin
        sc = scenario(:sir_mpx)
        cfg = sc.sim
        N, runs, base = cfg.N, cfg.nsims, Int(cfg.base_seed)
        @test (N, runs, cfg.graphs, cfg.algorithm) == (10_000, 200, :per_run, :next_reaction)
        grid = collect(sc.tgrid)
        sys = edge_based(sc)
        sol = solve_epidemic(sys, sc; TOL...)
        eb = permutedims(hcat(curve(sys, sol, :S), curve(sys, sol, :pop_I), curve(sys, sol, :pop_R)))
        γ, c = sc.params[:γ], sc.params[:c]
        ρ = only(last.(seed_fractions(sc.initial)))
        nseed = round(Int, ρ * N)
        # NetworkOutbreaks' OutbreakModel(cm) does not take named-layer contacts yet, so the
        # (layer × contact) rates τ_home = 3c, τ_comm = c are the layer weights of the sampled
        # MultiplexGraph with a unit contact rate: the same Markov process for this model (one
        # contact S + I → 2I per layer).
        model = NO.OutbreakModel([:S, :I, :R], [false, true, false],
                                 [NO.OutbreakTransition(:S, :I, 1.0, :infection; via = [:I]),
                                  NO.OutbreakTransition(:I, :R, γ, :spontaneous)])
        weights = Dict(:home => 3c, :comm => c)
        curves = Matrix{Float64}[]
        finals = Float64[]
        for r in 1:runs
            g, _ = NO.sample_graph(sc.network, N; rng = NO.stable_rng(base + r))           # fresh graph per run
            mg = NO.MultiplexGraph(g.layers, [weights[ℓ] for ℓ in layer_names(sc.network)])
            spec = NO.OutbreakSpec(; model, network = mg, initial = NO.SeedFraction(:I => ρ), tspan = (0.0, grid[end]))
            traj = NO.simulate(spec; algorithm = NO.NextReaction(), rng = NO.stable_rng(base + 2^32 + r))
            fin = NO.state_at(traj, grid[end])
            fin[2] + fin[3] - nseed >= cfg.condition.threshold * N || continue          # MajorOutbreak(0.05)
            push!(curves, reduce(hcat, [Float64.(NO.state_at(traj, t)[1:3]) ./ N for t in grid]))
            push!(finals, (fin[2] + fin[3]) / N)
        end
        all_runs = cat(curves...; dims = 3)
        μ = dropdims(mean(all_runs; dims = 3); dims = 3)
        se = dropdims(std(all_runs; dims = 3); dims = 3) ./ sqrt(length(curves))
        dI, kI = findmax(abs.(eb[2, :] .- μ[2, :]))
        dall, kall = findmax(abs.(eb .- μ))
        ΔR = curve(sys, sol, :cumulative)[end] - mean(finals)
        seR = std(finals) / sqrt(length(finals))
        @info "WP22 multiplex lift vs NetworkOutbreaks (:sir_mpx)" N runs major = length(curves) D∞_I = dI t_at = grid[kI] se_I_at = se[2, kI] D∞_SIR = dall se_at = se[kall] ΔR∞ = ΔR se_R∞ = seR
        @test length(curves) >= runs - 2                # P(major) ≈ 1 with ρN = 100 seeds
        @test dI < 0.005                                 # DESIGN §E.2 :exact_limit tolerances
        @test abs(ΔR) < 0.005
        @test dall < 0.01
    end

    @testset "acceptance 4: build_multiplex_sir returns an EdgeModelSystem (E13)" begin
        pA, pB = poisson_pgf(3.0), reg3()                       # Poisson(3) ⊗ 3-regular
        layers = [(:A, pA, 0.15, 0.1), (:B, pB, 0.10, 0.1)]
        @test Base.Docs.hasdoc(EdgeBasedModels, :build_multiplex_sir)
        doc = string(Base.Docs.doc(build_multiplex_sir))
        @test occursin("Rempała", doc) && occursin("Miller & Volz", doc) && !occursin("Burch, Miller", doc)
        # the 0.1 docstring that sat on a helper of src/multiplex.jl is gone with that file (WP29)
        @test !isdefined(EdgeBasedModels, :_same_recovery_parameter)
        m = build_multiplex_sir(layers)
        @test m isa EdgeModelSystem
        @test m.metadata[:kind] === :assembled && m.metadata[:closure] === :multiplex
        @test haskey(m.metadata[:seed_params], :I)             # the seed parameter seed_I (§A.3)
        @test build_multiplex_sir(:A => (pA, 0.15), :B => (pB, 0.10); γ = 0.1) isa EdgeModelSystem
        @test generate_multiplex_sir === build_multiplex_sir
        ic = default_initial_conditions(m; seed_fraction = 0.01)
        grid = 0.0:0.5:60.0
        sol = solve_epidemic(m; tspan = (0.0, 60.0), init = ic, saveat = grid, reltol = 1e-10, abstol = 1e-12)
        I, S = curve(m, sol, :I), curve(m, sol, :S)
        @test S[1] ≈ 0.99 && I[1] ≈ 0.01
        # Jacobsen et al. 2018 eq. (13), α_S = 1 − ρ: values of the E13 verifier's independent expanded ODE
        @test maximum(I) ≈ 0.5111163054162684 atol = 1e-8
        @test grid[argmax(I)] ≈ 12.5
        @test I[41] ≈ 0.33548103796855555 atol = 1e-8          # t = 20
        @test S[end] ≈ 0.0245416507597998 atol = 1e-8           # t = 60
        # … and our own transcription of eq. (13)
        ψA(x) = exp(3 * (x - 1)); dψA(x) = 3 * exp(3 * (x - 1)); ψB(x) = x^3; dψB(x) = 3x^2
        function jacobsen!(du, u, _, t)
            θA, θB, R = u
            q = 0.99
            du[1] = -0.15θA + 0.15 * q * dψA(θA) / 3 * ψB(θB) + 0.1 * (1 - θA)
            du[2] = -0.10θB + 0.10 * q * dψB(θB) / 3 * ψA(θA) + 0.1 * (1 - θB)
            du[3] = 0.1 * (1 - q * ψA(θA) * ψB(θB) - R)
        end
        ref = OrdinaryDiffEq.solve(OrdinaryDiffEq.ODEProblem(jacobsen!, [1.0, 1.0, 0.0], (0.0, 60.0)), Vern9();
                                   reltol = 1e-12, abstol = 1e-14, saveat = grid)
        Sref = [0.99 * ψA(u[1]) * ψB(u[2]) for u in ref.u]
        @test maxdiff(S, Sref) < 1e-8
        @test maxdiff(curve(m, sol, :R), [u[3] for u in ref.u]) < 1e-8
        @test maxdiff(curve(m, sol, :θ_A), [u[1] for u in ref.u]) < 1e-8
        # θ never increases, even on a slow layer (0.1: dθ_work/dt(0) = +2e-8)
        mneg = build_multiplex_sir([(:home, poisson_pgf(3.0), 0.3, 0.1), (:work, poisson_pgf(2.0), 0.02, 0.1)])
        sn = solve_epidemic(mneg; tspan = (0.0, 200.0), init = default_initial_conditions(mneg; seed_fraction = 1e-4),
                            reltol = 1e-12, abstol = 1e-14)
        @test all(diff(sn[mneg.variables[:θ_work]]) .<= 1e-12)
        # one shared recovery rate; no redundant per-layer γ parameters
        msym = build_multiplex_sir([(:A, pA, :τA, :γ), (:B, pB, :τB, :γ)])
        @test count(p -> startswith(string(p), "γ"), parameters(msym.system)) == 1
        @test_throws ArgumentError build_multiplex_sir([(:A, pA, 0.15, 0.1), (:B, pB, 0.10, 0.2)])
        @test_throws ArgumentError build_multiplex_sir([(:A, pA, 0.15)])
        # symbolic rates are accepted (0.1: MethodError Float64(::Num))
        @parameters βA
        ms = build_multiplex_sir([(:A, pA, βA, 0.1), (:B, pB, 0.10, 0.1)])
        @test ms isa EdgeModelSystem
        sols = solve_epidemic(ms; tspan = (0.0, 60.0), p = Dict(βA => 0.15),
                              init = default_initial_conditions(ms; seed_fraction = 0.01),
                              saveat = grid, reltol = 1e-10, abstol = 1e-12)
        @test maxdiff(curve(ms, sols, :I), I) < 1e-10
        # Symbol rates, set at solve time
        so = solve_epidemic(msym; p = Dict(:τA => 0.15, :τB => 0.10, :γ => 0.1), initial = SeedFraction(:I => 0.01),
                            tspan = (0.0, 60.0), saveat = grid, reltol = 1e-10, abstol = 1e-12)
        @test maxdiff(curve(msym, so, :I), I) < 1e-10
        # a single layer reduces to build_sir(:compact)
        m1 = build_multiplex_sir([(:A, pA, 0.15, 0.1)])
        s1 = build_sir(pA, 0.15, 0.1; form = :compact)
        a1 = solve_epidemic(m1; tspan = (0.0, 60.0), init = default_initial_conditions(m1; seed_fraction = 0.01),
                            saveat = grid, reltol = 1e-12, abstol = 1e-14)
        b1 = solve_epidemic(s1; tspan = (0.0, 60.0), init = default_initial_conditions(s1; seed_fraction = 0.01),
                            saveat = grid, reltol = 1e-12, abstol = 1e-14)
        @test maxdiff(curve(m1, a1, :I), curve(s1, b1, :I)) < 1e-10
        # the 0.1 tspan keyword is accepted with a deprecation; form = :compact gives the 0.1 shape
        mt = @test_deprecated build_multiplex_sir(layers; tspan = (0.0, 40.0))
        @test mt isa EdgeModelSystem
        mc = build_multiplex_sir(layers; form = :compact)
        @test length(ModelingToolkit.unknowns(mc.system)) == length(layers) + 1
        @test Set(keys(mc.variables)) ⊇ Set([:θ_A, :θ_B, :R])
        sc_ = solve_epidemic(mc; tspan = (0.0, 60.0), init = default_initial_conditions(mc; seed_fraction = 0.01),
                             saveat = grid, reltol = 1e-12, abstol = 1e-14)
        @test maxdiff(curve(mc, sc_, :I), I) < 1e-8
        # the corrected susceptible fraction carries the seed factor
        @test susceptible_fraction([pA, pB], [0.8, 0.9]; ρ = 0.01) ≈ 0.99 * ψA(0.8) * ψB(0.9)
        @test susceptible_fraction(MultiplexNetwork(:A => pA, :B => pB), [0.8, 0.9]; ρ = 0.01) ≈ 0.99 * ψA(0.8) * ψB(0.9)
        @test susceptible_fraction([pA, pB], [1.0, 1.0]) ≈ 1.0
    end

    @testset "literature: Miller & Volz 2013 §2.2.4, eq. (13), three modes of transmission" begin
        # Their example: k₁ ~ Bi(2, 1/2), k₂ geometric on {1, 2, …} with mean 2 (ψ₂ = x/(2 − x)),
        # k₃ ~ NB(1, 3/4) (mean 1/3, variance 4/9), independent; β = (1, 0.5, 3), γ = 1.
        @variables z
        geo = DegreePGF(z, z / (2 - z))
        net = MultiplexNetwork(:one => BinomialDegree(2, 0.5), :two => geo, :three => NegBinDegree(1.0, 0.75))
        cm = layered_sir(:one => 1.0, :two => 0.5, :three => 3.0; γ = 1.0)
        ρ = 0.01
        grid = 0.0:0.25:20.0
        Ψ(x) = (x[1] + 1)^2 / 4 * x[2] / (2 - x[2]) * 3 / (4 - x[3])
        ∂Ψ(x) = [(x[1] + 1) / 2 * x[2] / (2 - x[2]) * 3 / (4 - x[3]),
                 (x[1] + 1)^2 / 4 * 2 / (2 - x[2])^2 * 3 / (4 - x[3]),
                 (x[1] + 1)^2 / 4 * x[2] / (2 - x[2]) * 3 / (4 - x[3])^2]
        ∂Ψ1 = ∂Ψ([1.0, 1.0, 1.0])
        @test ∂Ψ1 ≈ [1.0, 2.0, 1 / 3]
        β = [1.0, 0.5, 3.0]
        function eq13!(du, u, _, t)       # θ̇_j = −β_jθ_j + β_j q∂_jΨ(θ)/∂_jΨ(1) + γ(1 − θ_j), Ṙ = γI
            θ = u[1:3]
            g = ∂Ψ(θ)
            for j in 1:3
                du[j] = -β[j] * θ[j] + β[j] * (1 - ρ) * g[j] / ∂Ψ1[j] + (1 - θ[j])
            end
            du[4] = 1 - (1 - ρ) * Ψ(θ) - u[4]
        end
        ref = OrdinaryDiffEq.solve(OrdinaryDiffEq.ODEProblem(eq13!, [1.0, 1.0, 1.0, 0.0], (0.0, 20.0)), Vern9();
                                   reltol = 1e-12, abstol = 1e-14, saveat = grid)
        Sref = [(1 - ρ) * Ψ(u[1:3]) for u in ref.u]
        for form in (:expanded, :compact)
            sys = edge_based(cm, net; form)
            sol = solve_epidemic(sys; initial = SeedFraction(:I => ρ), tspan = (0.0, 20.0), saveat = grid, TOL...)
            @test maxdiff(curve(sys, sol, :S), Sref) < 1e-10
            @test maxdiff(curve(sys, sol, :R), [u[4] for u in ref.u]) < 1e-10
            for (j, ℓ) in enumerate((:one, :two, :three))
                @test maxdiff(curve(sys, sol, Symbol(:θ_, ℓ)), [u[j] for u in ref.u]) < 1e-10
            end
        end
    end

    @testset "the compact form (Jacobsen et al. eq. (13)) = the expanded form" begin
        net = MultiplexNetwork(:home => RegularDegree(3), :comm => PoissonDegree(5), :work => NegBinDegree(; mean = 4, var = 8))
        cm = ContactModel(:c3; contacts = [Contact(:S, :I, :I, 0.12; layer = :home), Contact(:S, :I, :I, 0.03),
                                           Contact(:S, :I, :I, 0.05; layer = :work)],
                          transitions = [NodeTransition(:I, :R, 0.25)])
        ex, co = edge_based(cm, net), edge_based(cm, net; form = :compact)
        a, b = solve_mpx(ex), solve_mpx(co)
        for X in (:S, :R, :I, :cumulative, :θ_home, :θ_comm, :θ_work, :φ_S_comm)
            @test maxdiff(curve(ex, a, X), curve(co, b, X)) < 1e-10
        end
        @test co.metadata[:form] === :compact
        @test length(ModelingToolkit.unknowns(co.system)) == 4
        # the per-reaction table is that of the expanded form
        @test vector_fields_equal(symbolic_ode(co.metadata[:contributions]), symbolic_ode(ex))
        # SIR shape only; seeds in I only
        seir = ContactModel(:seir; contacts = [Contact(:S, :I, :E, 0.1; layer = :home)],
                            transitions = [NodeTransition(:E, :I, 0.2), NodeTransition(:I, :R, 0.25)])
        @test_throws ArgumentError edge_based(seir, net; form = :compact)
        @test_throws ArgumentError default_initial_conditions(co; initial = SeedFraction(:I => 0.01, :R => 0.01))
        @test_throws ArgumentError edge_based(cm, net; form = :bogus)
    end

    @testset "one layer is the configuration lift; :all = one contact per layer" begin
        for (d, cm, X) in ((NegBinDegree(; mean = 4, var = 8), sir_model(; τ = 1 / 6, γ = 1 / 4), :I),
                           (PoissonDegree(5), seir_model(; τ = 1 / 6, σ = 1 / 5, γ = 1 / 4), :E))
            one = edge_based(cm, MultiplexNetwork(:only => d))
            cfg = edge_based(cm, ConfigurationNetwork(d))
            a, b = solve_mpx(one; X, T = 150.0), solve_mpx(cfg; X, T = 150.0)
            @test maxdiff(curve(one, a, :θ_only), curve(cfg, b, :θ)) < 1e-10
            for Y in (:S, :cumulative, :pop_I, :pop_R)
                @test maxdiff(curve(one, a, Y), curve(cfg, b, Y)) < 1e-10
            end
        end
        net = MultiplexNetwork(:home => RegularDegree(3), :comm => PoissonDegree(5))
        @test vector_fields_equal(symbolic_ode(edge_based(layered_sir(:all => 0.1), net)),
                                  symbolic_ode(edge_based(layered_sir(:home => 0.1, :comm => 0.1), net)))
        @test !vector_fields_equal(symbolic_ode(edge_based(layered_sir(:all => 0.1), net)),
                                   symbolic_ode(edge_based(layered_sir(:home => 0.1, :comm => 0.2), net)))
        # a frequency-dependent layer contact uses its layer's mean degree (design §B.6)
        fd = ContactModel(:fd; contacts = [Contact(:S, :I, :I, :βh; layer = :home), Contact(:S, :I, :I, :βc; layer = :comm)],
                          transitions = [NodeTransition(:I, :R, 0.25)], convention = FrequencyDependent())
        sf = edge_based(fd, net)
        a = solve_epidemic(sf; p = Dict(:βh => 0.6, :βc => 0.5), initial = SeedFraction(:I => 0.01),
                           tspan = (0.0, 60.0), saveat = 1.0, TOL...)
        pc = edge_based(layered_sir(:home => 0.6 / 3, :comm => 0.5 / 5), net)
        @test maxdiff(curve(sf, a, :S), curve(pc, solve_mpx(pc; T = 60.0), :S)) < 1e-10
    end

    @testset "H6: the multiplex is the product-PGF network only for Poisson (or identical) layers" begin
        sir = sir_model(; τ = 0.1, γ = 0.25)                 # one contact on :all
        a = edge_based(sir, MultiplexNetwork(:a => PoissonDegree(3), :b => PoissonDegree(2)))
        b = edge_based(sir, ConfigurationNetwork(PoissonDegree(5)))
        @test maxdiff(curve(a, solve_mpx(a), :S), curve(b, solve_mpx(b), :S)) < 1e-10
        # a 3-regular layer and a bimodal {1, 7} layer vs one network with the summed degree {4, 10}:
        # stubs pair within layers, so the lifts differ (design §D.6 H6)
        c = edge_based(sir, MultiplexNetwork(:a => RegularDegree(3), :b => EmpiricalDegree(Dict(1 => 0.5, 7 => 0.5))))
        d = edge_based(sir, ConfigurationNetwork(EmpiricalDegree(Dict(4 => 0.5, 10 => 0.5))))
        @test maxdiff(curve(c, solve_mpx(c), :S), curve(d, solve_mpx(d), :S)) > 5e-3
    end

    @testset "per-reaction table, gluing (H1) and relabelling on a multiplex" begin
        net = MultiplexNetwork(:home => RegularDegree(3), :comm => PoissonDegree(5))
        tr = open_model(ContactModel(:tr; contacts = [Contact(:S, :I, :E, :τ; layer = :home), Contact(:S, :I, :E, :κ)]);
                        legs = [[:S], [:E, :I]])
        pr = open_model(ContactModel(:pr; transitions = [NodeTransition(:E, :I, :σ), NodeTransition(:I, :R, :γ)]);
                        legs = [[:E, :I, :R]])
        glued = glue(tr, pr; on = [:E, :I])
        tab = lift_contributions(tr, net)
        @test tab.closure === :multiplex
        @test Set(first.(tab.coordinates)) ⊇ Set([:θ_home, :θ_comm, :φ_I_home, :φ_E_comm, :pop_E])
        # the :home contact drains θ_home only; the :all contact both θs; each feeds φ_E on both layers
        rows = collect(tab)
        @test Set(first.(rows[1].terms)) == Set([:θ_home, :φ_I_home, :φ_E_home, :φ_E_comm, :pop_E])
        @test count(k -> startswith(string(k), "θ_"), first.(rows[2].terms)) == 2
        @test vector_fields_equal(symbolic_ode(edge_based(glued, net)),
                                  symbolic_ode(sum_contributions(lift_contributions(tr, net), lift_contributions(pr, net))))
        # pushforward along a species map: I ↦ J (the symbolic field of the relabelled model)
        f = Dict(:I => :J)
        @test vector_fields_equal(symbolic_ode(relabel(lift_contributions(glued, net), f)),
                                  symbolic_ode(edge_based(relabel(glued.model, f), net)))
        # a different network is not a sum (F5)
        @test_throws ArgumentError sum_contributions(lift_contributions(tr, net),
                                                     lift_contributions(pr, MultiplexNetwork(:home => RegularDegree(3))))
    end

    @testset "edgeless layers, admissibility, errors" begin
        # a layer of mean degree 0 is inert: no NaN, the same epidemic as without it
        z = edge_based(layered_sir(:a => 1 / 6, :z => 0.3), MultiplexNetwork(:a => RegularDegree(6), :z => PoissonDegree(0.0)))
        s6 = edge_based(sir_model(; τ = 1 / 6, γ = 1 / 4), ConfigurationNetwork(RegularDegree(6)))
        a = solve_mpx(z)
        @test all(isfinite, curve(z, a, :φ_S_z))
        @test maxdiff(curve(z, a, :S), curve(s6, solve_mpx(s6), :S)) < 1e-10
        # a symbolic layer mean degree, set at solve time, including a runtime 0 (the κ → 0 limit, E11/E32)
        @parameters κz
        zs = edge_based(layered_sir(:a => 1 / 6, :z => 0.3), MultiplexNetwork(:a => RegularDegree(6), :z => poisson_pgf(κz)))
        for κ in (0.0, 2.0)
            x = solve_epidemic(zs; p = Dict(κz => κ), initial = SeedFraction(:I => 0.01), tspan = (0.0, 80.0),
                               saveat = 1.0, TOL...)
            num = edge_based(layered_sir(:a => 1 / 6, :z => 0.3),
                             MultiplexNetwork(:a => RegularDegree(6), :z => PoissonDegree(κ)))
            @test all(isfinite, curve(zs, x, :φ_S_z))
            @test maxdiff(curve(zs, x, :S), curve(num, solve_mpx(num), :S)) < 1e-10
        end
        net = MultiplexNetwork(:home => RegularDegree(3), :comm => PoissonDegree(5))
        # the factory also takes a vector of layer pairs
        @test vector_fields_equal(symbolic_ode(build_multiplex_sir([:home => (RegularDegree(3), 0.1), :comm => (PoissonDegree(5), 0.2)]; γ = 0.25)),
                                  symbolic_ode(edge_based(layered_sir(:home => 0.1, :comm => 0.2), net)))
        @test_throws AdmissibilityError edge_based(sis_model(), net)
        @test_throws AdmissibilityError edge_based(sirs_model(), net)
        away = layered_sir(:school => 0.1)
        @test_throws AdmissibilityError edge_based(away, net)                  # a layer the network lacks
        @test_throws ArgumentError lift_contributions(away, net)
        @test_throws ArgumentError build_multiplex_sir(:a => (RegularDegree(3), 0.1), :a => (RegularDegree(3), 0.1); γ = 0.25)
        @test_throws ArgumentError build_multiplex_sir(:a => (RegularDegree(3),); γ = 0.25)
        # a stratified model has several susceptible classes: not on an untyped multiplex
        @test_throws AdmissibilityError edge_based(stratify(sir_model(), strata([:x, :y]; sizes = [0.5, 0.5])), net)
        @test_throws ArgumentError lift_contributions(stratify(sir_model(), strata([:x, :y]; sizes = [0.5, 0.5])), net)
    end

    @testset "the scenario :sir_mpx and model_curves" begin
        sc = scenario(:sir_mpx)
        sys = edge_based(sc)
        @test sys.metadata[:closure] === :multiplex
        sol = solve_epidemic(sys, sc; TOL...)
        mc = model_curves(sys, sol; t = sc.tgrid)
        @test Set(keys(mc.values)) ⊇ Set([:S, :I, :R, :cumulative, :infectious])
        long = solve_epidemic(sys; p = sc.params, initial = sc.initial, tspan = (0.0, 2000.0), saveat = 2000.0, TOL...)
        @test curve(sys, long, :cumulative)[end] ≈ sc.expected[:final_size] atol = 1e-8
        @test sc.expected[:R0] ≈ 2 rtol = 1e-8
    end
end
