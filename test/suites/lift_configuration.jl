# WP17: the per-reaction edge-based assembler on configuration networks (DESIGN §D.4, §J.2, §J.8).
#
# Every expected value here comes from an independent computation: the §D.4 field written out by
# hand in this file, NetworkEpiCore's final-size and growth-rate engine (an edge-kind branching
# process, WP11), Miller's final-size relation with the explicit seed q = 1 − ρ solved by
# bisection in this file, or a hand-written Float64 ODE. Verified issues: E06/E31 (the seed factor
# q), E14 (branching transmissibility), E23/E27 (pre-cancelled entry terms, high-degree PGFs),
# E11/E32 (runtime-zero mean degrees), E09 (Erlang exits), J.8 (the cumulative accumulator).

using EdgeBasedModels
using NetworkEpiCore
using ModelingToolkit
using Symbolics
using LinearAlgebra
using OrdinaryDiffEq: Vern9
using Test

const EBM = EdgeBasedModels
const TOL = (solver = Vern9(), reltol = 1e-12, abstol = 1e-14)

curve(sys, sol, X) = compartment(sys, sol, X)

# S + Σ pop − 1 (node conservation) and θ − φ_S − Σ φ (edge conservation), max over time.
function conservation_errors(sys, sol)
    S = curve(sys, sol, :S)
    pops = [k for k in keys(sys.variables) if startswith(string(k), "pop_")]
    node = maximum(abs.(S .+ sum(curve(sys, sol, k) for k in pops) .- 1))
    haskey(sys.variables, :θ) && haskey(sys.observables, :φ_S) || return node, 0.0
    φs = [k for k in keys(sys.variables) if startswith(string(k), "φ_")]
    edge = maximum(abs.(curve(sys, sol, :θ) .- curve(sys, sol, :φ_S) .- sum(curve(sys, sol, k) for k in φs)))
    return node, edge
end

# Bisection for the root of f on [a, b] (f(a), f(b) of opposite signs).
function bisect(f, a, b; tol = 1e-15)
    fa = f(a)
    for _ in 1:200
        m = (a + b) / 2
        fm = f(m)
        if sign(fm) == sign(fa)
            a, fa = m, fm
        else
            b = m
        end
        b - a < tol && break
    end
    return (a + b) / 2
end

# Miller's final size with an explicit seed (Miller 2014, eqs. 3–4, ρ in the infectious entry):
# θ∞ = 1 − T + T q ψ'(θ∞)/ψ'(1), R∞ = 1 − q ψ(θ∞), for the smallest root θ∞ ∈ (0, 1).
function miller_final_size(ψ, ψ1, k̄, T, ρ)
    q = 1 - ρ
    g(θ) = 1 - T + T * q * ψ1(θ) / k̄ - θ
    θ∞ = bisect(g, 1e-12, 1 - 1e-12)
    return 1 - q * ψ(θ∞)
end

# The value of a symbolic expression at the point `at` (a Dict of variables), constants folded.
numval(e, at) = Float64(Symbolics.value(Symbolics.substitute(e, at; fold = Val(true))))

# The numeric linearisation of an EB field at the disease-free state (θ = ξ = 1, q = 1, every φ
# and pop 0): its largest real eigenvalue is the early growth rate r when r > 0.
function early_growth(ode::SymbolicODE, p::AbstractDict{Symbol})
    xs = Num.(ode.states)
    J = Symbolics.jacobian(Num.(ode.rhs), xs)
    at = Dict{Any,Any}()
    for x in ode.states
        n = Symbol(Symbolics.getname(x))
        at[x] = (n === :θ || startswith(string(n), "θ_") || n === :ξ || startswith(string(n), "ξ_")) ? 1.0 : 0.0
    end
    for q in ode.parameters
        n = Symbol(Symbolics.getname(q))
        at[q] = startswith(string(n), "q_") ? 1.0 : p[n]
    end
    M = [numval(J[i, j], at) for i in axes(J, 1), j in axes(J, 2)]
    return maximum(real.(eigvals(M)))
end

@testset "lift: configuration networks" begin
    net5 = ConfigurationNetwork(PoissonDegree(5.0))

    @testset "the per-reaction field is the §D.4 table (hand-written, NegBin(4, 8))" begin
        # SEAIR with a removal, an exit and a Symbol/Expr rate mix: every row against D.4 by hand.
        cm = ContactModel(:mix; contacts = [Contact(:S, :I, :E, :τI), Contact(:S, :A, :E, :τA)],
                          transitions = [NodeTransition(:E, :I, :(p * σ)), NodeTransition(:E, :A, :((1 - p) * σ)),
                                         NodeTransition(:I, :R, :γ), NodeTransition(:A, nothing, :γ),
                                         NodeTransition(:S, :V, :ν)])
        d = NegBinDegree(mean = 4, var = 8)                        # r = 4, p = 1/2
        tab = lift_contributions(cm, ConfigurationNetwork(d))
        @test tab isa LiftContributions && length(tab) == 7
        @test first.(tab.coordinates) == [:θ, :ξ, :φ_E, :φ_I, :φ_A, :φ_R, :φ_V, :φ_removed,
                                          :pop_E, :pop_I, :pop_A, :pop_R, :pop_V, :pop_removed]
        @test [r.type for r in tab] == [:contact, :contact, :progress, :progress, :progress, :remove, :exit]
        @test tab[:A_to_∅].to === :removed && tab[:S_to_V].from === :S
        ψ(x) = (0.5 / (1 - 0.5x))^4
        ψ1(x) = 4 * 0.5 * 0.5^4 / (1 - 0.5x)^5
        ψ2(x) = 4 * 5 * 0.25 * 0.5^4 / (1 - 0.5x)^6
        k̄ = 4.0
        vars = Dict(Symbol(Symbolics.getname(v)) => v for (_, v) in tab.coordinates)
        @parameters τI τA σ p γ ν q_S
        pt = Dict(:θ => 0.73, :ξ => 0.91, :φ_E => 0.05, :φ_I => 0.11, :φ_A => 0.07, :φ_R => 0.2,
                  :φ_V => 0.03, :φ_removed => 0.01, :pop_E => 0.04, :pop_I => 0.09, :pop_A => 0.06,
                  :pop_R => 0.3, :pop_V => 0.05, :pop_removed => 0.02)
        par = Dict(:τI => 0.21, :τA => 0.13, :σ => 0.3, :p => 0.6, :γ => 0.25, :ν => 0.02, :q_S => 0.98)
        sub = merge(Dict{Any,Any}(vars[k] => v for (k, v) in pt),
                    Dict{Any,Any}(τI => par[:τI], τA => par[:τA], σ => par[:σ], p => par[:p], γ => par[:γ],
                                  ν => par[:ν], q_S => par[:q_S]))
        val(e) = numval(e, sub)
        θ, ξ, q = pt[:θ], pt[:ξ], par[:q_S]
        φS = q * ξ * ψ1(θ) / k̄
        want = Dict(
            :S_I_to_E => Dict(:θ => -par[:τI] * pt[:φ_I], :φ_I => -par[:τI] * pt[:φ_I],
                              :φ_E => par[:τI] * pt[:φ_I] * q * ξ * ψ2(θ) / k̄,
                              :pop_E => par[:τI] * pt[:φ_I] * q * ξ * ψ1(θ)),
            :S_A_to_E => Dict(:θ => -par[:τA] * pt[:φ_A], :φ_A => -par[:τA] * pt[:φ_A],
                              :φ_E => par[:τA] * pt[:φ_A] * q * ξ * ψ2(θ) / k̄,
                              :pop_E => par[:τA] * pt[:φ_A] * q * ξ * ψ1(θ)),
            :E_to_I => Dict(:φ_E => -0.18 * pt[:φ_E], :φ_I => 0.18 * pt[:φ_E],
                            :pop_E => -0.18 * pt[:pop_E], :pop_I => 0.18 * pt[:pop_E]),
            :E_to_A => Dict(:φ_E => -0.12 * pt[:φ_E], :φ_A => 0.12 * pt[:φ_E],
                            :pop_E => -0.12 * pt[:pop_E], :pop_A => 0.12 * pt[:pop_E]),
            :I_to_R => Dict(:φ_I => -0.25 * pt[:φ_I], :φ_R => 0.25 * pt[:φ_I],
                            :pop_I => -0.25 * pt[:pop_I], :pop_R => 0.25 * pt[:pop_I]),
            :A_to_∅ => Dict(:φ_A => -0.25 * pt[:φ_A], :φ_removed => 0.25 * pt[:φ_A],
                            :pop_A => -0.25 * pt[:pop_A], :pop_removed => 0.25 * pt[:pop_A]),
            :S_to_V => Dict(:ξ => -0.02 * ξ, :φ_V => 0.02 * φS, :pop_V => 0.02 * q * ξ * ψ(θ)))
        for r in tab
            got = Dict{Symbol,Float64}()
            for (k, v) in r.terms
                got[k] = get(got, k, 0.0) + val(v)
            end
            @test Set(keys(got)) == Set(keys(want[r.reaction]))
            for (k, v) in want[r.reaction]
                @test got[k] ≈ v rtol = 1e-12
            end
            # the node-level flux is the gain of pop_to
            @test val(r.flux) ≈ want[r.reaction][Symbol(:pop_, r.to)] rtol = 1e-12
        end
        # the table prints one row per reaction
        txt = sprint(show, MIME"text/plain"(), tab)
        @test occursin("S + I → E + I", txt) && occursin("A → ∅", txt) && occursin("exit", txt)
        @test occursin("NegBinDegree", txt) && !occursin("{", txt)
    end

    @testset "scenarios: conservation, NetworkEpiCore's final size and growth rate" begin
        # For every registered scenario lifted here, conservation holds to 1e-10 (the removal sink
        # included), the long-time cumulative incidence equals NEC's fixed-point final size, and
        # the linearisation of the EB field at the disease-free state has NEC's growth rate r
        # (NEC computes both from its own edge-kind branching process, WP11).
        ids = [:sir_reg6, :sir_pois5, :sir_nb4, :sir_bim, :sir_pl, :seir_pois5, :sir_erl3_pois5,
               :seair_pois5, :twostrain_pois5, :sir_vax_pois5, :sir_dense_pois20, :sir_pois5_1seed]
        for id in ids
            sc = scenario(id)
            @testset "$id" begin
                sys = edge_based(sc)
                @test sys.metadata[:kind] === :assembled && sys.metadata[:closure] === :configuration
                sol = solve_epidemic(sys; p = sc.params, initial = sc.initial, tspan = (0.0, 1200.0),
                                     saveat = 5.0, TOL...)
                @test string(sol.retcode) == "Success"
                node, edge = conservation_errors(sys, sol)
                @test node < 1e-10 && edge < 1e-10
                cum = curve(sys, sol, :cumulative)
                @test cum[1] ≈ sum(last, seed_fractions(sc.initial)) atol = 1e-14
                if haskey(sc.expected, :final_size)
                    @test cum[end] ≈ sc.expected[:final_size] atol = 1e-7
                end
                @test early_growth(symbolic_ode(sys), sc.params) ≈ sc.expected[:r] rtol = 1e-6
                if id === :sir_vax_pois5        # vaccinated nodes are not infected (J.8)
                    @test cum[end] ≈ 1 - curve(sys, sol, :S)[end] - curve(sys, sol, :pop_V)[end] atol = 1e-10
                    @test curve(sys, sol, :pop_V)[end] > 0.05
                else
                    @test maximum(abs.(cum .- (1 .- curve(sys, sol, :S)))) < 1e-10
                end
            end
        end
    end

    @testset "E06/E31: the seed factor q = 1 − ρ (S(0) = 1 − ρ, Miller's final size with ρ)" begin
        # Poisson(5) and the bimodal {2: 5/6, 10: 1/6}, at a large seed where a missing q shows.
        T = (1 / 6) / (1 / 6 + 1 / 4)
        pois = (x -> exp(5(x - 1)), x -> 5exp(5(x - 1)), 5.0)
        bim = (x -> 5 / 6 * x^2 + 1 / 6 * x^10, x -> 5 / 3 * x + 10 / 6 * x^9, 10 / 6 + 10 / 6)
        for (d, (ψ, ψ1, k̄)) in ((PoissonDegree(5.0), pois), (EmpiricalDegree(Dict(2 => 5 / 6, 10 => 1 / 6)), bim))
            for (cm, X) in ((sir_model(τ = 1 / 6, γ = 1 / 4), :I), (seir_model(τ = 1 / 6, σ = 1 / 5, γ = 1 / 4), :E))
                sys = edge_based(cm, ConfigurationNetwork(d))
                ρ = 0.1
                sol = solve_epidemic(sys; initial = SeedFraction(X => ρ), tspan = (0.0, 1500.0), saveat = 5.0, TOL...)
                @test curve(sys, sol, :S)[1] ≈ 1 - ρ atol = 1e-14
                @test curve(sys, sol, :φ_S)[1] ≈ 1 - ρ atol = 1e-14
                @test curve(sys, sol, Symbol(:pop_, X))[1] ≈ ρ atol = 1e-14
                @test 1 - curve(sys, sol, :S)[end] ≈ miller_final_size(ψ, ψ1, k̄, T, ρ) atol = 1e-8
            end
        end
    end

    @testset "E14: branching at infection and bypasses are lifted per reaction" begin
        # E → I at 1/2 and E → R at 1/2 (a bypass), β = γ = 1, Poisson(5): T = 1/4 and R₀ = 1.25, so
        # the final size is 0.371663 with ρ = 1e-4 in E (verified issue E14: an SSA gave 0.3708 ±
        # 0.0017, the old product formula 0.8926). The E → A | I split gives 0.892659.
        byp = ContactModel(:bypass; contacts = [Contact(:S, :I, :E, 1.0)],
                           transitions = [NodeTransition(:E, :I, 0.5), NodeTransition(:E, :R, 0.5),
                                          NodeTransition(:I, :R, 1.0)])
        sys = edge_based(byp, net5)
        sol = solve_epidemic(sys; initial = SeedFraction(:E => 1e-4), tspan = (0.0, 600.0), TOL...)
        @test 1 - curve(sys, sol, :S)[end] ≈ 0.371663 atol = 2e-6
        @test 1 - curve(sys, sol, :S)[end] ≈ final_size(byp, net5, Dict{Symbol,Float64}(); initial = SeedFraction(:E => 1e-4)) atol = 1e-7
        split = ContactModel(:split; contacts = [Contact(:S, :I, :E, 1.0), Contact(:S, :A, :E, 1.0)],
                             transitions = [NodeTransition(:E, :A, 0.5), NodeTransition(:E, :I, 0.5),
                                            NodeTransition(:A, :R, 1.0), NodeTransition(:I, :R, 1.0)])
        syss = edge_based(split, net5)
        sols = solve_epidemic(syss; initial = SeedFraction(:E => 1e-4), tspan = (0.0, 600.0), TOL...)
        @test 1 - curve(syss, sols, :S)[end] ≈ 0.892659 atol = 2e-6
    end

    @testset "E09: Erlang stages (erlang_stages exits at n·a) and the legacy expansion agree" begin
        prog = expand_erlang_stages([ErlangStage(:I, 3, 1 / 4; transmission_rate = 1 / 6), DiseaseStage(:R)],
                                    [DiseaseTransition(:I, :R, 3 / 4)]; entry = :I)
        a = build_edge_system(StaticConfigurationModel(poisson_pgf(5.0), prog))
        b = edge_based(erlang_stages(sir_model(τ = 1 / 6, γ = 1 / 4), :I, 3), net5)
        @test a.metadata[:kind] === :assembled
        sa = solve_epidemic(a; initial = SeedFraction(:I_1 => 0.01), tspan = (0.0, 60.0), saveat = 1.0, TOL...)
        sb = solve_epidemic(b; initial = SeedFraction(:I_1 => 0.01), tspan = (0.0, 60.0), saveat = 1.0, TOL...)
        @test maximum(abs.(curve(a, sa, :S) .- curve(b, sb, :S))) < 1e-12
        # T₃ = 1 − (3γ/(τ + 3γ))³ = 0.4523 gives the registry's final size (sir_erl3_pois5 above)
        @test vector_fields_equal(symbolic_ode(a), symbolic_ode(b))
    end

    @testset "exits, importation, tracing and removals: the cumulative accumulator (J.8)" begin
        p = Dict(:τ => 1 / 6, :γ => 1 / 4)
        # importation S → I (an exit into an infected state) counts as infection
        imp = ContactModel(:imp; contacts = [Contact(:S, :I, :I, :τ)],
                           transitions = [NodeTransition(:I, :R, :γ), NodeTransition(:S, :I, 0.01)])
        sys = edge_based(imp, net5)
        @test haskey(sys.variables, :ξ) && Set(sys.metadata[:infected]) == Set([:I])
        sol = solve_epidemic(sys; p, initial = SeedFraction(:I => 0.001), tspan = (0.0, 200.0), saveat = 1.0, TOL...)
        @test maximum(abs.(curve(sys, sol, :cumulative) .- (1 .- curve(sys, sol, :S)))) < 1e-10
        @test all(<(1e-10), conservation_errors(sys, sol))
        # contact tracing S + D → Q + D (the design's example): Q cannot reach an infector, so the
        # tracing contact is not an infection; D is an infector and infected, R is not
        trace = ContactModel(:trace; contacts = [Contact(:S, :I, :I, :τ), Contact(:S, :D, :Q, :α)],
                             transitions = [NodeTransition(:I, :D, :γ), NodeTransition(:D, :R, :δ)])
        syst = edge_based(trace, net5)
        @test Set(syst.metadata[:infected]) == Set([:I, :D])
        solt = solve_epidemic(syst; p = Dict(:τ => 0.3, :γ => 0.2, :δ => 0.3, :α => 0.1),
                              initial = SeedFraction(:I => 0.01), tspan = (0.0, 300.0), saveat = 1.0, TOL...)
        Q = curve(syst, solt, :pop_Q)
        @test Q[end] > 0.01
        @test maximum(abs.(curve(syst, solt, :cumulative) .- (1 .- curve(syst, solt, :S) .- Q))) < 1e-10
        @test all(<(1e-10), conservation_errors(syst, solt))
        # quarantine of latent infecteds E → Eq → Iq keeps infection status
        quar = ContactModel(:quar; contacts = [Contact(:S, :I, :E, :τ), Contact(:S, :Iq, :E, 0.02)],
                            transitions = [NodeTransition(:E, :I, 0.3), NodeTransition(:E, :Eq, 0.1),
                                           NodeTransition(:Eq, :Iq, 0.3), NodeTransition(:I, :R, :γ),
                                           NodeTransition(:Iq, :R, :γ)])
        sysq = edge_based(quar, net5)
        @test Set(sysq.metadata[:infected]) == Set([:E, :I, :Eq, :Iq])
        solq = solve_epidemic(sysq; p, initial = SeedFraction(:E => 0.01), tspan = (0.0, 300.0), saveat = 1.0, TOL...)
        @test maximum(abs.(curve(sysq, solq, :cumulative) .- (1 .- curve(sysq, solq, :S)))) < 1e-10
        # latent contacts isolated before they become infectious (E → Q, Q never infectious): the
        # node was infected on entering E, so it stays counted, as in NetworkOutbreaks'
        # final_size (WP3 handoff note); Q itself is not an infected state
        iso = ContactModel(:iso; contacts = [Contact(:S, :I, :E, :τ)],
                           transitions = [NodeTransition(:E, :I, 0.3), NodeTransition(:E, :Q, 0.2),
                                          NodeTransition(:I, :R, :γ)])
        sysi = edge_based(iso, net5)
        @test Set(sysi.metadata[:infected]) == Set([:E, :I])
        soli = solve_epidemic(sysi; p, initial = SeedFraction(:E => 0.01), tspan = (0.0, 300.0), saveat = 1.0, TOL...)
        @test curve(sysi, soli, :pop_Q)[end] > 0.01
        @test maximum(abs.(curve(sysi, soli, :cumulative) .- (1 .- curve(sysi, soli, :S)))) < 1e-10
        # removal X → ∅ goes to the absorbing sink :removed (J.2): conservation includes it, and the
        # dynamics of S are those of SIR with R
        rem = ContactModel(:rem; contacts = [Contact(:S, :I, :I, :τ)], transitions = [NodeTransition(:I, nothing, :γ)])
        sysr = edge_based(rem, net5)
        @test :removed in sysr.metadata[:sinks] && haskey(sysr.variables, :pop_removed)
        @test sysr.variables[:R] === sysr.variables[:pop_removed]
        solr = solve_epidemic(sysr; p, initial = SeedFraction(:I => 0.01), tspan = (0.0, 60.0), saveat = 1.0, TOL...)
        ref = edge_based(sir_model(), net5)
        solref = solve_epidemic(ref; p, initial = SeedFraction(:I => 0.01), tspan = (0.0, 60.0), saveat = 1.0, TOL...)
        @test maximum(abs.(curve(sysr, solr, :S) .- curve(ref, solref, :S))) < 1e-12
        @test all(<(1e-12), conservation_errors(sysr, solr))
        # an inert model species named `removed` absorbs the removals; a non-inert one is an error
        inert = ContactModel(:inert; contacts = [Contact(:S, :I, :I, :τ)],
                             transitions = [NodeTransition(:I, nothing, :γ)], species = [:S, :I, :removed])
        @test edge_based(inert, net5).metadata[:sinks] == Symbol[]
        busy = ContactModel(:busy; contacts = [Contact(:S, :I, :I, :τ)],
                            transitions = [NodeTransition(:I, nothing, :γ), NodeTransition(:removed, :I, 0.1)],
                            species = [:S, :I, :removed])
        @test_throws ArgumentError edge_based(busy, net5)
    end

    @testset "M9: the compact form on the invariant set of the expanded form" begin
        # SIR on Poisson(5) and the bimodal network (a non-PT PGF): the two forms agree, and
        # τφ_R + γθ − γ stays 0 along the expanded solution (the invariant set W).
        for d in (PoissonDegree(5.0), EmpiricalDegree(Dict(2 => 5 / 6, 10 => 1 / 6)))
            net = ConfigurationNetwork(d)
            e = edge_based(sir_model(τ = 1 / 6, γ = 1 / 4), net)
            c = edge_based(sir_model(τ = 1 / 6, γ = 1 / 4), net; form = :compact)
            @test length(ModelingToolkit.equations(c.system)) == 2
            # the states θ and pop_R; pop_I = 1 − S − R is an observable, also listed as a variable
            @test c.metadata[:form] === :compact && Set(keys(c.variables)) == Set([:θ, :pop_R, :pop_I, :R])
            @test Set(Symbol(Symbolics.getname(x)) for x in ModelingToolkit.unknowns(c.system)) == Set([:θ, :pop_R])
            se = solve_epidemic(e; initial = SeedFraction(:I => 0.01), tspan = (0.0, 80.0), saveat = 1.0, TOL...)
            sc = solve_epidemic(c; initial = SeedFraction(:I => 0.01), tspan = (0.0, 80.0), saveat = 1.0, TOL...)
            for X in (:S, :I, :R, :θ, :cumulative, :pop_I, :pop_R, :infectious, :φ_S)
                @test maximum(abs.(curve(e, se, X) .- curve(c, sc, X))) < 1e-10
            end
            me, mc = model_curves(e, se), model_curves(c, sc)
            @test Set(keys(me.values)) == Set(keys(mc.values))
            @test all(maximum(abs.(me[k] .- mc[k])) < 1e-10 for k in keys(me.values))
            # the legacy observable ψ_θ = ψ(θ)
            ψ = d isa PoissonDegree ? (x -> exp(5 * (x - 1))) : (x -> (5 * x^2 + x^10) / 6)
            @test curve(c, sc, :ψ_θ) ≈ ψ.(curve(c, sc, :θ)) rtol = 1e-12
            W = (1 / 6) .* curve(e, se, :φ_R) .+ (1 / 4) .* curve(e, se, :θ) .- 1 / 4
            @test maximum(abs.(W)) < 1e-12
        end
        # a removal I → ∅ is SIR-shaped too; SEIR, exits and seeding R are not compact
        rem = ContactModel(:rem; contacts = [Contact(:S, :I, :I, 1 / 6)], transitions = [NodeTransition(:I, nothing, 1 / 4)])
        @test edge_based(rem, net5; form = :compact).variables[:R] isa Any
        @test_throws ArgumentError edge_based(seir_model(), net5; form = :compact)
        @test_throws ArgumentError edge_based(sirv_model(), net5; form = :compact)
        @test_throws ArgumentError edge_based(sir_model(), net5; form = :bogus)
        c = edge_based(sir_model(τ = 1 / 6, γ = 1 / 4), net5; form = :compact)
        @test_throws ArgumentError default_initial_conditions(c; initial = SeedFraction(:I => 0.01, :R => 0.1))
    end

    @testset "E23/E27: pre-cancelled entry terms for high-degree polynomial PGFs" begin
        # p_k ∝ k^-2.5 on k = 20..150 (the case that crashed Symbolics.simplify in the legacy tensor
        # builder, E23) and Bin(100, 0.05) (which crashed the legacy excess-hazard simplify, E27):
        # the lift builds, and matches a hand-written Float64 compact ODE of Miller (2011).
        pk = zeros(151)
        for k in 20:150
            pk[k + 1] = k^-2.5
        end
        pk ./= sum(pk)
        ψ(x) = sum(pk[k + 1] * x^k for k in 0:150)
        ψ1(x) = sum(k * pk[k + 1] * x^(k - 1) for k in 1:150)
        k̄ = ψ1(1.0)
        β, γ, ρ = 0.3, 0.1, 1e-3
        for d in (EmpiricalDegree(pk), polynomial_pgf(pk))
            sys = edge_based(sir_model(τ = β, γ = γ), ConfigurationNetwork(d))
            sol = solve_epidemic(sys; initial = SeedFraction(:I => ρ), tspan = (0.0, 50.0), saveat = 0.5, TOL...)
            # hand ODE: θ̇ = −βθ + β q ψ'(θ)/ψ'(1) + γ(1 − θ), Ṙ = γ(1 − qψ(θ) − R), RK4 at h = 1e-3
            f(u) = (-β * u[1] + β * (1 - ρ) * ψ1(u[1]) / k̄ + γ * (1 - u[1]), γ * (1 - (1 - ρ) * ψ(u[1]) - u[2]))
            u = (1.0, 0.0)
            h = 1e-3
            Ihand = Float64[]
            for n in 0:50_000
                n % 500 == 0 && push!(Ihand, 1 - (1 - ρ) * ψ(u[1]) - u[2])
                k1 = f(u); k2 = f(u .+ h / 2 .* k1); k3 = f(u .+ h / 2 .* k2); k4 = f(u .+ h .* k3)
                u = u .+ h / 6 .* (k1 .+ 2 .* k2 .+ 2 .* k3 .+ k4)
            end
            @test maximum(abs.(curve(sys, sol, :I) .- Ihand)) < 1e-8
            @test maximum(curve(sys, sol, :I)) ≈ 0.93582 atol = 5e-5          # E23 skeptic: 0.93582
        end
        # the excess-hazard observable is evaluated, not simplified (legacy: the constant 1, then NaN)
        b30 = [binomial(30, k) * (1 / 6)^k * (5 / 6)^(30 - k) for k in 0:30]
        for d in (BinomialDegree(30, 1 / 6), polynomial_pgf(b30))
            sys = edge_based(sir_model(τ = 0.3, γ = 0.1), ConfigurationNetwork(d))
            sol = solve_epidemic(sys; initial = SeedFraction(:I => 0.01), tspan = (0.0, 30.0), saveat = 10.0, TOL...)
            θ = curve(sys, sol, :θ)
            ψ1b(x) = 30 / 6 * (5 / 6 + x / 6)^29
            ψ2b(x) = 30 * 29 / 36 * (5 / 6 + x / 6)^28
            @test curve(sys, sol, :excess_hazard) ≈ curve(sys, sol, :edge_hazard) .* ψ2b.(θ) ./ ψ1b.(θ) rtol = 1e-10
            @test all(isfinite, curve(sys, sol, :excess_hazard))
        end
        @test edge_based(sir_model(τ = 0.3, γ = 0.1), ConfigurationNetwork(BinomialDegree(100, 0.05))) isa EdgeModelSystem
    end

    @testset "E11/E32: a symbolic mean degree that is 0 at solve time selects the limit, not NaN" begin
        # A two-component mixture whose means are parameters (the E11 NaN case: Symbolics cannot
        # cancel k₁/(k₁ + k₂)); at k₁ = k₂ = 0 the network is edgeless: nothing happens, no NaN.
        @parameters k1 k2
        mix = MixtureDegree([0.5, 0.5], [PoissonDegree(k1), PoissonDegree(k2)])
        sys = edge_based(sir_model(τ = 0.5, γ = 1.0), ConfigurationNetwork(mix))
        ic = default_initial_conditions(sys; initial = SeedFraction(:I => 0.01))
        sol0 = solve_epidemic(sys; init = merge(ic, Dict(k1 => 0.0, k2 => 0.0)), tspan = (0.0, 30.0), saveat = 1.0, TOL...)
        @test string(sol0.retcode) == "Success"
        @test all(isfinite, curve(sys, sol0, :φ_S)) && all(isfinite, curve(sys, sol0, :S))
        @test maximum(abs.(curve(sys, sol0, :S) .- 0.99)) < 1e-12
        # The excess-hazard observable selects the same limit: edge_hazard·ψ'(θ)/ψ(θ), the rate at
        # which the limit φ_S = qψ(θ) decays, which is 0 at a vanishing mean degree (ψ ≡ 1). It
        # is neither 0/0 folded to 1 (numeric ψ) nor NaN (symbolic ψ), and it agrees with a tiny
        # positive mean (where it is edge_hazard·κ).
        eh0 = curve(sys, sol0, :excess_hazard)
        @test all(isfinite, eh0) && all(iszero, eh0)
        solε = solve_epidemic(sys; init = merge(ic, Dict(k1 => 1e-9, k2 => 1e-9)), tspan = (0.0, 30.0), saveat = 1.0, TOL...)
        @test maximum(abs.(curve(sys, solε, :excess_hazard) .- eh0)) < 1e-8
        @test maximum(abs.(curve(sys, solε, :S) .- curve(sys, sol0, :S))) < 1e-8
        # and at positive means it is the mixture network (compare with a numeric mixture)
        sol1 = solve_epidemic(sys; init = merge(ic, Dict(k1 => 2.0, k2 => 6.0)), tspan = (0.0, 30.0), saveat = 1.0, TOL...)
        num = edge_based(sir_model(τ = 0.5, γ = 1.0), ConfigurationNetwork(MixtureDegree([0.5, 0.5], [PoissonDegree(2.0), PoissonDegree(6.0)])))
        soln = solve_epidemic(num; initial = SeedFraction(:I => 0.01), tspan = (0.0, 30.0), saveat = 1.0, TOL...)
        @test maximum(abs.(curve(sys, sol1, :S) .- curve(num, soln, :S))) < 1e-10
        @test maximum(abs.(curve(sys, sol1, :excess_hazard) .- curve(num, soln, :excess_hazard))) < 1e-10
        @test all(>(0), curve(sys, sol1, :excess_hazard))
        # a numeric edgeless network is fine too, observables included
        sysz = edge_based(sir_model(τ = 0.5, γ = 1.0), ConfigurationNetwork(PoissonDegree(0.0)))
        solz = solve_epidemic(sysz; initial = SeedFraction(:I => 0.01), tspan = (0.0, 30.0), saveat = 1.0, TOL...)
        @test all(isfinite, curve(sysz, solz, :φ_S))
        @test curve(sysz, solz, :S)[end] ≈ 0.99 atol = 1e-12
        @test all(k -> all(isfinite, curve(sysz, solz, k)), keys(sysz.observables))
        @test all(iszero, curve(sysz, solz, :excess_hazard))               # legacy: the constant 1
        @test eltype(curve(sysz, solz, :excess_hazard)) === Float64
        @test curve(sysz, solz, :edge_hazard) ≈ 0.5 .* curve(sysz, solz, :φ_I) rtol = 1e-14
    end

    @testset "observables, model_curves and symbolic_ode" begin
        sys = edge_based(seair_model(), net5)
        p = Dict(:τI => 1 / 6, :τA => 1 / 12, :σ => 1 / 5, :p => 0.6, :γ => 1 / 4)
        sol = solve_epidemic(sys; p, initial = SeedFraction(:E => 0.01), tspan = (0.0, 60.0), saveat = 1.0, TOL...)
        @test curve(sys, sol, :I) ≈ curve(sys, sol, :pop_A) .+ curve(sys, sol, :pop_I) rtol = 1e-12
        @test curve(sys, sol, :infectious) ≈ curve(sys, sol, :I) rtol = 1e-14
        @test curve(sys, sol, :edge_hazard) ≈ (1 / 6) .* curve(sys, sol, :φ_I) .+ (1 / 12) .* curve(sys, sol, :φ_A) rtol = 1e-12
        mc = model_curves(sys, sol)
        @test Set(keys(mc.values)) == Set([:S, :E, :A, :I, :R, :infectious, :cumulative])
        @test mc[:cumulative] ≈ 1 .- mc[:S] atol = 1e-12
        raw = symbolic_ode(sys)
        @test raw isa SymbolicODE && :cumulative ∉ state_names(raw)
        @test Set(state_names(raw)) == Set([:θ, :φ_E, :φ_A, :φ_I, :φ_R, :pop_E, :pop_A, :pop_I, :pop_R])
        @test vector_fields_equal(raw, symbolic_ode(sys.metadata[:contributions]))
        @test sys.metadata[:entry] === :E && sys.metadata[:susceptible] === :S
        # a system not built by edge_based has no raw field (the 0.1 builders that made such systems
        # are deleted, WP29; a hand-assembled EdgeModelSystem stands for them)
        leg = EdgeModelSystem(sys.system, sys.variables, sys.observables, Dict{Symbol,Any}(:kind => :legacy))
        @test_throws ArgumentError symbolic_ode(leg)
    end
end
