# WP36c: the edge-based lift of mean-field social heterogeneity, MFSHNetwork(d) (Miller, Slim & Volz
# 2012, Part II §3.2.2, papers/1106.6319v1.md:153-161, the actual-degree formulation; DESIGN §C.3,
# §D.5 Λ3, §K WP36c).
#
# Every expected value comes from an independent source:
# - hand transcriptions, in this file, of MSV's MFSH equation θ̇ = −τθ + τθ·θψ'(θ)/ψ'(1) − γθ ln θ,
#   Ṙ = γI, S = ψ(θ) (with the explicit seed factor q: S = qψ(θ)), and of MSV's expected-degree
#   formulation (§3.1.2) with Ψ(Θ) = ψ(e^{Θ−1}) (§3.3.1), mapped onto the lift by semiconjugacies
#   that NetworkEpiCore's `verify` checks;
# - a hand-written mass-action ODE and the WellMixed(κ) lift of lift/wellmixed.jl (MFSH on a
#   κ-regular distribution is mass action);
# - the neighbour-exchange (DFD) lift of lift/dynamic.jl (WP21), whose η → ∞ limit is MFSH (Λ3);
# - NetworkEpiCore's MFSH next-generation matrix and final-size equation (WP11), and the closed forms
#   R₀ = τ(κ_ex + 1)/γ, r = τ(κ_ex + 1) − γ;
# - exact simulation of the fleeting-contact process in NetworkOutbreaks (WP36c, FleetingContactSSA):
#   fresh stub counts per run (run r's from NetworkOutbreaks.stable_rng(base + r), its SSA from
#   stable_rng(base + 2³² + r), design §J.7), exactly ρN seeds, runs conditioned on a major outbreak
#   (ever infected minus seeds ≥ 0.05 N, design §E.2), summarised by NetworkOutbreaks' `summarise`
#   and compared by NetworkEpiCore's `compare`.

using EdgeBasedModels
using NetworkEpiCore
using ModelingToolkit
using Symbolics
using Statistics
using Random
using OrdinaryDiffEq: Vern9
using Test

import NetworkOutbreaks as NO

const EBM = EdgeBasedModels
const TOL = (solver = Vern9(), reltol = 1e-11, abstol = 1e-13)

mfsh_net(d) = MFSHNetwork(d)
dfd(d, η) = DynamicNetwork(d, NeighbourExchange(η))
curve(sys, sol, X) = compartment(sys, sol, X)
numval(e, at) = Float64(Symbolics.value(Symbolics.substitute(e, at; fold = Val(true))))

const MSV_DEGREES = EmpiricalDegree(2 => 0.5, 8 => 0.5)     # MSV Part II Fig. 5: ψ(x) = (x² + x⁸)/2
const DEGREES = (PoissonDegree(5.0), MSV_DEGREES, RegularDegree(6), NegBinDegree(; mean = 4, var = 8))
const REMOVAL = ContactModel(:rem; contacts = [Contact(:S, :I, :I, 1 / 6)], transitions = [NodeTransition(:I, nothing, 1 / 4)])

# κ_ex + 1 = E[k²]/E[k] = ψ''(1)/ψ'(1) + 1
second_moment_ratio(d) = pgf_derivative(d, 1.0, 2) / pgf_derivative(d, 1.0, 1) + 1

# The observables of a model on a lifted system: S, every pop_X and the fraction ever infected.
function node_curves(sys, sol, cm)
    Xs = vcat([:S, :cumulative], [Symbol(:pop_, Y) for Y in species_names(cm) if Y ∉ susceptible_species(cm)])
    haskey(sys.variables, :pop_removed) && push!(Xs, :pop_removed)
    return Xs, reduce(hcat, [curve(sys, sol, X) for X in Xs])
end

# ---------------------------------------------------------------------------------------------
# MSV's MFSH equations, transcribed by hand (explicit seed q = q_S)
# ---------------------------------------------------------------------------------------------

# Actual degree (papers/1106.6319v1.md:157-159): θ̇ = −τθ + τθ·qθψ'(θ)/ψ'(1) − γθ ln θ,
# Ṙ = γ(1 − qψ(θ) − R). Two wrong transcriptions serve as negative controls: `:cm`, the static
# configuration-model equation of §3.2.1 (θ̇ = −τθ + τqψ'(θ)/ψ'(1) + γ(1 − θ)), and `:no_theta`, the
# edge-S qψ'(θ)/ψ'(1) where MSV's stub-S qθψ'(θ)/ψ'(1) belongs.
function msv_mfsh(d; variant::Symbol = :msv)
    τ, γ, q = as_parameter(:τ), as_parameter(:γ), as_parameter(:q_S)
    @variables t TH(t) R(t)
    ψ(x) = pgf(d, x)
    ψ1(x) = pgf_derivative(d, x, 1)
    k̄ = mean_degree(d)
    πS = variant === :no_theta ? q * ψ1(TH) / k̄ : q * TH * ψ1(TH) / k̄
    fθ = variant === :cm ? -τ * TH + τ * q * ψ1(TH) / k̄ + γ * (1 - TH) :
         -τ * TH + τ * TH * πS - γ * TH * log(TH)
    ode = SymbolicODE(:msv_mfsh_sir; states = Any[TH, R], rhs = Any[fθ, γ * (1 - q * ψ(TH) - R)],
                      parameters = Any[τ, γ, q], domain = Pair{Any,Tuple{Float64,Float64}}[TH => (0.3, 1.0)])
    return ode, (; TH, R, ψ, ψ1, k̄, τ, γ, q)
end

# MSV's equation is the invariant set {π_S + π_I + π_R = 1, τπ_R + γ ln θ = 0, S + Σpop = 1} of the
# expanded lift (seeds in I only): the inclusion is a semiconjugacy MSV → lift (kind :restriction).
function msv_inclusion(sys, d; kw...)
    ode, v = msv_mfsh(d; kw...)
    c = sys.metadata[:coords]
    πS = v.q * v.TH * v.ψ1(v.TH) / v.k̄
    πR = -(v.γ / v.τ) * log(v.TH)
    map = Pair{Any,Any}[c[:θ] => v.TH, c[:π_I] => 1 - πS - πR, c[:π_R] => πR,
                        c[:pop_I] => 1 - v.q * v.ψ(v.TH) - v.R, c[:pop_R] => v.R]
    return Semiconjugacy(:msv_mfsh_sir, ode, symbolic_ode(sys), map, Pair{Any,Any}[], :restriction, :exact,
                         [Evidence(:paper, "Miller, Slim & Volz 2012, Part II §3.2.2 (papers/1106.6319v1.md:157-159)")])
end

# Expected degree (§3.1.2, papers/1106.6319v1.md:107-109): Θ̇ = −τ + τqΨ'(Θ)/Ψ'(1) + γ(1 − Θ),
# Ṙ = γ(1 − qΨ(Θ) − R), with Ψ(Θ) = ψ(e^{Θ−1}) for actual degrees ψ (§3.3.1: Θ = 1 + ln θ).
function msv_expected(d)
    τ, γ, q = as_parameter(:τ), as_parameter(:γ), as_parameter(:q_S)
    @variables t TT(t) RR(t)
    x = exp(TT - 1)
    Ψ = pgf(d, x)
    Ψ1 = x * pgf_derivative(d, x, 1)             # dΨ/dΘ; Ψ'(1) = ψ'(1)
    ode = SymbolicODE(:msv_mfsh_expected; states = Any[TT, RR],
                      rhs = Any[-τ + τ * q * Ψ1 / mean_degree(d) + γ * (1 - TT), γ * (1 - q * Ψ - RR)],
                      parameters = Any[τ, γ, q], domain = Pair{Any,Tuple{Float64,Float64}}[TT => (-0.2, 1.0)])
    return ode, (; TT, RR)
end

# Mass action with β = κτ on fractions, by hand (states Sm, Em, Im, Rm; `latent` adds E), with q_S
# as a parameter of the map.
function mass_action_ode(κ; latent::Bool = false)
    τ, γ, σ, q = as_parameter(:τ), as_parameter(:γ), as_parameter(:σ), as_parameter(:q_S)
    @variables t Sm(t) Em(t) Im(t) Rm(t)
    inc = κ * τ * Sm * Im
    if latent
        states = Any[Sm, Em, Im, Rm]
        rhs = Any[-inc, inc - σ * Em, σ * Em - γ * Im, γ * Im]
        ps = Any[τ, σ, γ, q]
    else
        states = Any[Sm, Im, Rm]
        rhs = Any[-inc, inc - γ * Im, γ * Im]
        ps = Any[τ, γ, q]
    end
    ode = SymbolicODE(:mass_action; states, rhs, parameters = ps,
                      domain = Pair{Any,Tuple{Float64,Float64}}[Sm => (0.2, 0.9)])
    return ode, (; Sm, Em, Im, Rm, q)
end

# ---------------------------------------------------------------------------------------------
# NetworkOutbreaks ensembles
# ---------------------------------------------------------------------------------------------

const BASE = 20260926

# The reference summary of a scenario from NetworkOutbreaks' fleeting-contact process (the scenario's
# own N, runs, seeds, grid, conditioning), and the comparison table of the EB curves with it.
function against_fleeting(sc)
    ens = NO.simulate(sc.model, sc.network; N = sc.sim.N, p = sc.params, initial = sc.initial, tspan = sc.tspan,
                      nsims = sc.sim.nsims, seed = sc.sim.base_seed, keep = :events)
    @test all(tr -> tr.algorithm === :FleetingContactSSA, ens.trajectories)
    summary = NO.summarise(NO.scenario_ensemble(sc, ens.trajectories))
    sys = edge_based(sc)
    sol = solve_epidemic(sys, sc; TOL...)
    return compare(summary, model_curves(sys, sol; t = sc.tgrid, label = "edge-based")), summary, sys
end

# EB curves of `obs` and the NetworkOutbreaks runs conditioned on a major outbreak.
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

@testset "lift: mean-field social heterogeneity (MFSH)" begin
    @testset "structure: coordinates, seeds, observables, metadata, the table" begin
        net = mfsh_net(PoissonDegree(5.0))
        cm = sir_model(; τ = 1 / 12, γ = 1 / 4)
        sys = edge_based(cm, net)
        @test Set(keys(sys.variables)) == Set([:θ, :π_I, :π_R, :pop_I, :pop_R, :cumulative, :R])
        @test Set(keys(sys.observables)) == Set([:S, :I, :infectious, :π_S, :φ_S, :edge_hazard, :stub_hazard])
        md = sys.metadata
        @test md[:kind] === :assembled && md[:closure] === :mfsh && md[:form] === :expanded
        @test md[:network] == net && md[:model] == cm && md[:entry] === :I
        @test Set(keys(md[:seed_params])) == Set([:I, :R])
        table = md[:contributions]
        @test table isa LiftContributions && table.closure === :mfsh
        @test [r.type for r in table] == [:contact, :progress]
        @test first.(table.coordinates) == [:θ, :ξ, :π_I, :π_R, :pop_I, :pop_R]
        # the table's field is the system's field, and so is lift_contributions'
        @test vector_fields_equal(symbolic_ode(table), symbolic_ode(sys))
        @test vector_fields_equal(symbolic_ode(lift_contributions(cm, net)), symbolic_ode(sys))
        @test :ξ ∉ state_names(symbolic_ode(sys))                   # nothing exits: ξ ≡ 1 is dropped
        # the contact row: θ̇ −= τθπ_I, π̇_I += τθπ_I·qξ(ψ' + θψ'')/ψ'(1), pop_I' += τθπ_I·qξψ'(θ)
        row = table[1]
        @test row.type === :contact && table[row.reaction] === row
        @test Set(first.(row.terms)) == Set([:θ, :π_I, :pop_I])
        coord = Dict(table.coordinates)
        q = only(last.(table.seed_factors))
        at = Dict{Any,Any}(coord[:θ] => 0.8, coord[:π_I] => 0.1, coord[:ξ] => 1.0, q => 0.97)
        d = PoissonDegree(5.0)
        terms = Dict(row.terms)
        @test numval(terms[:θ], at) ≈ -(1 / 12) * 0.8 * 0.1 atol = 1e-15
        @test numval(terms[:π_I], at) ≈ (1 / 12) * 0.8 * 0.1 * 0.97 *
                                         (pgf_derivative(d, 0.8, 1) + 0.8 * pgf_derivative(d, 0.8, 2)) / 5 atol = 1e-15
        @test numval(terms[:pop_I], at) ≈ (1 / 12) * 0.8 * 0.1 * 0.97 * pgf_derivative(d, 0.8, 1) atol = 1e-15
        # initial conditions: θ = 1, π = pop = ρ in the seeded class, S(0) = 1 − ρ
        c = md[:coords]
        ic = default_initial_conditions(sys; initial = SeedFraction(:I => 0.01))
        @test ic[c[:θ]] == 1
        @test ic[c[:π_I]] == ic[c[:pop_I]] == 0.01
        @test ic[c[:π_R]] == ic[c[:pop_R]] == 0
        sol = solve_epidemic(sys; initial = SeedFraction(:I => 0.01), tspan = (0.0, 100.0), TOL...)
        @test curve(sys, sol, :S)[1] ≈ 0.99 atol = 1e-14
        @test curve(sys, sol, :π_S)[1] ≈ 0.99 atol = 1e-14
        @test curve(sys, sol, :cumulative) ≈ 1 .- curve(sys, sol, :S) atol = 1e-10       # SIR: ever infected = 1 − S
        θ = curve(sys, sol, :θ)
        @test curve(sys, sol, :φ_S) ≈ θ .* curve(sys, sol, :π_S) atol = 1e-14
        @test curve(sys, sol, :edge_hazard) ≈ θ .* curve(sys, sol, :stub_hazard) atol = 1e-14
        @test curve(sys, sol, :stub_hazard) ≈ (1 / 12) .* curve(sys, sol, :π_I) atol = 1e-14
        mc = model_curves(sys, sol; t = 0:1.0:100)
        @test mc.representation === :edge_based
        @test issubset([:S, :I, :R, :infectious, :cumulative], keys(mc.values))
        # a latent class, exits and removals get their own coordinates
        seir = edge_based(seir_model(), net)
        @test issubset([:π_E, :pop_E], keys(seir.variables)) && seir.metadata[:entry] === :E
        sirv = edge_based(sirv_model(), net)
        @test issubset([:ξ, :π_V, :pop_V], keys(sirv.variables))
        rem = edge_based(REMOVAL, net)
        @test issubset([:π_removed, :pop_removed], keys(rem.variables)) && rem.metadata[:sinks] == [:removed]
        # Symbol rates are parameters; the scenario form lifts the scenario's model and network
        @test issubset(Set([:τ, :σ, :γ]), Set(Symbol(Symbolics.getname(x)) for x in symbolic_ode(seir).parameters))
        sc = scenario(:sir_mfsh_pois5)
        @test edge_based(sc).metadata[:network] == sc.network
    end

    @testset "MSV Part II §3.2.2 (hand transcription) is the invariant set of the lift, for four ψ" begin
        for d in DEGREES
            sys = edge_based(sir_model(), mfsh_net(d))
            r = verify(msv_inclusion(sys, d))
            @test r.ok
            @test r.max_residual < 1e-12
            # the static CM equation and the edge-S in place of the stub-S are not the MFSH equation
            @test !verify(msv_inclusion(sys, d; variant = :cm)).ok
            @test !verify(msv_inclusion(sys, d; variant = :no_theta)).ok
        end
        @test verify(msv_inclusion(edge_based(sir_model(), mfsh_net(PoissonDegree(5.0))), PoissonDegree(5.0))).method === :symbolic
    end

    @testset "form = :compact is MSV's equation (a conjugacy), and the expanded form's trajectories" begin
        for d in DEGREES
            c = edge_based(sir_model(), mfsh_net(d); form = :compact)
            @test c.metadata[:form] === :compact && c.metadata[:closure] === :mfsh
            @test state_names(symbolic_ode(c)) == [:θ, :pop_R]
            ode, v = msv_mfsh(d)
            cc = c.metadata[:coords]
            m = Semiconjugacy(:msv_compact, ode, symbolic_ode(c), Pair{Any,Any}[cc[:θ] => v.TH, cc[:pop_R] => v.R],
                              Pair{Any,Any}[], :conjugacy, :exact, Evidence[])
            r = verify(m)
            @test r.ok && r.method === :symbolic && r.max_residual == 0
            # the per-reaction table of the compact system is the expanded one
            @test vector_fields_equal(symbolic_ode(c.metadata[:contributions]),
                                      symbolic_ode(edge_based(sir_model(), mfsh_net(d))))
        end
        # trajectories: compact = expanded (S, I, R, cumulative) for the scenarios' parameters
        for id in (:sir_mfsh_pois5, :sir_mfsh_msv)
            sc = scenario(id)
            ex = edge_based(sc)
            co = edge_based(sc.model, sc.network; form = :compact)
            se = solve_epidemic(ex, sc; TOL...)
            so = solve_epidemic(co, sc; TOL...)
            for X in (:S, :pop_I, :pop_R, :cumulative, :π_S)
                @test maximum(abs.(curve(ex, se, X) .- curve(co, so, X))) < 1e-9
            end
        end
        # with q = 1 the compact field is MSV's printed equation verbatim (no seed)
        d = MSV_DEGREES
        c = edge_based(sir_model(), mfsh_net(d); form = :compact)
        f = symbolic_ode(c)
        θ = c.metadata[:coords][:θ]
        τ, γ, q = as_parameter(:τ), as_parameter(:γ), as_parameter(:q_S)
        printed = -τ * θ + τ * θ * (θ * pgf_derivative(d, θ, 1) / mean_degree(d)) - γ * θ * log(θ)
        for (θv, τv, γv) in ((0.9, 0.5, 1.0), (0.4, 0.2, 0.3), (0.65, 1.7, 0.05))
            at = Dict{Any,Any}(θ => θv, τ => τv, γ => γv, q => 1.0)
            @test numval(f.rhs[1], at) ≈ numval(printed, at) atol = 1e-14
        end
    end

    @testset "MSV §3.3.1: the expected-degree formulation with Ψ(Θ) = ψ(e^{Θ−1}) (Θ = 1 + ln θ)" begin
        for d in DEGREES
            c = edge_based(sir_model(), mfsh_net(d); form = :compact)
            ode, v = msv_expected(d)
            cc = c.metadata[:coords]
            m = Semiconjugacy(:mfsh_expected_degree, symbolic_ode(c), ode,
                              Pair{Any,Any}[v.TT => 1 + log(cc[:θ]), v.RR => cc[:pop_R]], Pair{Any,Any}[],
                              :conjugacy, :exact,
                              [Evidence(:paper, "Miller, Slim & Volz 2012, Part II §3.3.1 (papers/1106.6319v1.md:223)")])
            r = verify(m)
            @test r.ok && r.max_residual < 1e-12
        end
    end

    @testset "conservation: π_S + Σπ = 1 and S + Σpop = 1 (SIR, SEIR, SEAIR, strains, exits, removals)" begin
        cases = ((sir_model(; τ = 1 / 12, γ = 1 / 4), SeedFraction(:I => 0.01)),
                 (seir_model(; τ = 1 / 6, σ = 1 / 5, γ = 1 / 4), SeedFraction(:E => 0.01)),
                 (seair_model(; τI = 1 / 6, τA = 1 / 12, σ = 1 / 5, p = 0.6, γ = 1 / 4), SeedFraction(:E => 0.01)),
                 (twostrain_model(; τ1 = 1 / 6, τ2 = 1 / 5, γ = 1 / 4), SeedFraction(:I1 => 0.005, :I2 => 0.005)),
                 (sirv_model(; τ = 1 / 6, γ = 1 / 4, ν = 0.02), SeedFraction(:I => 0.01)),
                 (REMOVAL, SeedFraction(:I => 0.01)))
        for (cm, initial) in cases, d in DEGREES
            sys = edge_based(cm, mfsh_net(d))
            sol = solve_epidemic(sys; initial, tspan = (0.0, 150.0), saveat = 0.0:1.0:150.0, TOL...)
            vars = sys.variables
            πsum = curve(sys, sol, :π_S) .+ sum(curve(sys, sol, k) for k in keys(vars) if startswith(string(k), "π_"))
            popsum = curve(sys, sol, :S) .+ sum(curve(sys, sol, k) for k in keys(vars) if startswith(string(k), "pop_"))
            @test maximum(abs.(πsum .- 1)) < 1e-10
            @test maximum(abs.(popsum .- 1)) < 1e-10
            @test all(>=(-1e-12), curve(sys, sol, :cumulative))
        end
    end

    @testset "RegularDegree(κ) is WellMixed(κ): mass action with β = κτ (symbolic, and trajectories to 1e-10)" begin
        # the hand-written mass-action ODE maps into the MFSH lift by θ = (S/q)^{1/κ}, π_X = pop_X = X
        for κ in (3, 6), latent in (false, true)
            cm = latent ? seir_model() : sir_model()
            sys = edge_based(cm, mfsh_net(RegularDegree(κ)))
            ode, v = mass_action_ode(κ; latent)
            c = sys.metadata[:coords]
            names = latent ? (:E, :I, :R) : (:I, :R)
            vars = latent ? (v.Em, v.Im, v.Rm) : (v.Im, v.Rm)
            map = Pair{Any,Any}[c[:θ] => (v.Sm / v.q)^(1 / κ)]
            for (X, x) in zip(names, vars)
                push!(map, c[Symbol(:π_, X)] => x, c[Symbol(:pop_, X)] => x)
            end
            r = verify(Semiconjugacy(:mass_action_in_mfsh, ode, symbolic_ode(sys), map, Pair{Any,Any}[],
                                     :restriction, :exact, Evidence[]))
            @test r.ok && r.max_residual < 1e-12
        end
        # every T_EB model: the same S, populations and cumulative incidence as the well-mixed lift (M1)
        cases = ((sir_model(; τ = 1 / 6, γ = 1 / 4), SeedFraction(:I => 0.01)),
                 (seair_model(; τI = 1 / 6, τA = 1 / 12, σ = 1 / 5, p = 0.6, γ = 1 / 4), SeedFraction(:E => 0.01)),
                 (twostrain_model(; τ1 = 1 / 6, τ2 = 1 / 5, γ = 1 / 4), SeedFraction(:I1 => 0.005, :I2 => 0.005)),
                 (sirv_model(; τ = 1 / 6, γ = 1 / 4, ν = 0.02), SeedFraction(:I => 0.01)),
                 (REMOVAL, SeedFraction(:I => 0.01)))
        for (cm, initial) in cases, κ in (3, 6)
            grid = 0.0:1.0:200.0
            a = edge_based(cm, mfsh_net(RegularDegree(κ)))
            b = edge_based(cm, WellMixed(κ))
            sa = solve_epidemic(a; initial, tspan = (0.0, 200.0), saveat = grid, TOL...)
            sb = solve_epidemic(b; initial, tspan = (0.0, 200.0), saveat = grid, TOL...)
            Xs, xa = node_curves(a, sa, cm)
            @test maximum(abs.(xa .- reduce(hcat, [curve(b, sb, X) for X in Xs]))) < 1e-10
        end
    end

    @testset "Λ3: MFSH is the slow manifold χ = θ², φ_X = θπ_X of neighbour exchange (symbolic)" begin
        # On that manifold the θ, ξ, π and pop components of the DFD field (lift/dynamic.jl) are the MFSH
        # field: the exchange terms act only on χ and φ, which relax to it at rate η.
        cases = (sir_model(), seir_model(), seair_model(), sirv_model(), REMOVAL)
        rng = Random.Xoshiro(36)
        for cm in cases, d in (PoissonDegree(5.0), MSV_DEGREES)
            dy = symbolic_ode(edge_based(cm, dfd(d, 1.0)))
            mf = symbolic_ode(edge_based(cm, mfsh_net(d)))
            dnames, mnames = state_names(dy), state_names(mf)
            θ = mf.states[findfirst(==(:θ), mnames)]
            manifold = Dict{Any,Any}()
            for (n, s) in zip(dnames, dy.states)
                n === :χ && (manifold[s] = θ^2)
                if startswith(string(n), "φ_")
                    X = Symbol(string(n)[4:end])
                    manifold[s] = θ * mf.states[findfirst(==(Symbol(:π_, X)), mnames)]
                end
            end
            @test length(manifold) == 1 + count(n -> startswith(string(n), "π_"), mnames)
            @test issubset(Set(mnames), Set(dnames))
            params = unique!(vcat(collect(dy.parameters), collect(mf.parameters)))
            for _ in 1:3
                at = Dict{Any,Any}(s => (n === :θ || n === :ξ ? 0.3 + 0.7rand(rng) : 0.2rand(rng))
                                   for (n, s) in zip(mnames, mf.states))
                for p in params
                    at[p] = 0.05 + rand(rng)
                end
                for (n, f) in zip(mnames, mf.rhs)
                    g = dy.rhs[findfirst(==(n), dnames)]
                    @test numval(Symbolics.substitute(g, manifold), at) ≈ numval(f, at) atol = 1e-13
                end
            end
        end
    end

    @testset "Λ3: the DFD lift approaches the MFSH lift as η → ∞ (O(1/η)), for SIR, SEIR and exits" begin
        cases = ((sir_model(; τ = 1 / 6, γ = 1 / 4), SeedFraction(:I => 0.01)),
                 (seir_model(; τ = 1 / 6, σ = 1 / 5, γ = 1 / 4), SeedFraction(:E => 0.01)),
                 (sirv_model(; τ = 1 / 6, γ = 1 / 4, ν = 0.02), SeedFraction(:I => 0.01)))
        for (cm, initial) in cases, d in (PoissonDegree(5.0), MSV_DEGREES)
            grid = 0.0:0.5:150.0
            mf = edge_based(cm, mfsh_net(d))
            smf = solve_epidemic(mf; initial, tspan = (0.0, 150.0), saveat = grid, TOL...)
            Xs, ref = node_curves(mf, smf, cm)
            errs = Float64[]
            for η in (1.0, 10.0, 100.0, 1000.0)
                dy = edge_based(cm, dfd(d, η))
                sdy = solve_epidemic(dy; initial, tspan = (0.0, 150.0), saveat = grid, TOL...)
                push!(errs, maximum(abs.(reduce(hcat, [curve(dy, sdy, X) for X in Xs]) .- ref)))
            end
            @info "WP36c Λ3: max |DFD(η) − MFSH| for η = 1, 10, 100, 1000" model = cm.name degrees = d errs = join(round.(errs; sigdigits = 3), ", ")
            @test issorted(errs; rev = true) && allunique(errs)
            @test errs[end] < 1e-3                                  # measured 1.4e-4 – 3.1e-4
            @test errs[end - 1] / errs[end] > 5                      # O(1/η): ratio ≈ 10
        end
        # the design's pair: :sir_ne_pois5_eta10 is close to :sir_mfsh_pois5, not to mass action (:sir_wm5)
        sc_ne, sc_mf, sc_wm = scenario(:sir_ne_pois5_eta10), scenario(:sir_mfsh_pois5), scenario(:sir_wm5)
        @test sc_ne.network.base.degrees == sc_mf.network.degrees && sc_ne.params == sc_mf.params
        grid = 0.0:0.5:100.0
        sols = map((sc_ne, sc_mf, sc_wm)) do sc
            sys = edge_based(sc)
            sol = solve_epidemic(sys; p = sc.params, initial = sc.initial, tspan = (0.0, 100.0), saveat = grid, TOL...)
            (curve(sys, sol, :cumulative), curve(sys, sol, :pop_I))
        end
        d_mf = maximum(abs.(sols[1][1] .- sols[2][1]))
        d_wm = maximum(abs.(sols[1][1] .- sols[3][1]))
        @info "WP36c Λ3 scenarios: max |cumulative(:sir_ne_pois5_eta10) − …|" mfsh = d_mf mass_action = d_wm
        @test d_mf < 0.03 && d_wm > 0.1
        @test sols[2][1][end] ≈ sc_mf.expected[:final_size] atol = 1e-5            # 0.6687
        @test sols[3][1][end] ≈ sc_wm.expected[:final_size] atol = 1e-5            # 0.8002 (same R₀ = 2)
        # design §D.5 Λ3: Poisson(5), τ = 1/6, γ = 1/4: R₀ = 4 and attack rate 0.905 (mass action: 3.33, 0.960)
        sys = edge_based(sir_model(; τ = 1 / 6, γ = 1 / 4), mfsh_net(PoissonDegree(5.0)))
        @test basic_reproduction_number(sys) ≈ 4 atol = 1e-12
        @test final_size(sys; initial = SeedFraction(:I => 0.01), method = :ode) ≈ 0.905 atol = 1e-3
    end

    @testset "R₀, r and the final size: closed forms and NetworkEpiCore's MFSH equations" begin
        for d in DEGREES, (τ, γ) in ((1 / 12, 1 / 4), (0.5, 1.0))
            cm = sir_model(; τ, γ)
            sys = edge_based(cm, mfsh_net(d))
            m2 = second_moment_ratio(d)
            @test basic_reproduction_number(sys) ≈ τ * m2 / γ rtol = 1e-10
            @test early_growth_rate(sys) ≈ τ * m2 - γ rtol = 1e-8
            if τ * m2 / γ > 1
                # the ODE (the lift, integrated to the end of the epidemic) against NetworkEpiCore's
                # fixed point −ln θ = A + qB(1 − θψ'(θ)/ψ'(1)), an independent implementation
                initial = SeedFraction(:I => 0.01)
                @test final_size(sys; initial, method = :ode) ≈ final_size(cm, mfsh_net(d); initial) atol = 1e-8
            end
        end
        # the growth rate of the lift itself: π_I grows like e^{rt} from a tiny seed
        d = MSV_DEGREES
        sys = edge_based(sir_model(; τ = 0.5, γ = 1.0), mfsh_net(d))
        sol = solve_epidemic(sys; initial = SeedFraction(:I => 1e-9), tspan = (0.0, 3.0), saveat = [2.0, 3.0], TOL...)
        πI = curve(sys, sol, :π_I)
        @test log(πI[2] / πI[1]) ≈ 0.5 * second_moment_ratio(d) - 1.0 rtol = 1e-4      # r = 2.4
        # SEIR, SEAIR, strains: the ODE final size equals NetworkEpiCore's fixed point
        cases = ((seir_model(; τ = 1 / 6, σ = 1 / 5, γ = 1 / 4), SeedFraction(:E => 0.01)),
                 (seair_model(; τI = 1 / 6, τA = 1 / 12, σ = 1 / 5, p = 0.6, γ = 1 / 4), SeedFraction(:E => 0.01)),
                 (REMOVAL, SeedFraction(:I => 0.01)))
        for (cm, initial) in cases, d in (PoissonDegree(5.0), MSV_DEGREES)
            sys = edge_based(cm, mfsh_net(d))
            @test final_size(sys; initial, method = :ode) ≈ final_size(cm, mfsh_net(d); initial) atol = 1e-8
        end
        # the scenarios' expected values (computed by NetworkEpiCore when they were registered)
        for id in (:sir_mfsh_pois5, :sir_mfsh_msv)
            sc = scenario(id)
            sys = edge_based(sc)
            @test basic_reproduction_number(sys; p = sc.params) ≈ sc.expected[:R0] rtol = 1e-10
            @test early_growth_rate(sys; p = sc.params) ≈ sc.expected[:r] rtol = 1e-8
            @test final_size(sys; p = sc.params, initial = sc.initial, method = :ode) ≈ sc.expected[:final_size] atol = 1e-8
        end
    end

    @testset "gluing (H1) and the pushforward on the MFSH closure" begin
        net = mfsh_net(MSV_DEGREES)
        tr = open_model(ContactModel(:tr; contacts = [Contact(:S, :I, :E, :τ)]); legs = [[:S], [:E, :I]])
        pr = open_model(ContactModel(:pr; transitions = [NodeTransition(:E, :I, :σ), NodeTransition(:I, :R, :γ)]);
                        legs = [[:E, :I, :R]])
        glued = symbolic_ode(edge_based(glue(tr, pr; on = [:E, :I]), net))
        @test vector_fields_equal(glued, sum_contributions(lift_contributions(tr, net), lift_contributions(pr, net)))
        @test vector_fields_equal(glued, symbolic_ode(edge_based(seir_model(), net)))
        # an exit part lifted with the susceptible class it acts on (the ξ factor)
        vx = ContactModel(:vx; transitions = [NodeTransition(:S, :V, :ν)])
        sirv = glue(open_model(sir_model(); legs = [[:S, :I, :R]]), open_model(vx; legs = [[:S]]); on = [:S])
        parts = sum_contributions(lift_contributions(sir_model(), net), lift_contributions(vx, net; susceptible = [:S]))
        @test vector_fields_equal(symbolic_ode(edge_based(sirv, net)), symbolic_ode(parts))
        @test :ξ in state_names(symbolic_ode(parts))
        # a namespaced gluing: the parts pushed along the inclusions (the π and pop coordinates are renamed)
        g2 = glue(tr, pr; on = [:E, :I], namespace = true)
        pushed = sum_contributions(relabel(lift_contributions(tr, net), g2.inclusions[1]),
                                   relabel(lift_contributions(pr, net), g2.inclusions[2]))
        @test vector_fields_equal(symbolic_ode(edge_based(g2, net)), symbolic_ode(pushed))
        # a table on another network does not add
        @test_throws ArgumentError sum_contributions(lift_contributions(tr, net),
                                                     lift_contributions(pr, ConfigurationNetwork(MSV_DEGREES)))
    end

    @testset "symbolic degree parameters and the κ → 0 limit" begin
        μ = as_parameter(:μ)
        sμ = edge_based(sir_model(), mfsh_net(PoissonDegree(μ)))
        s5 = edge_based(sir_model(), mfsh_net(PoissonDegree(5.0)))
        p = Dict(:τ => 1 / 12, :γ => 1 / 4)
        grid = 0.0:1.0:100.0
        solμ = solve_epidemic(sμ; p = merge(p, Dict(:μ => 5.0)), initial = SeedFraction(:I => 0.01), tspan = (0.0, 100.0),
                              saveat = grid, TOL...)
        sol5 = solve_epidemic(s5; p, initial = SeedFraction(:I => 0.01), tspan = (0.0, 100.0), saveat = grid, TOL...)
        @test maximum(abs.(curve(sμ, solμ, :S) .- curve(s5, sol5, :S))) < 1e-12
        # mean degree 0: no stub, no contact; S stays 1 − ρ and nothing is NaN (verified issues E11, E32)
        for d in (RegularDegree(0), PoissonDegree(0.0))
            s0 = edge_based(sir_model(; τ = 1.0, γ = 0.25), mfsh_net(d))
            so = solve_epidemic(s0; initial = SeedFraction(:I => 0.01), tspan = (0.0, 50.0), TOL...)
            @test all(isfinite, reduce(vcat, so.u))
            @test curve(s0, so, :S)[end] ≈ 0.99 atol = 1e-14
            @test curve(s0, so, :cumulative)[end] ≈ 0.01 atol = 1e-12
        end
    end

    @testset "errors: inadmissible models, forms, seeds, names" begin
        net = mfsh_net(PoissonDegree(5.0))
        @test_throws AdmissibilityError edge_based(sis_model(), net)
        @test_throws AdmissibilityError edge_based(sirs_model(), net)
        @test_throws ArgumentError edge_based(sir_model(), net; form = :pairwise)
        @test_throws ArgumentError edge_based(seir_model(), net; form = :compact)          # not SIR-shaped
        @test_throws ArgumentError edge_based(sirv_model(), net; form = :compact)          # an exit
        c = edge_based(sir_model(), net; form = :compact)
        @test_throws ArgumentError default_initial_conditions(c; initial = SeedFraction(:I => 0.01, :R => 0.01))
        @test_throws ArgumentError default_initial_conditions(edge_based(sir_model(), net);
                                                              initial = SeedFraction(:I => 0.7, :R => 0.7))
        # two susceptible classes need a typed network (the admissibility check names the alternatives)
        @test_throws AdmissibilityError edge_based(stratify(sir_model(), [:a, :b]), net)
        # a parameter named like a generated coordinate or observable is refused (E26)
        for bad in (:π_I, :stub_hazard)
            cm = ContactModel(:bad; contacts = [Contact(:S, :I, :I, bad)], transitions = [NodeTransition(:I, :R, :γ)])
            @test_throws ArgumentError edge_based(cm, net)
        end
    end

    @testset "against NetworkOutbreaks' fleeting-contact process: :sir_mfsh_pois5 and :sir_mfsh_msv" begin
        # Acceptance (design §E.2, back ends declared :exact_limit): D∞(I) < 0.005 and |ΔR∞| < 0.005 on the
        # scenarios' own ensembles (N = 10⁴, 200 runs, fresh stub counts per run, 1% seeded).
        for id in (:sir_mfsh_pois5, :sir_mfsh_msv)
            sc = scenario(id)
            @test sc.backends[:edge_based] === :exact_limit
            tab, summary, _ = against_fleeting(sc)
            @test tab.n == sc.sim.nsims                              # 100 seeds: every run is major
            rows = Dict(r.observable => r for r in tab)
            fmt(f) = join(("$X $(round(f(rows[X]); sigdigits = 3))" for X in (:S, :I, :R)), ", ")
            @info "WP36c EB vs NetworkOutbreaks (fleeting contacts)" scenario = id N = sc.sim.N runs = tab.n D∞ = fmt(r -> r.D∞) SE∞ = fmt(r -> r.SE∞) z∞ = fmt(r -> r.z∞) ΔR∞ = rows[:I].ΔR∞ ΔR∞_ci = rows[:I].ΔR∞_ci
            @test rows[:I].D∞ < 0.005
            @test abs(rows[:I].ΔR∞) < 0.005
            @test rows[:I].ΔR∞_ci[1] < 0 < rows[:I].ΔR∞_ci[2]           # R∞ within its 95% interval
            @test all(rows[X].D∞ < 0.01 for X in (:S, :R, :cumulative))
        end
        # N-scaling: at N = 4×10⁴ every observable is within 0.005 and within Monte Carlo error; the
        # scenario's N = 10⁴ S-curve difference (0.0066, z 3.3 for :sir_mfsh_pois5) is finite-size bias
        sc = derive(scenario(:sir_mfsh_pois5); N = 40_000, nsims = 100)
        tab, _, _ = against_fleeting(sc)
        @info "WP36c EB vs NetworkOutbreaks at N = 4×10⁴" scenario = :sir_mfsh_pois5 runs = tab.n D∞_z∞ = join(("$(r.observable) $(round(r.D∞; sigdigits = 3)) (z $(round(r.z∞; sigdigits = 3)))" for r in tab), ", ")
        for r in tab
            @test r.D∞ < 0.005
            @test r.z∞ < 4
        end
    end

    @testset "against NetworkOutbreaks: SEIR, SEAIR, SIR + vaccination and removals on MFSH Poisson(5), N = 10⁴" begin
        # The general T_EB lift (latency, branching with two infectors, an exit out of S, the removal sink),
        # 100 runs each, 1% seeded.
        N = 10_000
        net = mfsh_net(PoissonDegree(5))
        cases = ((seir_model(), Dict(:τ => 1 / 6, :σ => 1 / 5, :γ => 1 / 4), SeedFraction(:E => 0.01), 150.0,
                  [:S, :E, :I, :R]),
                 (seair_model(), Dict(:τI => 1 / 6, :τA => 1 / 12, :σ => 1 / 5, :p => 0.6, :γ => 1 / 4),
                  SeedFraction(:E => 0.01), 200.0, [:S, :E, :A, :I, :R]),
                 (sirv_model(), Dict(:τ => 1 / 6, :γ => 1 / 4, :ν => 0.02), SeedFraction(:I => 0.01), 80.0,
                  [:S, :I, :R, :V]),
                 (ContactModel(:rem; contacts = [Contact(:S, :I, :I, :τ)], transitions = [NodeTransition(:I, nothing, :γ)]),
                  Dict(:τ => 1 / 12, :γ => 1 / 4), SeedFraction(:I => 0.01), 100.0, [:S, :I, :removed]))
        for (cm, p, initial, T, obs) in cases
            grid = collect(0.0:1.0:T)
            sys = edge_based(cm, net)
            sol = solve_epidemic(sys; p, initial, tspan = (0.0, T), saveat = grid, TOL...)
            eb = permutedims(reduce(hcat, [X === :S ? curve(sys, sol, :S) : curve(sys, sol, Symbol(:pop_, X)) for X in obs]))
            runs, n = no_runs(cm, net, p, initial, grid; N, nsims = 100, obs)
            @test length(runs) >= n - 2
            dd = discrepancy(eb, runs)
            @info "WP36c MFSH vs NetworkOutbreaks" model = cm.name N runs = n major = length(runs) D∞ = dd.D se_at_max = dd.se z∞ = dd.D / dd.se observable = obs[dd.at[1]] t = grid[dd.at[2]]
            @test dd.D < 0.01
            @test dd.D / dd.se < 4
        end
    end
end
