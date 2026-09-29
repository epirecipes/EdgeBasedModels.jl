# WP36f: heterogeneous susceptibility (DESIGN §K WP36f, §B.2, §C.2 `unstructured`, §D.5 M10, §E.2, §J.6, §J.7;
# Miller & Volz 2013 §2.2.2, papers/miller_volz.md). Several susceptible classes on one configuration network, as
# fixed node attributes: edge_based(model, net, st), the lift on unstructured(net, st) whose shared (unlabelled)
# species the multitype lift cannot take.
#
# - The lift: coordinates θ_<a>, φ_<Y>_<a>, pop_<Y>; the per-reaction terms; conservation θ_e = Σ_a φ_{s_a} + Σ_Y φ_{Y,e}
#   and Σ_a S_a + Σ pop = 1, with exits (vaccination of one class) and removals.
# - Acceptance 1, M10: the field is the quotient of the multitype lift of the stratified model on unstructured(net, st)
#   (a Semiconjugacy that `verify` checks, and equal trajectories); a fully stratified model gives the same node
#   curves through both closures; one class, and equal rates in every class, give the untyped configuration lift.
# - Literature: a hand transcription of Miller & Volz (2013) eqs. (7)–(8) (K² edge variables θ_{lj}, the leaky vaccine
#   of their Fig. 6 on NB(3/2, 8/9) degrees; and heterogeneous susceptibility alone), against the K-coordinate lift.
# - Threshold quantities: R₀ = κ_ex Σ_a n_a T_a, NetworkEpiCore's NGM and final size of the stratified model, the
#   final-size fixed point of the Miller–Volz equations.
# - Seeding: NetworkOutbreaks' placement on the typed graph (checked against NetworkOutbreaks.initial_state).
# - Composition (H1, relabel) and the errors.
# - Acceptance 2: validated against NetworkOutbreaks with per-class susceptibility (a local ensemble with the §E.2
#   protocol: N = 10⁴, 200 runs, a fresh typed graph per run from the stable_rng streams of §J.7, NextReaction,
#   MajorOutbreak(0.05)), with a negative control (the homogeneous model with the mean susceptibility).

using EdgeBasedModels
using NetworkEpiCore
using ModelingToolkit
using Symbolics
using LinearAlgebra
using OrdinaryDiffEq: ODEProblem, Vern9, solve as ode_solve
import NetworkOutbreaks as NO
using Test

const TOL = (solver = Vern9(), reltol = 1e-12, abstol = 1e-14)
const ST = strata([:lo, :hi]; sizes = [0.4, 0.6])
const P = Dict(:τ_lo => 0.05, :τ_hi => 0.3, :γ => 0.25)
const POIS5 = ConfigurationNetwork(PoissonDegree(5.0))
const BIMODAL = ConfigurationNetwork(EmpiricalDegree(Dict(2 => 5 / 6, 10 => 1 / 6)))   # excess degree 5, not PT

lab(base, a) = SpeciesLabel(base; stratum = a)
curve(sys, sol, X) = compartment(sys, sol, X)
maxdiff(a, b) = maximum(abs.(a .- b))

# A symbolic expression evaluated with values given by variable name (states θ_lo(t) are named θ_lo).
function numat(e, vals::AbstractDict{Symbol})
    sub = Dict{Any,Any}(x => vals[Symbol(Symbolics.getname(x))] for x in Symbolics.get_variables(e))
    return Float64(Symbolics.value(Symbolics.substitute(e, sub; fold = Val(true))))
end

# Heterogeneous susceptibility with a shared I and R: S_lo + I → 2I (τ_lo), S_hi + I → 2I (τ_hi), I → R (γ).
function het_sir(; τ_lo = :τ_lo, τ_hi = :τ_hi, γ = :γ)
    return ContactModel(:sir_het; contacts = [Contact(:S_lo, :I, :I, τ_lo), Contact(:S_hi, :I, :I, τ_hi)],
                        transitions = [NodeTransition(:I, :R, γ)],
                        labels = Dict(:S_lo => lab(:S, :lo), :S_hi => lab(:S, :hi)))
end

# The same model, stratified: S_a + I_b → I_a + I_b at τ_a, I_a → R_a.
strat_sir() = stratify(sir_model(), ST; contact_rates = (a, b) -> a === :lo ? :τ_lo : :τ_hi)

# A richer model: class-specific latent stages E_a (rates σ_a), a shared I and R, vaccination of the hi class into a
# shared V, and removal of the vaccinated at rate μ (to the sink `removed`).
function het_seirv()
    return ContactModel(:seirv_het;
        contacts = [Contact(:S_lo, :I, :E_lo, :τ_lo), Contact(:S_hi, :I, :E_hi, :τ_hi)],
        transitions = [NodeTransition(:E_lo, :I, :σ_lo), NodeTransition(:E_hi, :I, :σ_hi), NodeTransition(:I, :R, :γ),
                       NodeTransition(:S_hi, :V, :ν), NodeTransition(:V, nothing, :μ)],
        labels = Dict(:S_lo => lab(:S, :lo), :S_hi => lab(:S, :hi), :E_lo => lab(:E, :lo), :E_hi => lab(:E, :hi)))
end
const P_SEIRV = Dict(:τ_lo => 0.08, :τ_hi => 0.3, :σ_lo => 0.5, :σ_hi => 0.2, :γ => 0.25, :ν => 0.01, :μ => 0.05)

# The §E.2 reference ensemble of `model` on the typed network `net`, from NetworkOutbreaks.simulate with the
# scenario streams (graph r from stable_rng(b + r), run r from b + 2^32 + r; §J.7), a fresh graph per run and
# NextReaction, conditioned on MajorOutbreak(0.05) (cumulative incidence − seeds ≥ 0.05 by t_end): the pointwise
# mean and standard error over the major runs of each species, `:infectious` and `:cumulative` (fractions of N).
# `never` lists the compartments of nodes that were never infected (the susceptible classes, the vaccinated and their
# removal sink), so `:cumulative` = 1 − Σ never. (A NetworkEpiCore `Scenario`, hence `scenario_ensemble` and
# `summarise`, does not yet accept a seeded species shared by the node types of a MultitypeNetwork.)
function no_reference(model, net, p, initial, tspan; never, N = 10_000, nsims = 200, base = 20260926, step = 0.25)
    t = collect(range(tspan[1], tspan[2]; step))
    ens = NO.simulate(model, net; N, p, initial, tspan, nsims, seed = base, tgrid = t)
    om = ens.spec.model
    ρ0 = sum(last, seed_fractions(initial))
    fs = NO.final_size(ens)
    major = findall(f -> f - ρ0 >= 0.05, fs)
    row(tr, X) = tr.counts[om.index_of[X], :] ./ N
    series = Dict{Symbol,Function}(X => (tr -> row(tr, X)) for X in species_names(contact_model(model)))
    infectors = unique([c.infector for c in contacts(contact_model(model))])
    series[:infectious] = tr -> sum(row(tr, J) for J in infectors)
    series[:cumulative] = tr -> 1 .- sum(row(tr, X) for X in never)
    trajs = ens.trajectories
    cumfs = all(abs(series[:cumulative](tr)[end] - f) < 1e-12 for (tr, f) in zip(trajs, fs))
    n = length(major)
    mean = Dict{Symbol,Vector{Float64}}()
    se = Dict{Symbol,Vector{Float64}}()
    for (X, f) in series
        M = reduce(hcat, (f(trajs[r]) for r in major))           # grid × runs
        μ = vec(sum(M; dims = 2)) ./ n
        mean[X] = μ
        se[X] = sqrt.(vec(sum(abs2, M .- μ; dims = 2)) ./ (n - 1)) ./ sqrt(n)
    end
    fsm = sum(fs[major]) / n
    fsse = sqrt(sum(abs2, fs[major] .- fsm) / (n - 1)) / sqrt(n)
    return (t = t, N = N, runs = nsims, n = n, mean = mean, se = se, final_size = fsm, final_size_se = fsse,
            cumulative_is_final_size = cumfs)
end

# D∞ = max_t |x_det − x̄| and the standard error of the mean at the argmax (§E.2 metrics).
function deviation(x, ref, X)
    d = abs.(x .- ref.mean[X])
    k = argmax(d)
    return (D∞ = d[k], SE∞ = ref.se[X][k], t = ref.t[k])
end

# Node conservation Σ_a S_a + Σ pop = 1 and edge conservation θ_e = Σ_a φ_{s_a} + Σ_Y φ_{Y,e} (max over time).
function het_conservation(sys, sol)
    cls = sys.metadata[:classes]
    sus = [cls.susceptible[a] for a in cls.names]
    pops = [k for k in keys(sys.variables) if startswith(string(k), "pop_")]
    node = maxdiff(sum(curve(sys, sol, s) for s in sus) .+ sum(curve(sys, sol, k) for k in pops), 1)
    info = sys.metadata[:contributions].coordinate_info
    edge = 0.0
    for e in cls.names
        total = sum(curve(sys, sol, Symbol(:φ_, s)) for s in sus)
        for x in info
            (x.role === :φ && last(x.types) === e) && (total = total .+ curve(sys, sol, x.name))
        end
        edge = max(edge, maxdiff(curve(sys, sol, Symbol(:θ_, e)), total))
    end
    return node, edge
end

@testset "WP36f heterogeneous susceptibility" begin
    @testset "the lift: coordinates, per-reaction terms, conservation" begin
        sys = edge_based(het_sir(), POIS5, ST)
        md = sys.metadata
        @test md[:kind] === :assembled && md[:closure] === :heterogeneous
        @test md[:network] == unstructured(POIS5, ST)
        @test md[:susceptible] == [:S_lo, :S_hi] && md[:entry] === :I
        @test Set(keys(sys.variables)) ==
              Set([:θ_lo, :θ_hi, :φ_I_lo, :φ_I_hi, :φ_R_lo, :φ_R_hi, :pop_I, :pop_R, :cumulative, :R])
        for k in (:S_lo, :S_hi, :S, :φ_S_lo, :φ_S_hi, :I, :infectious, :edge_hazard_lo, :edge_hazard_hi)
            @test haskey(sys.observables, k)
        end
        # K classes give K θ's (the multitype lift of the stratified model has K²)
        mt = edge_based(strat_sir(), unstructured(POIS5, ST))
        @test count(x -> x.role === :θ, md[:contributions].coordinate_info) == 2
        @test count(x -> x.role === :θ, mt.metadata[:contributions].coordinate_info) == 4
        # per-reaction terms of the contact S_lo + I → 2I, by hand (n_lo = 0.4, ψ = exp(5(x − 1)))
        tab = lift_contributions(het_sir(), POIS5, ST)
        @test tab.closure === :heterogeneous && length(tab) == 3
        row = tab[:S_lo_I_to_I]
        @test row.type === :contact && row.from === :S_lo && row.to === :I
        at = Dict(:θ_lo => 0.7, :φ_I_lo => 0.2, :ξ_S_lo => 1.0, :τ_lo => 0.1, :q_S_lo => 0.9)
        num(e) = numat(e, at)
        terms = Dict{Symbol,Vector{Any}}()
        for (k, e) in row.terms
            push!(get!(terms, k, Any[]), e)
        end
        h = 0.1 * 0.2
        @test num(only(terms[:θ_lo])) ≈ -h rtol = 1e-14
        @test sum(num, terms[:φ_I_lo]) ≈ -h + h * 0.4 * 0.9 * 25exp(5(0.7 - 1)) / 5 rtol = 1e-14
        @test num(only(terms[:φ_I_hi])) ≈ h * 0.4 * 0.9 * 25exp(5(0.7 - 1)) / 5 rtol = 1e-14
        @test num(only(terms[:pop_I])) ≈ h * 0.4 * 0.9 * 5exp(5(0.7 - 1)) rtol = 1e-14
        @test num(row.flux) ≈ num(only(terms[:pop_I]))

        # SEIR with class-specific latent stages, vaccination of one class and removals: conservation with the sink
        sysv = edge_based(het_seirv(), BIMODAL, ST)
        @test haskey(sysv.variables, :ξ_S_hi) && !haskey(sysv.variables, :ξ_S_lo)
        @test haskey(sysv.variables, :pop_removed) && sysv.metadata[:sinks] == [:removed]
        @test Set(sysv.metadata[:infected]) == Set([:E_lo, :E_hi, :I])
        solv = solve_epidemic(sysv; p = P_SEIRV, initial = SeedFraction(:I => 0.01), tspan = (0.0, 200.0),
                              saveat = 1.0, TOL...)
        node, edge = het_conservation(sysv, solv)
        @test node < 1e-10 && edge < 1e-10
        # cumulative = 1 − susceptibles − vaccinated who were never infected (V is not an infected state)
        @test curve(sysv, solv, :cumulative)[end] ≈ 1 - curve(sysv, solv, :S_lo)[end] - curve(sysv, solv, :S_hi)[end] -
                                                    curve(sysv, solv, :pop_V)[end] - curve(sysv, solv, :pop_removed)[end] atol = 1e-10
        # the exit survival factor of the vaccinated class is exact: ξ̇ = −νξ
        @test maxdiff(curve(sysv, solv, :ξ_S_hi), exp.(-P_SEIRV[:ν] .* solv.t)) < 1e-10
        @test curve(sysv, solv, :pop_V)[end] + curve(sysv, solv, :pop_removed)[end] > 0.005
    end

    @testset "M10 (acceptance 1): the quotient of the stratified model on unstructured(net)" begin
        for base in (POIS5, BIMODAL)
            net = unstructured(base, ST)
            sys = edge_based(het_sir(), base, ST)
            mt = edge_based(strat_sir(), net)
            # the linear quotient θ_a = Σ_b n_b θ_{b→a}, φ_{Y,a} = Σ_b n_b φ_{Y_b,a}, pop_Y = Σ_b pop_{Y_b}
            src, tgt = symbolic_ode(mt), symbolic_ode(sys)
            u = mt.variables
            n = Dict(:lo => 0.4, :hi => 0.6)
            map = Pair{Any,Any}[]
            for a in (:lo, :hi)
                push!(map, sys.variables[Symbol(:θ_, a)] => sum(n[b] * u[Symbol(:θ_, b, :_, a)] for b in (:lo, :hi)))
                for Y in (:I, :R)
                    push!(map, sys.variables[Symbol(:φ_, Y, :_, a)] =>
                               sum(n[b] * u[Symbol(:φ_, Y, :_, b, :_, a)] for b in (:lo, :hi)))
                end
            end
            for Y in (:I, :R)
                push!(map, sys.variables[Symbol(:pop_, Y)] => u[Symbol(:pop_, Y, :_lo)] + u[Symbol(:pop_, Y, :_hi)])
            end
            m = Semiconjugacy(:M10_heterogeneous, src, tgt, map; kind = :semiconjugacy, exactness = :exact)
            res = verify(m)
            @test res.ok
            @info "WP36f M10 quotient (stratified multitype lift → heterogeneous lift) on $(nameof(typeof(base.degrees)))" res
            # a wrong quotient (unweighted sum) is rejected, so `verify` has power here
            bad = Pair{Any,Any}[k => (k === sys.variables[:θ_lo] ? u[:θ_lo_lo] : v) for (k, v) in map]
            @test !verify(Semiconjugacy(:bad, src, tgt, bad)).ok
            # trajectories: proportional seeds for the stratified model = uniform seeds of the shared I
            sol = solve_epidemic(sys; p = P, initial = SeedFraction(:I => 0.01), tspan = (0.0, 120.0), saveat = 1.0, TOL...)
            solm = solve_epidemic(mt; p = P, initial = SeedFraction(:I_lo => 0.004, :I_hi => 0.006), tspan = (0.0, 120.0),
                                  saveat = 1.0, TOL...)
            for a in (:lo, :hi)
                @test maxdiff(curve(sys, sol, Symbol(:S_, a)), curve(mt, solm, Symbol(:S_, a))) < 1e-10
                @test maxdiff(curve(sys, sol, Symbol(:θ_, a)),
                              sum(n[b] .* curve(mt, solm, Symbol(:θ_, b, :_, a)) for b in (:lo, :hi))) < 1e-10
            end
            @test maxdiff(curve(sys, sol, :pop_I), curve(mt, solm, :pop_I_lo) .+ curve(mt, solm, :pop_I_hi)) < 1e-10
            @test maxdiff(curve(sys, sol, :cumulative), curve(mt, solm, :cumulative)) < 1e-10
            node, edge = het_conservation(sys, sol)
            @test node < 1e-10 && edge < 1e-10
        end

        # A fully stratified model (every species labelled) through both closures: the same node curves, K vs K² θ's.
        # SEIR with class-specific rates, vaccination of one class and a removal, on the non-PT bimodal law.
        seir = seir_model(τ = :τ, σ = :σ, γ = :γ)
        full = stratify(seir, ST; contact_rates = (a, b) -> a === :lo ? :(τ * s_lo * i_b) : :(τ * i_b),
                        transition_rates = (t, a) -> t.from === :E ? (a === :lo ? :σ_lo : :σ) : :γ)
        full = ContactModel(:full; contacts = contacts(full),
            transitions = vcat(node_transitions(full), [NodeTransition(:S_hi, :V_hi, :ν), NodeTransition(:R_lo, nothing, :μ)]),
            species = vcat(species_names(full), [:V_hi]),
            labels = merge(species_labels(full), Dict(:V_hi => lab(:V, :hi))))
        pf = Dict(:τ => 0.2, :s_lo => 0.5, :i_b => 0.8, :σ_lo => 0.4, :σ => 0.2, :γ => 0.25, :ν => 0.01, :μ => 0.1)
        init = SeedFraction(:E_lo => 0.002, :E_hi => 0.003, :I_hi => 0.001)
        sysf = edge_based(full, BIMODAL, ST)
        mtf = edge_based(full, unstructured(BIMODAL, ST))
        @test count(x -> x.role === :θ, sysf.metadata[:contributions].coordinate_info) == 2
        solf = solve_epidemic(sysf; p = pf, initial = init, tspan = (0.0, 150.0), saveat = 1.0, TOL...)
        solmf = solve_epidemic(mtf; p = pf, initial = init, tspan = (0.0, 150.0), saveat = 1.0, TOL...)
        for X in (:S_lo, :S_hi, :cumulative)
            @test maxdiff(curve(sysf, solf, X), curve(mtf, solmf, X)) < 1e-10
        end
        for X in (:E_lo, :E_hi, :I_lo, :I_hi, :R_lo, :R_hi, :V_hi, :removed_lo)
            @test maxdiff(curve(sysf, solf, Symbol(:pop_, X)), curve(mtf, solmf, Symbol(:pop_, X))) < 1e-10
        end
        node, edge = het_conservation(sysf, solf)
        @test node < 1e-10 && edge < 1e-10

        # The unit law: one class is literally the untyped configuration lift (the same field up to renaming).
        one = strata([:a])
        sir1 = ContactModel(:sir1; contacts = [Contact(:S, :I, :I, :τ)], transitions = [NodeTransition(:I, :R, :γ)],
                            labels = Dict(:S => lab(:S, :a)))
        sys1 = edge_based(sir1, BIMODAL, one)
        ref = edge_based(sir_model(), BIMODAL)
        @test vector_fields_equal(symbolic_ode(sys1), symbolic_ode(ref);
                                  rename = Dict(:θ_a => :θ, :φ_I_a => :φ_I, :φ_R_a => :φ_R))
        # Equal rates in every class: θ_a = θ, φ_{X,a} = φ_X, S_a = n_a S (the diagonal embedding of M10).
        same = edge_based(het_sir(τ_lo = :τ, τ_hi = :τ), BIMODAL, ST)
        pp = Dict(:τ => 1 / 6, :γ => 1 / 4)
        sol = solve_epidemic(same; p = pp, initial = SeedFraction(:I => 0.01), tspan = (0.0, 100.0), saveat = 1.0, TOL...)
        solr = solve_epidemic(ref; p = pp, initial = SeedFraction(:I => 0.01), tspan = (0.0, 100.0), saveat = 1.0, TOL...)
        for a in (:lo, :hi)
            @test maxdiff(curve(same, sol, Symbol(:θ_, a)), curve(ref, solr, :θ)) < 1e-10
            @test maxdiff(curve(same, sol, Symbol(:φ_I_, a)), curve(ref, solr, :φ_I)) < 1e-10
        end
        @test maxdiff(curve(same, sol, :S_lo), 0.4 .* curve(ref, solr, :S)) < 1e-10
        @test maxdiff(curve(same, sol, :S), curve(ref, solr, :S)) < 1e-10
        @test maxdiff(curve(same, sol, :cumulative), curve(ref, solr, :cumulative)) < 1e-10
    end

    @testset "Miller & Volz (2013) §2.2.2, eqs. (7)–(8): a hand transcription" begin
        # θ_{lj}: an edge from a type-l partner to a type-j test node has not transmitted; θ̄_j = Σ_l Q(l) θ_{lj};
        #   θ̇_{lj} = −β_{lj}θ_{lj} + β_{lj} q ψ'(θ̄_l)/ψ'(1) + γ_l(1 − θ_{lj}),  S_j = qψ(θ̄_j),  Ṙ_j = γ_j I_j,
        #   I_j = 1 − S_j − R_j   (within-type fractions; q = 1 − ρ for a uniform seed ρ; MV2013 take q → 1).
        # The leaky vaccine of their Fig. 6: NB degrees ψ(x) = (9 − 8x)^{−3/2} (mean 12), half the population
        # vaccinated (v), who are half as susceptible and half as infectious and recover at twice the rate.
        ψ(x) = (9 - 8x)^(-1.5)
        ψ1(x) = 12 * (9 - 8x)^(-2.5)
        β0, γ0, ρ = 0.1, 0.3, 0.001
        types = (:u, :v)
        Q = Dict(:u => 0.5, :v => 0.5)
        s = Dict(:u => 1.0, :v => 0.5)                  # susceptibility of the test node
        i = Dict(:u => 1.0, :v => 0.5)                  # infectiousness of the partner
        γ = Dict(:u => γ0, :v => 2γ0)
        β(l, j) = β0 * i[l] * s[j]
        q = 1 - ρ
        idx = Dict((l, j) => k for (k, (l, j)) in enumerate([(l, j) for l in types for j in types]))
        function mv!(du, x, _, _)
            θbar(j) = sum(Q[l] * x[idx[(l, j)]] for l in types)
            for l in types, j in types
                k = idx[(l, j)]
                du[k] = -β(l, j) * x[k] + β(l, j) * q * ψ1(θbar(l)) / ψ1(1.0) + γ[l] * (1 - x[k])
            end
            for (m, j) in enumerate(types)
                du[4 + m] = γ[j] * (1 - q * ψ(θbar(j)) - x[4 + m])     # Ṙ_j = γ_j I_j
            end
        end
        tgrid = 0.0:1.0:120.0
        mvsol = ode_solve(ODEProblem(mv!, vcat(ones(4), zeros(2)), (0.0, 120.0)), Vern9(); reltol = 1e-12, abstol = 1e-14,
                          saveat = tgrid)
        θbar_mv(j) = [sum(Q[l] * x[idx[(l, j)]] for l in types) for x in mvsol.u]
        stv = strata([:u, :v]; sizes = [0.5, 0.5])
        vacc = stratify(sir_model(), stv; contact_rates = (a, b) -> β0 * s[a] * i[b], transition_rates = a -> γ[a])
        nb = ConfigurationNetwork(NegBinDegree(1.5, 1 / 9))
        sys = edge_based(vacc, nb, stv)
        sol = solve_epidemic(sys; initial = SeedFraction(:I_u => 0.5ρ, :I_v => 0.5ρ), tspan = (0.0, 120.0),
                             saveat = tgrid, TOL...)
        for (m, j) in enumerate(types)
            @test maxdiff(curve(sys, sol, Symbol(:θ_, j)), θbar_mv(j)) < 1e-9
            @test maxdiff(curve(sys, sol, Symbol(:S_, j)), 0.5 .* q .* ψ.(θbar_mv(j))) < 1e-9
            @test maxdiff(curve(sys, sol, Symbol(:pop_R_, j)), 0.5 .* [x[4 + m] for x in mvsol.u]) < 1e-9
        end
        @test curve(sys, sol, :cumulative)[end] > 0.3                     # a real epidemic, not a trivial match

        # Heterogeneous susceptibility alone (β_{lj} = τ_j, one γ): the same equations with a shared I and R.
        τc = Dict(:lo => P[:τ_lo], :hi => P[:τ_hi])
        n = Dict(:lo => 0.4, :hi => 0.6)
        ψp(x) = exp(5(x - 1))
        ψp1(x) = 5exp(5(x - 1))
        q2 = 0.99
        cls = (:lo, :hi)
        k2 = Dict((l, j) => k for (k, (l, j)) in enumerate([(l, j) for l in cls for j in cls]))
        function mv2!(du, x, _, _)
            θb(j) = sum(n[l] * x[k2[(l, j)]] for l in cls)
            for l in cls, j in cls
                k = k2[(l, j)]
                du[k] = -τc[j] * x[k] + τc[j] * q2 * ψp1(θb(l)) / 5 + P[:γ] * (1 - x[k])
            end
        end
        s2 = ode_solve(ODEProblem(mv2!, ones(4), (0.0, 120.0)), Vern9(); reltol = 1e-12, abstol = 1e-14, saveat = tgrid)
        sysh = edge_based(het_sir(), POIS5, ST)
        solh = solve_epidemic(sysh; p = P, initial = SeedFraction(:I => 0.01), tspan = (0.0, 120.0), saveat = tgrid, TOL...)
        for j in cls
            θb = [sum(n[l] * x[k2[(l, j)]] for l in cls) for x in s2.u]
            @test maxdiff(curve(sysh, solh, Symbol(:θ_, j)), θb) < 1e-9
            @test maxdiff(curve(sysh, solh, Symbol(:S_, j)), n[j] .* q2 .* ψp.(θb)) < 1e-9
        end
    end

    @testset "threshold quantities and the final size" begin
        for base in (POIS5, BIMODAL)
            sys = edge_based(het_sir(), base, ST)
            κ = excess_degree(base)
            T = Dict(a => P[Symbol(:τ_, a)] / (P[Symbol(:τ_, a)] + P[:γ]) for a in (:lo, :hi))
            R0 = κ * (0.4 * T[:lo] + 0.6 * T[:hi])
            @test basic_reproduction_number(sys; p = P) ≈ R0 rtol = 1e-12
            K = next_generation_matrix(sys; p = P)                           # rank one: K_{e,c} = κ_ex n_c T_c
            @test size(K) == (2, 2)
            @test sort(vec(K)) ≈ sort([κ * 0.4 * T[:lo], κ * 0.6 * T[:hi], κ * 0.4 * T[:lo], κ * 0.6 * T[:hi]]) rtol = 1e-12
            # NetworkEpiCore's own NGM of the stratified model on the same network (independent code)
            net = unstructured(base, ST)
            @test basic_reproduction_number(sys; p = P) ≈ basic_reproduction_number(strat_sir(), net, P) rtol = 1e-10
            @test early_growth_rate(sys; p = P) ≈ early_growth_rate(edge_based(strat_sir(), net); p = P) rtol = 1e-10
            @test_throws ArgumentError transmissibility(sys; p = P)
            # the final size: the ODE, NetworkEpiCore's fixed point of the stratified model, and the fixed point of
            # the Miller–Volz equations θ_c = T_c Σ_b σ_b ψ'(θ_b)/ψ'(1) + 1 − T_c (φ_R = γ(1 − θ)/τ), σ_b = 0.99 n_b
            fs = final_size(sys; p = P, initial = SeedFraction(:I => 0.01), method = :ode)
            @test fs ≈ final_size(strat_sir(), net, P; initial = SeedFraction(:I_lo => 0.004, :I_hi => 0.006)) atol = 1e-8
            d = base.degrees
            σ = Dict(:lo => 0.99 * 0.4, :hi => 0.99 * 0.6)
            θ = Dict(:lo => 1.0, :hi => 1.0)
            for _ in 1:100_000
                edgeS = sum(σ[b] * pgf_derivative(d, θ[b], 1) for b in (:lo, :hi)) / mean_degree(d)
                θ = Dict(c => T[c] * edgeS + 1 - T[c] for c in (:lo, :hi))
            end
            @test fs ≈ 1 - sum(σ[c] * pgf(d, θ[c]) for c in (:lo, :hi)) atol = 1e-8
        end
    end

    @testset "seeding: NetworkOutbreaks' placement on the typed graph (§J.6)" begin
        sys = edge_based(het_seirv(), POIS5, ST)
        v = sys.variables
        ps = parameters(sys.system)
        qpar(s) = only(filter(x -> Symbol(Symbolics.getname(x)) === Symbol(:q_, s), ps))
        # uniform shared seeds: q_a = 1 − ρ; φ_{Y,a}(0) = pop_Y(0) = ρ_Y
        ic = default_initial_conditions(sys; initial = SeedFraction(:I => 0.01))
        @test ic[qpar(:S_lo)] ≈ 0.99 && ic[qpar(:S_hi)] ≈ 0.99
        @test ic[v[:φ_I_lo]] == 0.01 && ic[v[:φ_I_hi]] == 0.01 && ic[v[:pop_I]] == 0.01 && ic[v[:cumulative]] == 0.01
        @test ic[v[:θ_lo]] == 1.0 && ic[v[:ξ_S_hi]] == 1.0
        # the default: the unique entry state? (two entries E_lo, E_hi: an explicit initial is needed)
        @test_throws ArgumentError default_initial_conditions(sys)
        icd = default_initial_conditions(edge_based(het_sir(), POIS5, ST))           # entry I, ε = 10⁻³, uniform
        sysd = edge_based(het_sir(), POIS5, ST)
        @test icd[only(filter(x -> Symbol(Symbolics.getname(x)) === :q_S_lo, parameters(sysd.system)))] ≈ 0.999
        # the cases of `_het_susceptible_fractions`, by hand, and NetworkOutbreaks' own placement at N = 10⁵
        om = NO.OutbreakModel(het_seirv(), P_SEIRV; network = unstructured(POIS5, ST))
        g, _ = NO.sample_graph(unstructured(POIS5, ST), 100_000; rng = NO.stable_rng(36))
        cases = [SeedFraction(:I => 0.01),
                 SeedFraction(:E_lo => 0.004, :I => 0.006),                 # a class-specific and a shared seed
                 SeedFraction(:S_lo => 0.3, :I => 0.01),                    # a named susceptible class
                 SeedFraction(:E_hi => 0.02, :S_hi => 0.5, :V => 0.03),     # V is shared (vaccinated at t = 0)
                 SeedFraction(:I => 0.01, :E_lo => 0.1; default = :V)]      # the rest vaccinated
        for init in cases
            ic = default_initial_conditions(sys; initial = init)
            σ = Dict(a => 0.4 * ic[qpar(:S_lo)] for a in (:lo,))
            σ[:hi] = 0.6 * ic[qpar(:S_hi)]
            state = NO.initial_state(NO.OutbreakSpec(om, g, init, (0.0, 1.0)), NO.stable_rng(37))
            frac(X) = count(==(om.index_of[X]), state) / length(state)
            @test abs(frac(:S_lo) - σ[:lo]) < 2e-3
            @test abs(frac(:S_hi) - σ[:hi]) < 2e-3
            for X in (:E_lo, :E_hi, :I, :V)
                @test abs(frac(X) - ic[v[Symbol(:pop_, X)]]) < 2e-3
            end
            @test sum(frac(X) for X in (:S_lo, :S_hi, :E_lo, :E_hi, :I, :V)) ≈ 1
        end
        # by hand: SeedFraction(:S_lo => 0.3, :I => 0.01) leaves f = (0.1, 0.6), and 1/70 of them take the shared I
        ic = default_initial_conditions(sys; initial = SeedFraction(:S_lo => 0.3, :I => 0.01))
        @test 0.4 * ic[qpar(:S_lo)] ≈ 0.3 + 0.1 * (1 - 0.01 / 0.7) rtol = 1e-14
        @test 0.6 * ic[qpar(:S_hi)] ≈ 0.6 * (1 - 0.01 / 0.7) rtol = 1e-14
        # the default takes every node that would have been susceptible
        ic = default_initial_conditions(sys; initial = SeedFraction(:I => 0.01, :E_lo => 0.1; default = :V))
        @test ic[qpar(:S_lo)] == 0 && ic[qpar(:S_hi)] == 0 && ic[v[:pop_V]] ≈ 0.89
        # errors: too many nodes in the compartments of a class (seeds, or a named susceptible class), a default with
        # a class, a sink, an unknown species
        @test_throws ArgumentError default_initial_conditions(sys; initial = SeedFraction(:E_lo => 0.5))
        @test_throws ArgumentError default_initial_conditions(sys; initial = SeedFraction(:S_lo => 0.45, :I => 0.01))
        @test_throws ArgumentError default_initial_conditions(sys; initial = SeedFraction(:I => 0.01; default = :S_lo))
        @test_throws ArgumentError default_initial_conditions(sys; initial = SeedFraction(:I => 0.01; default = :E_hi))
        @test_throws ArgumentError default_initial_conditions(sys; initial = SeedFraction(:removed => 0.01))
        @test_throws ArgumentError default_initial_conditions(sys; initial = SeedFraction(:Z => 0.01))
        # SeedCount needs N; with N it is the same seeding
        icc = default_initial_conditions(sys; initial = SeedCount(:I => 100), N = 10_000)
        @test icc[qpar(:S_hi)] ≈ 0.99 && icc[v[:pop_I]] ≈ 0.01
        # the initially susceptible fractions are set by `initial`, never by p
        @test_throws ArgumentError solve_epidemic(sys; p = merge(P_SEIRV, Dict(:q_S_lo => 0.5)),
                                                  initial = SeedFraction(:I => 0.01), tspan = (0.0, 1.0))
    end

    @testset "composition: gluing (H1) and relabelling" begin
        L = Dict(:S_lo => lab(:S, :lo), :S_hi => lab(:S, :hi))
        tr = open_model(ContactModel(:tr; contacts = [Contact(:S_lo, :I, :E, :τ_lo), Contact(:S_hi, :I, :E, :τ_hi)],
                                     labels = L); legs = [[:S_lo, :S_hi], [:E, :I]])
        pr = open_model(ContactModel(:pr; transitions = [NodeTransition(:E, :I, :σ), NodeTransition(:I, :R, :γ)]);
                        legs = [[:E, :I, :R]])
        glued = glue(tr, pr; on = [:E, :I])
        sys = edge_based(glued, BIMODAL, ST)
        parts = sum_contributions(lift_contributions(tr, BIMODAL, ST), lift_contributions(pr, BIMODAL, ST))
        @test parts.closure === :heterogeneous
        @test vector_fields_equal(symbolic_ode(sys), symbolic_ode(parts))
        # relabel: the lift of a renamed model is the pushforward of the lift (Lean `NEP.lift_map`)
        renamed = ContactModel(:sir_het2; contacts = [Contact(:S_lo, :J, :J, :τ_lo), Contact(:S_hi, :J, :J, :τ_hi)],
                               transitions = [NodeTransition(:J, :R, :γ)], labels = L)
        pushed = relabel(lift_contributions(renamed, POIS5, ST), Dict(:J => :I))
        @test vector_fields_equal(symbolic_ode(pushed), symbolic_ode(lift_contributions(het_sir(), POIS5, ST)))
    end

    @testset "§L.7: edge_based(het, unstructured(net, st)) and edge_based(sc::Scenario)" begin
        # design §L.7: the lift on the typed network, like NetworkOutbreaks' simulate(het, unstructured(net, st)),
        # is the same system as edge_based(het, net, st)
        for (model, base, p, init) in ((het_sir(), POIS5, P, SeedFraction(:I => 0.01)),
                                       (het_seirv(), BIMODAL, P_SEIRV, SeedFraction(:E_lo => 0.004, :E_hi => 0.006)))
            s3 = edge_based(model, base, ST)
            su = edge_based(model, unstructured(base, ST))
            @test su.metadata[:closure] === :heterogeneous && su.metadata[:network] == unstructured(base, ST)
            @test vector_fields_equal(symbolic_ode(su), symbolic_ode(s3))
            @test Set(keys(su.variables)) == Set(keys(s3.variables))
            sol3 = solve_epidemic(s3; p, initial = init, tspan = (0.0, 100.0), saveat = 1.0, TOL...)
            solu = solve_epidemic(su; p, initial = init, tspan = (0.0, 100.0), saveat = 1.0, TOL...)
            for X in (:S_lo, :S_hi, :cumulative, :pop_I)
                @test maxdiff(curve(su, solu, X), curve(s3, sol3, X)) < 1e-12
            end
            # final_size(sys) chooses the ODE route for these systems (NetworkEpiCore's fixed point assigns
            # every species to a node type), so the default method needs no `method = :ode`
            @test final_size(su; p, initial = init) ≈ final_size(s3; p, initial = init, method = :ode) atol = 1e-10
        end
        # the scenario form: a Scenario on unstructured(net, st) whose seeds are class-specific (E_lo, E_hi)
        sc = Scenario(:het_seirv_l7; model = het_seirv(), network = unstructured(BIMODAL, ST), params = P_SEIRV,
                      initial = SeedFraction(:E_lo => 0.004, :E_hi => 0.006), tspan = (0.0, 100.0), tstep = 1.0)
        ssc = edge_based(sc)
        @test ssc.metadata[:closure] === :heterogeneous
        solsc = solve_epidemic(ssc, sc; TOL...)
        ref = edge_based(het_seirv(), BIMODAL, ST)
        solref = solve_epidemic(ref; p = P_SEIRV, initial = sc.initial, tspan = sc.tspan, saveat = sc.tgrid, TOL...)
        @test maxdiff(curve(ssc, solsc, :cumulative), curve(ref, solref, :cumulative)) < 1e-12
        mc = model_curves(ssc, solsc; t = sc.tgrid)
        @test haskey(mc.values, :S_lo) && haskey(mc.values, :S_hi) && haskey(mc.values, :I)
        # on a structured MultitypeNetwork the hook does not apply: shared species need stratify
        sbm = sbm_network(ST; mean_contacts = [4.0 2.0; 4 / 3 5.0])
        @test_throws ArgumentError edge_based(het_sir(), sbm)
    end

    @testset "errors" begin
        # without the strata a model with several susceptible classes has no class sizes (:multiple_sus)
        @test_throws AdmissibilityError edge_based(het_sir(), POIS5)
        # susceptible classes must be labelled, one per stratum
        @test_throws AdmissibilityError edge_based(sir_model(), POIS5, ST)
        two = ContactModel(:two; contacts = [Contact(:S1, :I, :I, :τ), Contact(:S2, :I, :I, :τ)],
                           transitions = [NodeTransition(:I, :R, :γ)],
                           labels = Dict(:S1 => lab(:S, :lo), :S2 => lab(:S, :lo)))
        @test_throws AdmissibilityError edge_based(two, POIS5, ST)
        # a node may enter only species of its own class, or shared ones
        cross = ContactModel(:cross; contacts = [Contact(:S_lo, :I, :E_hi, :τ), Contact(:S_hi, :I, :E_hi, :τ)],
                             transitions = [NodeTransition(:E_hi, :I, :σ), NodeTransition(:I, :R, :γ)],
                             labels = Dict(:S_lo => lab(:S, :lo), :S_hi => lab(:S, :hi), :E_hi => lab(:E, :hi)))
        err = try
            edge_based(cross, POIS5, ST)
            nothing
        catch e
            e
        end
        @test err isa ArgumentError && occursin("fixed node attributes", err.msg)
        forget = ContactModel(:forget; contacts = [Contact(:S_lo, :I, :I, :τ), Contact(:S_hi, :I, :I, :τ)],
                              transitions = [NodeTransition(:I, :R_lo, :γ)],
                              labels = Dict(:S_lo => lab(:S, :lo), :S_hi => lab(:S, :hi), :R_lo => lab(:R, :lo)))
        @test_throws ArgumentError edge_based(forget, POIS5, ST)       # a shared I does not know its class
        vac = ContactModel(:vac; contacts = contacts(het_sir()),
                           transitions = [NodeTransition(:I, :R, :γ), NodeTransition(:S_lo, :V_hi, :ν)],
                           species = [:S_lo, :S_hi, :I, :R, :V_hi],
                           labels = Dict(:S_lo => lab(:S, :lo), :S_hi => lab(:S, :hi), :V_hi => lab(:V, :hi)))
        @test_throws ArgumentError edge_based(vac, POIS5, ST)          # an exit into another class
        # a species of an unknown class
        odd = ContactModel(:odd; contacts = contacts(het_sir()), transitions = [NodeTransition(:I, :R, :γ)],
                           labels = Dict(:S_lo => lab(:S, :lo), :S_hi => lab(:S, :hi), :R => lab(:R, :mid)))
        @test_throws ArgumentError edge_based(odd, POIS5, ST)
        # only the expanded form; only unstructured networks for shared species
        @test_throws ArgumentError edge_based(het_sir(), POIS5, ST; form = :compact)
        sbm = sbm_network(ST; mean_contacts = [4.0 2.0; 4 / 3 5.0])
        @test_throws ArgumentError EdgeBasedModels._heterogeneous_lift(het_sir(), sbm)
        # stratified rates must be per contact
        fd = ContactModel(:fd; contacts = contacts(het_sir()), transitions = node_transitions(het_sir()),
                          labels = species_labels(het_sir()), convention = FrequencyDependent())
        @test_throws ArgumentError edge_based(fd, POIS5, ST)
    end

    @testset "acceptance 2: validated against NetworkOutbreaks with per-class susceptibility" begin
        # The §E.2 protocol (N = 10⁴, 200 runs, a fresh typed graph per run from the stable_rng streams of §J.7,
        # NextReaction, MajorOutbreak(0.05), tgrid step 0.25). NetworkOutbreaks seeds the shared I uniformly and
        # starts every other class-a node in S_a (its TypedGraph seeding), as the lift assumes.
        cases = [(id = :sir_hetsus_bim, model = het_sir(), base = BIMODAL, p = P, tspan = (0.0, 60.0),
                  never = [:S_lo, :S_hi]),
                 (id = :seirv_hetsus_pois5, model = het_seirv(), base = POIS5, p = P_SEIRV, tspan = (0.0, 120.0),
                  never = [:S_lo, :S_hi, :V, :removed])]
        init = SeedFraction(:I => 0.01)
        refs = Dict{Symbol,Any}()
        for c in cases
            ref = no_reference(c.model, unstructured(c.base, ST), c.p, init, c.tspan; never = c.never)
            refs[c.id] = ref
            # the cumulative incidence read from the counts is NetworkOutbreaks' structural final size
            @test ref.cumulative_is_final_size
            @test ref.n >= 195                                   # P(major) ≈ 1 with ρN = 100 seeds
            sys = edge_based(c.model, c.base, ST)
            sol = solve_epidemic(sys; p = c.p, initial = init, tspan = c.tspan, saveat = ref.t, TOL...)
            mc = model_curves(sys, sol; t = ref.t, label = "EB")
            @test Set(keys(ref.mean)) ⊆ Set(keys(mc.values))
            rows = Dict(X => deviation(mc.values[X], ref, X) for X in keys(ref.mean))
            for (X, r) in rows
                @test r.D∞ < 0.01
            end
            # the §E.2 tolerances of an :exact_limit back end, and each susceptibility class
            @test rows[:infectious].D∞ < 0.005
            @test rows[:S_lo].D∞ < 0.005 && rows[:S_hi].D∞ < 0.005
            ΔR∞ = mc.values[:cumulative][end] - ref.final_size
            @test abs(ΔR∞) < 0.005
            @info "WP36f: heterogeneous lift vs NetworkOutbreaks, $(c.id)" N = ref.N runs = ref.runs major = ref.n D∞_I = rows[:infectious].D∞ SE∞_I = rows[:infectious].SE∞ D∞_S_lo = rows[:S_lo].D∞ D∞_S_hi = rows[:S_hi].D∞ D∞_max = maximum(r.D∞ for r in values(rows)) ΔR∞ ΔR∞_se = ref.final_size_se
        end
        # negative control: the homogeneous model with the mean susceptibility τ̄ = Σ_a n_a τ_a misses the ensemble
        ref = refs[:sir_hetsus_bim]
        τbar = 0.4 * P[:τ_lo] + 0.6 * P[:τ_hi]
        homo = edge_based(sir_model(τ = τbar, γ = P[:γ]), BIMODAL)
        solh = solve_epidemic(homo; initial = init, tspan = (0.0, 60.0), saveat = ref.t, TOL...)
        mch = model_curves(homo, solh; t = ref.t, label = "homogeneous")
        rI = deviation(mch.values[:infectious], ref, :infectious)
        ΔR∞h = mch.values[:cumulative][end] - ref.final_size
        sysh = edge_based(het_sir(), BIMODAL, ST)
        solhet = solve_epidemic(sysh; p = P, initial = init, tspan = (0.0, 60.0), saveat = ref.t, TOL...)
        rhet = deviation(model_curves(sysh, solhet; t = ref.t).values[:infectious], ref, :infectious)
        @test abs(ΔR∞h) > 0.03
        @test rI.D∞ > 5 * rhet.D∞
        @info "WP36f negative control (mean susceptibility τ̄ on the same network)" D∞_I = rI.D∞ ΔR∞ = ΔR∞h
    end
end
