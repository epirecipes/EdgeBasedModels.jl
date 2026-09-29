# WP36a: the edge-based lift on DegreeCorrelatedNetwork (DESIGN_NetworkEpiCore.md §K WP36a, §C.3): one θ per degree
# class, Wang, Ma, Cao & Li (2018, J. Theor. Biol. 454:164; papers/degreecorrelation.md eqs (21)–(24)), extended
# reaction by reaction; verified issue E20 (support restriction).
#
# Acceptance (§K WP36a):
#   1. R₀ = ρ of the (l − 1)Q(l | k) next-generation matrix agrees with NetworkEpiCore's NGM;
#   2. r = 0 reproduces the uncorrelated edge-based model to 1e-10;
#   3. D∞ < 0.01 against NetworkOutbreaks on :sir_dc_bim_{r0,r05,rn05} (a local ensemble with the scenarios' own
#      protocol, §E.2: N = 10⁴, 200 runs, a fresh 2K graph per run from the stable_rng streams of §J.7, NextReaction,
#      conditioned on MajorOutbreak(0.05)), until WP30 commits the summaries.
# Also: the field is Wang et al.'s (hand transcription), the lift is the exact quotient of the multitype lift of
# MultitypeNetwork(net) (branching, two infectors, exits), conservation, the NetworkEpiCore final size, the legacy
# CorrelatedPGF bridge (E20) and the error texts.

using EdgeBasedModels
using NetworkEpiCore
using LinearAlgebra
using Random
using Symbolics
using OrdinaryDiffEq: Vern9
using Test

import NetworkOutbreaks as NO

const TOL = (solver = Vern9(), reltol = 1e-11, abstol = 1e-13)
const BIMODAL = EmpiricalDegree(Dict(2 => 5 / 6, 10 => 1 / 6))

# A three-class law with isolated and degree-1 nodes, and a random symmetric edge-end matrix with the right marginals
# (e = diag(q)·Q with Q a random stochastic matrix obeying detailed balance, via a random symmetric positive matrix
# scaled by Sinkhorn to row sums q).
function random_edge_ends(q::Vector{Float64}, rng)
    K = length(q)
    A = rand(rng, K, K) .+ 0.1
    A = A + A'
    a = ones(K)
    for _ in 1:10_000
        a .= sqrt.(a .* q ./ (A * a))
    end
    e = a .* A .* a'
    return (e + e') / 2
end

function three_class_network(rng)
    ks = [0, 1, 3, 6]
    p = [0.1, 0.2, 0.4, 0.3]
    kbar = sum(ks .* p)
    q = ks[2:end] .* p[2:end] ./ kbar
    e = zeros(7, 7)
    e[ks[2:end] .+ 1, ks[2:end] .+ 1] .= random_edge_ends(q, rng)
    pfull = zeros(7)
    pfull[ks .+ 1] .= p
    return degree_correlated(pfull, e)
end

Qmatrix(net) = net.edge_ends ./ sum(net.edge_ends; dims = 2)

# Evaluate a symbolic expression at a point given by variable name (states and parameters alike).
function evaluate(e, point::AbstractDict{Symbol})
    sub = Dict{Any,Any}(v => point[Symbol(Symbolics.getname(v))] for v in Symbolics.get_variables(e))
    return Float64(Symbolics.value(Symbolics.substitute(e, sub; fold = Val(true))))
end

# The linearisation of the lifted field (symbolic_ode(sys), with q_S a parameter) at the disease-free state over the
# φ coordinates of `chain`: the symbolic Jacobian J there and the names of those coordinates. `ngm_parts` evaluates
# F = J(q = 1) − J(q = 0) (new infections) and V = −J(q = 0) numerically at the parameter values `p`.
function linearisation(sys, chain::Vector{Symbol})
    raw = symbolic_ode(sys)
    info = sys.metadata[:contributions].coordinate_info
    states = collect(raw.states)
    coord(s) = info[findfirst(x -> isequal(x.var, s), info)]
    idx = [i for (i, s) in enumerate(states) if coord(s).role === :φ && coord(s).species in chain]
    J = Symbolics.jacobian(collect(raw.rhs)[idx], states[idx])
    dfe = Dict{Symbol,Float64}(coord(s).name => (coord(s).role in (:θ, :ξ) ? 1.0 : 0.0) for s in states)
    return (J = J, dfe = dfe, names = [coord(states[i]).name for i in idx])
end
function ngm_parts(L, p::AbstractDict{Symbol})
    point(qv) = merge(L.dfe, Dict{Symbol,Float64}(:q_S => qv), Dict{Symbol,Float64}(p))
    J1 = [evaluate(x, point(1.0)) for x in L.J]
    J0 = [evaluate(x, point(0.0)) for x in L.J]
    return J1 .- J0, -J0
end
ngm_parts(sys, p::AbstractDict{Symbol}, chain::Vector{Symbol}) = ngm_parts(linearisation(sys, chain), p)

@testset "degree-correlated lift (WP36a)" begin
    @testset "coordinates, observables and the per-reaction table" begin
        sc = scenario(:sir_dc_bim_r05)
        sys = edge_based(sc)
        @test sys.metadata[:kind] === :assembled && sys.metadata[:closure] === :degree_correlated
        @test sys.metadata[:network] == sc.network
        for x in (:θ_k2, :θ_k10, :φ_I_k2, :φ_I_k10, :φ_R_k2, :φ_R_k10, :pop_I, :pop_R, :cumulative, :R)
            @test haskey(sys.variables, x)
        end
        @test !haskey(sys.variables, :ξ)                          # no exits: ξ ≡ 1 is dropped
        for x in (:S, :I, :infectious, :S_k2, :S_k10, :φ_S_k2, :φ_S_k10, :edge_hazard_k2, :edge_hazard_k10)
            @test haskey(sys.observables, x)
        end
        table = sys.metadata[:contributions]
        @test table.closure === :degree_correlated && length(table) == 2
        @test [r.type for r in table] == [:contact, :progress]
        # lift_contributions gives the same table
        @test [first(c) for c in lift_contributions(sc.model, sc.network).coordinates] ==
              [first(c) for c in table.coordinates]
        # a degree-0 class has a susceptible observable but no coordinates; degree 1 has coordinates
        net3 = three_class_network(Random.MersenneTwister(3))
        sys3 = edge_based(sir_model(), net3)
        @test haskey(sys3.observables, :S_k0) && !haskey(sys3.variables, :θ_k0)
        @test haskey(sys3.variables, :θ_k1) && haskey(sys3.variables, :φ_I_k6)
    end

    @testset "errors" begin
        net = scenario(:sir_dc_bim_r05).network
        err = try
            edge_based(sir_model(), net; form = :compact)
        catch e
            e
        end
        @test err isa ArgumentError && occursin("only the expanded form", err.msg)
        # two susceptible classes: NetworkEpiCore's admissibility refuses them on an untyped descriptor
        @test_throws AdmissibilityError edge_based(stratify(sir_model(), [:k2, :k10]), net)
        # strata that pass admissibility (one stratum) are refused by the lift, which names the multitype form
        err = try
            edge_based(stratify(sir_model(), [:k2]), net)
        catch e
            e
        end
        @test err isa ArgumentError && occursin("MultitypeNetwork(net)", err.msg) && occursin("k2, k10", err.msg)
        @test_throws AdmissibilityError edge_based(sis_model(), net)
        @test_throws AdmissibilityError edge_based(sirs_model(), net)
    end

    @testset "the field is Wang et al. (2018) eqs (21)–(24)" begin
        # θ_k' = −τφ_k (21); φ_k' = −(τ + γ)φ_k + qτ Σ_l (l − 1)Q(l | k)θ_l^{l−2}φ_l (23); pop_I' = qτ Σ_k k p_k
        # θ_k^{k−1}φ_k − γ pop_I (24b); S = q Σ_k p_k θ_k^k (24a). Eq. (23) as printed has θ_l^{l−1}; the derivative
        # of their h_k = q Σ_l Q(l | k)θ_l^{l−1} (eq. (22)) gives θ_l^{l−2}, which is also what reduces (23) to
        # Miller's eq. (15), qτψ''(θ)/ψ'(1)·φ, when Q(l | k) = l p_l/⟨k⟩. φ_{R,k}' = γφ_k closes the lift.
        rng = Random.MersenneTwister(20260926)
        for net in (scenario(:sir_dc_bim_r05).network, scenario(:sir_dc_bim_rn05).network, three_class_network(rng))
            sys = edge_based(sir_model(), net)
            raw = symbolic_ode(sys)
            ks = net.degrees
            p = net.probabilities
            Q = Qmatrix(net)
            E = findall(>(0), ks)
            cls = [Symbol("k", k) for k in ks]
            for trial in 1:5
                pt = Dict{Symbol,Float64}(:τ => rand(rng), :γ => rand(rng), :q_S => rand(rng))
                for i in E
                    pt[Symbol(:θ_, cls[i])] = 0.2 + 0.8rand(rng)
                    pt[Symbol(:φ_I_, cls[i])] = 0.3rand(rng)
                    pt[Symbol(:φ_R_, cls[i])] = 0.3rand(rng)
                end
                pt[:pop_I] = 0.2rand(rng)
                pt[:pop_R] = 0.2rand(rng)
                τ, γ, q = pt[:τ], pt[:γ], pt[:q_S]
                θ(i) = pt[Symbol(:θ_, cls[i])]
                φ(i) = pt[Symbol(:φ_I_, cls[i])]
                hand = Dict{Symbol,Float64}()
                for i in E
                    hand[Symbol(:θ_, cls[i])] = -τ * φ(i)
                    hand[Symbol(:φ_I_, cls[i])] = -(τ + γ) * φ(i) +
                        q * τ * sum((ks[j] - 1) * Q[i, j] * θ(j)^(ks[j] - 2) * φ(j) for j in E if ks[j] > 1; init = 0.0)
                    hand[Symbol(:φ_R_, cls[i])] = γ * φ(i)
                end
                hand[:pop_I] = q * τ * sum(ks[i] * p[i] * θ(i)^(ks[i] - 1) * φ(i) for i in E) - γ * pt[:pop_I]
                hand[:pop_R] = γ * pt[:pop_I]
                for (s, f) in zip(raw.states, raw.rhs)
                    name = Symbol(Symbolics.getname(s))
                    @test evaluate(f, pt) ≈ hand[name] rtol = 1e-12 atol = 1e-14
                end
            end
            @test length(raw.states) == 3length(E) + 2
            # (24a) along a solution: S = q Σ_k p_k θ_k^k, and the per-class fractions p_k qθ_k^k
            ρ = 0.01
            sol = solve_epidemic(sys; p = Dict(:τ => 0.3, :γ => 0.25), initial = SeedFraction(:I => ρ),
                                 tspan = (0.0, 40.0), saveat = 0:0.5:40, TOL...)
            θs = [ks[i] > 0 ? compartment(sys, sol, Symbol(:θ_, cls[i])) : ones(length(sol.t)) for i in eachindex(ks)]
            S24 = (1 - ρ) .* sum(p[i] .* θs[i] .^ ks[i] for i in eachindex(ks))
            @test maximum(abs.(compartment(sys, sol, :S) .- S24)) < 1e-12
            for i in eachindex(ks)
                @test maximum(abs.(compartment(sys, sol, Symbol(:S_, cls[i])) .- (1 - ρ) .* p[i] .* θs[i] .^ ks[i])) < 1e-12
            end
        end
    end

    @testset "acceptance 2: r = 0 reproduces the uncorrelated edge-based model (1e-10)" begin
        grid = collect(0.0:0.25:60.0)
        cases = [
            (sir_model(τ = 1 / 6, γ = 1 / 4), BIMODAL, SeedFraction(:I => 0.01), (:S, :I, :pop_R, :cumulative)),
            (seir_model(τ = 0.3, σ = 0.5, γ = 0.25), EmpiricalDegree([0.1, 0.2, 0.0, 0.4, 0.0, 0.0, 0.3]),
             SeedFraction(:E => 0.005, :I => 0.005), (:S, :pop_E, :pop_I, :pop_R, :cumulative)),
            (sirv_model(τ = 1 / 6, γ = 1 / 4, ν = 0.02), BIMODAL, SeedFraction(:I => 0.01),
             (:S, :pop_I, :pop_R, :pop_V, :cumulative)),
            (seair_model(τI = 0.4, τA = 0.2, σ = 0.5, p = 0.6, γ = 0.25), BinomialDegree(6, 0.5),
             SeedFraction(:E => 0.01), (:S, :pop_E, :pop_A, :pop_I, :pop_R, :cumulative)),
        ]
        for (cm, d, init, obs) in cases
            dc = degree_correlated(d; r = 0.0)
            @test degree_assortativity(dc) ≈ 0 atol = 1e-12
            sysA = edge_based(cm, dc)
            sysB = edge_based(cm, ConfigurationNetwork(d))
            solA = solve_epidemic(sysA; initial = init, tspan = (0.0, 60.0), saveat = grid, TOL...)
            solB = solve_epidemic(sysB; initial = init, tspan = (0.0, 60.0), saveat = grid, TOL...)
            for X in obs
                a, b = compartment(sysA, solA, X), compartment(sysB, solB, X)
                @test maximum(abs.(a .- b)) < 1e-10
            end
            # every θ_k is the configuration θ
            θB = compartment(sysB, solB, :θ)
            for k in dc.degrees
                k > 0 || continue
                @test maximum(abs.(compartment(sysA, solA, Symbol(:θ_k, k)) .- θB)) < 1e-10
            end
        end
        # the scenario pair: :sir_dc_bim_r0 is :sir_bim
        sc0, scb = scenario(:sir_dc_bim_r0), scenario(:sir_bim)
        sys0, sysb = edge_based(sc0), edge_based(scb)
        mc0 = model_curves(sys0, solve_epidemic(sys0, sc0; TOL...); t = sc0.tgrid)
        mcb = model_curves(sysb, solve_epidemic(sysb, scb; TOL...); t = scb.tgrid)
        @test maximum(mc0.values[:I]) > 0.1                                    # an epidemic happens
        for X in (:S, :I, :R, :cumulative)
            @test maximum(abs.(mc0.values[X] .- mcb.values[X])) < 1e-10
        end
    end

    @testset "the exact quotient of the multitype lift of MultitypeNetwork(net)" begin
        # θ_{l→k} = θ_{l→k'} in the multitype lift, and θ_k = Σ_l Q(l | k)θ_{l→k}: the totals agree exactly, for
        # branching, two infectors and exits alike. Seeds are uniform: ρ_X p_k in class k (a fraction of all nodes).
        grid = collect(0.0:0.5:60.0)
        rng = Random.MersenneTwister(7)
        nets = (scenario(:sir_dc_bim_r05).network, scenario(:sir_dc_bim_rn05).network, three_class_network(rng))
        models = ((sir_model(τ = 1 / 6, γ = 1 / 4), [:I => 0.01], [:S, :I, :R]),
                  (seair_model(τI = 0.3, τA = 0.15, σ = 0.5, p = 0.6, γ = 0.25), [:E => 0.01],
                   [:S, :E, :A, :I, :R]),
                  (sirv_model(τ = 0.2, γ = 0.25, ν = 0.02), [:I => 0.01], [:S, :I, :R, :V]))
        for net in nets, (cm, seeds, species) in models
            cls = [Symbol("k", k) for k in net.degrees]
            sys = edge_based(cm, net)
            mt = MultitypeNetwork(net)
            sysM = edge_based(stratify(cm, cls), mt)
            initM = SeedFraction([Symbol(X, :_, c) => ρ * net.probabilities[i] for (X, ρ) in seeds
                                  for (i, c) in enumerate(cls)]...)
            sol = solve_epidemic(sys; initial = SeedFraction(seeds...), tspan = (0.0, 60.0), saveat = grid, TOL...)
            solM = solve_epidemic(sysM; initial = initM, tspan = (0.0, 60.0), saveat = grid, TOL...)
            for X in species
                mine = X === :S ? compartment(sys, sol, :S) : compartment(sys, sol, Symbol(:pop_, X))
                theirs = sum(X === :S ? compartment(sysM, solM, Symbol(:S_, c)) :
                             compartment(sysM, solM, Symbol(:pop_, X, :_, c)) for c in cls)
                @test maximum(abs.(mine .- theirs)) < 1e-9
            end
            for c in cls                                     # the susceptible fraction per degree class
                @test maximum(abs.(compartment(sys, sol, Symbol(:S_, c)) .- compartment(sysM, solM, Symbol(:S_, c)))) < 1e-9
            end
            @test maximum(abs.(compartment(sys, sol, :cumulative) .- compartment(sysM, solM, :cumulative))) < 1e-9
        end
    end

    @testset "acceptance 1: R₀ = T ρ((l − 1)Q(l | k)) = NetworkEpiCore's NGM (E20: support only)" begin
        rng = Random.MersenneTwister(11)
        nets = Any[scenario(Symbol(:sir_dc_bim_, t)).network for t in (:r0, :r05, :rn05)]
        push!(nets, three_class_network(rng))
        push!(nets, degree_correlated(PoissonDegree(5.0); r = 0.3))
        push!(nets, degree_correlated(EmpiricalDegree(Dict(3 => 0.5, 7 => 0.5)); r = 0.8))
        for net in nets
            sys = edge_based(sir_model(), net)
            L = linearisation(sys, [:I])
            E = findall(>(0), net.degrees)
            Q = Qmatrix(net)
            D = [(net.degrees[l] - 1) * Q[k, l] for k in E, l in E]      # Wang et al.'s D_kl = (l − 1)Q(l | k)
            @test L.names == [Symbol(:φ_I_k, net.degrees[i]) for i in E]
            for (τ, γ) in ((1 / 6, 1 / 4), (0.9, 0.1), (0.05, 1.0))
                p = Dict(:τ => τ, :γ => γ)
                T = τ / (τ + γ)
                F, V = ngm_parts(L, p)
                K = F / V
                @test K ≈ T .* D rtol = 1e-12 atol = 1e-14
                R0 = maximum(abs, eigvals(K))
                @test R0 ≈ basic_reproduction_number(sir_model(), net, p) rtol = 1e-10
                @test R0 ≈ T * maximum(abs, eigvals(D)) rtol = 1e-12
                # the early growth rate is the spectral abscissa of F − V (NetworkEpiCore: the multitype form)
                @test maximum(real, eigvals(F - V)) ≈ early_growth_rate(sir_model(), net, p) rtol = 1e-9 atol = 1e-12
                # EdgeBasedModels' own linearisation of the lifted field (analysis.jl) gives the same matrix
                @test next_generation_matrix(sys; p) ≈ T .* D rtol = 1e-10 atol = 1e-13
                @test basic_reproduction_number(sys; p) ≈ R0 rtol = 1e-10
                @test early_growth_rate(sys; p) ≈ maximum(real, eigvals(F - V)) rtol = 1e-9 atol = 1e-12
            end
        end
        # two degree classes: the closed-form Perron root of the symbolic 2×2 NGM, T(a + d)/2 + T√(((a − d)/2)² + bc)
        sys = edge_based(sir_model(), nets[2])
        R0sym = basic_reproduction_number(sys)
        p = Dict(:τ => 1 / 6, :γ => 1 / 4)
        @test evaluate(R0sym, p) ≈ basic_reproduction_number(sir_model(), nets[2], p) rtol = 1e-10
        @test evaluate(R0sym, p) ≈ 2.736931687685298 rtol = 1e-12       # 0.4·(3.75 + √9.5625), by hand
        # SEIR and SEAIR (branching, two infectors): ρ(F V⁻¹) over the chain against NetworkEpiCore
        for net in nets[1:4]
            for (cm, p, chain) in ((seir_model(), Dict(:τ => 0.3, :σ => 0.5, :γ => 0.25), [:E, :I]),
                                   (seair_model(), Dict(:τI => 0.3, :τA => 0.15, :σ => 0.5, :p => 0.6, :γ => 0.25),
                                    [:E, :A, :I]))
                F, V = ngm_parts(edge_based(cm, net), p, chain)
                @test maximum(abs, eigvals(F / V)) ≈ basic_reproduction_number(cm, net, p) rtol = 1e-9
            end
        end
        # E20 regression inputs: zero-padded distributions through the legacy CorrelatedPGF (the legacy correlated_R0
        # returned T·max(1, r(K − 1)) for the padded 2-regular ring, e.g. 1.8 at T = 0.9, r = 0.5, and 11.2 instead of
        # 5.6655 for {3, 7} padded to K = 15 at r = 0.8)
        p09 = Dict(:τ => 0.9, :γ => 0.1)
        for r in (0.0, 0.5, 0.8, 1.0)
            net = degree_correlated(assortative_correlated_pgf([0.0, 0.0, 1.0, 0.0, 0.0, 0.0], r))
            @test net.degrees == [2]
            F, V = ngm_parts(edge_based(sir_model(), net), p09, [:I])
            @test maximum(abs, eigvals(F / V)) ≈ 0.9 atol = 1e-12
            @test basic_reproduction_number(sir_model(), net, p09) ≈ 0.9 atol = 1e-12
        end
        probs = zeros(8)
        probs[4] = probs[8] = 0.5
        ρex(r) = 12 / 5 + 8r / 5 + 2sqrt(16r^2 - 27r + 36) / 5     # exact support-block spectral radius (E20, sympy)
        R0s = Float64[]
        for r in (0.0, 0.3, 0.8, 1.0), padded in (probs, [probs; zeros(8)])
            net = degree_correlated(assortative_correlated_pgf(padded, r))
            @test net.degrees == [3, 7]
            F, V = ngm_parts(edge_based(sir_model(), net), p09, [:I])
            R0 = maximum(abs, eigvals(F / V))
            @test R0 ≈ 0.9 * ρex(r) rtol = 1e-10
            padded === probs && push!(R0s, R0)
        end
        @test issorted(R0s)                                   # Newman r-mixing never lowers R₀ (E20)
    end

    @testset "the final size is NetworkEpiCore's fixed point; conservation" begin
        for t in (:r0, :r05, :rn05)
            sc = scenario(Symbol(:sir_dc_bim_, t))
            sys = edge_based(sc)
            sol = solve_epidemic(sys; p = sc.params, initial = sc.initial, tspan = (0.0, 2000.0), TOL...)
            fs = final_size(sc.model, sc.network, sc.params; initial = sc.initial)
            @test compartment(sys, sol, :cumulative)[end] ≈ fs rtol = 1e-8
            @test final_size(sys; p = sc.params, initial = sc.initial) ≈ fs rtol = 1e-12
            @test final_size(sys; p = sc.params, initial = sc.initial, method = :ode) ≈ fs rtol = 1e-7
            @test 1 - compartment(sys, sol, :S)[end] ≈ fs rtol = 1e-8
        end
        # SEAIR with vaccination S → V and a removal A → ∅ (to the sink :removed): θ_k = φ_{S,k} + Σ_Y φ_{Y,k} and
        # S + Σ pop = 1 along the trajectory, on a network with degree-0 and degree-1 classes
        cm = ContactModel(:seairv; contacts = [Contact(:S, :I, :E, 0.3), Contact(:S, :A, :E, 0.15)],
                          transitions = [NodeTransition(:E, :I, 0.3), NodeTransition(:E, :A, 0.2),
                                         NodeTransition(:I, :R, 0.25), NodeTransition(:A, nothing, 0.25),
                                         NodeTransition(:S, :V, 0.01)])
        net = three_class_network(Random.MersenneTwister(5))
        sys = edge_based(cm, net)
        @test haskey(sys.variables, :ξ) && haskey(sys.variables, :pop_removed)
        grid = collect(0.0:1.0:80.0)
        sol = solve_epidemic(sys; initial = SeedFraction(:E => 0.01, :I => 0.005), tspan = (0.0, 80.0),
                             saveat = grid, TOL...)
        nodes = (:E, :I, :A, :R, :V, :removed)
        total = compartment(sys, sol, :S) .+ sum(compartment(sys, sol, Symbol(:pop_, Y)) for Y in nodes)
        @test maximum(abs.(total .- 1)) < 1e-10
        for k in net.degrees
            k > 0 || continue
            c = Symbol(:k, k)
            lhs = compartment(sys, sol, Symbol(:θ_, c))
            rhs = compartment(sys, sol, Symbol(:φ_S_, c)) .+ sum(compartment(sys, sol, Symbol(:φ_, Y, :_, c)) for Y in nodes)
            @test maximum(abs.(lhs .- rhs)) < 1e-10
            # the edge hazard observable: θ̇_k = −Σ_r τ_r φ_{J_r,k} = −(0.3φ_{I,k} + 0.15φ_{A,k})
            h = compartment(sys, sol, Symbol(:edge_hazard_, c))
            @test h ≈ 0.3 .* compartment(sys, sol, Symbol(:φ_I_, c)) .+ 0.15 .* compartment(sys, sol, Symbol(:φ_A_, c)) rtol = 1e-12
        end
        # the per-class susceptible fractions add up to S (degree 0 included)
        @test maximum(abs.(sum(compartment(sys, sol, Symbol(:S_k, k)) for k in net.degrees) .- compartment(sys, sol, :S))) < 1e-12
    end

    @testset "the legacy CorrelatedPGF bridge (E20)" begin
        probs = zeros(11)
        probs[3], probs[11] = 5 / 6, 1 / 6
        for r in (0.0, 0.5, 1.0)
            c = assortative_correlated_pgf(probs, r)
            net = degree_correlated(c)
            ref = degree_correlated(BIMODAL; r)
            @test net.degrees == ref.degrees && net.probabilities ≈ ref.probabilities
            @test net.edge_ends ≈ ref.edge_ends atol = 1e-14
            # edge_based(model, ::CorrelatedPGF) is the lift of the descriptor
            @test vector_fields_equal(symbolic_ode(edge_based(sir_model(), c)), symbolic_ode(edge_based(sir_model(), ref)))
        end
        # a mixing matrix without detailed balance has no symmetric edge-end matrix
        bad = correlated_pgf([0.0, 0.5, 0.5], [1.0 0.0 0.0; 0.0 0.9 0.1; 0.0 0.9 0.1])
        @test_throws ArgumentError degree_correlated(bad)
    end

    @testset "acceptance 3: D∞ < 0.01 against NetworkOutbreaks on :sir_dc_bim_*" begin
        # The reference ensembles use NetworkOutbreaks' 2K sampler (sample_graph(::DegreeCorrelatedNetwork)) through
        # the scenario runner, with the scenarios' SimConfig (N = 10⁴, 200 runs, base seed 20260926).
        results = Dict{Symbol,Any}()
        for t in (:r0, :r05, :rn05)
            sc = scenario(Symbol(:sir_dc_bim_, t))
            summ = NO.summarise(NO.scenario_ensemble(sc))
            sys = edge_based(sc)
            sol = solve_epidemic(sys, sc; solver = Vern9(), reltol = 1e-10, abstol = 1e-12)
            cmp = compare(summ, model_curves(sys, sol; t = sc.tgrid, label = "EB"))
            results[sc.id] = cmp
            @test cmp.n >= 195                                    # P(major) ≈ 1 with ρN = 100 seeds
            for row in cmp
                @test row.D∞ < 0.01                              # WP36a acceptance
            end
            # the §E.2 tolerances of an :exact_limit back end
            @test cmp["EB", :I].D∞ < 0.005
            @test abs(cmp["EB", :cumulative].ΔR∞) < 0.005
            @info "WP36a: edge-based lift vs NetworkOutbreaks (2K graphs), $(sc.id)" N = sc.sim.N runs = sc.sim.nsims major = cmp.n D∞_I = cmp["EB", :I].D∞ SE∞_I = cmp["EB", :I].SE∞ D∞_S = cmp["EB", :S].D∞ ΔR∞ = cmp["EB", :cumulative].ΔR∞ ΔR∞_ci = cmp["EB", :cumulative].ΔR∞_ci
        end
        # negative control: the uncorrelated lift on the same degree law misses the assortative ensemble by far
        sc = scenario(:sir_dc_bim_r05)
        summ = NO.summarise(NO.scenario_ensemble(sc))
        plain = edge_based(sc.model, ConfigurationNetwork(BIMODAL))
        sol = solve_epidemic(plain, sc; solver = Vern9(), reltol = 1e-10, abstol = 1e-12)
        cmp = compare(summ, model_curves(plain, sol; t = sc.tgrid, label = "uncorrelated"))
        @test cmp["uncorrelated", :cumulative].D∞ > 0.05
        @test cmp["uncorrelated", :I].D∞ > 10 * results[:sir_dc_bim_r05]["EB", :I].D∞
    end
end
