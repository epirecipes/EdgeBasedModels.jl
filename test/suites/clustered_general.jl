# WP36d: clustered networks beyond SIR (src/lift/clustered_general.jl). This is the edge-based
# model of Volz, Miller, Galvani & Ancel Meyers (2011, PLoS Comput Biol 7:e1002042;
# papers/clustering1.md) with triangle pair states, for every T_EB model with one susceptible
# class.
#
# Acceptance (DESIGN_NetworkEpiCore.md §K, WP36d):
#   1. SIR is reproduced exactly against WP20. This covers WP20's own SIR/SEIR path, general
#      presentations of SIR and SEIR that lump onto it, and the reproduction number;
#   2. D∞ < 0.01 against NetworkOutbreaks on :seir_clust_s2t2 and :seair_clust_s2t2, using the
#      scenario runner with the scenarios' N, runs, seeds and streams (design §E.2, §J.7), or the
#      committed summaries once they exist (design §E.4).
# Also tested:
#   - SEAIR, several strains, exits and more, against an independent pair-state reference;
#   - invariants, the empty-block limits and the final-size relation;
#   - the tree-of-triangles R₀ for general models, against the threshold of the lifted field;
#   - the threshold body `_clustered_threshold` (R₀, next-generation matrix, transmissibility,
#     early growth rate) that analysis.jl's `_numeric_threshold(::Val{:clustered}, …)` serves:
#     WP20's E04 matrices for SIR/SEIR, and the growth rate against the exponential rate of the
#     independent reference; the public route (analysis.jl's extension point) against the body;
#   - the public `final_size` of general models (the ODE route);
#   - more general models against NetworkOutbreaks (two strains, vaccination, cross infection).
#
# References that are independent of the package code:
# - an ORDERED, S-explicit transcription of the pair-state rules of Volz et al. for any T_EB
#   model (no χ coordinates; outside hazards divided by g_x(θ), g_y(θ) as in the paper), in
#   plain Julia;
# - the tree-of-triangles final-size relation (Volz et al. eq. 27), generalised to phase-type
#   infectious periods;
# - the growth rate of the lifted field at the disease-free state, which tests the R₀ threshold;
# - exact stochastic simulation with NetworkOutbreaks on freshly drawn Newman–Miller graphs.

using EdgeBasedModels
using NetworkEpiCore
using LinearAlgebra
using Symbolics
using Test
using ModelingToolkit: @parameters
using OrdinaryDiffEq: ODEProblem, Vern9, solve
import NetworkOutbreaks as NO

const EBM = EdgeBasedModels
const TOL = (solver = Vern9(), reltol = 1e-12, abstol = 1e-13)

# ---------------------------------------------------------------------------------------------
# Networks and their PGFs (own closed forms)
# ---------------------------------------------------------------------------------------------

pois(ks, kt) = ClusteredNetwork(PoissonDegree(ks), PoissonDegree(kt))
const S2T2 = ClusteredNetwork(RegularDegree(2), RegularDegree(2))
const PJ = [0.05 0.10 0.05; 0.10 0.20 0.05; 0.05 0.15 0.10; 0.0 0.1 0.05]   # p_{s,t}, s ≤ 3, t ≤ 2

poisson_g(ks, kt) = (x, y, i, j) -> ks^i * kt^j * exp(ks * (x - 1) + kt * (y - 1))
function joint_g(P)
    ff(n, k) = prod(Float64(n - m) for m in 0:(k - 1); init = 1.0)
    return (x, y, i, j) -> sum(P[a, b] * ff(a - 1, i) * ff(b - 1, j) * x^(a - 1 - i) * y^(b - 1 - j)
                               for a in axes(P, 1), b in axes(P, 2) if P[a, b] != 0 && a - 1 >= i && b - 1 >= j;
                               init = 0.0)
end
const NETS = [("Poisson (1, 2)", pois(1.0, 2.0), poisson_g(1.0, 2.0)),
              ("joint 4×3 law", ClusteredNetwork(PJ), joint_g(PJ)),
              ("regular (2, 2)", S2T2, joint_g([0 0 0; 0 0 0; 0 0 1.0])),
              ("triangles only", pois(0.0, 1.5), poisson_g(0.0, 1.5))]

# ---------------------------------------------------------------------------------------------
# Independent reference: ordered, S-explicit pair states for any T_EB model
# ---------------------------------------------------------------------------------------------

# A model written out by hand: `states` = [s, X₁, …] (the susceptible class first; removals go to
# a species written out here), contacts (J, X, τ) for s + J → X + J, transitions (A, B, a) among
# the non-susceptible species, exits (Y, ν) for s → Y.
struct Spec
    states::Vector{Symbol}
    contacts::Vector{Tuple{Symbol,Symbol,Float64}}
    transitions::Vector{Tuple{Symbol,Symbol,Float64}}
    exits::Vector{Tuple{Symbol,Float64}}
end

# The rules of Volz et al. for a test node u that does not transmit, in ORDERED pair states
# O[a, b] (partner 1 in a, partner 2 in b, neither has transmitted to u), the susceptible class
# included (index 1):
#   - a partner in J transmits to u at τ_r (for each contact r with infector J);
#   - a susceptible partner is infected from outside by reaction r at A_r = −(share of r in)
#     d ln g_y(θ₂, θ₃)/dt, and by the other partner, when that one is in J_r, at τ_r; either way
#     it enters X_r; it exits to Y at ν;
#   - each partner follows the node transitions.
# Single edges likewise, with the line partner's outside rate h_r = −(share of r in)
# d ln g_x/dt. Then θ₂' = −Σ τ_r φ2_{J_r}, θ₃' = −Σ τ_r E[#partners in J_r], ξ' = −Σν ξ and
# S = qξ g(θ₂, θ₃); the populations take the node-level fluxes. Seeds are placed independently,
# so O(0) = ρ ⊗ ρ with ρ_s = q.
function pair_state_reference(g, sp::Spec, ρ::AbstractDict; T = 100.0, saveat = 0.5, abstol = 1e-13)
    n = length(sp.states)
    id = Dict(X => k for (k, X) in enumerate(sp.states))
    q = 1 - sum(values(ρ))
    gx1, gy1 = g(1.0, 1.0, 1, 0), g(1.0, 1.0, 0, 1)
    C = [(id[J], id[X], τ) for (J, X, τ) in sp.contacts]
    Tr = [(id[A], id[B], a) for (A, B, a) in sp.transitions]
    Ex = [(id[Y], ν) for (Y, ν) in sp.exits]
    νtot = sum(last, Ex; init = 0.0)
    iφ(a) = 3 + a
    iO(a, b) = 3 + n + (a - 1) * n + b
    ip(a) = 3 + n + n * n + a
    function f!(du, u, _, t)
        fill!(du, 0.0)
        θ2, θ3, ξ = u[1], u[2], u[3]
        O(a, b) = u[iO(a, b)]
        H2 = [τ * u[iφ(J)] for (J, _, τ) in C]
        H3 = [τ * sum(((a == J) + (b == J)) * O(a, b) for a in 1:n, b in 1:n) for (J, _, τ) in C]
        du[1] = -sum(H2; init = 0.0)
        du[2] = -sum(H3; init = 0.0)
        du[3] = -νtot * ξ
        gx, gy = g(θ2, θ3, 1, 0), g(θ2, θ3, 0, 1)
        gxx, gxy, gyy = g(θ2, θ3, 2, 0), g(θ2, θ3, 1, 1), g(θ2, θ3, 0, 2)
        h = gx1 > 0 ? [(gxx * H2[r] + gxy * H3[r]) / gx for r in eachindex(C)] : zeros(length(C))
        A = gy1 > 0 ? [(gxy * H2[r] + gyy * H3[r]) / gy for r in eachindex(C)] : zeros(length(C))
        φS = u[iφ(1)]
        for (r, (J, X, τ)) in enumerate(C)
            du[iφ(1)] -= h[r] * φS
            du[iφ(X)] += h[r] * φS
            du[iφ(J)] -= τ * u[iφ(J)]
        end
        for (Y, ν) in Ex
            du[iφ(1)] -= ν * φS
            du[iφ(Y)] += ν * φS
        end
        for (a, b, rate) in Tr
            du[iφ(a)] -= rate * u[iφ(a)]
            du[iφ(b)] += rate * u[iφ(a)]
        end
        for a in 1:n, b in 1:n
            o = O(a, b)
            for (J, _, τ) in C
                du[iO(a, b)] -= τ * ((a == J) + (b == J)) * o
            end
            if a == 1
                for (r, (J, X, τ)) in enumerate(C)
                    k = A[r] + τ * (b == J)
                    du[iO(a, b)] -= k * o
                    du[iO(X, b)] += k * o
                end
                for (Y, ν) in Ex
                    du[iO(a, b)] -= ν * o
                    du[iO(Y, b)] += ν * o
                end
            end
            if b == 1
                for (r, (J, X, τ)) in enumerate(C)
                    k = A[r] + τ * (a == J)
                    du[iO(a, b)] -= k * o
                    du[iO(a, X)] += k * o
                end
                for (Y, ν) in Ex
                    du[iO(a, b)] -= ν * o
                    du[iO(a, Y)] += ν * o
                end
            end
            for (x, y, rate) in Tr
                a == x && (du[iO(a, b)] -= rate * o; du[iO(y, b)] += rate * o)
                b == x && (du[iO(a, b)] -= rate * o; du[iO(a, y)] += rate * o)
            end
        end
        for (r, (J, X, τ)) in enumerate(C)
            du[ip(X)] += q * ξ * (gx * H2[r] + gy * H3[r])
        end
        S = q * ξ * g(θ2, θ3, 0, 0)
        for (Y, ν) in Ex
            du[ip(Y)] += ν * S
        end
        for (a, b, rate) in Tr
            du[ip(a)] -= rate * u[ip(a)]
            du[ip(b)] += rate * u[ip(a)]
        end
        return nothing
    end
    u0 = zeros(3 + n + n * n + n)
    u0[1] = u0[2] = u0[3] = 1.0
    r0 = [k == 1 ? q : Float64(get(ρ, sp.states[k], 0.0)) for k in 1:n]
    for a in 1:n
        u0[iφ(a)] = r0[a]
        a > 1 && (u0[ip(a)] = r0[a])
        for b in 1:n
            u0[iO(a, b)] = r0[a] * r0[b]
        end
    end
    sol = solve(ODEProblem(f!, u0, (0.0, T)), Vern9(); reltol = 1e-12, abstol, saveat)
    pair(X, Y) = X === Y ? [u[iO(id[X], id[X])] for u in sol.u] :
                           [u[iO(id[X], id[Y])] + u[iO(id[Y], id[X])] for u in sol.u]
    return (S = [q * u[3] * g(u[1], u[2], 0, 0) for u in sol.u], pop = X -> [u[ip(id[X])] for u in sol.u],
            φ2 = X -> [u[iφ(id[X])] for u in sol.u], pair = pair, θ2 = [u[1] for u in sol.u],
            θ3 = [u[2] for u in sol.u])
end

# The largest deviation of an edge-based system from the reference: S, every population, every
# (unordered) triangle pair state (the susceptible ones are observables), θ₂ and θ₃.
function max_deviation(sys, sol, ref, sp::Spec)
    C(X) = compartment(sys, sol, X)
    has(nm) = haskey(sys.variables, nm) || haskey(sys.observables, nm)
    d = Pair{String,Float64}["S" => maximum(abs.(C(:S) .- ref.S))]
    for X in sp.states[2:end]
        push!(d, "pop_$X" => maximum(abs.(C(Symbol(:pop_, X)) .- ref.pop(X))))
    end
    s = sp.states[1]
    for (i, X) in enumerate(sp.states), Y in sp.states[i:end]
        nm = has(Symbol(:φ3_, X, :_, Y)) ? Symbol(:φ3_, X, :_, Y) : Symbol(:φ3_, Y, :_, X)
        (has(nm) || !has(:θ₃)) || error("no pair state $nm")
        has(nm) && push!(d, string(nm) => maximum(abs.(C(nm) .- ref.pair(X, Y))))
    end
    has(:θ₂) && push!(d, "θ₂" => maximum(abs.(C(:θ₂) .- ref.θ2)))
    has(:θ₃) && push!(d, "θ₃" => maximum(abs.(C(:θ₃) .- ref.θ3)))
    has(Symbol(:φ2_, s)) && push!(d, "φ2_$s" => maximum(abs.(C(Symbol(:φ2_, s)) .- ref.φ2(s))))
    return argmax(last, d)
end

# ---------------------------------------------------------------------------------------------
# The general models (numeric rates), with their hand-written specifications
# ---------------------------------------------------------------------------------------------

const SEAIR = seair_model(; τI = 0.5, τA = 0.25, p = 0.6, σ = 0.5, γ = 0.4)
const SEAIR_SPEC = Spec([:S, :E, :I, :A, :R], [(:I, :E, 0.5), (:A, :E, 0.25)],
                        [(:E, :I, 0.3), (:E, :A, 0.2), (:I, :R, 0.4), (:A, :R, 0.4)], [])
const TWOSTRAIN = twostrain_model(; τ1 = 0.5, τ2 = 0.7, γ = 0.6)
const TWOSTRAIN_SPEC = Spec([:S, :I1, :I2, :R], [(:I1, :I1, 0.5), (:I2, :I2, 0.7)],
                            [(:I1, :R, 0.6), (:I2, :R, 0.6)], [])
const SIRV = sirv_model(; τ = 0.6, γ = 0.5, ν = 0.05)
const SIRV_SPEC = Spec([:S, :I, :R, :V], [(:I, :I, 0.6)], [(:I, :R, 0.5)], [(:V, 0.05)])
# importation: an exit s → I into the infector, and a removal I → ∅ (to the sink :removed)
const IMPORT = ContactModel(:importation; contacts = [Contact(:S, :I, :I, 0.4)],
                            transitions = [NodeTransition(:I, nothing, 0.5), NodeTransition(:S, :I, 0.01)])
const IMPORT_SPEC = Spec([:S, :I, :removed], [(:I, :I, 0.4)], [(:I, :removed, 0.5)], [(:I, 0.01)])
# cross infection: infections by I enter A and infections by A enter I (two entry states that
# alternate along chains of transmission)
const CROSS = ContactModel(:cross; contacts = [Contact(:S, :I, :A, 0.8), Contact(:S, :A, :I, 0.3)],
                           transitions = [NodeTransition(:I, :R, 1.0), NodeTransition(:A, :R, 0.25)])
const CROSS_SPEC = Spec([:S, :I, :A, :R], [(:I, :A, 0.8), (:A, :I, 0.3)], [(:I, :R, 1.0), (:A, :R, 0.25)], [])
# three Erlang stages, every stage infectious (as erlang_stages(sir_model(), :I, 3))
const ERLANG = ContactModel(:erlang3; contacts = [Contact(:S, :I1, :I1, 0.5), Contact(:S, :I2, :I1, 0.5),
                                                  Contact(:S, :I3, :I1, 0.5)],
                            transitions = [NodeTransition(:I1, :I2, 1.5), NodeTransition(:I2, :I3, 1.5),
                                           NodeTransition(:I3, :R, 1.5)])
const ERLANG_SPEC = Spec([:S, :I1, :I2, :I3, :R], [(:I1, :I1, 0.5), (:I2, :I1, 0.5), (:I3, :I1, 0.5)],
                         [(:I1, :I2, 1.5), (:I2, :I3, 1.5), (:I3, :R, 1.5)], [])
# SI: an absorbing infector
const SI = ContactModel(:si; contacts = [Contact(:S, :I, :I, 0.3)])
const SI_SPEC = Spec([:S, :I], [(:I, :I, 0.3)], [], [])
# branching into two latent classes, two infectors, and a removal to the sink
const BRANCH = ContactModel(:branch; contacts = [Contact(:S, :I, :E1, 0.3), Contact(:S, :I, :E2, 0.2),
                                                 Contact(:S, :A, :E1, 0.5)],
                            transitions = [NodeTransition(:E1, :I, 0.5), NodeTransition(:E2, :A, 2.0),
                                           NodeTransition(:I, :R, 1.0), NodeTransition(:A, nothing, 0.7)])
const BRANCH_SPEC = Spec([:S, :I, :E1, :E2, :A, :R, :removed], [(:I, :E1, 0.3), (:I, :E2, 0.2), (:A, :E1, 0.5)],
                         [(:E1, :I, 0.5), (:E2, :A, 2.0), (:I, :R, 1.0), (:A, :removed, 0.7)], [])

lift(cm, net) = edge_based(cm, net)
solveρ(sys, ρ; T = 100.0, saveat = 0.5) =
    solve_epidemic(sys; initial = SeedFraction(ρ...), tspan = (0.0, T), saveat, TOL...)
C(sys, sol, X) = compartment(sys, sol, X)
# an unordered triangle pair state, named in either order (the lift orders by species index)
function Cpair(sys, sol, X, Y)
    nm = Symbol(:φ3_, X, :_, Y)
    haskey(sys.variables, nm) || haskey(sys.observables, nm) || (nm = Symbol(:φ3_, Y, :_, X))
    return compartment(sys, sol, nm)
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

# The tree-of-triangles final size of a model with one entry state (Volz et al. 2011, eq. 27,
# with q_k, the probability that an infective transmits along none of k given edges, of any
# phase-type infectious history): a line partner escapes with s_L + (1 − s_L)q₁; a triangle's two
# partners with s_T² + 2s_T(1 − s_T)(q₂ + (q₁ − q₂)q₁) + (1 − s_T)²q₁², where s_L and s_T are the
# probabilities of not being infected from outside.
function triangle_final_size(g, q1, q2; ρ)
    q = 1 - ρ
    gx1, gy1 = g(1.0, 1.0, 1, 0), g(1.0, 1.0, 0, 1)
    θ2 = θ3 = 0.0
    for _ in 1:200_000
        sL = gx1 > 0 ? q * g(θ2, θ3, 1, 0) / gx1 : 0.0
        sT = gy1 > 0 ? q * g(θ2, θ3, 0, 1) / gy1 : 0.0
        n2 = sL + (1 - sL) * q1
        n3 = sT^2 + 2sT * (1 - sT) * (q2 + (q1 - q2) * q1) + (1 - sT)^2 * q1^2
        done = abs(n2 - θ2) + abs(n3 - θ3) < 1e-15
        θ2, θ3 = n2, n3
        done && break
    end
    return 1 - q * g(θ2, θ3, 0, 0)
end

# Species from which an infector can be reached along transitions.
function live_species(cm)
    live = Set{Symbol}(c.infector for c in contacts(cm))
    changed = true
    while changed
        changed = false
        for t in node_transitions(cm)
            if t.to !== nothing && t.to in live && !(t.from in live) && !(t.from in susceptible_species(cm))
                push!(live, t.from)
                changed = true
            end
        end
    end
    return live
end

# The growth rate of the lifted field at the disease-free state, as a function of the contact
# rate scale λ (the model's contact rates are λ·τ_r): the largest real part of the eigenvalues
# of the Jacobian over the coordinates that can still transmit (φ2_X, χ_X for X from which an
# infector is reachable, and the pair states containing such an X). The entry terms are linear
# in these coordinates at θ = 1, q = 1, so this subsystem is closed at first order.
function dfe_growth(cm, net)
    ode = symbolic_ode(lift(cm, net))
    names = [string(Symbolics.getname(x)) for x in ode.states]
    live = Set(string.(live_species(cm)))
    function transmitting(nm)
        for pre in ("φ2_", "χ_")
            startswith(nm, pre) && return nm[(ncodeunits(pre) + 1):end] in live
        end
        startswith(nm, "φ3_") && return any(in(live), split(nm[(ncodeunits("φ3_") + 1):end], "_"))
        return false
    end
    idx = findall(transmitting, names)
    J = Symbolics.jacobian(ode.rhs[idx], ode.states[idx])
    return function (λ)
        at = Dict{Any,Any}(x => (nm in ("θ₂", "θ₃", "ξ") ? 1.0 : 0.0) for (x, nm) in zip(ode.states, names))
        for p in ode.parameters
            nm = Symbol(Symbolics.getname(p))
            nm === :q_S && (at[p] = 1.0)
            nm === :λ && (at[p] = λ)
        end
        Jn = [Float64(Symbolics.value(Symbolics.substitute(x, at; fold = Val(true)))) for x in J]
        return maximum(real, eigvals(Jn))
    end
end

R0g(args...; kw...) = EBM._clustered_general_reproduction_number(args...; kw...)
R0w(cm, net; kw...) = EBM._clustered_reproduction_number(cm, net; kw...)
# the threshold body, with the system's parameter defaults overridden by p (as analysis.jl passes them)
TH(f, sys; p = Dict{Symbol,Float64}(), kw...) =
    EBM._clustered_threshold(f, sys, merge(Dict{Symbol,Float64}(parameter_defaults(sys)), p); kw...)

# The exponential growth rate of the independent reference from a tiny seed: d ln y/dt for the
# population y of the transmission chain, by a central difference, where y first reaches 10⁻¹²
# (supercritical; after 18 decades of growth the transients have died out, and depletion is of
# relative order y, so it is below the 1e-6 tolerance) or at T (subcritical). A seed of 10⁻¹⁴
# read at y = 10⁻⁶ is biased low by the depletion (relative 3e-6 on Poisson (1, 2)).
function reference_growth(g, sp::Spec, chain, seed::Symbol; ρ = 1e-30, T = 60.0, h = 0.01)
    ref = pair_state_reference(g, sp, Dict(seed => ρ); T, saveat = h, abstol = 1e-80)
    y = reduce(+, (ref.pop(X) for X in chain))
    k = something(findfirst(>=(1e-12), y), length(y) - 1)
    return (log(y[k + 1]) - log(y[k - 1])) / (2h)
end

# ---------------------------------------------------------------------------------------------
# Comparison with NetworkOutbreaks through the scenario runner (design §E.2, §J.7)
# ---------------------------------------------------------------------------------------------

# The reference summary of a scenario: the committed one (design §E.4) when NetworkOutbreaks has
# a valid committed summary for a canonical scenario, otherwise the scenario's own ensemble,
# computed here (graph r from stable_rng(b + r), run r from stable_rng(b + 2³² + r),
# NextReaction, exactly ρN seeds, a fresh Newman–Miller graph per run). Both come from the same
# SimConfig, so they agree.
function reference_summary(sc::Scenario)
    if sc.id in scenario_ids() && isempty(NO.missing_scenario_summaries([sc.id]; companions = false))
        return NO.scenario_summary(sc; policy = :committed), "committed summary"
    end
    return NO.summarise(NO.scenario_ensemble(sc)), "local ensemble"
end

# The reference summary, conditioned on major outbreaks, compared with the edge-based lift and
# with the lift on the unclustered configuration network of the same degree law (the negative
# control).
function against_simulation(sc::Scenario, unclustered::NetworkDescriptor)
    summ, source = reference_summary(sc)
    @info "WP36d reference for :$(sc.id): $source"
    sys = edge_based(sc)
    sol = solve_epidemic(sys, sc; solver = Vern9(), reltol = 1e-10, abstol = 1e-12)
    plain = edge_based(sc.model, unclustered)
    sol0 = solve_epidemic(plain, sc; solver = Vern9(), reltol = 1e-10, abstol = 1e-12)
    return compare(summ, model_curves(sys, sol; t = sc.tgrid, label = "EB"),
                   model_curves(plain, sol0; t = sc.tgrid, label = "unclustered"))
end

function report(cmp, sc, what)
    rows = [r for r in cmp if r.label == "EB"]
    @info "WP36d clustered lift vs NetworkOutbreaks :$(sc.id) ($what)" N = sc.sim.N runs = sc.sim.nsims major = cmp.n D∞ = join(("$(r.observable) $(round(r.D∞; sigdigits = 3)) (SE∞ $(round(r.SE∞; sigdigits = 2)), z∞ $(round(r.z∞; sigdigits = 3)))" for r in rows), "; ") ΔR∞ = cmp["EB", :cumulative].ΔR∞ ΔR∞_ci = cmp["EB", :cumulative].ΔR∞_ci unclustered_D∞_S = cmp["unclustered", :S].D∞
end

@testset "clustered lift beyond SIR (WP36d)" begin
    @testset "the gate: every T_EB model with one susceptible class lifts" begin
        @test EBM._clustered_supported(Val(:general))
        shape(cm) = EBM._clustered_shape(EBM._lift_model(cm, S2T2, susceptible_species(cm); context = "test"))
        @test shape(sir_model()) === :sir
        @test shape(seir_model()) === :seir
        net = pois(1.0, 2.0)
        # WP20 refused these (acceptance 4 of test/suites/clustered.jl); now they lift, with
        # symbolic rates, through the same clustered closure
        for cm in (seair_model(), sirv_model(), twostrain_model(), erlang_stages(sir_model(), :I, 2),
                   ContactModel(:si2; contacts = [Contact(:S, :I, :I, :τ)],
                                transitions = [NodeTransition(:I, :J, :γ), NodeTransition(:J, :R, :γ)]),
                   IMPORT, CROSS, BRANCH, SI)
            @test shape(cm) === :general
            sys = edge_based(cm, net)
            @test sys.metadata[:closure] === :clustered && sys.metadata[:kind] === :assembled
            @test haskey(sys.variables, :θ₂) && haskey(sys.variables, :θ₃)
            @test any(n -> startswith(string(n), "φ3_"), keys(sys.variables))
            tab = lift_contributions(cm, net)
            @test tab.closure === :clustered
            @test vector_fields_equal(symbolic_ode(sys), symbolic_ode(tab))
        end
        # still refused: several susceptible classes, layers, SIS/SIRS (not T_EB), the compact
        # form, and pushing a clustered table forward (the lift is only lax under gluing)
        st = strata([:a, :b]; sizes = [0.5, 0.5])
        @test_throws AdmissibilityError edge_based(stratify(sir_model(; τ = 0.6, γ = 1.0), st), net)
        layered = ContactModel(:layered; contacts = [Contact(:S, :I, :I, 0.6; layer = :home)],
                               transitions = [NodeTransition(:I, :R, 1.0)])
        @test_throws AdmissibilityError edge_based(layered, net)
        @test_throws AdmissibilityError edge_based(sis_model(), net)
        @test_throws AdmissibilityError edge_based(sirs_model(), net)
        @test_throws ArgumentError edge_based(SEAIR, net; form = :compact)
        @test_throws ArgumentError relabel(lift_contributions(SEAIR, net), Dict(:A => :B))
        # the canonical stretch scenarios lift through edge_based(sc)
        for id in (:seir_clust_s2t2, :seair_clust_s2t2)
            sc = scenario(id)
            @test :clustered_general in sc.tags
            @test edge_based(sc).metadata[:closure] === :clustered
        end
    end

    @testset "acceptance 1: SIR (and SEIR) reproduced exactly against WP20" begin
        for (label, net, g) in NETS
            @testset "$label" begin
                sir = sir_model(; τ = 0.6, γ = 1.0)
                a = lift(sir, net)                              # WP20's SIR-shaped path
                sa = solveρ(a, [:I => 1e-3]; T = 60.0)
                # the SIR path against the independent pair-state reference
                ref = pair_state_reference(g, Spec([:S, :I, :R], [(:I, :I, 0.6)], [(:I, :R, 1.0)], []),
                                           Dict(:I => 1e-3); T = 60.0)
                @test last(max_deviation(a, sa, ref, Spec([:S, :I, :R], [], [], []))) < 1e-8
                # (i) SIR with a zero-rate vaccination (an exit, so a general shape): the same S, I, R
                v = lift(sirv_model(; τ = 0.6, γ = 1.0, ν = 0.0), net)
                sv = solveρ(v, [:I => 1e-3]; T = 60.0)
                for X in (:S, :pop_I, :pop_R, :cumulative, :θ₃)
                    @test C(v, sv, X) ≈ C(a, sa, X) atol = 1e-11
                end
                # (ii) SIR with a trailing stage R → D (a general shape): R = pop_R + pop_D
                rd = lift(ContactModel(:sird; contacts = [Contact(:S, :I, :I, 0.6)],
                                       transitions = [NodeTransition(:I, :R, 1.0), NodeTransition(:R, :D, 0.3)]), net)
                srd = solveρ(rd, [:I => 1e-3]; T = 60.0)
                @test C(rd, srd, :S) ≈ C(a, sa, :S) atol = 1e-11
                @test C(rd, srd, :pop_I) ≈ C(a, sa, :pop_I) atol = 1e-11
                @test C(rd, srd, :pop_R) .+ C(rd, srd, :pop_D) ≈ C(a, sa, :pop_R) atol = 1e-11
                # (iii) SIR with a lumpable split of I (two infectious stages with the same τ and γ,
                # I1 → I2 at 0.7): the pair states lump onto WP20's
                l = lift(ContactModel(:sirsplit; contacts = [Contact(:S, :I1, :I1, 0.6), Contact(:S, :I2, :I1, 0.6)],
                                      transitions = [NodeTransition(:I1, :I2, 0.7), NodeTransition(:I1, :R, 1.0),
                                                     NodeTransition(:I2, :R, 1.0)]), net)
                sl = solveρ(l, [:I1 => 1e-3]; T = 60.0)
                @test EBM._clustered_shape(EBM._lift_model(l.metadata[:model], net, [:S]; context = "t")) === :general
                @test C(l, sl, :S) ≈ C(a, sa, :S) atol = 1e-11
                @test C(l, sl, :cumulative) ≈ C(a, sa, :cumulative) atol = 1e-11
                @test C(l, sl, :pop_I1) .+ C(l, sl, :pop_I2) ≈ C(a, sa, :pop_I) atol = 1e-11
                if haskey(a.variables, :θ₂)
                    @test C(l, sl, :θ₂) ≈ C(a, sa, :θ₂) atol = 1e-11
                    @test C(l, sl, :φ2_I1) .+ C(l, sl, :φ2_I2) ≈ C(a, sa, :φ2_I) atol = 1e-11
                end
                @test C(l, sl, :θ₃) ≈ C(a, sa, :θ₃) atol = 1e-11
                @test C(l, sl, :χ_I1) .+ C(l, sl, :χ_I2) ≈ C(a, sa, :χ_I) atol = 1e-11
                @test Cpair(l, sl, :I1, :I1) .+ Cpair(l, sl, :I1, :I2) .+ Cpair(l, sl, :I2, :I2) ≈ Cpair(a, sa, :I, :I) atol = 1e-11
                @test Cpair(l, sl, :I1, :R) .+ Cpair(l, sl, :I2, :R) ≈ Cpair(a, sa, :I, :R) atol = 1e-11
                @test Cpair(l, sl, :S, :I1) .+ Cpair(l, sl, :S, :I2) ≈ Cpair(a, sa, :S, :I) atol = 1e-11
                # (iv) SEIR, WP20's stretch path, against a lumpable split of E
                seir = lift(seir_model(; τ = 0.6, σ = 0.5, γ = 1.0), net)
                ss = solveρ(seir, [:E => 1e-3]; T = 100.0)
                e2 = lift(ContactModel(:seirsplit; contacts = [Contact(:S, :I, :E1, 0.6)],
                                       transitions = [NodeTransition(:E1, :E2, 2.0), NodeTransition(:E1, :I, 0.5),
                                                      NodeTransition(:E2, :I, 0.5), NodeTransition(:I, :R, 1.0)]), net)
                se2 = solveρ(e2, [:E1 => 1e-3]; T = 100.0)
                @test C(e2, se2, :S) ≈ C(seir, ss, :S) atol = 1e-11
                @test C(e2, se2, :pop_I) ≈ C(seir, ss, :pop_I) atol = 1e-11
                @test C(e2, se2, :pop_E1) .+ C(e2, se2, :pop_E2) ≈ C(seir, ss, :pop_E) atol = 1e-11
                @test Cpair(e2, se2, :E1, :I) .+ Cpair(e2, se2, :E2, :I) ≈ Cpair(seir, ss, :E, :I) atol = 1e-11
                # (v) the reproduction number: the typed computation of this file equals WP20's
                # tree-of-triangles R₀ (both kinds) for SIR, SEIR and the lumpable SIR
                for kind in (:generation, :clump)
                    @test R0g(sir, net; kind) ≈ R0w(sir, net; kind) rtol = 1e-12
                    @test R0g(seir_model(; τ = 0.6, σ = 0.5, γ = 1.0), net; kind) ≈
                          R0w(seir_model(; τ = 0.6, σ = 0.5, γ = 1.0), net; kind) rtol = 1e-12
                    @test R0g(l.metadata[:model], net; kind) ≈ R0w(sir, net; kind) rtol = 1e-12
                end
            end
        end
    end

    @testset "exact against the independent ordered pair-state reference" begin
        cases = [("SEAIR, seeded in E and I", SEAIR, SEAIR_SPEC, [:E => 0.01, :I => 0.005], 150.0),
                 ("two strains", TWOSTRAIN, TWOSTRAIN_SPEC, [:I1 => 0.005, :I2 => 0.005], 100.0),
                 ("SIR + vaccination (exit)", SIRV, SIRV_SPEC, [:I => 0.01], 100.0),
                 ("importation (exit into I, removal to the sink)", IMPORT, IMPORT_SPEC, [:I => 0.001], 100.0),
                 ("cross infection (alternating entries)", CROSS, CROSS_SPEC, [:I => 0.005, :A => 0.005], 100.0),
                 ("three Erlang stages", ERLANG, ERLANG_SPEC, [:I1 => 0.01], 100.0),
                 ("SI (absorbing infector)", SI, SI_SPEC, [:I => 0.01], 60.0)]
        for (label, net, g) in NETS, (mlabel, cm, sp, ρ, T) in cases
            @testset "$mlabel on $label" begin
                sys = lift(cm, net)
                sol = solveρ(sys, ρ; T)
                @test string(sol.retcode) == "Success"
                ref = pair_state_reference(g, sp, Dict(ρ...); T)
                worst = max_deviation(sys, sol, ref, sp)
                @test last(worst) < 1e-8
                last(worst) < 1e-8 || @info "worst deviation" label mlabel worst
            end
        end
        # branching into two latent classes with two infectors (one law suffices here)
        sys = lift(BRANCH, ClusteredNetwork(PJ))
        sol = solveρ(sys, [:E1 => 0.01]; T = 150.0)
        @test last(max_deviation(sys, sol, pair_state_reference(joint_g(PJ), BRANCH_SPEC, Dict(:E1 => 0.01); T = 150.0),
                                 BRANCH_SPEC)) < 1e-8
    end

    @testset "invariants: θ₃ = Σφ3, θ₂ = φ2_S + Σφ2_X, S + Σpop = 1 (to 1e-10)" begin
        for (cm, ρ) in ((SEAIR, [:E => 0.01]), (TWOSTRAIN, [:I1 => 0.005, :I2 => 0.005]), (SIRV, [:I => 0.01]),
                        (IMPORT, [:I => 0.01]), (BRANCH, [:E1 => 0.01, :A => 0.01])),
            (_, net, _) in NETS[1:3]
            sys = lift(cm, net)
            sol = solveρ(sys, ρ; T = 120.0)
            vars = sort!(collect(keys(sys.variables)))
            pair = vcat([n for n in vars if startswith(string(n), "φ3_")],
                        [n for n in keys(sys.observables) if startswith(string(n), "φ3_")])
            @test maximum(abs.(C(sys, sol, :θ₃) .- reduce(+, (C(sys, sol, n) for n in pair)))) < 1e-10
            φ2 = [n for n in vars if startswith(string(n), "φ2_")]
            @test maximum(abs.(C(sys, sol, :θ₂) .- C(sys, sol, :φ2_S) .- reduce(+, (C(sys, sol, n) for n in φ2)))) < 1e-10
            pops = [n for n in vars if startswith(string(n), "pop_")]
            @test maximum(abs.(C(sys, sol, :S) .+ reduce(+, (C(sys, sol, n) for n in pops)) .- 1)) < 1e-10
            for n in pair
                @test all(x -> -1e-12 <= x <= 1 + 1e-12, C(sys, sol, n))
            end
        end
    end

    @testset "empty blocks, the κ → 0 limit and symbolic network means" begin
        # no triangles: the configuration-model lift of g(x, 1)
        s0 = lift(SEAIR, pois(5.0, 0.0))
        @test !haskey(s0.variables, :θ₃) && !any(n -> startswith(string(n), "φ3_"), keys(s0.variables))
        c0 = lift(SEAIR, ConfigurationNetwork(PoissonDegree(5.0)))
        for X in (:S, :pop_E, :pop_I, :pop_A, :cumulative)
            @test C(s0, solveρ(s0, [:E => 0.01]), X) ≈ C(c0, solveρ(c0, [:E => 0.01]), X) atol = 1e-10
        end
        # no single edges: no θ₂
        s1 = lift(TWOSTRAIN, pois(0.0, 1.5))
        @test !haskey(s1.variables, :θ₂) && !any(n -> startswith(string(n), "φ2_"), keys(s1.variables))
        # symbolic Poisson means, set at solve time (0 selects the limit, without NaN)
        @parameters κs κt
        sk = lift(SEAIR, ClusteredNetwork(PoissonDegree(κs), PoissonDegree(κt)))
        for (a, b) in ((1.0, 2.0), (5.0, 0.0), (0.0, 1.5))
            sol = solve_epidemic(sk; p = Dict(:κs => a, :κt => b), initial = SeedFraction(:E => 0.01),
                                 tspan = (0.0, 100.0), saveat = 0.5, TOL...)
            @test string(sol.retcode) == "Success"
            ref = lift(SEAIR, pois(a, b))
            @test C(sk, sol, :S) ≈ C(ref, solveρ(ref, [:E => 0.01]), :S) atol = 1e-9
        end
    end

    @testset "final size: the tree-of-triangles relation (one entry state)" begin
        # SEAIR: E → I with probability p, E → A with 1 − p; q_k over the infectious phase
        q(k) = 0.6 * 0.4 / (0.4 + k * 0.5) + 0.4 * 0.4 / (0.4 + k * 0.25)
        # three Erlang stages at rate 1.5, each transmitting at 0.5
        qe(k) = (1.5 / (1.5 + k * 0.5))^3
        for (label, net, g) in NETS[1:2]
            for (cm, entry, q1, q2) in ((SEAIR, :E, q(1), q(2)), (ERLANG, :I1, qe(1), qe(2)))
                sys = lift(cm, net)
                sol = solveρ(sys, [entry => 1e-3]; T = 400.0, saveat = 400.0)
                R∞ = C(sys, sol, :cumulative)[end]
                @test R∞ ≈ triangle_final_size(g, q1, q2; ρ = 1e-3) atol = 1e-7
                @test R∞ ≈ 1 - C(sys, sol, :S)[end] atol = 1e-10
                # the public final_size (the ODE route: a ClusteredNetwork has no fixed-point equation)
                @test final_size(sys; initial = SeedFraction(entry => 1e-3)) ≈ R∞ atol = 1e-8
            end
        end
        # several entry states and exits (no tree-of-triangles relation): the public final size is
        # the limit of the cumulative incidence
        for (cm, ρ) in ((TWOSTRAIN, [:I1 => 0.005, :I2 => 0.005]), (SIRV, [:I => 0.01]))
            sys = lift(cm, pois(1.0, 2.0))
            sol = solveρ(sys, ρ; T = 400.0, saveat = 400.0)
            @test final_size(sys; initial = SeedFraction(ρ...)) ≈ C(sys, sol, :cumulative)[end] atol = 1e-8
        end
        @test_throws ArgumentError final_size(lift(SEAIR, pois(1.0, 2.0)))    # no fixed point: a seeding is needed
    end

    @testset "symbolic rates, parameters and constant divisors (E27)" begin
        net = ClusteredNetwork(PJ)
        sym = lift(seair_model(), net)
        p = Dict(:τI => 0.5, :τA => 0.25, :p => 0.6, :σ => 0.5, :γ => 0.4)
        sol = solve_epidemic(sym; p, initial = SeedFraction(:E => 0.01), tspan = (0.0, 150.0), saveat = 0.5, TOL...)
        num = lift(SEAIR, net)
        @test C(sym, sol, :S) ≈ C(num, solveρ(num, [:E => 0.01]; T = 150.0), :S) atol = 1e-10
        # the field divides only by the constant means g_x(1,1), g_y(1,1), never by a state expression
        for s in (sym, lift(TWOSTRAIN, net), lift(SIRV, net), lift(BRANCH, net))
            ode = symbolic_ode(s)
            @test all(f -> isempty(state_divisions(f, ode.states)), ode.rhs)
        end
    end

    @testset "R₀ on a tree of triangles for general models" begin
        net = pois(1.0, 2.0)
        # without triangles it is NetworkEpiCore's configuration next-generation R₀ (typed by entry)
        for cm in (SEAIR, TWOSTRAIN, CROSS, BRANCH, ERLANG)
            @test R0g(cm, pois(5.0, 0.0)) ≈ basic_reproduction_number(cm, ConfigurationNetwork(PoissonDegree(5.0))) rtol = 1e-10
        end
        # two strains with full cross-immunity: the larger of the two strains' SIR R₀
        @test R0g(TWOSTRAIN, net) ≈ max(R0w(sir_model(; τ = 0.5, γ = 0.6), net; kind = :clump),
                                        R0w(sir_model(; τ = 0.7, γ = 0.6), net; kind = :clump)) rtol = 1e-12
        # one entry state: the generation kind has WP20's closed form with SEAIR's q₁, q₂
        q(k) = 0.6 * 0.4 / (0.4 + k * 0.5) + 0.4 * 0.4 / (0.4 + k * 0.25)
        T, c = 1 - q(1), q(1) - q(2)
        g = poisson_g(1.0, 2.0)
        A, B = T * g(1.0, 1.0, 2, 0) / g(1.0, 1.0, 1, 0), 2T * g(1.0, 1.0, 1, 1) / g(1.0, 1.0, 1, 0)
        Cc, D = T * g(1.0, 1.0, 1, 1) / g(1.0, 1.0, 0, 1), 2T * g(1.0, 1.0, 0, 2) / g(1.0, 1.0, 0, 1)
        @test R0g(SEAIR, net; kind = :generation) ≈ maximum(real, eigvals([A B 0; Cc D c; Cc D 0])) rtol = 1e-12
        # the clump kind of one entry state: μ = 2T(1 + c) (WP20's R_*)
        μ = 2T * (1 + c)
        a, b, cc, d = T * g(1.0, 1.0, 2, 0) / g(1.0, 1.0, 1, 0), μ * g(1.0, 1.0, 1, 1) / g(1.0, 1.0, 1, 0),
                      T * g(1.0, 1.0, 1, 1) / g(1.0, 1.0, 0, 1), μ * g(1.0, 1.0, 0, 2) / g(1.0, 1.0, 0, 1)
        @test R0g(SEAIR, net) ≈ (a + d + sqrt((a - d)^2 + 4b * cc)) / 2 rtol = 1e-12
        # the threshold: R₀ = 1 exactly where the growth rate of the lifted field changes sign,
        # for models with several entry states, infectors and races inside the triangles
        λcases = [("two strains", ContactModel(:ts; contacts = [Contact(:S, :I1, :I1, :(λ * 0.3)), Contact(:S, :I2, :I2, :(λ * 0.1))],
                                               transitions = [NodeTransition(:I1, :R, 1.0), NodeTransition(:I2, :R, 0.2)]), net),
                  ("cross infection", ContactModel(:cr; contacts = [Contact(:S, :I, :A, :(λ * 0.8)), Contact(:S, :A, :I, :(λ * 0.1))],
                                                   transitions = [NodeTransition(:I, :R, 1.0), NodeTransition(:A, :R, 0.25)]), S2T2),
                  ("cross infection, triangles only", ContactModel(:cr; contacts = [Contact(:S, :I, :A, :(λ * 0.8)), Contact(:S, :A, :I, :(λ * 0.1))],
                                                                   transitions = [NodeTransition(:I, :R, 1.0), NodeTransition(:A, :R, 0.25)]), pois(0.0, 1.5)),
                  ("SEAIR", ContactModel(:se; contacts = [Contact(:S, :I, :E, :(λ / 6)), Contact(:S, :A, :E, :(λ / 12))],
                                         transitions = [NodeTransition(:E, :I, 0.12), NodeTransition(:E, :A, 0.08),
                                                        NodeTransition(:I, :R, 0.25), NodeTransition(:A, :R, 0.25)]), S2T2),
                  ("branching, joint law", ContactModel(:br; contacts = [Contact(:S, :I, :E1, :(λ * 0.3)), Contact(:S, :I, :E2, :(λ * 0.2)),
                                                                         Contact(:S, :A, :E1, :(λ * 0.5))],
                                                        transitions = [NodeTransition(:E1, :I, 0.5), NodeTransition(:E2, :A, 2.0),
                                                                       NodeTransition(:I, :R, 1.0), NodeTransition(:A, nothing, 0.7)]),
                   ClusteredNetwork(PJ))]
        for (label, cm, nt) in λcases
            @testset "$label" begin
                lo, hi = 0.01, 20.0
                for _ in 1:100
                    mid = sqrt(lo * hi)
                    R0g(cm, nt; p = Dict(:λ => mid)) > 1 ? (hi = mid) : (lo = mid)
                end
                λ⁺ = sqrt(lo * hi)
                growth = dfe_growth(cm, nt)
                @test abs(growth(λ⁺)) < 1e-9
                @test growth(λ⁺ * (1 - 1e-4)) < 0 < growth(λ⁺ * (1 + 1e-4))
                # the threshold body's early growth rate is this growth rate
                for λ in (λ⁺, 0.5λ⁺, 2λ⁺)
                    @test TH(early_growth_rate, lift(cm, nt); p = Dict(:λ => λ)) ≈ growth(λ) atol = 1e-10
                end
                # the unclustered R₀ (same degrees, triangles opened into lines) has another threshold
                k = nt === S2T2 ? ConfigurationNetwork(RegularDegree(6)) : nothing
                k === nothing || @test abs(basic_reproduction_number(cm, k, Dict(:λ => λ⁺)) - 1) > 0.05
            end
        end
        # errors and the system form
        @test_throws ArgumentError R0g(TWOSTRAIN, net; kind = :generation)     # two entry states
        @test_throws ArgumentError R0g(SEAIR, net; kind = :bogus)
        @test_throws ArgumentError R0g(seair_model(), net)                     # no numeric rates
        @test R0g(seair_model(), net; p = Dict(:τI => 0.5, :τA => 0.25, :p => 0.6, :σ => 0.5, :γ => 0.4)) ≈ R0g(SEAIR, net) rtol = 1e-14
        @test_throws AdmissibilityError R0g(sis_model(; τ = 0.5, γ = 1.0), net)
        @test R0g(lift(SEAIR, net)) ≈ R0g(SEAIR, net) rtol = 1e-14
        @test R0g(SIRV, net) ≈ R0g(sir_model(; τ = 0.6, γ = 0.5), net) rtol = 1e-12   # exits at ξ = 1
        @test_throws ArgumentError R0g(lift(SEAIR, ConfigurationNetwork(PoissonDegree(5.0))))
        # symbolic network means are taken from p by name (and missing ones are an error)
        @parameters κs κt
        @test_throws ArgumentError R0g(SEAIR, ClusteredNetwork(PoissonDegree(κs), PoissonDegree(1.0)))
        sk = ClusteredNetwork(PoissonDegree(κs), PoissonDegree(κt))
        @test R0g(SEAIR, sk; p = Dict(:κs => 1.0, :κt => 2.0)) ≈ R0g(SEAIR, net) rtol = 1e-12
        @test R0g(lift(SEAIR, sk); p = Dict(:κs => 1.0, :κt => 2.0), kind = :generation) ≈
              R0g(SEAIR, net; kind = :generation) rtol = 1e-12
        @test R0g(TWOSTRAIN, sk; p = Dict(:κs => 0.0, :κt => 1.5)) ≈ R0g(TWOSTRAIN, pois(0.0, 1.5)) rtol = 1e-12
        @test_throws ArgumentError R0g(SEAIR, sk; p = Dict(:κs => 1.0))
    end

    @testset "threshold quantities: the body of _numeric_threshold(::Val{:clustered}, …)" begin
        T1, c1 = 0.6 / 1.6, 1 / 1.6 - 1 / 2.2          # SIR, τ = 0.6, γ = 1: T = 1 − q₁, c = q₁ − q₂
        for (label, net, g) in NETS
            @testset "$label" begin
                gx, gy = g(1.0, 1.0, 1, 0), g(1.0, 1.0, 0, 1)
                # SIR and SEIR: WP20's generation R₀ and its 3-type matrix (verified issue E04)
                Cc, D = T1 * g(1.0, 1.0, 1, 1) / gy, 2T1 * g(1.0, 1.0, 0, 2) / gy
                Kref = if gx > 0
                    A, B = T1 * g(1.0, 1.0, 2, 0) / gx, 2T1 * g(1.0, 1.0, 1, 1) / gx
                    [A B 0; Cc D c1; Cc D 0]
                else
                    [D c1; D 0]
                end
                for cm in (sir_model(; τ = 0.6, γ = 1.0), seir_model(; τ = 0.6, σ = 0.5, γ = 1.0))
                    sys = lift(cm, net)
                    @test TH(next_generation_matrix, sys) ≈ Kref rtol = 1e-12
                    @test TH(basic_reproduction_number, sys) ≈ R0w(cm, net; kind = :generation) rtol = 1e-12
                    @test TH(basic_reproduction_number, sys; kind = :clump) ≈ R0w(cm, net; kind = :clump) rtol = 1e-12
                    @test TH(transmissibility, sys) ≈ T1 rtol = 1e-12
                end
                # one entry state: the generation kind; several: the typed clump kind (same threshold)
                @test TH(basic_reproduction_number, lift(SEAIR, net)) ≈ R0g(SEAIR, net; kind = :generation) rtol = 1e-12
                @test size(TH(next_generation_matrix, lift(SEAIR, net))) == (gx > 0 ? (3, 3) : (2, 2))
                for cm in (TWOSTRAIN, CROSS)
                    sys = lift(cm, net)
                    @test TH(basic_reproduction_number, sys) ≈ R0g(cm, net) rtol = 1e-12
                    @test TH(next_generation_matrix, sys) ≈ EBM._clustered_general_ngm(cm, net) rtol = 1e-12
                    @test size(TH(next_generation_matrix, sys)) == (gx > 0 ? (4, 4) : (2, 2))
                    @test_throws ArgumentError TH(next_generation_matrix, sys; kind = :generation)
                end
            end
        end
        # transmissibility: 1 − q₁ from the entered state, independent of the network
        net = pois(1.0, 2.0)
        q(k) = 0.6 * 0.4 / (0.4 + k * 0.5) + 0.4 * 0.4 / (0.4 + k * 0.25)
        sys = lift(SEAIR, net)
        @test TH(transmissibility, sys) ≈ 1 - q(1) rtol = 1e-12
        @test TH(transmissibility, sys) ≈
              transmissibility(SEAIR, ConfigurationNetwork(PoissonDegree(5.0)), Dict{Symbol,Float64}()) rtol = 1e-12
        @test TH(transmissibility, sys; from = :I) ≈ 0.5 / 0.9 rtol = 1e-12
        @test TH(transmissibility, sys; from = :A) ≈ 0.25 / 0.65 rtol = 1e-12
        @test TH(transmissibility, sys; from = :R) == 0.0
        ts = lift(TWOSTRAIN, net)
        @test TH(transmissibility, ts; from = :I1) ≈ 0.5 / 1.1 rtol = 1e-12
        @test TH(transmissibility, ts; from = :I2) ≈ 0.7 / 1.3 rtol = 1e-12
        @test_throws ArgumentError TH(transmissibility, ts)                     # two entry states
        @test_throws ArgumentError TH(transmissibility, sys; from = :S)
        @test_throws ArgumentError TH(transmissibility, sys; from = :Z)
        @test_throws ArgumentError TH(final_size, sys)
        @test_throws ArgumentError EBM._clustered_threshold(basic_reproduction_number,
                                                            lift(SEAIR, ConfigurationNetwork(PoissonDegree(5.0))),
                                                            Dict{Symbol,Float64}())
        # the early growth rate against the independent reference's exponential rate
        gcases = [("SIR, Poisson (1, 2)", sir_model(; τ = 0.6, γ = 1.0), NETS[1][3], net,
                   Spec([:S, :I, :R], [(:I, :I, 0.6)], [(:I, :R, 1.0)], []), [:I], :I),
                  ("SIR, subcritical", sir_model(; τ = 0.1, γ = 1.0), NETS[1][3], net,
                   Spec([:S, :I, :R], [(:I, :I, 0.1)], [(:I, :R, 1.0)], []), [:I], :I),
                  ("SEAIR, joint law", SEAIR, NETS[2][3], NETS[2][2], SEAIR_SPEC, [:E, :I, :A], :E),
                  ("cross infection, regular (2, 2)", CROSS, NETS[3][3], S2T2, CROSS_SPEC, [:I, :A], :I),
                  ("three Erlang stages, triangles only", ERLANG, NETS[4][3], NETS[4][2], ERLANG_SPEC,
                   [:I1, :I2, :I3], :I1)]
        for (label, cm, g, nt, sp, chain, seed) in gcases
            @testset "growth: $label" begin
                sys = lift(cm, nt)
                r = TH(early_growth_rate, sys)
                @test r ≈ reference_growth(g, sp, chain, seed) rtol = 1e-6
                @test sign(r) == sign(TH(basic_reproduction_number, sys) - 1)
            end
        end
        # the public API: analysis.jl reaches this body through _numeric_threshold(::Val{:clustered}, …),
        # which lift/clustered_general.jl defines (design §G.1 extension point)
        @test basic_reproduction_number(sys) ≈ TH(basic_reproduction_number, sys) rtol = 1e-12
        @test next_generation_matrix(sys) ≈ TH(next_generation_matrix, sys) rtol = 1e-12
        @test transmissibility(sys) ≈ TH(transmissibility, sys) rtol = 1e-12
        @test early_growth_rate(sys) ≈ TH(early_growth_rate, sys) rtol = 1e-10
        @test basic_reproduction_number(ts) ≈ R0g(TWOSTRAIN, net) rtol = 1e-12
        @test basic_reproduction_number(lift(sir_model(; τ = 0.6, γ = 1.0), net)) ≈
              R0w(sir_model(; τ = 0.6, γ = 1.0), net; kind = :generation) rtol = 1e-12
        # symbolic rates take their values by name from p
        sirsys = lift(sir_model(), net)
        @test basic_reproduction_number(sirsys; p = Dict(:τ => 0.3, :γ => 1.0)) ≈
              R0w(sir_model(; τ = 0.3, γ = 1.0), net; kind = :generation) rtol = 1e-12
    end

    @testset "acceptance 2: D∞ < 0.01 against NetworkOutbreaks on :seir_clust_s2t2 and :seair_clust_s2t2" begin
        # The reference ensembles are the scenarios' own (N = 10⁴, 200 runs, base seed 20260926, a
        # fresh Newman–Miller (2, 2) graph per run), conditioned on major outbreaks. The negative
        # control is the lift on the 6-regular configuration network (the same degrees, no
        # triangles).
        for id in (:seir_clust_s2t2, :seair_clust_s2t2)
            sc = scenario(id)
            @test sc.backends[:edge_based] === :exact_limit
            cmp = against_simulation(sc, ConfigurationNetwork(RegularDegree(6)))
            report(cmp, sc, "acceptance")
            @test cmp.n >= 195                                   # P(major) ≈ 1 with ρN = 100 seeds
            for row in cmp
                row.label == "EB" && @test row.D∞ < 0.01         # the WP36d acceptance, every observable
            end
            # the §E.2 tolerances of an :exact_limit back end
            @test cmp["EB", :I].D∞ < 0.005
            @test abs(cmp["EB", :cumulative].ΔR∞) < 0.005
            # the test has power: without the triangles the prediction is far off
            @test cmp["unclustered", :S].D∞ > 5 * max(cmp["EB", :S].D∞, 0.005)
        end
    end

    @testset "more general models against NetworkOutbreaks (local scenarios)" begin
        # the scenario runner on scenarios built here (the canonical SimConfig: N = 10⁴, 200 runs)
        cross = ContactModel(:cross; contacts = [Contact(:S, :I, :A, :τI), Contact(:S, :A, :I, :τA)],
                             transitions = [NodeTransition(:I, :R, :γI), NodeTransition(:A, :R, :γA)])
        local_scenarios = [
            (Scenario(:twostrain_clust_s2t2; model = twostrain_model(), network = S2T2,
                      params = Dict(:τ1 => 1 / 6, :τ2 => 1 / 5, :γ => 1 / 4),
                      initial = SeedFraction(:I1 => 0.005, :I2 => 0.005), tspan = (0, 60)),
             ConfigurationNetwork(RegularDegree(6))),
            (Scenario(:sirv_clust_pois12; model = sirv_model(), network = pois(1.0, 2.0),
                      params = Dict(:τ => 0.6, :γ => 1.0, :ν => 0.05), initial = SeedFraction(:I => 0.01),
                      tspan = (0, 20), tstep = 0.1),
             ConfigurationNetwork(PoissonDegree(5.0))),
            (Scenario(:cross_clust_s2t2; model = cross, network = S2T2,
                      params = Dict(:τI => 0.4, :τA => 0.1, :γI => 0.5, :γA => 0.25),
                      initial = SeedFraction(:I => 0.005, :A => 0.005), tspan = (0, 80)),
             ConfigurationNetwork(RegularDegree(6)))]
        for (sc, unclustered) in local_scenarios
            @testset "$(sc.id)" begin
                cmp = against_simulation(sc, unclustered)
                report(cmp, sc, "local scenario")
                @test cmp.n >= 195
                for row in cmp
                    row.label == "EB" && @test row.D∞ < 0.01
                end
                @test abs(cmp["EB", :cumulative].ΔR∞) < 0.005
                @test cmp["unclustered", :S].D∞ > 5 * max(cmp["EB", :S].D∞, 0.005)
            end
        end
    end
end
