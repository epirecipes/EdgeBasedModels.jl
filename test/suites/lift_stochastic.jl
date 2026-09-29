# WP17 acceptance 4: the exit type against exact stochastic simulation (NetworkOutbreaks), on the
# graphs of :sir_vax_pois5 (SIR + vaccination S → V on Poisson(5), τ = 1/6, γ = 1/4, ν = 0.02,
# 1% seeded in I): max_t |S_EB(t) − mean S_sim(t)| ≤ 0.01 at N = 2×10⁴ (DESIGN §G.2 WP17). The
# same protocol checks the multitype lift on the stochastic block model of :sir_sbm2.
#
# Protocol (DESIGN §E.2 with §J.7): a fresh graph per run (graph r from
# NetworkOutbreaks.stable_rng(base + r), the SSA of run r from stable_rng(base + 2³² + r)),
# NextReaction, exactly ρN seeds placed uniformly (within each type for the SBM), runs
# conditioned on a major outbreak (ever infected minus seeds ≥ 0.05 N by t_end). The reported
# SE is the standard error of the conditioned mean at the time of the largest difference.

using EdgeBasedModels
using NetworkEpiCore
using Statistics
using Random
using OrdinaryDiffEq: Vern9
using Test

import Graphs
import NetworkOutbreaks as NO

const N = 20_000
const RUNS = 40
const BASE = 20260926
const GRID = collect(0.0:0.5:60.0)
const TOL = (solver = Vern9(), reltol = 1e-10, abstol = 1e-12)

# Run the ensemble: `graph(rng)` draws a graph, `seeds(rng)` a SeedSpec, `observe(counts)` the
# vector of observed fractions at one time, `infected(counts_end)` the fraction ever infected.
function ensemble(model, graph, seeds, observe, ever_infected; nseed)
    curves = Vector{Matrix{Float64}}()
    for r in 1:RUNS
        g = graph(NO.stable_rng(BASE + r))
        spec = NO.OutbreakSpec(; model, network = g, initial = seeds(NO.stable_rng(BASE + 2^33 + r)),
                               tspan = (0.0, GRID[end]))
        traj = NO.simulate(spec; algorithm = NO.NextReaction(), rng = NO.stable_rng(BASE + 2^32 + r))
        obs = reduce(hcat, [observe(NO.state_at(traj, t)) ./ N for t in GRID])
        ever_infected(NO.state_at(traj, GRID[end])) - nseed >= 0.05 * N && push!(curves, obs)
    end
    return curves
end

# max over time and observables of |EB − mean|, with the SE there.
function discrepancy(eb::Matrix{Float64}, curves)
    runs = cat(curves...; dims = 3)
    μ = dropdims(mean(runs; dims = 3); dims = 3)
    se = dropdims(std(runs; dims = 3); dims = 3) ./ sqrt(length(curves))
    d = abs.(eb .- μ)
    k = argmax(d)
    return d[k], se[k], k
end

@testset "lift: against NetworkOutbreaks (exits, multitype)" begin
    @testset "acceptance 4: SIR + vaccination on :sir_vax_pois5 graphs, N = 2×10⁴" begin
        sc = scenario(:sir_vax_pois5)
        p = sc.params
        sys = edge_based(sc)
        sol = solve_epidemic(sys; p, initial = sc.initial, tspan = (0.0, GRID[end]), saveat = GRID, TOL...)
        eb = permutedims(hcat(compartment(sys, sol, :S), compartment(sys, sol, :pop_I),
                              compartment(sys, sol, :pop_R), compartment(sys, sol, :pop_V)))
        ρ = only(last.(seed_fractions(sc.initial)))
        model = NO.OutbreakModel([:S, :I, :R, :V], [false, true, false, false],
                                 [NO.OutbreakTransition(:S, :I, p[:τ], :infection),
                                  NO.OutbreakTransition(:I, :R, p[:γ], :spontaneous),
                                  NO.OutbreakTransition(:S, :V, p[:ν], :spontaneous)])
        μ = 5.0
        curves = ensemble(model, rng -> Graphs.erdos_renyi(N, μ / (N - 1); rng),
                          rng -> NO.SeedFraction(:I => ρ), c -> Float64.(c[1:4]), c -> c[2] + c[3];
                          nseed = round(Int, ρ * N))
        @test length(curves) >= RUNS - 2                                      # P(major) ≈ 1 at ρN = 200
        dS, seS, _ = discrepancy(eb[1:1, :], [c[1:1, :] for c in curves])
        dall, seall, k = discrepancy(eb, curves)
        @info "WP17 exit type vs NetworkOutbreaks (:sir_vax_pois5 graphs)" N runs = RUNS major = length(curves) max_abs_dS = dS se_at_max = seS max_abs_any = dall
        @test dS <= 0.01
        @test dall <= 0.01
        # without the survival factor ξ (exits ignored on edges) the edge-based model is far off:
        # the naive S = (1 − ρ)e^{−νt}ψ(θ) with θ from the plain SIR lift (design §D.4: 0.10)
        plain = edge_based(sir_model(τ = p[:τ], γ = p[:γ]), sc.network)
        sp = solve_epidemic(plain; initial = sc.initial, tspan = (0.0, GRID[end]), saveat = GRID, TOL...)
        naive = compartment(plain, sp, :S) .* exp.(-p[:ν] .* GRID)
        dn, _, _ = discrepancy(permutedims(naive), [c[1:1, :] for c in curves])
        @test dn > 5 * dS
    end

    @testset "the multitype lift on the stochastic block model of :sir_sbm2, N = 2×10⁴" begin
        sc = scenario(:sir_sbm2)
        p = sc.params
        sys = edge_based(sc)
        sol = solve_epidemic(sys; p, initial = sc.initial, tspan = (0.0, GRID[end]), saveat = GRID, TOL...)
        keys_ = (:S_a, :pop_I_a, :pop_R_a, :S_b, :pop_I_b, :pop_R_b)
        eb = permutedims(reduce(hcat, [compartment(sys, sol, k) for k in keys_]))
        net = sc.network
        n = round.(Int, net.sizes .* N)
        c = [mean_degree(net.degrees[i], net.types[j]) for i in 1:2, j in 1:2]
        τ, γ = p[:τ], p[:γ]
        model = NO.OutbreakModel([:S_a, :I_a, :R_a, :S_b, :I_b, :R_b], [false, true, false, false, true, false],
                                 [NO.OutbreakTransition(:S_a, :I_a, τ, :infection; via = [:I_a, :I_b]),
                                  NO.OutbreakTransition(:S_b, :I_b, τ, :infection; via = [:I_a, :I_b]),
                                  NO.OutbreakTransition(:I_a, :R_a, γ, :spontaneous),
                                  NO.OutbreakTransition(:I_b, :R_b, γ, :spontaneous)])
        ρ = Dict(seed_fractions(sc.initial))
        ka, kb = round(Int, ρ[:I_a] * N), round(Int, ρ[:I_b] * N)
        function seeds(rng)
            A = randperm(rng, n[1])
            B = n[1] .+ randperm(rng, n[2])
            return NO.SeedNodes(:I_a => A[1:ka], :S_a => A[(ka + 1):end], :I_b => B[1:kb]; default = :S_b)
        end
        curves = ensemble(model, rng -> Graphs.stochastic_block_model(c, n; rng), seeds, x -> Float64.(x[1:6]),
                          x -> x[2] + x[3] + x[5] + x[6]; nseed = ka + kb)
        @test length(curves) >= RUNS - 2
        d, se, k = discrepancy(eb, curves)
        @info "WP17 multitype lift vs NetworkOutbreaks (:sir_sbm2 SBM graphs)" N runs = RUNS major = length(curves) max_abs = d se_at_max = se observable = keys_[k[1]]
        @test d <= 0.01
    end
end
