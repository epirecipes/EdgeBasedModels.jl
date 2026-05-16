"""
Shared validation helpers for EBM vignettes.

Provides `gillespie_ribbon` which builds a NetworkOutbreaks `OutbreakModel`
from an EBM `DiseaseProgression` and runs an ensemble of stochastic SSA
trajectories on a sequence of host graphs, returning grids of mean and
standard deviation per compartment.
"""

using NetworkOutbreaks
using Graphs
using StableRNGs
using Statistics
using Random
using LinearAlgebra

"""
    gillespie_ribbon(prog, params, graph_builder; N, n_graphs, nsims_per_graph,
                     tspan, seed_fraction, tgrid, base_seed, infected = :I)

Run a Gillespie SSA ensemble across `n_graphs` independent host-graph
realisations × `nsims_per_graph` epidemic replicates each.

`graph_builder(rng) -> AbstractGraph` returns one host graph per call.
`prog` is an EBM `DiseaseProgression`. `params` is `Dict{Symbol,<:Real}` of
rate values (e.g. `Dict(:β => β_val, :γ => γ_val)`).

Returns `(tgrid, mean_dict, std_dict)` where each dict maps compartment
symbol to the time-series of (mean / N) and (std / N) across all runs.
"""
function gillespie_ribbon(prog, params, graph_builder;
                          N::Int = 1000,
                          n_graphs::Int = 5,
                          nsims_per_graph::Int = 20,
                          tspan = (0.0, 40.0),
                          seed_fraction::Real = 0.01,
                          tgrid = collect(tspan[1]:0.5:tspan[2]),
                          base_seed::Int = 20240501,
                          infected::Symbol = :I)
    no_model = OutbreakModel(prog, params)
    rng = StableRNG(base_seed)
    nsamples = n_graphs * nsims_per_graph
    comps = collect(keys(no_model.index_of))
    series = Dict(c => Matrix{Float64}(undef, nsamples, length(tgrid)) for c in comps)
    row = 1
    for gi in 1:n_graphs
        g = graph_builder(rng)
        spec = OutbreakSpec(model = no_model, network = g,
                            initial = SeedFraction(infected => seed_fraction),
                            tspan = tspan)
        ens = simulate_ensemble(spec; nsims = nsims_per_graph,
                                seed = base_seed + 1000 * gi,
                                parallel = true)
        for traj in ens.trajectories
            for (j, t) in enumerate(tgrid)
                st = state_at(traj, t)
                for c in comps
                    series[c][row, j] = Float64(st[no_model.index_of[c]])
                end
            end
            row += 1
        end
    end
    means = Dict(c => vec(mean(M; dims = 1)) ./ N for (c, M) in series)
    stds  = Dict(c => vec(std(M;  dims = 1)) ./ N for (c, M) in series)
    return tgrid, means, stds
end

"Default Erdős–Rényi builder for a Poisson configuration model with mean degree κ."
poisson_graph_builder(N::Int, κ::Real) =
    rng -> erdos_renyi(N, κ / (N - 1); rng = rng)

"Random k-regular graph builder."
regular_graph_builder(N::Int, k::Int) =
    rng -> random_regular_graph(N, k; rng = rng)

"Configuration-model graph from explicit degree distribution `pk` (vector of probabilities for k=0,1,2,…)."
function configuration_graph_builder(N::Int, pk::AbstractVector{<:Real})
    rng -> begin
        ks = Int[]
        for _ in 1:N
            push!(ks, _sample_from_pk(pk, rng))
        end
        if isodd(sum(ks))
            ks[end] += 1
        end
        random_configuration_model(N, ks; check_graphical = false)
    end
end

"""
    clustered_poisson_graph_builder(N, κ_s, κ_t)

Newman–Miller "doubly Poisson" clustered configuration model. Each node
gets Poisson(κ_s) single-edge stubs and Poisson(κ_t) triangle-corner stubs.
Single stubs are randomly paired into edges; triangle stubs are randomly
grouped into triangles (3 stubs per triangle, all pairwise edges added).

Mean total degree = κ_s + 2 κ_t. Returns `rng -> SimpleGraph`.
"""
function clustered_poisson_graph_builder(N::Int, κ_s::Real, κ_t::Real)
    rng -> begin
        s_stubs = [randn_pois(rng, κ_s) for _ in 1:N]
        t_stubs = [randn_pois(rng, κ_t) for _ in 1:N]
        # Make sums fit (single stubs even, triangle stubs multiple of 3)
        if isodd(sum(s_stubs)); s_stubs[end] += 1; end
        rem3 = sum(t_stubs) % 3
        if rem3 != 0
            t_stubs[end] += (3 - rem3)
        end
        g = SimpleGraph(N)
        # Pair single stubs
        slist = Int[]
        for (v, k) in enumerate(s_stubs), _ in 1:k
            push!(slist, v)
        end
        shuffle!(rng, slist)
        for i in 1:2:(length(slist)-1)
            u, v = slist[i], slist[i+1]
            u != v && add_edge!(g, u, v)
        end
        # Group triangle stubs in 3s
        tlist = Int[]
        for (v, k) in enumerate(t_stubs), _ in 1:k
            push!(tlist, v)
        end
        shuffle!(rng, tlist)
        for i in 1:3:(length(tlist)-2)
            a, b, c = tlist[i], tlist[i+1], tlist[i+2]
            a != b && add_edge!(g, a, b)
            a != c && add_edge!(g, a, c)
            b != c && add_edge!(g, b, c)
        end
        g
    end
end

"Sample a Poisson(λ) integer using Knuth's algorithm (no extra deps)."
function randn_pois(rng, λ::Real)
    L = exp(-λ); k = 0; p = 1.0
    while true
        k += 1; p *= rand(rng)
        p <= L && return k - 1
    end
end

"""
    xulvi_brunet_sokolov_rewire!(g, n_swaps, p_assort; rng)

Apply `n_swaps` Xulvi-Brunet–Sokolov rewiring steps to graph `g`. With
probability `p_assort` an attempted swap is accepted only if it increases
local degree-degree correlation (assortative); otherwise the swap is
neutral (configuration-model preserving). Sets `p_assort = 0` for neutral
edge-swap mixing; `p_assort = 1` for fully assortative rewiring;
negative values for disassortative.
"""
function xulvi_brunet_sokolov_rewire!(g::SimpleGraph, n_swaps::Int,
                                       p_assort::Real; rng::AbstractRNG)
    elist = collect(edges(g))
    isempty(elist) && return g
    for _ in 1:n_swaps
        i = rand(rng, 1:length(elist))
        j = rand(rng, 1:length(elist))
        i == j && continue
        e1, e2 = elist[i], elist[j]
        a, b = src(e1), dst(e1)
        c, d = src(e2), dst(e2)
        nodes = [a, b, c, d]
        length(unique(nodes)) == 4 || continue
        if rand(rng) < abs(p_assort)
            # sort endpoints by degree, pair (high,high)+(low,low) for assort,
            # or (high,low)+(low,high) for disassort
            sortednodes = sort(nodes; by = v -> degree(g, v))
            if p_assort > 0
                u1, v1 = sortednodes[1], sortednodes[2]
                u2, v2 = sortednodes[3], sortednodes[4]
            else
                u1, v1 = sortednodes[1], sortednodes[4]
                u2, v2 = sortednodes[2], sortednodes[3]
            end
        else
            # neutral random swap
            if rand(rng) < 0.5
                u1, v1, u2, v2 = a, c, b, d
            else
                u1, v1, u2, v2 = a, d, b, c
            end
        end
        # Skip if would create self-loops or duplicate edges
        (u1 == v1 || u2 == v2) && continue
        has_edge(g, u1, v1) && continue
        has_edge(g, u2, v2) && continue
        rem_edge!(g, a, b); rem_edge!(g, c, d)
        add_edge!(g, u1, v1); add_edge!(g, u2, v2)
        elist[i] = Edge(u1, v1)
        elist[j] = Edge(u2, v2)
    end
    return g
end

"""
    correlated_bimodal_builder(N, k_lo, k_hi, frac_lo, p_assort; n_swaps_factor=20)

Build a configuration-model graph whose nodes have degree `k_lo` (with
probability `frac_lo`) or `k_hi` (with probability `1-frac_lo`), then apply
Xulvi-Brunet–Sokolov rewiring with the given assortativity bias.
`n_swaps_factor * E` rewiring attempts are made.
"""
function correlated_bimodal_builder(N::Int, k_lo::Int, k_hi::Int,
                                    frac_lo::Real, p_assort::Real;
                                    n_swaps_factor::Int = 20)
    rng -> begin
        ks = [rand(rng) < frac_lo ? k_lo : k_hi for _ in 1:N]
        if isodd(sum(ks)); ks[end] += 1; end
        g = random_configuration_model(N, ks; check_graphical = false)
        xulvi_brunet_sokolov_rewire!(g, n_swaps_factor * ne(g), p_assort; rng = rng)
        g
    end
end

"""
    gillespie_final_size_sweep(progression_factory, params_factory, graph_builder, sweep_vals;
                               N, n_graphs, nsims_per_graph, tspan, seed_fraction,
                               recovered=:R, base_seed)

For each value `x` in `sweep_vals`, build the EBM `DiseaseProgression` via
`progression_factory(x)` and rate dictionary via `params_factory(x)`,
simulate `n_graphs × nsims_per_graph` SSA trajectories on graphs from
`graph_builder(rng)`, and report the per-sweep distribution of final sizes
(fraction in compartment `recovered` at end of `tspan`).

Returns a NamedTuple `(values, means, stds, q025, q975, all)` where each
field except `values` is a Vector aligned with `sweep_vals` and `all` is
a `Vector{Vector{Float64}}` of the per-sweep raw final-size samples.
"""
function gillespie_final_size_sweep(progression_factory, params_factory,
                                    graph_builder, sweep_vals;
                                    N::Int = 1000,
                                    n_graphs::Int = 3,
                                    nsims_per_graph::Int = 20,
                                    tspan = (0.0, 200.0),
                                    seed_fraction::Real = 0.01,
                                    recovered::Symbol = :R,
                                    base_seed::Int = 20240601,
                                    infected::Symbol = :I)
    means = Float64[]; stds = Float64[]; q025 = Float64[]; q975 = Float64[]
    all_samples = Vector{Vector{Float64}}()
    rng = StableRNG(base_seed)
    for (xi, x) in enumerate(sweep_vals)
        prog = progression_factory(x)
        params = params_factory(x)
        no_model = OutbreakModel(prog, params)
        ridx = no_model.index_of[recovered]
        samples = Float64[]
        for gi in 1:n_graphs
            g = graph_builder(rng)
            spec = OutbreakSpec(model = no_model, network = g,
                                initial = SeedFraction(infected => seed_fraction),
                                tspan = tspan)
            ens = simulate_ensemble(spec; nsims = nsims_per_graph,
                                    seed = base_seed + 100*xi + gi,
                                    parallel = true)
            for traj in ens.trajectories
                push!(samples, Float64(traj.counts[ridx, end]) / N)
            end
        end
        push!(all_samples, samples)
        push!(means, mean(samples))
        push!(stds,  std(samples))
        sorted = sort(samples)
        n = length(sorted)
        push!(q025, sorted[max(1, floor(Int, 0.025*n))])
        push!(q975, sorted[max(1, ceil(Int,  0.975*n))])
    end
    return (values = collect(sweep_vals), means = means, stds = stds,
            q025 = q025, q975 = q975, all = all_samples)
end

"""
    multiplex_graph_builder(N, layer_specs)

Return a function `rng -> MultiplexNetwork(...)` that, on each call,
samples one host graph per layer and bundles them with a per-layer
relative-rate weight.

`layer_specs` is a vector of `(rate_weight, layer_builder)` tuples,
where `layer_builder(N, rng) -> AbstractGraph`.

Convenience wrappers `poisson_layer(κ)` and `regular_layer(k)` are
provided.
"""
function multiplex_graph_builder(N::Int,
                                 layer_specs::AbstractVector{<:Tuple})
    rng -> begin
        layers = [spec[2](N, rng) for spec in layer_specs]
        weights = [Float64(spec[1]) for spec in layer_specs]
        MultiplexNetwork(layers, weights)
    end
end

"Layer factory: Poisson(κ) Erdős–Rényi graph for a multiplex layer."
poisson_layer(κ::Real) = (N, rng) -> erdos_renyi(N, κ / (N - 1); rng = rng)

"Layer factory: random k-regular graph for a multiplex layer."
regular_layer(k::Int) = (N, rng) -> random_regular_graph(N, k; rng = rng)

function _sample_from_pk(pk, rng)
    u = rand(rng)
    c = 0.0
    for (i, p) in enumerate(pk)
        c += p
        u <= c && return i - 1
    end
    return length(pk) - 1
end

# ---------------------------------------------------------------------------
# Multi-type / SBM support
# ---------------------------------------------------------------------------

"""
    sbm_typed_graph_builder(type_sizes, κ_matrix)

`type_sizes` is a `Vector{Pair{Symbol,Int}}` giving the population of each
type in order. `κ_matrix` is an `OrderedDict` (or insertion-stable `Dict`) of
the form `Dict((:Y,:Y) => 6.0, (:Y,:O) => 2.0, ...)` where the entry
`(l, k)` is the mean number of type-`k` neighbours that a type-`l` node has.

Returns `rng -> (graph, types::Vector{Symbol})`. The returned graph is a
single (untyped) `SimpleGraph`; the parallel `types` vector records each
node's type. Within-type edges are sampled at probability
`κ_{ll} / (n_l - 1)`; between-type edges at `κ_{lk} / n_k` (consistent
with `κ_{lk}·n_l = κ_{kl}·n_k`).
"""
function sbm_typed_graph_builder(type_sizes::AbstractVector{<:Pair},
                                 κ_matrix::AbstractDict)
    rng -> begin
        type_syms = Symbol[t for (t, _) in type_sizes]
        sizes = Int[n for (_, n) in type_sizes]
        N = sum(sizes)
        type_of = Vector{Symbol}(undef, N)
        offsets = Dict{Symbol,Int}()
        cursor = 0
        for (t, n) in type_sizes
            offsets[t] = cursor
            for i in 1:n
                type_of[cursor + i] = t
            end
            cursor += n
        end
        g = SimpleGraph(N)
        for (li, lt) in enumerate(type_syms)
            n_l = sizes[li]
            for (ki, kt) in enumerate(type_syms)
                n_k = sizes[ki]
                κ = haskey(κ_matrix, (lt, kt)) ? κ_matrix[(lt, kt)] :
                    haskey(κ_matrix, (kt, lt)) ? κ_matrix[(kt, lt)] : 0.0
                κ > 0 || continue
                if lt == kt
                    p = κ / max(n_l - 1, 1)
                    p > 0 || continue
                    for i in 1:n_l, j in (i+1):n_l
                        if rand(rng) < p
                            add_edge!(g, offsets[lt] + i, offsets[lt] + j)
                        end
                    end
                elseif li < ki  # only do each unordered pair once
                    p = κ / n_k
                    p > 0 || continue
                    for i in 1:n_l, j in 1:n_k
                        if rand(rng) < p
                            add_edge!(g, offsets[lt] + i, offsets[kt] + j)
                        end
                    end
                end
            end
        end
        (g, type_of)
    end
end

"""
    multitype_outbreak_model(types, base_progression_compartments, β, γ; via_all=true)

Build a NetworkOutbreaks `OutbreakModel` whose compartments are the cross
product of `types` and the base SIR compartments `(:S, :I, :R)`. The model
is suitable for a constant-β multi-type SIR; per-pair β matrices can be
supplied as a `Dict((src_type, infectious_type) => β)` to differentiate
within-pair rates.
"""
function multitype_sir_model(types::AbstractVector{Symbol};
                             β::Real, γ::Real,
                             β_matrix::Union{Nothing,AbstractDict}=nothing,
                             name=:multitype_sir)
    comps = Symbol[]
    for t in types, c in (:S, :I, :R)
        push!(comps, Symbol(c, :_, t))
    end
    inf_flag = [endswith(string(c), "_$(t)") && startswith(string(c), "I_")
                for c in comps, t in [first(types)]]
    infectious = [startswith(string(c), "I_") for c in comps]

    trs = OutbreakTransition[]
    via_I = [Symbol(:I_, t) for t in types]
    for tl in types
        S_t = Symbol(:S_, tl); I_t = Symbol(:I_, tl); R_t = Symbol(:R_, tl)
        if β_matrix === nothing
            push!(trs, OutbreakTransition(S_t, I_t, β, :infection; via=via_I))
        else
            for tk in types
                rate = get(β_matrix, (tl, tk), β)
                rate > 0 || continue
                push!(trs, OutbreakTransition(S_t, I_t, rate, :infection;
                                              via=[Symbol(:I_, tk)]))
            end
        end
        push!(trs, OutbreakTransition(I_t, R_t, γ, :spontaneous))
    end
    return OutbreakModel(comps, infectious, trs; name = name)
end

"""
    seed_nodes_by_type(types::Vector{Symbol}, type_of::Vector{Symbol}, seed_fraction; rng)

Build a `SeedNodes` initial spec that places `seed_fraction` of EACH type
into `:I_<type>` and the rest into `:S_<type>`.
"""
function seed_nodes_by_type(types::AbstractVector{Symbol},
                            type_of::AbstractVector{Symbol},
                            seed_fraction::Real, rng::AbstractRNG)
    pairs = Pair{Symbol, Vector{Int}}[]
    for t in types
        all_nodes = findall(==(t), type_of)
        nseed = max(1, round(Int, seed_fraction * length(all_nodes)))
        perm = randperm(rng, length(all_nodes))
        I_nodes = all_nodes[perm[1:nseed]]
        S_nodes = all_nodes[perm[(nseed+1):end]]
        push!(pairs, Symbol(:I_, t) => I_nodes)
        push!(pairs, Symbol(:S_, t) => S_nodes)
    end
    return SeedNodes(pairs...)
end

"""
    gillespie_multitype_ribbon(types, sbm_builder; β, γ, β_matrix=nothing, ...)

Run an SSA ensemble across `n_graphs` independent SBM realisations ×
`nsims_per_graph` epidemic replicates and collect per-type compartment
ribbons (mean / std of fractions of each type's population).

`sbm_builder(rng) -> (graph, type_of)`. Returns `(tgrid, mean_dict, std_dict)`
where each dict maps `(compartment, type)` symbols (e.g. `:S_Young`) to the
time-series of (mean fraction within that type) and (std).
"""
function gillespie_multitype_ribbon(types::AbstractVector{Symbol},
                                    sbm_builder;
                                    β::Real, γ::Real,
                                    β_matrix=nothing,
                                    n_graphs::Int = 5,
                                    nsims_per_graph::Int = 20,
                                    tspan = (0.0, 40.0),
                                    seed_fraction::Real = 0.01,
                                    tgrid = collect(tspan[1]:0.5:tspan[2]),
                                    base_seed::Int = 20240501,
                                    major_outbreak_thresh::Real = 0.0)
    no_model = multitype_sir_model(types; β=β, γ=γ, β_matrix=β_matrix)
    rng = StableRNG(base_seed)
    nsamples = n_graphs * nsims_per_graph
    out_keys = [(c, t) for t in types, c in (:S, :I, :R)]
    series = Dict((c,t) => Matrix{Float64}(undef, nsamples, length(tgrid))
                  for (c,t) in out_keys)
    type_pop = Dict{Symbol,Int}()
    row = 1
    for gi in 1:n_graphs
        g, type_of = sbm_builder(rng)
        for t in types
            type_pop[t] = count(==(t), type_of)
        end
        seed_spec = seed_nodes_by_type(types, type_of, seed_fraction, rng)
        spec = OutbreakSpec(model = no_model, network = g,
                            initial = seed_spec, tspan = tspan)
        ens = simulate_ensemble(spec; nsims = nsims_per_graph,
                                seed = base_seed + 1000 * gi,
                                parallel = true)
        for traj in ens.trajectories
            for (j, t_now) in enumerate(tgrid)
                st = state_at(traj, t_now)
                for (c, ttype) in out_keys
                    sym = Symbol(c, :_, ttype)
                    series[(c, ttype)][row, j] = Float64(st[no_model.index_of[sym]]) / type_pop[ttype]
                end
            end
            row += 1
        end
    end
    # Major-outbreak filter: keep runs where max type-level attack rate ≥ threshold
    keep = trues(nsamples)
    if major_outbreak_thresh > 0
        for i in 1:nsamples
            max_attack = maximum(1.0 - series[(:S, t)][i, end] for t in types)
            keep[i] = max_attack >= major_outbreak_thresh
        end
    end
    means = Dict((c,t) => vec(mean(M[keep, :]; dims = 1)) for ((c,t), M) in series)
    stds  = Dict((c,t) => vec(std(M[keep, :];  dims = 1)) for ((c,t), M) in series)
    return tgrid, means, stds
end

# ---------------------------------------------------------------------------
# Maximum Mean Discrepancy (MMD) — kernel two-sample test for trajectories
# ---------------------------------------------------------------------------

"""
    pairwise_sqdist(X, Y)

Squared Euclidean distance between every row of `X` and every row of `Y`.
"""
function pairwise_sqdist(X::AbstractMatrix, Y::AbstractMatrix)
    n, m = size(X, 1), size(Y, 1)
    D = Matrix{Float64}(undef, n, m)
    sx = sum(X.^2; dims = 2)[:]
    sy = sum(Y.^2; dims = 2)[:]
    XY = X * Y'
    @inbounds for i in 1:n, j in 1:m
        D[i, j] = max(0.0, sx[i] + sy[j] - 2 * XY[i, j])
    end
    return D
end

"""
    median_heuristic_sigma(X) -> σ

Median-of-pairwise-distances bandwidth for a Gaussian RBF kernel.
"""
function median_heuristic_sigma(X::AbstractMatrix)
    D = pairwise_sqdist(X, X)
    n = size(D, 1)
    vals = Float64[]
    @inbounds for i in 1:n, j in (i+1):n
        push!(vals, sqrt(D[i, j]))
    end
    isempty(vals) && return 1.0
    σ = median(vals)
    return σ > 0 ? σ : 1.0
end

"""
    mmd2_gaussian(X, Y; σ = nothing) -> Float64

Biased two-sample MMD² estimate with a Gaussian RBF kernel
`k(x,y) = exp(-|x-y|² / (2σ²))`. `X` and `Y` are matrices whose rows are
samples (e.g. trajectories flattened over a time grid). If `σ` is `nothing`
it is set to the median pairwise distance over `[X; Y]` (the "median
heuristic").

Returns `MMD² = E[k(X,X')] - 2 E[k(X,Y)] + E[k(Y,Y')]`. Values near 0
indicate the two samples come from indistinguishable distributions; large
positive values indicate detectable mismatch.
"""
function mmd2_gaussian(X::AbstractMatrix, Y::AbstractMatrix; σ = nothing)
    σ = σ === nothing ? median_heuristic_sigma(vcat(X, Y)) : σ
    s2 = 2 * σ^2
    Kxx = exp.(-pairwise_sqdist(X, X) ./ s2)
    Kyy = exp.(-pairwise_sqdist(Y, Y) ./ s2)
    Kxy = exp.(-pairwise_sqdist(X, Y) ./ s2)
    return mean(Kxx) - 2 * mean(Kxy) + mean(Kyy)
end

"""
    mmd2_permutation_pvalue(X, Y; σ = nothing, n_perm = 200, rng = StableRNG(20240701))

Permutation-test p-value for the two-sample MMD² statistic. Returns
`(mmd2, p_value, σ_used)`. A small p-value indicates the two samples are
distinguishable.
"""
function mmd2_permutation_pvalue(X::AbstractMatrix, Y::AbstractMatrix;
                                 σ = nothing, n_perm::Int = 200,
                                 rng = StableRNG(20240701))
    Z = vcat(X, Y)
    σ = σ === nothing ? median_heuristic_sigma(Z) : σ
    obs = mmd2_gaussian(X, Y; σ = σ)
    n = size(X, 1); m = size(Y, 1)
    nz = n + m
    count_ge = 0
    for _ in 1:n_perm
        perm = randperm(rng, nz)
        Xp = Z[perm[1:n], :]
        Yp = Z[perm[(n+1):end], :]
        mp = mmd2_gaussian(Xp, Yp; σ = σ)
        mp >= obs && (count_ge += 1)
    end
    return obs, (count_ge + 1) / (n_perm + 1), σ
end

"""
    ssa_feature_matrix(builder, prog, params, comps, tgrid; N, n_graphs, nsims_per_graph,
                       tspan, seed_fraction, base_seed, infected = :I)

Run an SSA ensemble and return a feature matrix where each row is one
trajectory's concatenation `[c1(tgrid)... ; c2(tgrid)... ; ...]` for the
list of compartments `comps`, normalised by `N`.
"""
function ssa_feature_matrix(builder, prog, params, comps::AbstractVector{Symbol},
                            tgrid; N::Int, n_graphs::Int, nsims_per_graph::Int,
                            tspan, seed_fraction::Real,
                            base_seed::Int = 20240701,
                            infected::Symbol = :I)
    no_model = OutbreakModel(prog, params)
    rng = StableRNG(base_seed)
    nsamp = n_graphs * nsims_per_graph
    nfeat = length(comps) * length(tgrid)
    F = Matrix{Float64}(undef, nsamp, nfeat)
    row = 1
    for gi in 1:n_graphs
        g = builder(rng)
        spec = OutbreakSpec(model = no_model, network = g,
                            initial = SeedFraction(infected => seed_fraction),
                            tspan = tspan)
        ens = simulate_ensemble(spec; nsims = nsims_per_graph,
                                seed = base_seed + 1000 * gi,
                                parallel = true)
        for traj in ens.trajectories
            col = 1
            for c in comps
                cidx = no_model.index_of[c]
                for tn in tgrid
                    st = state_at(traj, tn)
                    F[row, col] = Float64(st[cidx]) / N
                    col += 1
                end
            end
            row += 1
        end
    end
    return F
end

"""
    ebm_feature_row(sol, model, comps, tgrid)

Pack the deterministic EBM compartment trajectories (looked up by
`compartment(sol, model, c)`) at `tgrid` into a single-row feature matrix,
matching the layout of `ssa_feature_matrix`.
"""
function ebm_feature_row(sol, model, comps::AbstractVector{Symbol}, tgrid)
    nfeat = length(comps) * length(tgrid)
    row = Vector{Float64}(undef, nfeat)
    col = 1
    for c in comps
        # `compartment(sol, model, c)` returns one value per saved sol.t; we
        # need values at tgrid via interpolation through the ODESolution.
        for tn in tgrid
            row[col] = _ebm_compartment_at(sol, model, c, tn)
            col += 1
        end
    end
    return reshape(row, 1, nfeat)
end

# Small helper: evaluate an EBM compartment observable at arbitrary time t
# by exploiting that the underlying ODESolution is callable.
function _ebm_compartment_at(sol, model, comp::Symbol, t)
    # Fall back to nearest-saved-time linear interpolation on the saved grid
    ts = sol.t
    vals = compartment(sol, model, comp)
    t <= ts[1]  && return vals[1]
    t >= ts[end] && return vals[end]
    j = searchsortedfirst(ts, t)
    t0, t1 = ts[j-1], ts[j]
    v0, v1 = vals[j-1], vals[j]
    α = (t - t0) / (t1 - t0)
    return (1 - α) * v0 + α * v1
end
