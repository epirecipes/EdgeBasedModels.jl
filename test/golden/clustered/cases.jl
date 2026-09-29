# Golden cases: the clustered edge-based model of Volz et al. (2011) with triangle pair states
# (src/lift/clustered.jl) and the clustered analysis quantities.
# Owner: WP20 (DESIGN_NetworkEpiCore.md, section G.2). WP20 deliberately replaced the goldens of the
# legacy clustered EBCM, which treated the two partners of a triangle as independent edges
# (S = g(θ₂, θ₃²); verified issue E02), in the bug-fix change that validates the new numbers in
# test/suites/clustered.jl: against Volz et al.'s own equations and final-size relation (eq. 27),
# the E02/E04 verifiers' exact simulations, and NetworkOutbreaks ensembles on Newman–Miller graphs.

using EdgeBasedModels
using NetworkEpiCore

const ρ = 0.01

const VOLZ_NOTE = "Volz et al. (2011) clustered EBCM with triangle pair states (WP20; replaces the legacy " *
                  "independent-edge EBCM of verified issue E02, whose seed parameter ρ (E26) is now seed_<X>). " *
                  "w1 reference for (κs, κt) = (1, 2), τ = 0.6, γ = 1, ρ = 1e-3: SSA final size 0.7121 ± 0.0002, " *
                  "Volz 0.7125, this lift 0.712501 (test/suites/clustered.jl)."

[
    GoldenCase("clustered", "clustered_sir_pois12";
        description = "build_clustered_sir(clustered_poisson_pgf(1.0, 2.0), τ = 0.6, γ = 1.0), seed ρ = 0.01, t = 0:1:20 " *
                      "(the network and rates of scenario :sir_clust_pois12)",
        issues = String[], notes = VOLZ_NOTE,
        run = () -> edge_system_trajectory(build_clustered_sir(clustered_poisson_pgf(1.0, 2.0), 0.6, 1.0);
            T = 20, seed_fraction = ρ,
            setup = Dict("builder" => "build_clustered_sir", "network" => "clustered_poisson_pgf(1.0, 2.0)",
                         "tau" => 0.6, "gamma" => 1.0))),
    GoldenCase("clustered", "clustered_seir_pois12";
        description = "build_clustered_seir(clustered_poisson_pgf(1.0, 2.0), σ = 1.0, τ = 0.6, γ = 1.0), seed ρ = 0.01 " *
                      "in E, t = 0:1:30",
        issues = String[], notes = VOLZ_NOTE,
        run = () -> edge_system_trajectory(build_clustered_seir(clustered_poisson_pgf(1.0, 2.0), 1.0, 0.6, 1.0);
            T = 30, seed_fraction = ρ,
            setup = Dict("builder" => "build_clustered_seir", "network" => "clustered_poisson_pgf(1.0, 2.0)",
                         "tau" => 0.6, "gamma" => 1.0, "sigma" => 1.0))),
    GoldenCase("clustered", "clustered_sir_joint";
        description = "build_clustered_sir(clustered_pgf([0.1 0.2; 0.3 0.4]), τ = 0.5, γ = 0.1), seed ρ = 0.01, t = 0:1:100",
        issues = String[],
        notes = join_notes(VOLZ_NOTE, "A subcritical tree of triangles (SSA final size 0.0075 at ρ = 1e-3; the legacy " *
                                      "EBCM predicted 0.63). E27: every divisor of the field is a constant."),
        run = () -> edge_system_trajectory(build_clustered_sir(clustered_pgf([0.1 0.2; 0.3 0.4]), 0.5, 0.1);
            T = 100, seed_fraction = ρ,
            setup = Dict("builder" => "build_clustered_sir", "network" => "clustered_pgf([0.1 0.2; 0.3 0.4])",
                         "tau" => 0.5, "gamma" => 0.1))),
    GoldenCase("clustered", "clustered_sir_s2t2";
        description = "edge_based(sir_model(τ = 1/6, γ = 1/4), ClusteredNetwork(RegularDegree(2), RegularDegree(2))), " *
                      "seed ρ = 0.01, t = 0:1:60 (the network and rates of scenario :sir_clust_s2t2)",
        issues = String[],
        notes = join_notes(VOLZ_NOTE, "Against NetworkOutbreaks on :sir_clust_s2t2 (N = 10⁴, 200 runs): D∞ < 0.005."),
        run = () -> edge_system_trajectory(edge_based(sir_model(; τ = 1 / 6, γ = 1 / 4),
                                                      ClusteredNetwork(RegularDegree(2), RegularDegree(2)));
            T = 60, seed_fraction = ρ,
            setup = Dict("builder" => "edge_based", "network" => "ClusteredNetwork(RegularDegree(2), RegularDegree(2))",
                         "tau" => 1 / 6, "gamma" => 0.25))),
    GoldenCase("clustered", "clustered_scalars"; kind = :scalars,
        description = "mean single/triangle degrees, the clustering coefficient (transitivity), the triangle-edge " *
                      "fraction and the tree-of-triangles R₀ (generation and clump) of clustered networks",
        issues = String[],
        notes = "E03: the clustering coefficient is the transitivity 2⟨t⟩/⟨k(k−1)⟩ (NetworkEpiCore, 2/27 for (3, 1), " *
                "3/7 for the joint law); the fraction of edges in triangles is triangle_edge_fraction. E04: R₀ is the " *
                "Perron root of the 3-type generation matrix of the tree of triangles (kind = :generation) or the " *
                "clump reproduction number R_* (kind = :clump); both are 1 at the Volz threshold. The legacy golden " *
                "pinned the legacy clustering_coefficient(::ClusteredPGF) and the heuristic legacy R₀, which are wrong.",
        run = function ()
            s = Dict{String, Any}()
            R0(pgf, τ, γ; kind) = EdgeBasedModels._clustered_reproduction_number(sir_model(; τ, γ),
                                                                                 ClusteredNetwork(pgf); kind)
            for (label, pgf) in (("pois_3_1", clustered_poisson_pgf(3.0, 1.0)),
                                 ("pois_45_025", clustered_poisson_pgf(4.5, 0.25)),
                                 ("pois_1_2", clustered_poisson_pgf(1.0, 2.0)),
                                 ("pois_5_0", clustered_poisson_pgf(5.0, 0.0)),
                                 ("joint", clustered_pgf([0.1 0.2; 0.3 0.4])))
                net = ClusteredNetwork(pgf)
                s["$(label)_mean_single_degree"] = mean_single_degree(pgf)
                s["$(label)_mean_triangle_degree"] = mean_triangle_degree(pgf)
                s["$(label)_clustering_coefficient"] = clustering_coefficient(net)
                s["$(label)_triangle_edge_fraction"] = triangle_edge_fraction(net)
            end
            for kind in (:generation, :clump)
                s["R0_$(kind)_pois_3_1_tau01_gamma005"] = R0(clustered_poisson_pgf(3.0, 1.0), 0.1, 0.05; kind)
                s["R0_$(kind)_pois_45_025_tau01_gamma005"] = R0(clustered_poisson_pgf(4.5, 0.25), 0.1, 0.05; kind)
                s["R0_$(kind)_pois_5_0_tau01_gamma005"] = R0(clustered_poisson_pgf(5.0, 0.0), 0.1, 0.05; kind)
                s["R0_$(kind)_pois_1_2_tau06_gamma1"] = R0(clustered_poisson_pgf(1.0, 2.0), 0.6, 1.0; kind)
                s["R0_$(kind)_joint_tau05_gamma01"] = R0(clustered_pgf([0.1 0.2; 0.3 0.4]), 0.5, 0.1; kind)
            end
            return scalar_result(Dict("R0_rates" => "tau/gamma as in each key", "networks" =>
                ["clustered_poisson_pgf(3,1)", "clustered_poisson_pgf(4.5,0.25)", "clustered_poisson_pgf(1,2)",
                 "clustered_poisson_pgf(5,0)", "clustered_pgf([0.1 0.2; 0.3 0.4])"]), s)
        end),
]
