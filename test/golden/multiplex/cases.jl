# Golden cases: the multiplex edge-based lift (WP22, DESIGN_NetworkEpiCore.md §G.2) and multiplex R₀.
# Owner: WP22.
#
# WP22 replaced the Phase-0 goldens of the 0.1 builder deliberately (design §G.1), in the bug-fix
# change for verified issues E12 and E13:
# - E13: 0.1's build_multiplex_sir returned a (system, u0, tspan, p) tuple seeded with
#   θᵢ(0) = 1 − 1e-6 and no seed fraction (an unphysical initial condition, with φ_I < 0 possible).
#   It now returns an EdgeModelSystem of the per-reaction assembler, seeded with θ_ℓ(0) = 1 and
#   S(0) = 1 − ρ (Jacobsen, Burch, Tien & Rempała 2018, eq. (13));
# - E12: multiplex_R0 returned the sum of the layer R₀s; it is now the spectral radius ρ(K).
# The literature and simulation tests of the replacement are in test/suites/multiplex.jl: Miller &
# Volz (2013) eq. (13), Jacobsen et al. eq. (13) with the E13 verifier's reference values, the
# 6-regular equivalence of two 3-regular layers, NetworkEpiCore's (layer, entry) NGM and final size,
# and NetworkOutbreaks on :sir_mpx (N = 10⁴, 200 runs).

using EdgeBasedModels
using ModelingToolkit
using Symbolics

const γ = 1 / 4

const NOTE = "Replaced by WP22 (E12/E13 fix): the per-reaction multiplex lift, seeded with θ_ℓ(0) = 1 and " *
             "S(0) = 1 − ρ; validated in test/suites/multiplex.jl (Miller & Volz 2013 eq. (13), Jacobsen et al. " *
             "2018 eq. (13), NetworkOutbreaks on :sir_mpx)."

function multiplex_case(name, description, build, T; seed_fraction = 0.01, setup = Dict{String, Any}(),
                        op_extra = sys -> Dict())
    return GoldenCase("multiplex", name; description = description, notes = NOTE,
        run = function ()
            sys = build()
            return edge_system_trajectory(sys; T = T, seed_fraction = seed_fraction, op_extra = op_extra(sys),
                                          setup = merge(Dict{String, Any}("builder" => "build_multiplex_sir"), setup))
        end)
end

reg3() = polynomial_pgf([0, 0, 0, 1.0])

# The parameters of a lifted scenario model, set to the scenario's values.
function scenario_parameters(sys, params)
    out = Dict{Any, Float64}()
    for p in ModelingToolkit.parameters(sys.system)
        n = Symbol(Symbolics.getname(p))
        haskey(params, n) && (out[p] = params[n])
    end
    return out
end

[
    multiplex_case("multiplex_sir_reg3_pois5",
        "build_multiplex_sir([(:home, 3-regular, 0.15, 1/4), (:comm, poisson_pgf(5.0), 0.05, 1/4)]) (expanded), " *
        "1% seeded in I, t = 0:1:80",
        () -> build_multiplex_sir([(:home, reg3(), 0.15, γ), (:comm, poisson_pgf(5.0), 0.05, γ)]), 80;
        setup = Dict("networks" => ["polynomial_pgf(3-regular)", "poisson_pgf(5.0)"], "layers" => ["home", "comm"],
                     "tau" => [0.15, 0.05], "gamma" => γ, "form" => "expanded")),
    multiplex_case("multiplex_sir_reg3x2",
        "build_multiplex_sir with two identical 3-regular layers, τ = 1/6, γ = 1/4 (expanded), 1% seeded in I, " *
        "t = 0:1:80 (equal to the 6-regular single-layer lift, tested in test/suites/multiplex.jl)",
        () -> build_multiplex_sir([(:l1, reg3(), 1 / 6, γ), (:l2, reg3(), 1 / 6, γ)]), 80;
        setup = Dict("networks" => ["polynomial_pgf(3-regular)", "polynomial_pgf(3-regular)"], "layers" => ["l1", "l2"],
                     "tau" => [1 / 6, 1 / 6], "gamma" => γ, "form" => "expanded")),
    multiplex_case("multiplex_sir_pois3_pois2",
        "build_multiplex_sir([(:home, poisson_pgf(3.0), 0.3, 0.1), (:work, poisson_pgf(2.0), 0.2, 0.1)]; " *
        "form = :compact) (the 0.1 shape: θ per layer and R), 1% seeded in I, t = 0:1:100",
        () -> build_multiplex_sir([(:home, poisson_pgf(3.0), 0.3, 0.1), (:work, poisson_pgf(2.0), 0.2, 0.1)];
                                  form = :compact), 100;
        setup = Dict("networks" => ["poisson_pgf(3.0)", "poisson_pgf(2.0)"], "layers" => ["home", "work"],
                     "tau" => [0.3, 0.2], "gamma" => 0.1, "form" => "compact")),
    multiplex_case("multiplex_sir_mpx",
        "edge_based(scenario(:sir_mpx)): household 3-regular (τ = 3c) and community Poisson(5) (τ = c), c " *
        "calibrated to R₀ = ρ(K) = 2, γ = 1/4, 1% seeded in I, t = 0:1:80",
        () -> edge_based(scenario(:sir_mpx); name = :sir_mpx), 80;
        op_extra = sys -> scenario_parameters(sys, scenario(:sir_mpx).params),
        setup = Dict("builder" => "edge_based(scenario(:sir_mpx))", "c" => scenario(:sir_mpx).params[:c],
                     "gamma" => γ, "form" => "expanded")),
    GoldenCase("multiplex", "multiplex_scalars"; kind = :scalars,
        description = "multiplex_R0 (and basic_reproduction_number(layers)) and susceptible_fraction",
        notes = "Replaced by WP22 (E12 fix): multiplex_R0 is the spectral radius ρ(K) of the layer " *
                "next-generation matrix (0.1 returned the sum of the layer R₀s, e.g. 1.5833 for reg3+pois5 " *
                "instead of 1.7608); Poisson and single-layer values are unchanged. Validated in " *
                "test/suites/multiplex.jl against NetworkEpiCore's NGM and the lifted ODE's linearisation.",
        run = function ()
            l1 = [(:home, reg3(), 0.15, γ), (:comm, poisson_pgf(5.0), 0.05, γ)]
            l2 = [(:home, poisson_pgf(3.0), 0.3, 0.1), (:work, poisson_pgf(2.0), 0.2, 0.1)]
            l3 = [(:only, polynomial_pgf([0.0, 0.2, 0.5, 0.3]), 0.4, 0.1)]
            β22 = 0.22 / 0.78
            l4 = [(:a, reg3(), β22, 1.0), (:b, reg3(), β22, 1.0)]
            bim = polynomial_pgf([0, 0.5, 0, 0, 0, 0, 0, 0.5])
            l5 = [(:a, bim, 0.1 / 0.9, 1.0), (:b, bim, 0.1 / 0.9, 1.0)]
            s = Dict{String, Any}(
                "R0_reg3_pois5" => multiplex_R0(l1),
                "R0_pois3_pois2" => multiplex_R0(l2),
                "R0_single_poly" => multiplex_R0(l3),
                "R0_reg3x2_T022" => multiplex_R0(l4),
                "R0_bim2_T010" => multiplex_R0(l5),
                "brn_pois3_pois2" => basic_reproduction_number(l2),
                "S_pois3_pois2_at_08_09" => susceptible_fraction([poisson_pgf(3.0), poisson_pgf(2.0)], [0.8, 0.9]),
                "S_pois3_pois2_at_08_09_seed001" =>
                    susceptible_fraction([poisson_pgf(3.0), poisson_pgf(2.0)], [0.8, 0.9]; ρ = 0.01),
            )
            return scalar_result(Dict("layer_sets" => ["reg3(0.15)+pois5(0.05), γ = 1/4",
                                                       "pois3(0.3)+pois2(0.2), γ = 0.1",
                                                       "poly[0,0.2,0.5,0.3](0.4), γ = 0.1",
                                                       "reg3+reg3 at T = 0.22, γ = 1",
                                                       "bimodal{1,7} x2 at T = 0.10, γ = 1"]), s)
        end),
]
