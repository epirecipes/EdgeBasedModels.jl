# Golden cases: scalar outputs of the LEGACY analysis functions (analysis.jl, R₀ in builders.jl, pgf.jl).
# Owner after Phase 0: WP19 (DESIGN_NetworkEpiCore.md, section G.2). Canonical anchors (section E.2):
# τ = 1/6, γ = 1/4, σ = 1/5 on Poisson(5) and bimodal {2: 5/6, 10: 1/6} (excess degree 5, R₀ = 2).
# Rates are numeric (verified issue E10).
#
# Replaced by WP19 (the owner) in the bug-fix change for E14, E15, E16, E17, E18 and E31(i), with the
# literature and simulation tests of test/suites/analysis.jl (Ball 2021, the verifiers' references,
# NetworkOutbreaks ensembles). The R₀ values come from src/builders.jl, where WP29 fixed E14 and E17
# (multistage_analysis regenerated: R0_bypass = 1.0, R0_sirs removed; see `notes`).
# Progressions are built explicitly, not with sir_model()/seir_model()/sirs_model()/sis_model(): those
# factories move to NetworkEpiCore in 0.2 and return a ContactModel, and these goldens must not depend on
# the 0.2 shims. The constructions below are field-for-field those of the 0.1 factories (src/disease.jl).

using EdgeBasedModels

const τ = 1 / 6
const γ = 1 / 4
const σ = 1 / 5
const P_BIMODAL = [k == 2 ? 5 / 6 : k == 10 ? 1 / 6 : 0.0 for k in 0:10]

const SIR_NOTES = "Fixed by WP19: final_size solves θ = 1 - T + T(1-ρ)ψ'(θ)/ψ'(1) by Brent's method with an exact " *
                  "threshold test (E18), ρ → 0 by default and ρ = 0.01 in final_size_R_infinity_rho001 (E31(i), EoN " *
                  "Attack_rate_cts_time 0.8002040 on Poisson(5)); epidemic_probability is the infector-side mixed-" *
                  "binomial formula (E15: 0.6094 on Poisson(5), not R∞); confidence_bands is Ball (2021) Theorem 2.2, " *
                  "NSW (confidence_bands_*) and MR (confidence_bands_variance_MR) (E16). Still legacy, E21: " *
                  "disease_free_equilibrium keys are S, θ, the stage names and φ_<stage>: φ_S (= 1) is missing and " *
                  "the stage keys are not the builders' pop_<stage> keys (E for SEIR resolves to nothing), so " *
                  "[structure].dfe_keys pins the legacy key set; disease_free_equilibrium(sys) of a lowered system " *
                  "is keyed by the system's variables."

function sir_scalars(pgf, prog; N = 10_000)
    model = StaticConfigurationModel(pgf, prog)
    fs = final_size(model)
    cb = confidence_bands(model, N)
    s = Dict{String, Any}(
        "R0" => basic_reproduction_number(model),
        "final_size_R_infinity" => fs.R_infinity,
        "final_size_theta_infinity" => fs.θ_infinity,
        "final_size_R_infinity_rho001" => final_size(model; seed_fraction = 0.01).R_infinity,
        "confidence_bands_variance_MR" => confidence_bands(model, N; graph = :MR).variance,
        "epidemic_probability" => epidemic_probability(model),
        "confidence_bands_lower" => cb.lower,
        "confidence_bands_mean" => cb.mean,
        "confidence_bands_upper" => cb.upper,
        "confidence_bands_variance" => cb.variance,
        "confidence_bands_std_error" => cb.std_error,
        "epidemic_threshold" => epidemic_threshold(model),
    )
    dfe = disease_free_equilibrium(model)
    for (k, v) in dfe
        s["dfe_$(k)"] = v
    end
    return s, Dict{String, Any}("dfe_keys" => sort!(string.(collect(keys(dfe)))))
end

sir(β, g) = DiseaseProgression([DiseaseStage(:I; transmission_rate = β), DiseaseStage(:R; transmission_rate = 0)],
                               [DiseaseTransition(:I, :R, g)]; entry = :I)
seir(σ, β, g) = DiseaseProgression([DiseaseStage(:E; transmission_rate = 0), DiseaseStage(:I; transmission_rate = β),
                                    DiseaseStage(:R; transmission_rate = 0)],
                                   [DiseaseTransition(:E, :I, σ), DiseaseTransition(:I, :R, g)]; entry = :E)

[
    GoldenCase("analysis", "sir_pois5_analysis"; kind = :scalars,
        description = "R₀, final_size, epidemic_probability, confidence_bands(N = 10⁴), epidemic_threshold and " *
                      "disease_free_equilibrium for SIR (τ = 1/6, γ = 1/4) on poisson_pgf(5.0)",
        issues = ["E15", "E16", "E18", "E21", "E31"], notes = SIR_NOTES,
        run = function ()
            s, st = sir_scalars(poisson_pgf(5.0), sir(τ, γ))
            return scalar_result(Dict("network" => "poisson_pgf(5.0)", "tau" => τ, "gamma" => γ, "N" => 10_000), s;
                                 structure = st)
        end),
    GoldenCase("analysis", "sir_bim_analysis"; kind = :scalars,
        description = "as sir_pois5_analysis on the bimodal network {2: 5/6, 10: 1/6}",
        issues = ["E15", "E16", "E18", "E21", "E31"], notes = SIR_NOTES,
        run = function ()
            s, st = sir_scalars(polynomial_pgf(P_BIMODAL), sir(τ, γ))
            return scalar_result(Dict("network" => "polynomial_pgf(bimodal {2: 5/6, 10: 1/6})", "tau" => τ,
                                      "gamma" => γ, "N" => 10_000), s; structure = st)
        end),
    GoldenCase("analysis", "seir_pois5_analysis"; kind = :scalars,
        description = "as sir_pois5_analysis for SEIR (σ = 1/5, τ = 1/6, γ = 1/4) on poisson_pgf(5.0)",
        issues = ["E15", "E16", "E18", "E21", "E31"], notes = SIR_NOTES,
        run = function ()
            s, st = sir_scalars(poisson_pgf(5.0), seir(σ, τ, γ))
            return scalar_result(Dict("network" => "poisson_pgf(5.0)", "tau" => τ, "gamma" => γ, "sigma" => σ,
                                      "N" => 10_000), s; structure = st)
        end),
    GoldenCase("analysis", "multistage_analysis"; kind = :scalars,
        description = "R₀ and final sizes for multistage, branching, re-susceptibilising and sub-threshold " *
                      "progressions on poisson_pgf(5.0)",
        issues = ["E14", "E17"],
        notes = "Correct: the Erlang(3, 3γ) value 5(1 - (3γ/(3γ+τ))³) and the linear two-stage chain. Fixed by WP19 " *
                "(src/analysis.jl): with an E → R bypass (probability 1/2) the absorbing-chain transmissibility is " *
                "T = τ/(2(τ+γ)) = 0.2, so R₀ = 1: final_size_bypass and epidemic_probability_bypass are 0 (the " *
                "legacy final size was the SIR value 0.7968) and epidemic_threshold_bypass = γ/(κ/2 - 1) = 1/6 = τ " *
                "(E14, E15); epidemic_threshold refuses SIS " *
                "(E17: the SIS threshold is γ/κ on the pairwise model, not γ/(κ-1); the old entry " *
                "epidemic_threshold_sis = 0.0625 is removed). Fixed by WP29 (src/builders.jl): the legacy R₀ uses the " *
                "same absorbing-chain transmissibility, so R0_bypass = 5·0.2 = 1.0 (the 0.1 single-stage shortcut gave " *
                "2.0, E14; test/suites/analysis.jl checks bypassp(0.5) = 1.25 against the lifted system), and it " *
                "refuses SIRS (E17), so the entry R0_sirs (the unguarded SIR formula, 2.0) is removed.",
        run = function ()
            pgf = poisson_pgf(5.0)
            erl = expand_erlang_stages([ErlangStage(:I, 3, γ; transmission_rate = τ), DiseaseStage(:R)],
                                       [DiseaseTransition(:I, :R, 3γ)]; entry = :I)
            twostage = DiseaseProgression(
                [DiseaseStage(:E; transmission_rate = 0), DiseaseStage(:I1; transmission_rate = τ),
                 DiseaseStage(:I2; transmission_rate = τ / 2), DiseaseStage(:R; transmission_rate = 0)],
                [DiseaseTransition(:E, :I1, σ), DiseaseTransition(:I1, :I2, 2γ), DiseaseTransition(:I2, :R, 2γ)];
                entry = :E)
            bypass = DiseaseProgression(
                [DiseaseStage(:E; transmission_rate = 0), DiseaseStage(:I; transmission_rate = τ),
                 DiseaseStage(:R; transmission_rate = 0)],
                [DiseaseTransition(:E, :I, σ / 2), DiseaseTransition(:E, :R, σ / 2), DiseaseTransition(:I, :R, γ)];
                entry = :E)
            sub = StaticConfigurationModel(pgf, sir(0.01, 1.0))
            fs_sub = final_size(sub)
            m(p) = StaticConfigurationModel(pgf, p)
            s = Dict{String, Any}(
                "R0_erlang3" => basic_reproduction_number(m(erl)),
                "final_size_erlang3" => final_size(m(erl)).R_infinity,
                "R0_twostage" => basic_reproduction_number(m(twostage)),
                "final_size_twostage" => final_size(m(twostage)).R_infinity,
                "R0_bypass" => basic_reproduction_number(m(bypass)),
                "final_size_bypass" => final_size(m(bypass)).R_infinity,
                "epidemic_threshold_bypass" => epidemic_threshold(m(bypass)),
                "epidemic_probability_bypass" => epidemic_probability(m(bypass)),
                "subthreshold_R_infinity" => fs_sub.R_infinity,
                "subthreshold_theta_infinity" => fs_sub.θ_infinity,
                "subthreshold_epidemic_probability" => epidemic_probability(sub),
            )
            return scalar_result(Dict("network" => "poisson_pgf(5.0)", "tau" => τ, "gamma" => γ, "sigma" => σ,
                                      "subthreshold_tau" => 0.01, "subthreshold_gamma" => 1.0), s)
        end),
    GoldenCase("analysis", "correlated_analysis"; kind = :scalars,
        description = "correlated_R0 for neutral and assortative CorrelatedPGFs",
        issues = ["E20"],
        notes = "E20: assortative_correlated_pgf adds r·δ_kk to rows with p_k = 0, so zero-padding above kmax " *
                "creates a spurious eigenvalue r(k-1) (padded 2-regular with r = 0.8 below).",
        run = function ()
            pk = [0.0, 0.2, 0.5, 0.3]
            κ = 4.0
            pois = [exp(-κ) * κ^k / factorial(k) for k in 0:20]
            pois ./= sum(pois)
            s = Dict{String, Any}(
                "R0_neutral_T04" => correlated_R0(neutral_correlated_pgf(pk), 0.4),
                "R0_assortative_r05_T04" => correlated_R0(assortative_correlated_pgf(pk, 0.5), 0.4),
                "R0_assortative_r1_T04" => correlated_R0(assortative_correlated_pgf(pk, 1.0), 0.4),
                "R0_padded_reg2_r08_T1" => correlated_R0(assortative_correlated_pgf([0.0, 0.0, 1.0, 0.0, 0.0, 0.0], 0.8), 1.0),
                "R0_poisson4_truncated_neutral_T03" => correlated_R0(neutral_correlated_pgf(pois), 0.3),
            )
            return scalar_result(Dict("pk" => pk, "poisson_mean" => κ, "poisson_kmax" => 20), s)
        end),
]
