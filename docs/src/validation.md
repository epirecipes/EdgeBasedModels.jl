# Morphisms and validation

## Morphisms: "back to mass action", and to pairwise

Each exact map between representations is returned as a runtime `Semiconjugacy` π, which
NetworkEpiCore's `verify` checks (the residual Jπ·F − G∘π, symbolic first, then numeric
probes). Every map carries an **exactness label**. Only `:exact` maps are morphisms. Limits
and calibrations are labelled as such, and `verify` rejects them. The results below are for
the `sys` of the example on the Home page (SIR on Poisson(5)) and for `edge_based(model, WellMixed(5))`.

| call | statement (design §D.5) | kind | exactness | `verify(img.morphism)` |
|---|---|---|---|---|
| `mass_action(edge_based(model, WellMixed(κ)); form = :exact)` | M1 well-mixed unit: MA with rate κτ, S = q e^{κ(θ−1)} | conjugacy | `:exact` | ok, residual 0 (symbolic) |
| `mass_action(sys; form = :exact)` on Poisson(μ) | M2 Poisson isomorphism: MA(D_μ P) on edge copies Φ_X and node copies X | conjugacy | `:exact` | ok, residual 0 (symbolic) |
| `mass_action(sys; form = :edge)` on Poisson(μ) | M3 Rempała quotient: MA(β = μτ, γ + τ) on the model's own species. **Its "I" is the edge variable φ_I, not prevalence** | semiconjugacy | `:exact` | ok, residual 0 (symbolic) |
| `mass_action(sys; form = :exact)` on a Poisson-type ψ (ψ' = αψ^κ) | M4 power-law kinetics | conjugacy | `:exact` | ok, residual ≤ 1e-10 (tested on `:sir_nb4`, `:sir_reg6`) |
| `mass_action(sys; form = :general)` | M5 general kinetics in an auxiliary Θ, for any ψ (an encoding) | conjugacy | `:exact` | ok, residual 0 (symbolic) |
| `pairwise_image(sys)` | M6 EB → S-anchored pairwise with closure K_ψ = ψψ''/ψ'², for every C² ψ | semiconjugacy | `:exact` | ok, residual 0 |
| `mass_action(sys; form = :limit)` | Λ1 dense limit MA(⟨k⟩τ): error O(1/μ) | – | `:limit` | **fails** (residual 0.63) |
| `mass_action(sys; form = :calibrated)` | MA with R₀ matched | – | `:calibration` | **fails** (residual 0.78) |

`pushforward(img.morphism, sol, tgrid)` maps an edge-based solution into the target's
coordinates. `as_reaction_system(sys; form)` returns the target reaction network, and
`Catalyst.ReactionSystem` converts it. The old `to_mass_action` kept γ where the quotient needs
γ + τ. `verify` rejects its map with the residual −τφ_I in dI/dt (`test/suites/reverse.jl`), so
it is now an error. NodeBasedModels checks
that its `PGFClosure` S-anchored system has the vector field of `pairwise_image(sys)`. For
Poisson-type degree distributions K_ψ is the constant ⟨k(k−1)⟩/⟨k⟩², so the usual constant
closure is exact **only** for them.

## Validation

Every exact-limit claim is tested against simulation. The references are the committed
NetworkOutbreaks ensembles of the shared NEC scenarios (`NetworkOutbreaks.jl/data/scenarios`,
53 summaries). Each ensemble has N = 10⁴ nodes, 200 runs, a fresh graph per run and seeds
placed uniformly. Runs are conditioned on a major outbreak, and each summary is hash-keyed on
the scenario and `ALGORITHM_REVISION`. The pages and tests load them in strict-cache mode: a
missing or stale summary is an error, never a silent re-simulation.

```julia
using NetworkOutbreaks                           # for scenario_summary
sc  = scenario(:sir_pois5)
ref = scenario_summary(sc)                       # committed ensemble
sys = edge_based(sc); sol = solve_epidemic(sys, sc)
compare(ref, model_curves(sys, sol; t = sc.tgrid, label = "edge-based"))   # D∞, z∞, ΔR∞ (95% CI), …
```

The table shows a selection of the numbers this code prints. D∞ = max_t |I_EB(t) − Ī(t)| is
taken over the prevalence of infectious nodes, and ΔR∞ = R_EB − mean final size. The
acceptance rule is D∞ < 0.005 and |ΔR∞| < 0.005 at N = 10⁴.

| scenario | network | N | runs | EB R∞ | D∞(I) | ΔR∞ (95% CI) |
|---|---|---:|---:|---:|---:|---|
| `:sir_reg6` | 6-regular | 10⁴ | 200 | 0.9295 | 0.00171 | +0.00026 (−0.00027, 0.00079) |
| `:sir_pois5` | Poisson(5) | 10⁴ | 200 | 0.8002 | 0.00223 | +0.00011 (−0.00086, 0.00108) |
| `:sir_nb4` | negative binomial | 10⁴ | 200 | 0.6408 | 0.00115 | +0.00034 (−0.00098, 0.00165) |
| `:sir_bim` | bimodal | 10⁴ | 200 | 0.4956 | 0.00232 | −0.00035 (−0.00204, 0.00134) |
| `:sir_pl` | power law | 10⁴ | 200 | 0.2898 | 0.00265 | +0.00173 (−0.00054, 0.00400) |
| `:seir_pois5` | Poisson(5) | 10⁴ | 200 | 0.8002 | 0.00033 | +0.00003 (−0.00095, 0.00102) |
| `:sir_vax_pois5` | Poisson(5), vaccination | 10⁴ | 200 | 0.5581 | 0.00191 | +0.00213 (−0.00018, 0.00443) |
| `:sir_clust_s2t2` | clustered | 10⁴ | 200 | 0.9229 | 0.00135 | +0.00030 (−0.00039, 0.00099) |
| `:sir_sbm2` | two-block SBM | 10⁴ | 200 | 0.7749 | 0.00172 | +0.00111 (−0.00009, 0.00231) |
| `:sir_mpx` | multiplex | 10⁴ | 200 | 0.8781 | 0.00080 | −0.00020 (−0.00104, 0.00064) |
| `:sir_ne_reg6_eta1` | neighbour exchange, η = 1 | 5000 | 100 | 0.7469 | 0.00193 | −0.00024 (−0.00302, 0.00254) |
| `:sir_dc_bim_r05` | degree-correlated, r = 0.5 | 10⁴ | 200 | 0.3869 | 0.00268 | +0.00005 (−0.00087, 0.00098) |
| `:sir_dormant_dvd` | dormant contacts | 10⁴ | 200 | 0.6440 | 0.00128 | +0.00048 (−0.00070, 0.00166) |
| `:sir_mfsh_msv` | MFSH | 10⁴ | 200 | 0.7846 | 0.00145 | −0.00001 (−0.00085, 0.00082) |

Vignette E14 runs all 48 exact-limit scenarios, and 44 pass. The four that fail are the
N = 10³ variants of `:sir_pois5`, `:sir_bim`, `:sir_pl` and `:sir_clust_s2t2`. At that size the
finite-N error is larger than the threshold, which is exactly what the N-scaling protocol
measures.

**N-scaling.** A single N cannot tell an exact large-N limit from a small structural bias. So
four scenarios are also simulated at N = 10³ (2000 runs) and N = 10⁵ (20 runs). For an exact
limit, D∞ falls with N until it reaches the Monte Carlo floor. For a biased approximation it
levels off at a positive value. On `:sir_pl` the constant-closure pairwise model levels off at
ΔR∞ ≈ +0.07 (see the NodeBasedModels documentation).

| scenario | N = 10³: D∞ / ΔR∞ | N = 10⁴: D∞ / ΔR∞ | N = 10⁵: D∞ / ΔR∞ |
|---|---|---|---|
| `:sir_pois5` | 0.01361 / +0.00070 | 0.00223 / +0.00011 | 0.00093 / +0.00018 |
| `:sir_pl` | 0.01180 / +0.01480 | 0.00265 / +0.00173 | 0.00140 / −0.00027 |

**Cross-check with EoN.** The reference values come from EoN 1.2rc1 on the same exact Poisson(5)
network, with τ = 1/6, γ = 1/4 and ρ = 0.01
(`test/golden/eon/eon_like_for_like.toml` in the repository, generated by `test/golden/eon/generate_eon.py`). The
EdgeBasedModels values use `saveat = 0.2`, `reltol = 1e-10` and `abstol = 1e-12`.

| quantity | EdgeBasedModels 0.2 | EoN 1.2rc1 |
|---|---:|---:|
| peak prevalence I (t = 11.4) | 0.2323412 | 0.2323412 (`EBCM_uniform_introduction`) |
| R(40) | 0.7985035 | 0.7985035 |
| R∞, ρ → 0 | 0.7968121 | 0.7968121 (`Attack_rate_cts_time`) |
| R∞, ρ = 0.01 | 0.8002040 | 0.8002040 |

The 0.1 README compared against EoN on a single ER(1000) graph (0.2328, 0.7971). It also
reported R(40) as the "final size", and it showed an SIS reinfection-counting row. SIS is no
longer an edge-based model: its pairwise and reinfection-counting versions are in
NodeBasedModels. Note that P(major) ≠ R∞: with τ = 1/6 and γ = 1/4 on Poisson(5),
`epidemic_probability` gives the infector-side 0.6094, while R∞ = 0.7968.

