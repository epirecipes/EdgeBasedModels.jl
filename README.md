# EdgeBasedModels.jl

Edge-based compartmental models (EBCMs) for epidemics on networks: the Miller–Slim–Volz
equations, which are the exact large-population limit of an epidemic on a configuration-model
random graph, generated as ModelingToolkit systems.

Version 0.2 is built on [NetworkEpiCore.jl](../NetworkEpiCore.jl) (NEC), whose names it
re-exports. A model is a NEC `ContactModel`, a network is a NEC `NetworkDescriptor`, and the
verb is `edge_based(model, network)`. The same two objects go to
[NodeBasedModels.jl](../NodeBasedModels.jl) (`node_based`, pairwise and other node-level
closures) and to [NetworkOutbreaks.jl](../NetworkOutbreaks.jl) (`simulate`, exact stochastic
simulation). The three packages load together without name clashes. Changes from 0.1 are
listed in [MIGRATION.md](MIGRATION.md).

## Quick start: the low-level API

A model can come from Catalyst, from ModelingToolkit, from the direct constructor or from the
canned `sir_model()` and friends. Every route ends in the same `ContactModel`. Contacts
`S + J → X + J` have a **per-contact (per-edge) rate τ**; β is used only for mass-action rates.

```julia
using NetworkEpiCore, EdgeBasedModels, Catalyst

sir = @reaction_network sir begin
    @parameters τ γ
    τ, S + I --> 2I        # contact: per-contact rate τ; S converted, I unchanged
    γ, I --> R             # node-local transition
end
model = contact_model(sir)                       # prints the typing report
isequivalent(model, sir_model())                 # true

net = ConfigurationNetwork(PoissonDegree(5))
p   = Dict(:τ => 1/6, :γ => 1/4)
basic_reproduction_number(model, net, p)         # 2.0  (T = τ/(τ+γ) = 0.4, excess degree 5)

sys  = edge_based(model, net)                    # an EdgeModelSystem (ModelingToolkit inside)
init = SeedFraction(:I => 0.01)
sol  = solve_epidemic(sys; p, initial = init, tspan = (0.0, 40.0), saveat = 0.2)
compartment(sys, sol, :I)                        # prevalence; its peak is 0.23233 at t = 11.4
final_size(sys; p, initial = init)               # 0.80020 (with a 1% seed; 0.79681 as ρ → 0)
```

By default infections are seeded into the model's **unique entry state**: I for SIR, E for SEIR.
A model with several entry states, such as two strains, needs an explicit `initial`.

### Factories

The 0.1 factories keep their signatures. They are one-line wrappers around `edge_based`, and they
accept NEC degree distributions and Symbol rates:

```julia
sysF = build_sir(PoissonDegree(5), :τ, :γ)                       # also build_seir, build_clustered_sir, …
vector_fields_equal(symbolic_ode(sys), symbolic_ode(sysF))       # true: the same equations
```

`build_sis`, `build_sis_reinfection`, `to_mass_action`, `compare_models`, `compose` and
`verify_functoriality` raise errors that name their replacements. They returned wrong numbers or
checked nothing (see MIGRATION.md).

### What `edge_based` accepts

| network (NEC descriptor) | lift | shared scenarios |
|---|---|---|
| `ConfigurationNetwork(d)`, for any degree distribution `d` (`PoissonDegree`, `RegularDegree`, `NegBinDegree`, `EmpiricalDegree`, `PowerLawDegree`, `MixtureDegree`, …) | per-reaction EBCM, `form = :expanded` or `:compact` (SIR shape) | `:sir_pois5`, `:sir_reg6`, `:sir_nb4`, `:sir_bim`, `:sir_pl`, `:seir_pois5`, `:seair_pois5`, `:twostrain_pois5`, `:sir_vax_pois5`, Erlang stages |
| `WellMixed(κ)` | the well-mixed unit: mass action with rate κτ | `:sir_wm5` |
| `MultitypeNetwork` (`sbm_network`, `unstructured`); `edge_based(model, net, strata)` for heterogeneous susceptibility | multitype EBCM | `:sir_sbm2`, `:sir_unstr2`, `:sir_age2`, `:sir_hetsus_bim`, `:seirv_hetsus_pois5` |
| `ClusteredNetwork` | triangles (Volz 2011): SIR, and SEIR/SEAIR through the general clustered lift | `:sir_clust_s2t2`, `:sir_clust_pois12`, `:seir_clust_s2t2`, `:seair_clust_s2t2` |
| `DynamicNetwork(base, NeighbourExchange(η))`, `DynamicNetwork(base, DormantContacts(…))` | dynamic partnerships (MSV Part II) | `:sir_ne_*`, `:sir_dormant_*` |
| `MFSHNetwork(d)` | mean-field social heterogeneity | `:sir_mfsh_*` |
| `MultiplexNetwork(:home => …, :work => …)` | layered contacts | `:sir_mpx` |
| `degree_correlated(d; r)` | degree-correlated EBCM (Miller & Volz 2013) | `:sir_dc_bim_*` |

The lift is **strictly partial**. A reaction that produces a susceptible class (SIS, SIRS) breaks
the edge-independence assumption, so the model is refused. The error names the back ends that
accept it:

```julia
edge_based(sis_model(), net)
# AdmissibilityError: … `γ, I --> S` (type resus: node → sus) produces the susceptible species S. …
#   Back ends that accept this model: node_based (pairwise, individual, pair, motif,
#   neighbourhood), simulate, mass_action
```

Exits from the susceptible class, such as vaccination `S → V`, are admitted. They enter the
model through a survival factor ξ.

## Morphisms: "back to mass action", and to pairwise

Each exact map between representations is returned as a runtime `Semiconjugacy` π, which
NetworkEpiCore's `verify` checks (the residual Jπ·F − G∘π, symbolic first, then numeric
probes). Every map carries an **exactness label**. Only `:exact` maps are morphisms. Limits
and calibrations are labelled as such, and `verify` rejects them. The results below are for
the `sys` of the quick start (SIR on Poisson(5)) and for `edge_based(model, WellMixed(5))`.

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
ΔR∞ ≈ +0.07 (NodeBasedModels README).

| scenario | N = 10³: D∞ / ΔR∞ | N = 10⁴: D∞ / ΔR∞ | N = 10⁵: D∞ / ΔR∞ |
|---|---|---|---|
| `:sir_pois5` | 0.01361 / +0.00070 | 0.00223 / +0.00011 | 0.00093 / +0.00018 |
| `:sir_pl` | 0.01180 / +0.01480 | 0.00265 / +0.00173 | 0.00140 / −0.00027 |

**Cross-check with EoN.** The reference values come from EoN 1.2rc1 on the same exact Poisson(5)
network, with τ = 1/6, γ = 1/4 and ρ = 0.01
(`test/golden/eon/eon_like_for_like.toml`, generated by `test/golden/eon/generate_eon.py`). The
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

## Vignettes

The Quarto pages under [`vignettes/`](vignettes/) are rendered with the strict cache. Every
number on a page is printed by code on that page. Each page shows the low-level call next to the
factory, and compares the result with the committed ensemble.

| page | topic |
|---|---|
| [E01](vignettes/E01_reaction_network_to_ebm/index.md) | from a reaction network to an edge-based model (the shared first cell) |
| [E02](vignettes/E02_writing_models/index.md) | writing models: Catalyst, ModelingToolkit, plain Julia |
| [E03](vignettes/E03_degree_heterogeneity/index.md) | degree heterogeneity: same R₀, different epidemics |
| [E04](vignettes/E04_natural_history/index.md) | latency, stages, branching, strains, vaccination |
| [E05](vignettes/E05_mass_action/index.md) | three roads back to mass action (M1–M5, Λ1, calibrations) |
| [E06](vignettes/E06_edge_based_and_pairwise/index.md) | edge-based and pairwise (M6–M8) |
| [E07](vignettes/E07_final_size/index.md) | final size, R₀ and the probability of a major outbreak |
| [E08](vignettes/E08_clustering/index.md) | clustered networks |
| [E09](vignettes/E09_dynamic_partnerships/index.md) | dynamic partnerships |
| [E10](vignettes/E10_multitype/index.md) | multitype populations, stratification, heterogeneous susceptibility |
| [E11](vignettes/E11_multiplex/index.md) | multiplex networks |
| [E12](vignettes/E12_composition/index.md) | composition: open models, gluing, stratification |
| [E13](vignettes/E13_sis_sirs/index.md) | where edge-based models stop: SIS and SIRS |
| [E14](vignettes/E14_validation/index.md) | validation methodology and the N-scaling protocol |
| [E15](vignettes/E15_degree_correlations/index.md) | degree correlations |
| [E16](vignettes/E16_dormant_fleeting/index.md) | dormant and fleeting contacts (DVD, MFSH) |

## Lean proofs

The Lean mathematics behind this package is in **`NetworkEpiCore.jl/proofs`** (library
`NetworkEpi`, namespace `NEP`). The vignettes cite only theorem names listed in its `CITABLE.txt` whose alignment claims pass
SA-PASS and were rated strong in the spot check.
Examples are `NEP.rempala_general` (M3 for every T_EB model), `NEP.poisson_iso` (M2),
`NEP.wellmixed_unit` (M1), `NEP.eb_to_pws` (M6), `NEP.pt_iff_const_closure` (M8) and
`NEP.lift_append` (strict gluing). See the NetworkEpiCore README for the axiom gate and the
alignment status.

`proofs/` in this repository is the **legacy** tree, `EBCMCategory`. It is **not cited**, and
its theorems are not theorems about the ODEs this package integrates. In phase 0 its inconsistent
axiom `tree_pair_exactness` (which proved 1 = 0) and five content-free axioms were deleted. The
axiom gate (`proofs/scripts/axiom_gate.sh`) now checks that no `axiom` remains. The SA-PASS
alignment audit checks whether each Lean statement says what its text claims. Its latest run
(`proofs/Alignment/SUMMARY.md`, 2026-09-26) found 182 of 467 required claims aligned (39.0%). The
tree is kept for reference only.

## Installation

The four packages are developed side by side and are not registered yet:

```julia
using Pkg
Pkg.develop([PackageSpec(path = "NetworkEpiCore.jl"), PackageSpec(path = "EdgeBasedModels.jl")])
```

Catalyst is needed only for the `contact_model(::ReactionSystem)` front end, and NetworkOutbreaks
only for `scenario_summary`.

## License

MIT
