# Migrating from EdgeBasedModels 0.1 to 0.2

EdgeBasedModels 0.2 is built on **NetworkEpiCore** (NEC), which it re-exports. The model object is
NEC's `ContactModel` (contacts `S + J → X + J` at a **per-contact rate τ**, node transitions
`X → Y`), the network object is a NEC `NetworkDescriptor`, and the verb is `edge_based(model, net)`.
The same model and network objects are accepted by NodeBasedModels (`node_based`) and
NetworkOutbreaks (`simulate`).

Deprecation policy:

- renamed but correct functionality keeps working for one release, with a deprecation warning
  (run Julia with `--depwarn=yes` to see them; `Pkg.test` does);
- functionality that returned wrong numbers, or checked nothing, is an **error** whose message names
  the replacement.

The references in brackets are the verified issues of `VERIFIED_ISSUES.md`.

## At a glance

```julia
using EdgeBasedModels                          # also brings in NetworkEpiCore's API

# 0.1
pgf  = poisson_pgf(5.0)
prog = sir_model(; β = 0.3, γ = 0.1)            # a DiseaseProgression
sys  = build_edge_system(StaticConfigurationModel(pgf, prog))
sol  = solve_epidemic(sys; tspan = (0.0, 30.0))
R    = compartment(sol, sys, :R)

# 0.2
model = sir_model(; τ = 0.3, γ = 0.1)            # a ContactModel; τ is the per-contact rate
sys   = edge_based(model, ConfigurationNetwork(PoissonDegree(5.0)))
sol   = solve_epidemic(sys; initial = SeedFraction(:I => 1e-3), tspan = (0.0, 30.0))
R     = compartment(sys, sol, :R)                # (sys, sol, X): the NetworkEpiCore order

# factories keep their signatures, and accept NEC degree distributions and Symbol rates
sys = build_sir(PoissonDegree(5.0), :τ, :γ)
sol = solve_epidemic(sys; p = Dict(:τ => 0.3, :γ => 0.1), tspan = (0.0, 30.0))
```

## Models

| 0.1 | 0.2 | Behaviour in 0.2 |
|---|---|---|
| `sir_model(; β, γ)`, `seir_model`, `sis_model`, `sirs_model` returned a `DiseaseProgression` | NEC's `sir_model(; τ, γ)` & co. return a `ContactModel` (default rates `:τ`, `:γ`, …) | `β =` and `susceptible =` are deprecated aliases (depwarn) |
| `edge_sir_model`, `edge_seir_model`, `edge_sis_model`, `edge_sirs_model` | `sir_model` & co. | depwarn; they still return the legacy `DiseaseProgression` |
| `DiseaseProgression`, `DiseaseStage`, `DiseaseTransition` | `ContactModel`, `Contact`, `NodeTransition` | kept; `contact_model(prog)` and `DiseaseProgression(cm)` convert both ways. `DiseaseProgression(cm)` throws for what it cannot express (several entry states, several susceptible classes, removals `X → ∅`, exits `S → V`, layered contacts) |
| `progression_from_catalyst(rn)` | `contact_model(rn)` (NEC's Catalyst front end; load Catalyst) | depwarn; returns `DiseaseProgression(contact_model(rn))`, whose symbolic rates keep the network's parameter defaults (`@parameters τ = 0.3`), so it solves without `p` as in 0.1; a non-zero `transmission_rates[X]` still overrides the rate the reactions give stage X. Branching at infection, which 0.1 dropped silently, is now an error. Duplicate reactions (two `S + I --> 2I` at β₁, β₂) still have their rates added (the shim passes `merge_duplicates = true`); `contact_model(rn)` itself refuses them unless you pass `merge_duplicates = true` |
| `StaticConfigurationModel(pgf, prog)` + `build_edge_system` | `edge_based(cm, ConfigurationNetwork(d))` | kept (forwards to `edge_based`); the legacy model types also accept a `ContactModel`, and `StaticConfigurationModel` a NEC degree distribution |
| `with_reinfection_counting(::DiseaseProgression, L)` (and of a `StaticConfigurationModel`) | NEC's `with_reinfection_counting(cm::ContactModel, L)` | **error**: the counted model has one susceptible class per count, which a `DiseaseProgression` cannot hold, and no edge-based model |
| `base_compartment_of(::Symbol)`, `infection_count_of(::Symbol)` | NEC's name parsers | the names are NEC's bindings |

Things to update in user code:

- `sir_model(...).stages`, `.transitions[i].source` and friends are fields of the legacy type; on a
  `ContactModel` use `species_names(cm)`, `contacts(cm)`, `node_transitions(cm)` (fields `from`,
  `to`, `rate`), or convert with `DiseaseProgression(cm)`.
- `sir_model()` now defaults to the rate names `:τ` and `:γ` (0.1: `:β`, `:γ`).
- `edge_sir_model === sir_model` is no longer true.

## Networks

- `DegreePGF` is a NEC `DegreeDistribution`. `poisson_pgf` and `polynomial_pgf` record the
  distribution they came from (`pgf.distribution`), so `ConfigurationNetwork(poisson_pgf(5.0))` can
  be sampled by NetworkOutbreaks and hashed in scenarios. `DegreePGF(d)` builds the symbolic PGF of
  any NEC distribution (`PoissonDegree`, `RegularDegree`, `NegBinDegree`, `EmpiricalDegree`,
  `PowerLawDegree`, `MixtureDegree`, …).
- `ClusteredPGF` records its `ClusteredDegree` likewise: `ClusteredNetwork(clustered_poisson_pgf(1.0, 2.0))`.
- `mean_degree(::DegreePGF)` returns a `Float64` for a numeric PGF (a symbolic expression otherwise).

## Building and solving

- `edge_based(model, net)` accepts anything `contact_model` accepts (a `ContactModel`, a Catalyst
  `ReactionSystem`, a ModelingToolkit `System`, a legacy `DiseaseProgression`) and a
  `NetworkDescriptor`. It checks admissibility first: SIS and SIRS raise an `AdmissibilityError`
  that names the back ends accepting them.
- Every system is built by the **per-reaction assembler** (design §D.4); the 0.1 builders are
  deleted, and every legacy entry point (`build_edge_system`, the factories, `build_multiplex_sir`,
  the deprecated `open_sir`/`tensor`) goes through it. Exits (vaccination, through the survival
  factor ξ), removals (to the sink `:removed`), branching and several entry states are lifted, on
  `ConfigurationNetwork` (expanded, and compact for SIR-shaped models), `WellMixed`,
  `MultitypeNetwork`, `ClusteredNetwork` (Volz et al. 2011; the 0.1 clustered model rewired every
  triangle into two independent edges [E02]), `DynamicNetwork` with `NeighbourExchange` or
  `DormantContacts`, `MultiplexNetwork`, `DegreeCorrelatedNetwork` and `MFSHNetwork`.
- **New names in every system** (the numbers of the 0.1 names are unchanged): a `:cumulative`
  variable (the fraction ever infected, including the seeds; one more equation), an `:infectious`
  observable (the legacy `:I`), `pop_<X>` for every species (also in the compact form), and one
  seed parameter `seed_<X>` per node species, in place of 0.1's `ρ` / `ρ_<type>` [E26].
- **Clustered networks** (`build_clustered_sir`, `build_clustered_seir`, `edge_based(cm,
  ::ClusteredNetwork)`, `build_edge_system(::ClusteredConfigurationModel)`) give the Volz et al.
  (2011) model with triangle pair states, so the numbers change: the final size for
  `clustered_poisson_pgf(1, 2)`, τ = 0.6, γ = 1, ρ = 10⁻³ is 0.7125 (0.1: 0.7293, the value of the
  network with every triangle rewired into two independent edges) [E02]. The per-edge `φ3_X`
  variables are replaced by the pair states `φ3_X_Y` and `χ_X`, and the observable `φ3_S` by
  `χ_S`, `φ3_S_S` and `φ3_S_X`. Every edge-based-admissible model with one susceptible class is
  accepted.
- **Heterogeneous susceptibility** (several susceptible classes as fixed node attributes) is new:
  `edge_based(model, ConfigurationNetwork(d), st::Strata)`, or equivalently
  `edge_based(model, unstructured(ConfigurationNetwork(d), st))` and `edge_based(sc)` for a scenario
  on that network (design §L.7), with the susceptible classes labelled by stratum and shared
  (unlabelled) infected species.
- **Symbol and expression rates** become ModelingToolkit parameters in every builder
  (`build_sir(pgf, :τ, :γ)` failed with `*(::Symbol, ::Num)` in 0.1) [E10]. Give their values with
  `solve_epidemic(sys; p = Dict(:τ => …))` (or a `NamedTuple`, or symbolic keys).
- **Parameter defaults** of the model are kept, with the NetworkEpiCore semantics (as in
  `instantiate` and NodeBasedModels): a Catalyst model with `@parameters τ = 0.3 γ = 0.1`, or a
  `ContactModel(…; defaults)`, solves without `p`, and `p` (then `init`) takes precedence over the
  defaults. `parameter_defaults(sys)` lists them; the lifted parameters also carry them as
  ModelingToolkit defaults, so `ODEProblem(sys.system, u0, tspan)` works too. The legacy
  `DiseaseProgression` has no field for defaults and keeps them as 0.1 did, on symbolic rate
  parameters: `DiseaseProgression(cm)` turns a rate that uses a parameter with a default into
  that symbolic rate (the other rates keep their Symbols), and `contact_model(prog)` reads the
  defaults back.
- Parameter names [E26]: the seed fractions are the parameters `seed_<X>`, so a rate or PGF
  parameter named `ρ` (which 0.1 silently merged with its seed fraction) is an ordinary parameter
  now. A name that collides with a generated one (`θ`, `ξ`, a species, `seed_<X>`, `q_<s>`, the
  `φ_`/`pop_` coordinates, `cumulative`, `t`) is an `ArgumentError`, and so are multitype type and
  species names whose `_`-joined coordinate names collide. The `contact_matrix` multipliers of a
  `MultiTypeConfigurationModel` may be Symbols (parameters set with `p`), which in 0.1 was a
  `MethodError`. A stage named `S` next to another susceptible name (0.1 shadowed its `φ_S`) is
  lifted correctly: the susceptible observables are named after the susceptible species (`U`,
  `φ_U`).
- `default_initial_conditions(sys; initial = SeedFraction(:I => ρ))` and
  `solve_epidemic(sys; initial = …)` take a NEC `SeedSpec`, which may seed any node species (fractions
  of all nodes, design §J.6); the default seeds the unique entry state (I for SIR, E for SEIR), and a
  model with several entry states needs `initial`. `seed_fraction` keeps working.
- `solve_epidemic(sys, sc::Scenario)` and `edge_based(sc)` use a NEC scenario;
  `model_curves(sys, sol; t, label)` returns the NEC `ModelCurves` that `compare` and the plot
  recipes accept.
- `compartment(sol, sys, X)`, `compartments(sol, sys, Xs)` and `population_fraction(sol, sys, X)`
  are deprecated: use the `(sys, sol, X)` order.
- `compartment(sys, sol, :I)` is still the legacy observable, the fraction in **all** transmitting
  stages (for SEAIR `pop_A + pop_I`), while `model_curves(sys, sol)` reports one curve per species,
  so its `:I` is the stage named I (`pop_I`) and its `:infectious` the legacy `:I`.

## Analysis

- `epidemic_probability` is the infector-side (Markov) value of Ball (2021, §2.4), lower than the 0.1
  value (which was the final size): 0.6094 instead of 0.7968 for τ = 1/6, γ = 1/4 on Poisson(5)
  [E15]. `confidence_bands` uses Ball's (2021) Theorem 2.2 variance (e.g. 0.560 instead of 0.2205 at
  that anchor) and has a new keyword `graph = :NSW | :MR` [E16]. `final_size` has a new keyword
  `seed_fraction` (the ρ → 0 relation stays the default) [E31].
- SIS, SIRS and reinfection-counted models are refused by `final_size`, `epidemic_probability`,
  `confidence_bands`, `epidemic_threshold` and the legacy `basic_reproduction_number` (they have no
  one-shot transmissibility) [E17]. The legacy `basic_reproduction_number(::StaticConfigurationModel)`
  uses the absorbing-chain transmissibility of the whole progression (1.25, not 2.5, for a
  progression with an E → R bypass) [E14]; that of a `ClusteredConfigurationModel` is the
  tree-of-triangles R₀ [E04].
- `epidemic_threshold` of a legacy model returns a `Float64` for numeric input (symbolic otherwise).
- The same functions take a lowered system: `basic_reproduction_number(sys; p)`,
  `next_generation_matrix`, `transmissibility`, `early_growth_rate`, `final_size(sys; p, initial,
  method)`, `epidemic_probability`, `confidence_bands`, `epidemic_threshold(sys; p, vary)` and
  `disease_free_equilibrium(sys)`, with the parameter values as the keyword `p`.
- `clustering_coefficient(::ClusteredPGF)` is the transitivity 2E[t]/E[k(k − 1)] (2/27 for
  `clustered_poisson_pgf(3, 1)`); 0.1 returned the fraction of edges in triangles (0.4 there), which
  is `triangle_edge_fraction(pgf)` [E03].
- `build_multiplex_sir(layers)` returns an `EdgeModelSystem` (0.1: a `(system, u0, tspan, p)` tuple;
  its `tspan` keyword is deprecated), with cross-layer factors and a seed factor [E13], and
  `multiplex_R0` is the spectral radius of the layer next-generation matrix, not the sum of the layer
  R₀s [E12]. `NetworkLayer` and `MultiplexModel` still exist, but nothing consumes them.

## Removed (errors with a migration message)

| 0.1 | Why | Use instead |
|---|---|---|
| `build_sis`, `generate_sis`, SIS through `build_edge_system` | the model was the SIR edge-based equation relabelled (its I was the cumulative incidence); SIS has no exact edge-based model [E01] | `NodeBasedModels.node_based(sis_model(), net)`, `NetworkOutbreaks.simulate(sis_model(), net; …)` |
| `build_sis_reinfection(pgf, τ, γ, L)` | a pairwise model (its numbers were right), not an edge-based one; SIS has no exact edge-based model [E01] | `NodeBasedModels.node_based(with_reinfection_counting(sis_model(; τ, γ), L), ConfigurationNetwork(d))` with `initial = SeedFraction(:I_1 => ρ)` (`:I_0` for L = 0) for the 0.1 `seed_fraction = ρ`: the same equations (I(30), I(120) = 0.654740646584, 0.654792120088 for L = 0 at τ = 1/6, γ = 1/4 on Poisson(5), checked against the 0.1 code before it was deleted); `NetworkOutbreaks.simulate` for stochastic runs |
| `with_reinfection_counting` of a `DiseaseProgression` or `StaticConfigurationModel` | the counted model cannot be a `DiseaseProgression` (several susceptible classes) | NEC's `with_reinfection_counting(contact_model(prog), L)` with NodeBasedModels or NetworkOutbreaks |
| `build_edge_system(::DynamicConfigurationModel)` | not the Miller–Slim–Volz model: a Volz–Meyers equation with a typo, no seed factor, η₁ unused, every model built as SIR [E05, E06, E07] | `edge_based(contact_model(prog), DynamicNetwork(ConfigurationNetwork(d), NeighbourExchange(η₂)))`, or `DormantContacts(η_form = η₁, η_break = η₂)` for dormant contacts |
| lowering a `ClusteredPGF` without `ClusteredDegree` provenance (`build_clustered_sir`, `build_edge_system(::ClusteredConfigurationModel)`) | only the 0.1 clustered builder, which was not the Volz model [E02], accepted it | build the PGF with `clustered_pgf` or `clustered_poisson_pgf`, or use `ClusteredNetwork(ClusteredDegree(…))` |
| `to_mass_action`, `compare_models` | the map MA(τψ''(1)/ψ'(1), γ) is not a reduction; on Poisson networks the exact one is MA(μτ, γ + τ) (Rempała 2023), whose I is the edge variable φ_I [E08] | `mass_action(sys; form)` with `form ∈ (:exact, :edge, :general, :limit, :calibrated)` |
| `compose` (no longer exported), `verify_functoriality`, `EBCMFunctor` | wired composition never built a model; the functoriality check compared θ only and could pass vacuously [E22] | NEC `glue(A, B; on)` / `disjoint_union`, then `edge_based`; `verify`, `check_naturality`, `vector_fields_equal` |
| `stratify(::OpenEBCM, strata, mixing)` | it replaced the degree distribution by a multivariate Poisson and accepted mixing matrices no network realises [E24] | NEC `stratify(cm, strata(names; sizes))` on `sbm_network(st; mean_contacts)`, `unstructured(ConfigurationNetwork(d), st)`, or a `MultitypeNetwork` of `SplitDegrees(d, M[i, :])` (the pull-back of a mixing matrix M) |
| EdgeBasedModels' `NaturalTransformation(name, source, target, description)` (a legacy model type as `source`) | metadata only; it checked nothing, and its documented use ("EBCM → mass-action; valid when network is Poisson") stood for the wrong map [E08] | NEC's `NaturalTransformation(name; source, target, applies, component)` (re-exported), `Semiconjugacy`, `verify`; `mass_action(sys; form)` |

## Deprecated (still working in 0.2)

| 0.1 | Use instead |
|---|---|
| `open_sir`, `open_seir`, `OpenEBCM`, `Port` | `open_model(sir_model(; τ, γ); legs = [[:S], [:I], [:R]])` on `ConfigurationNetwork(d)`, lifted with `edge_based` |
| `tensor(m1, m2)` | `disjoint_union(:a => cm1, :b => cm2)` on a block-diagonal `MultitypeNetwork` (no cross-type edges); the component names must differ |
| `build_edge_system(::MultiTypeConfigurationModel)` | `edge_based(stratify(cm, strata(types; sizes); contact_rates), MultitypeNetwork(types, sizes, degrees))` |

What the deprecated layer does in 0.2 (the 0.1 categorical layer is deleted):

- `open_sir` and `open_seir` return an `OpenEBCM` that holds the replacement objects: NEC's open
  model (`o.model`, an `OpenContactModel`) and its network (`o.network`); `edge_based(o)` and
  `build_edge_system(o)` lift it. `build_edge_system(o.model)`, the 0.1 idiom, no longer works
  (the open model has no network). `Port` and the 0.1 port roles are kept.
- `tensor(m1, m2)` forwards to `disjoint_union(m1.name => m1.model, m2.name => m2.model)` on the
  block-diagonal `MultitypeNetwork` with sizes 1/2; `default_initial_conditions(sys; seed_fraction
  = ρ)` seeds ρ of each component, as in 0.1. Components with a latent stage are accepted now (the
  0.1 refusal [E23] was for a 0.1 observable that is gone).
- `build_edge_system(::MultiTypeConfigurationModel)` forwards to the multitype lift of the
  stratified model. The PGFs must record their degree laws (`multivariate_poisson_pgf` and
  `independent_pgf` do); the type sizes, which 0.1 did not have, are inferred from edge
  reciprocity (equal sizes where a mean degree is symbolic); the contact-matrix entry (b, a)
  multiplies the rate at which type b infects type a [E32(a)]; `default_initial_conditions(sys;
  seed_fraction = ρ)` seeds ρ of each type, as in 0.1.
- For both forwarded multitype paths, compartments are **fractions of all nodes** (design §J.6):
  `pop_I_a` is n_a times the 0.1 within-type fraction, `S_a` likewise, and there are no `I_a`/`R_a`
  aliases; the edge variables `θ_<b>_<a>` and `φ_<X>_<b>_<a>` keep their 0.1 meaning and values.

## Dependencies

- New: NetworkEpiCore (and Random, stdlib).
- Removed from `[deps]`: Catalyst (the Catalyst front end is NEC's extension, loaded when you load
  Catalyst), NodeBasedModels, OrdinaryDiffEq, Graphs and JSON3 (test-only).
