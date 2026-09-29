# EdgeBasedModels.jl

EdgeBasedModels builds edge-based compartmental models (EBCMs): the Miller–Slim–Volz equations,
which are the exact large-population limit of an epidemic on a configuration-model random graph.
They are generated as ModelingToolkit systems.

Version 0.2 is built on NetworkEpiCore (NEC), whose names it re-exports:

- a model is a NEC `ContactModel`, with contacts `S + J → X + J` at a per-contact (per-edge)
  rate τ, and node transitions `X → Y | ∅`;
- a network is a NEC `NetworkDescriptor`;
- the verb is [`edge_based`](@ref).

The same objects go to NodeBasedModels (`node_based`) and NetworkOutbreaks (`simulate`). The
changes from 0.1 are listed in [Migrating from 0.1](migration.md).

## The low-level API

A model can come from Catalyst, from ModelingToolkit, from the direct constructor, or from the
canned `sir_model()` and friends. Every route ends in the same `ContactModel`:

```julia
using NetworkEpiCore, EdgeBasedModels, Catalyst

sir = @reaction_network sir begin
    @parameters τ γ
    τ, S + I --> 2I        # contact: per-contact rate τ
    γ, I --> R             # node-local transition
end
model = contact_model(sir)                       # prints the typing report
net   = ConfigurationNetwork(PoissonDegree(5))
p     = Dict(:τ => 1/6, :γ => 1/4)
basic_reproduction_number(model, net, p)         # 2.0

sys  = edge_based(model, net)
init = SeedFraction(:I => 0.01)
sol  = solve_epidemic(sys; p, initial = init, tspan = (0.0, 40.0), saveat = 0.2)
compartment(sys, sol, :I)                        # peak 0.23233 at t = 11.4
final_size(sys; p, initial = init)               # 0.80020
model_curves(sys, sol; t = 0:0.25:40)            # NEC ModelCurves: S, I, R, :infectious, :cumulative
```

By default the seed goes into the model's unique entry state: I for SIR, E for SEIR. The system
can be read with `compartment`, `compartments`, `population_fraction` and `model_curves`, and
analysed with `basic_reproduction_number(sys; p)`, `next_generation_matrix`,
`early_growth_rate`, `final_size`, `epidemic_probability` and `epidemic_threshold`.
`lift_contributions(model, net)` tabulates the θ̇, φ̇ and pop terms that each reaction adds to
the field.

## Factories

The 0.1 factories keep their signatures. They are one-liners over `edge_based`:

```julia
sysF = build_sir(PoissonDegree(5), :τ, :γ)       # also build_seir, build_clustered_sir, build_clustered_seir,
                                                 # build_multiplex_sir, build_edge_system(legacy model)
vector_fields_equal(symbolic_ode(sys), symbolic_ode(sysF))   # true
```

The legacy types (`DegreePGF`, `DiseaseProgression`, `StaticConfigurationModel`, …) are kept, and
they convert to and from the new ones. Functions that returned wrong numbers or checked nothing
now raise errors that name the replacement: `build_sis`, `build_sis_reinfection`,
`to_mass_action`, `compare_models`, `compose` and `verify_functoriality`.

## Networks

The lift accepts these descriptors:

- `ConfigurationNetwork(d)`, for any degree distribution;
- `WellMixed(κ)`;
- `MultitypeNetwork` (`sbm_network`, `unstructured`), and `edge_based(model, net, strata)` for
  heterogeneous susceptibility;
- `ClusteredNetwork`, with triangles;
- `DynamicNetwork(base, NeighbourExchange(η))` and `DynamicNetwork(base, DormantContacts(…))`;
- `MFSHNetwork`;
- `MultiplexNetwork`;
- `degree_correlated(d; r)`.

The lift is **strictly partial**. A reaction that produces a susceptible class, as in SIS and
SIRS, raises an `AdmissibilityError` that names the back ends that accept the model.

## Companion packages

- [NetworkEpiCore.jl](https://github.com/epirecipes/NetworkEpiCore.jl): the shared model,
  network, scenario and morphism objects.
- [NodeBasedModels.jl](https://epirecip.es/NodeBasedModels.jl/): pairwise and other node-level
  closures.
- [NetworkOutbreaks.jl](https://epirecip.es/NetworkOutbreaks.jl/): exact stochastic simulation
  and the reference ensembles.
