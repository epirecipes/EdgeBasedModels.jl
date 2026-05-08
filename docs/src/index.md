# EdgeBasedModels.jl

EdgeBasedModels.jl builds edge-based compartmental epidemic models for
configuration-model networks. It provides probability-generating function
utilities, disease-progression builders, edge-based SIR/SEIR/SIS systems,
multi-type and dynamic-network variants, and SIS reinfection-counting closures
with history-stratified edge states.

## Installation

```julia
using Pkg
Pkg.add(url = "https://github.com/epirecipes/EdgeBasedModels.jl")
```

## Example

```julia
using EdgeBasedModels

pgf = poisson_pgf(5.0)
sys = build_sir(pgf, 0.3, 1.0)
sol = solve_epidemic(sys; tspan = (0.0, 20.0), saveat = 0.1)

I = compartment(sys, sol, :I)
```

## Documentation contents

- [Vignettes](vignettes.md) — worked examples covering SIR, SEIR, SIS,
  multi-type, dynamic, clustered, multiplex, and reinfection-counting models.
- [API reference](api.md) — exported types and functions.

## Companion packages

- [NodeBasedModels.jl](https://epirecip.es/NodeBasedModels.jl/) — node- and
  pair-level approximations and Gillespie simulators.
- [NetworkOutbreaks.jl](https://epirecip.es/NetworkOutbreaks.jl/) — stochastic
  simulation algorithms (DirectSSA, NextReaction, CompositionRejection, HAS).

## License

EdgeBasedModels.jl is licensed under the MIT License.
