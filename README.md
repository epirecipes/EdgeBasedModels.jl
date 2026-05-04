# EdgeBasedModels.jl

EdgeBasedModels.jl builds edge-based compartmental epidemic models for
configuration-model networks. It provides probability-generating function
utilities, disease-progression builders, edge-based SIR/SEIR/SIS systems,
multi-type and dynamic-network variants, and SIS reinfection-counting closures
with history-stratified edge states.

## Installation

```julia
using Pkg
Pkg.add("EdgeBasedModels")
```

Until the package is registered, use a local checkout:

```julia
using Pkg
Pkg.develop(path = "/path/to/EdgeBasedModels.jl")
```

## Example

```julia
using EdgeBasedModels

pgf = poisson_pgf(5.0)
sys = build_sir(pgf, 0.3, 1.0)
sol = solve_epidemic(sys; tspan = (0.0, 20.0), saveat = 0.1)

I = compartment(sys, sol, :I)
```

## Development

```bash
julia --project=. -e 'using Pkg; Pkg.instantiate(); Pkg.test()'
```

## License

EdgeBasedModels.jl is licensed under the MIT License.

