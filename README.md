# EdgeBasedModels.jl

Edge-based compartmental models (EBCMs) for epidemics on configuration-model networks.

## Features

| Model | Builder | Description |
|-------|---------|-------------|
| Static SIR/SEIR | `build_sir`, `build_seir`, `build_edge_system` | Compact and expanded PGF-based ODEs |
| Static SIS | `build_sis`, `build_sis_reinfection` | SIS with reinfection-counting closure (Keeling et al. 2016) |
| Multi-type | `MultiTypeConfigurationModel` | Type-stratified populations with mixing matrices |
| Dynamic networks | `DynamicConfigurationModel` | Volz–Meyers (2007) neighbour-exchange model |
| Clustering | `ClusteredConfigurationModel` | Volz (2011) bivariate PGF with triangles |
| Degree correlation | `CorrelatedPGF`, `correlated_R0` | Assortative/disassortative mixing |
| Multiplex | `build_multiplex_sir` | Multi-layer contact networks |
| Method of stages | `ErlangStage`, `expand_erlang_stages` | Erlang-distributed sojourn times |
| Categorical composition | `tensor`, `compose`, `stratify` | Open-system algebra |
| Final size | `final_size`, `Attack_rate` | Analytic attack-rate computation |

## Canonical parameters

All vignettes use **R₀ = 2, γ = 0.25, ε = 0.01** as the anchor. The per-edge transmissibility is T = β/(β+γ) and:
- Poisson(κ): R₀ = T·κ → β = R₀·γ / (κ − R₀) = 1/6 for κ = 5
- k-regular: R₀ = (k−1)·T → β = R₀·γ / (k−1−R₀) for the appropriate k

## Cross-validation

All models are cross-validated against [EoN](https://github.com/springer-math/Mathematics-of-Epidemics-on-Networks) (Python, Kiss–Miller–Simon):

| Test | Julia | EoN | Error |
|------|-------|-----|-------|
| EBCM SIR peak I (Poisson κ=5) | 0.2323 | 0.2328 | 0.2% |
| SIR final size | 0.7985 | 0.7971 | 0.2% |
| SIS endemic I (reinfection L=1) | 0.6528 | 0.6514 | 0.2% |

## Installation

```julia
using Pkg
Pkg.develop(path = "/path/to/EdgeBasedModels.jl")
```

## Quick start

```julia
using EdgeBasedModels, ModelingToolkit, OrdinaryDiffEq

pgf = poisson_pgf(5.0)
sys = build_sir(pgf, 1/6, 0.25; form = :expanded)
ic  = default_initial_conditions(sys; seed_fraction = 0.01)
sol = solve(ODEProblem(sys.system, ic, (0.0, 40.0)), Tsit5())
I   = compartment(sol, sys, :I)
```

## Lean proofs

Machine-checked proofs in `proofs/` verify model properties:
conservation laws, R₀ independence of rewiring, PGF identities,
Volz–Meyers equation-level invariants (8111 Lean build jobs).

## License

MIT
