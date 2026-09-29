# API reference

EdgeBasedModels re-exports every NetworkEpiCore name (`ContactModel`, `sir_model`,
`ConfigurationNetwork`, `SeedFraction`, `scenario`, `compare`, `verify`, …). Those names are
documented in NetworkEpiCore. The docstrings below are EdgeBasedModels' own, including its
methods of the NetworkEpiCore generics, such as `basic_reproduction_number`, `final_size`,
`solve_epidemic`, `model_curves` and `mass_action` on an `EdgeModelSystem`.

## Building and lifting

```@autodocs
Modules = [EdgeBasedModels]
Pages   = ["EdgeBasedModels.jl", "system.jl", "lift/edge_based.jl", "lift/assembler.jl",
           "lift/configuration.jl", "lift/wellmixed.jl", "lift/multitype.jl", "lift/clustered.jl",
           "lift/clustered_general.jl", "lift/dynamic.jl", "lift/dormant.jl", "lift/mfsh.jl",
           "lift/multiplex.jl", "lift/correlated.jl", "lift/heterogeneous.jl"]
```

## Reverse maps: mass-action forms and the pairwise image

```@autodocs
Modules = [EdgeBasedModels]
Pages   = ["reverse.jl"]
```

## Analysis

```@autodocs
Modules = [EdgeBasedModels]
Pages   = ["analysis.jl"]
```

## Factories and the 0.1 types

```@autodocs
Modules = [EdgeBasedModels]
Pages   = ["factories.jl", "builders.jl", "pgf.jl", "disease.jl", "compat.jl"]
```

## Deprecations and migration errors

```@autodocs
Modules = [EdgeBasedModels]
Pages   = ["deprecated.jl"]
```

## Index

```@index
Modules = [EdgeBasedModels]
```
