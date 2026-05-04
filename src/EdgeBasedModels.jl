module EdgeBasedModels

"""
    EdgeBasedModels

Edge-based compartmental models (EBCMs) for infectious-disease dynamics on networks.

EdgeBasedModels.jl programmatically generates ODE systems based on the edge-based
formulation of Miller (2011) and Miller & Volz (2013). Network structure is encoded
through probability generating functions (PGFs); disease progression through
`DiseaseProgression` graphs. The package supports:

- Single- and multi-type configuration-model networks with arbitrary degree distributions
- Clustered networks (triangle-aware EBCMs)
- Multiplex networks (multiple edge layers sharing nodes)
- Dynamic networks (random rewiring, dormant contacts)
- Catalyst.jl integration for disease specifications
- Stage-population observables for direct compartment tracking
- Categorical composition (`OpenEBCM`, `tensor`, `compose`, `stratify`)
- Symbolic R₀ computation, final-size, epidemic-probability, and confidence-band analytics

Top-level workflow:

```julia
pgf = poisson_pgf(5.0)
prog = sir_model(; β = :β, γ = :γ)
model = StaticConfigurationModel(pgf, prog)
sys = build_edge_system(model)
sol = solve_epidemic(sys; tspan = (0.0, 30.0))
```

See the vignettes under `vignettes/` for end-to-end examples.
"""
EdgeBasedModels

using LinearAlgebra
using Symbolics
using ModelingToolkit
import Catalyst

export DegreePGF,
    DiseaseProgression,
    DiseaseStage,
    DiseaseTransition,
    sir_model,
    seir_model,
    sis_model,
    sirs_model,
    ErlangStage,
    GammaApproxStage,
    expand_erlang_stages,
    DynamicConfigurationModel,
    EdgeModelSystem,
    MultiTypeConfigurationModel,
    MultivariatePGF,
    StaticConfigurationModel,
    ClusteredPGF,
    ClusteredConfigurationModel,
    build_edge_system,
    build_seir,
    build_sir,
    build_sis,
    build_clustered_sir,
    build_clustered_seir,
    generate_edge_system,
    generate_sir,
    generate_seir,
    generate_sis,
    generate_clustered_sir,
    generate_clustered_seir,
    generate_multiplex_sir,
    basic_reproduction_number,
    final_size,
    epidemic_probability,
    epidemic_threshold,
    disease_free_equilibrium,
    default_initial_conditions,
    compartment,
    compartments,
    population_fraction,
    solve_epidemic,
    eval_multivariate_pgf,
    independent_pgf,
    mean_degree,
    mean_single_degree,
    mean_triangle_degree,
    clustering_coefficient,
    mixed_partial,
    multivariate_poisson_pgf,
    partial_derivative,
    pgf_derivative,
    poisson_pgf,
    polynomial_pgf,
    clustered_pgf,
    clustered_poisson_pgf,
    progression_from_catalyst,
    CorrelatedPGF,
    correlated_pgf,
    neutral_correlated_pgf,
    assortative_correlated_pgf,
    correlated_R0,
    confidence_bands,
    NetworkLayer,
    MultiplexModel,
    build_multiplex_sir,
    multiplex_R0,
    susceptible_fraction,
    # Categorical composition framework
    Port,
    OpenEBCM,
    open_sir,
    open_seir,
    compose,
    tensor,
    stratify,
    NaturalTransformation,
    to_mass_action,
    compare_models,
    EBCMFunctor,
    verify_functoriality,
    edge_sir_model,
    edge_sis_model,
    edge_seir_model,
    edge_sirs_model,
    # Reinfection counting (Keeling et al. 2016, Approx. 1)
    with_reinfection_counting,
    build_sis_reinfection,
    base_compartment_of,
    infection_count_of,
    reinfection_totals

include("pgf.jl")
include("disease.jl")
include("builders.jl")
include("analysis.jl")
include("multiplex.jl")
include("categorical.jl")
include("reinfection_counting.jl")

# --- Disambiguating aliases for the cross-package `sir_model` collision ---
const edge_sir_model  = sir_model
const edge_sis_model  = sis_model
const edge_seir_model = seir_model
const edge_sirs_model = sirs_model

# multiplex parity alias (defined here because multiplex.jl loads after analysis.jl)
const generate_multiplex_sir = build_multiplex_sir

end
