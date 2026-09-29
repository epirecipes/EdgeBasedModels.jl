module EdgeBasedModels

"""
    EdgeBasedModels

Edge-based compartmental models (EBCMs) for infectious-disease dynamics on networks: the exact
large-population limits of Miller, Slim & Volz (2012) for epidemics on configuration-model
random graphs, generated as ModelingToolkit systems.

EdgeBasedModels builds on NetworkEpiCore, whose objects it re-exports: a model is a
`ContactModel` (contacts `S + I → 2I` at a per-contact rate τ and node transitions), written
directly, with the canned `sir_model()` & co., or from Catalyst and ModelingToolkit through
`contact_model`; a network is a `NetworkDescriptor` (`ConfigurationNetwork(PoissonDegree(5))`,
`ClusteredNetwork`, …). The verb is [`edge_based`](@ref); the factories (`build_sir`,
`build_seir`, …) are one-liners over it. The lift is exact and strictly partial: models with an
arrow back into the susceptible class (SIS, SIRS) are refused, with the back ends that accept
them named (NodeBasedModels, NetworkOutbreaks).

```julia
using EdgeBasedModels
sys = edge_based(sir_model(; τ = 0.3, γ = 0.1), ConfigurationNetwork(PoissonDegree(5.0)))
sol = solve_epidemic(sys; initial = SeedFraction(:I => 1e-3), tspan = (0.0, 30.0))
R30 = compartment(sys, sol, :R)[end]              # 0.8806
sysF = build_sir(PoissonDegree(5.0), :τ, :γ)       # the factory, with Symbol rates …
solF = solve_epidemic(sysF; p = Dict(:τ => 0.3, :γ => 0.1), tspan = (0.0, 30.0))   # … set here
```

The legacy 0.1 types (`DegreePGF`, `DiseaseProgression`, `StaticConfigurationModel`, …) are kept
and convert both ways; MIGRATION.md lists what changed. See the vignettes under `vignettes/`.
"""
EdgeBasedModels

using LinearAlgebra
using Random
using Symbolics
using ModelingToolkit
using ModelingToolkit: SciMLBase

# NetworkEpiCore: EdgeBasedModels adds methods to its generics and re-exports every binding it
# exports (the same bindings, so EdgeBasedModels, NodeBasedModels, NetworkOutbreaks and
# NetworkEpiCore can be loaded together without ambiguity; design §A.7, §A.8).
using NetworkEpiCore
import NetworkEpiCore: basic_reproduction_number, final_size, epidemic_probability,
                       epidemic_threshold, disease_free_equilibrium, default_initial_conditions,
                       solve_epidemic, model_curves, compartment, compartments, population_fraction,
                       mean_degree, pgf, pgf_derivative, clustering_coefficient, contact_model,
                       stratify, with_reinfection_counting, reinfection_totals, canonical_text,
                       degree_probabilities, is_poisson_type

for name in names(NetworkEpiCore)
    name === :NetworkEpiCore || @eval export $name
end

# EdgeBasedModels' own names. Every later file carries its own `export` lines (design §G.1).
export DegreePGF,
    DiseaseProgression,
    DiseaseStage,
    DiseaseTransition,
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
    eval_multivariate_pgf,
    independent_pgf,
    mean_single_degree,
    mean_triangle_degree,
    mixed_partial,
    multivariate_poisson_pgf,
    partial_derivative,
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
    # The 0.1 categorical layer: deprecated shims and removed functions (src/deprecated.jl)
    Port,
    OpenEBCM,
    open_sir,
    open_seir,
    tensor,
    to_mass_action,
    compare_models,
    EBCMFunctor,
    verify_functoriality,
    edge_sir_model,
    edge_sis_model,
    edge_seir_model,
    edge_sirs_model,
    # Reinfection counting (Keeling et al. 2016, Approx. 1): removed, a migration error (src/deprecated.jl)
    build_sis_reinfection

# Include order: a file may use the types of every file included before it in signatures; function
# bodies may call functions of any file.
include("pgf.jl")               # DegreePGF <: DegreeDistribution, legacy PGF constructors
include("disease.jl")           # legacy DiseaseProgression and friends
include("system.jl")            # EdgeModelSystem
include("builders.jl")          # legacy model types; default_initial_conditions, solve_epidemic
include("compat.jl")            # converters ContactModel ⇄ legacy types; rate lifting (E10)
include("lift/edge_based.jl")   # edge_based; parameters; observing solutions
include("lift/assembler.jl")    # WP17
include("lift/configuration.jl")    # WP17
include("lift/wellmixed.jl")        # WP17
include("lift/multitype.jl")        # WP17
include("lift/clustered.jl")        # WP20
include("lift/dynamic.jl")          # WP21
include("lift/multiplex.jl")        # WP22
include("lift/correlated.jl")       # WP36a
include("lift/dormant.jl")          # WP36b
include("lift/mfsh.jl")             # WP36c
include("lift/clustered_general.jl")    # WP36d
include("lift/heterogeneous.jl")        # WP36f
include("factories.jl")         # build_* over edge_based; the legacy build_edge_system entry points
include("analysis.jl")          # analysis of legacy models and lowered systems (WP19)

"""
    generate_multiplex_sir(layers; kw...)

Alias of [`build_multiplex_sir`](@ref) (the `generate_*` names mirror NodeBasedModels 0.1).
"""
const generate_multiplex_sir = build_multiplex_sir

include("reverse.jl")           # WP18
include("deprecated.jl")        # shims and migration errors (A.7)

end
