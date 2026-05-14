# Multi-type Populations
Simon Frost
2026-05-14

- [Introduction](#introduction)
- [Setup](#setup)
- [Multivariate PGFs](#multivariate-pgfs)
  - [PGF properties](#pgf-properties)
- [Two-type SIR model](#two-type-sir-model)
  - [Building the model](#building-the-model)
- [Solving the two-type model](#solving-the-two-type-model)
  - [Extracting population
    trajectories](#extracting-population-trajectories)
- [Assortative mixing with a contact
  matrix](#assortative-mixing-with-a-contact-matrix)
- [Scaling to more types](#scaling-to-more-types)
- [Summary](#summary)
- [Simulation validation](#simulation-validation)

## Introduction

Real populations are rarely homogeneous. Age groups, risk groups,
spatial patches, and other forms of heterogeneity lead to structured
contact patterns where individuals of different types mix at different
rates. Multi-type edge-based compartmental models extend the EBCM
framework to track the epidemic on each type of edge separately.

For $K$ population types and $M$ disease stages, the package
automatically generates $K^2(1 + M) + K M$ ODEs — the $K^2$ comes from
tracking $\theta_{jl}$ (probability that an edge from type $l$ to type
$j$ has not transmitted) for every ordered pair of types, $K^2 M$ from
the $\phi$ variables for each disease stage and type pair, and $K M$
from the per-stage population trackers (one per stage and type). This
automates what would be extremely tedious bookkeeping by hand.

## Setup

``` julia
using EdgeBasedModels
using ModelingToolkit
using Symbolics
using OrdinaryDiffEq
using Plots
```

## Multivariate PGFs

In a multi-type network, each type $l$ has its own probability
generating function $\psi_l(x_1, \ldots, x_K)$ that describes its
connections to all $K$ types. For a type-$l$ node, the variable $x_k$
corresponds to edges connecting to type-$k$ neighbors. The PGF encodes
the joint degree distribution — the probability that a randomly chosen
type-$l$ node has $d_1$ type-1 neighbors, $d_2$ type-2 neighbors, etc.

For Poisson degree distributions (the simplest case), the multivariate
PGF takes the form:

$$\psi_l(x_1, \ldots, x_K) = \exp\!\left(\sum_{k=1}^K \kappa_{lk}(x_k - 1)\right)$$

where $\kappa_{lk}$ is the mean number of type-$k$ neighbors that a
type-$l$ node has.

Let’s define a two-type network with “Young” and “Old” populations:

``` julia
@parameters κ_YY κ_YO κ_OY κ_OO
pgf_Y = multivariate_poisson_pgf([:Young, :Old], Dict(:Young => κ_YY, :Old => κ_YO))
pgf_O = multivariate_poisson_pgf([:Young, :Old], Dict(:Young => κ_OY, :Old => κ_OO))
```

    MultivariatePGF([:Young, :Old], Any[z_Young, z_Old], exp((-1 + z_Old)*κ_OO + (-1 + z_Young)*κ_OY))

Here `κ_YY` is the mean number of Young neighbors a Young individual
has, `κ_YO` is the mean number of Old neighbors a Young individual has,
and so on.

### PGF properties

We can compute mean degrees and partial derivatives symbolically:

``` julia
println("Mean Young neighbors of a Young node: ", mean_degree(pgf_Y, :Young))
println("Mean Old neighbors of a Young node:   ", mean_degree(pgf_Y, :Old))
println("Mean Young neighbors of an Old node:  ", mean_degree(pgf_O, :Young))
println("Mean Old neighbors of an Old node:    ", mean_degree(pgf_O, :Old))
```

    Mean Young neighbors of a Young node: κ_YY
    Mean Old neighbors of a Young node:   κ_YO
    Mean Young neighbors of an Old node:  κ_OY
    Mean Old neighbors of an Old node:    κ_OO

Partial derivatives describe higher-order degree structure:

``` julia
println("∂ψ_Y/∂x_Young = ", partial_derivative(pgf_Y, :Young, 1))
println("∂²ψ_Y/∂x_Young² = ", partial_derivative(pgf_Y, :Young, 2))
println("∂²ψ_Y/(∂x_Young ∂x_Old) = ", mixed_partial(pgf_Y, :Young, :Old))
```

    ∂ψ_Y/∂x_Young = exp((-1 + z_Old)*κ_YO + (-1 + z_Young)*κ_YY)*κ_YY
    ∂²ψ_Y/∂x_Young² = exp((-1 + z_Old)*κ_YO + (-1 + z_Young)*κ_YY)*(κ_YY^2)
    ∂²ψ_Y/(∂x_Young ∂x_Old) = exp((-1 + z_Old)*κ_YO + (-1 + z_Young)*κ_YY)*κ_YO*κ_YY

We can also evaluate the PGF at specific points:

``` julia
println("ψ_Y(1, 1) = ", eval_multivariate_pgf(pgf_Y, Dict(:Young => 1, :Old => 1)))
```

    ψ_Y(1, 1) = 1

## Two-type SIR model

Now we combine the multivariate PGFs with a disease progression to build
a multi-type edge-based model. We’ll use a standard SIR progression:

``` julia
@parameters β γ
progression = DiseaseProgression(
    [
        DiseaseStage(:I; transmission_rate = β),
        DiseaseStage(:R; transmission_rate = 0),
    ],
    [DiseaseTransition(:I, :R, γ)];
    entry = :I,
)
```

    DiseaseProgression(:S, :I, DiseaseStage[DiseaseStage(:I, β), DiseaseStage(:R, 0)], DiseaseTransition[DiseaseTransition(:I, :R, γ)])

### Building the model

The `MultiTypeConfigurationModel` constructor takes the list of types,
one PGF per type, and the disease progression:

``` julia
model = MultiTypeConfigurationModel(
    types = [:Young, :Old],
    pgfs = Dict(:Young => pgf_Y, :Old => pgf_O),
    progression = progression,
)
result = build_edge_system(model)
```

    EdgeModelSystem(Model multitype_ebm:
    Equations (16):
      16 standard: see equations(multitype_ebm)
    Unknowns (16): see unknowns(multitype_ebm)
      pop_R_Old(t)
      pop_I_Old(t)
      pop_R_Young(t)
      pop_I_Young(t)
      ⋮
    Parameters (8): see parameters(multitype_ebm)
      κ_YY
      κ_YO
      ρ_Young
      κ_OO
      ⋮
    Observed (8): see observed(multitype_ebm), Dict{Symbol, Any}(:φ_I_Old_Old => φ_I_Old_Old(t), :θ_Young_Young => θ_Young_Young(t), :R_Young => pop_R_Young(t), :φ_I_Old_Young => φ_I_Old_Young(t), :θ_Old_Young => θ_Old_Young(t), :φ_R_Young_Young => φ_R_Young_Young(t), :pop_I_Old => pop_I_Old(t), :pop_R_Old => pop_R_Old(t), :pop_R_Young => pop_R_Young(t), :R_Old => pop_R_Old(t)…), Dict{Symbol, Any}(:edge_hazard_Young_Young => φ_I_Young_Young(t)*β, :excess_hazard_Young_Young => φ_I_Young_Young(t)*β*κ_YY + φ_I_Old_Young(t)*β*κ_YO, :φ_S_Young_Young => φ_S_Young_Young(t), :edge_hazard_Old_Old => φ_I_Old_Old(t)*β, :φ_S_Young_Old => φ_S_Young_Old(t), :excess_hazard_Old_Old => φ_I_Young_Old(t)*β*κ_OY + φ_I_Old_Old(t)*β*κ_OO, :excess_hazard_Young_Old => φ_I_Young_Young(t)*β*κ_YY + φ_I_Old_Young(t)*β*κ_YO, :I_Old => I_Old(t), :I_Young => I_Young(t), :S_Old => S_Old(t)…), Dict{Symbol, Any}(:rho_params => Any[ρ_Young, ρ_Old], :seed_groups => Any[(entry = pop_I_Young(t), susceptible_expr = exp((-1 + θ_Old_Young(t))*κ_YO + (-1 + θ_Young_Young(t))*κ_YY)), (entry = pop_I_Old(t), susceptible_expr = exp((-1 + θ_Old_Old(t))*κ_OO + (-1 + θ_Young_Old(t))*κ_OY))], :edge_seed_groups => Any[(entry = φ_I_Young_Young(t), phi_S_expr = exp((-1 + θ_Old_Young(t))*κ_YO + (-1 + θ_Young_Young(t))*κ_YY)*(1 - ρ_Young)), (entry = φ_I_Young_Old(t), phi_S_expr = exp((-1 + θ_Old_Young(t))*κ_YO + (-1 + θ_Young_Young(t))*κ_YY)*(1 - ρ_Young)), (entry = φ_I_Old_Young(t), phi_S_expr = exp((-1 + θ_Old_Old(t))*κ_OO + (-1 + θ_Young_Old(t))*κ_OY)*(1 - ρ_Old)), (entry = φ_I_Old_Old(t), phi_S_expr = exp((-1 + θ_Old_Old(t))*κ_OO + (-1 + θ_Young_Old(t))*κ_OY)*(1 - ρ_Old))]))

Let’s inspect what the model builder generated:

``` julia
n_eqs = length(ModelingToolkit.equations(result.system))
println("Number of equations: ", n_eqs)
```

    Number of equations: 16

With $K = 2$ types and $M = 2$ disease stages (I, R), we expect
$K^2(1 + M) + K M = 4 \times 3 + 2 \times 2 = 16$ equations.

``` julia
println("State variables:")
for (name, var) in sort(collect(result.variables), by = x -> string(x[1]))
    println("  ", name, " → ", var)
end
```

    State variables:
      R_Old → pop_R_Old(t)
      R_Young → pop_R_Young(t)
      pop_I_Old → pop_I_Old(t)
      pop_I_Young → pop_I_Young(t)
      pop_R_Old → pop_R_Old(t)
      pop_R_Young → pop_R_Young(t)
      θ_Old_Old → θ_Old_Old(t)
      θ_Old_Young → θ_Old_Young(t)
      θ_Young_Old → θ_Young_Old(t)
      θ_Young_Young → θ_Young_Young(t)
      φ_I_Old_Old → φ_I_Old_Old(t)
      φ_I_Old_Young → φ_I_Old_Young(t)
      φ_I_Young_Old → φ_I_Young_Old(t)
      φ_I_Young_Young → φ_I_Young_Young(t)
      φ_R_Old_Old → φ_R_Old_Old(t)
      φ_R_Old_Young → φ_R_Old_Young(t)
      φ_R_Young_Old → φ_R_Young_Old(t)
      φ_R_Young_Young → φ_R_Young_Young(t)

``` julia
println("\nObservable quantities:")
for (name, obs) in sort(collect(result.observables), by = x -> string(x[1]))
    println("  ", name)
end
```


    Observable quantities:
      I_Old
      I_Young
      S_Old
      S_Young
      edge_hazard_Old_Old
      edge_hazard_Old_Young
      edge_hazard_Young_Old
      edge_hazard_Young_Young
      excess_hazard_Old_Old
      excess_hazard_Old_Young
      excess_hazard_Young_Old
      excess_hazard_Young_Young
      φ_S_Old_Old
      φ_S_Old_Young
      φ_S_Young_Old
      φ_S_Young_Young

The variables follow a naming convention:

- **$\theta_{jl}$** (`θ_Young_Young`, `θ_Old_Young`, etc.): probability
  that an edge from type $l$ to type $j$ has not transmitted infection
- **$\phi_{m,jl}$** (`φ_I_Young_Young`, `φ_R_Old_Young`, etc.):
  probability that a type-$j$ neighbor reached via a type-$l$ edge is in
  disease stage $m$
- **$R_l$** (`R_Young`, `R_Old`): fraction of type-$l$ population that
  has recovered

## Solving the two-type model

We assign numeric parameter values representing a contact structure
where Young individuals have more contacts (especially with each other),
and Old individuals have fewer contacts overall:

| Parameter     | Value | Meaning                                     |
|---------------|-------|---------------------------------------------|
| $\kappa_{YY}$ | 6     | Young → Young contacts                      |
| $\kappa_{YO}$ | 2     | Young → Old contacts                        |
| $\kappa_{OY}$ | 2     | Old → Young contacts                        |
| $\kappa_{OO}$ | 4     | Old → Old contacts                          |
| $\gamma$      | 0.25  | Recovery rate                               |
| $T$           | 0.75  | Edge transmissibility                       |
| $\beta$       | 0.75  | Transmission rate ($\beta = T\gamma/(1-T)$) |

**Canonical anchor.** This vignette uses $\gamma = 0.25$ and per-edge
transmissibility $T = \beta/(\beta+\gamma) = 0.75$, giving
$\beta = T\gamma/(1-T) = 0.75$. $R_0 = T\,\rho(M)$ where $M$ is the
next-generation matrix derived from the contact structure; preserving
$T$ preserves $R_0$.

``` julia
κ_YY_val = 6.0
κ_YO_val = 2.0
κ_OY_val = 2.0
κ_OO_val = 4.0
γ_val = 0.25
T_val = 0.75
β_val = T_val * γ_val / (1 - T_val)
ε = 1e-3
tspan = (0.0, 40.0)
```

    (0.0, 40.0)

Set up initial conditions and parameters:

``` julia
ic = default_initial_conditions(result; ε = ε)
params = Dict(
    κ_YY => κ_YY_val, κ_YO => κ_YO_val,
    κ_OY => κ_OY_val, κ_OO => κ_OO_val,
    β => β_val, γ => γ_val,
)

prob = ODEProblem(result.system, merge(ic, params), tspan)
sol = solve(prob, Tsit5())
```

    retcode: Success
    Interpolation: specialized 4th order "free" interpolation
    t: 37-element Vector{Float64}:
      0.0
      0.06946190779757472
      0.16375767891920934
      0.27596647760556997
      0.4090865803230596
      0.5598945154443804
      0.7279034394145996
      0.9118990062021185
      1.1138403410552504
      1.3428827678274047
      ⋮
     16.691903088449628
     18.746154313138156
     21.24072006365667
     23.973152667811135
     26.94332690464325
     30.12812374209264
     33.55658423763541
     37.280490173376414
     40.0
    u: 37-element Vector{Vector{Float64}}:
     [0.0, 0.001, 0.0, 0.001, 0.0, 0.0, 0.0, 0.0, 0.0010000000000000009, 0.0010000000000000009, 0.0010000000000000009, 0.0010000000000000009, 1.0, 1.0, 1.0, 1.0]
     [2.0180488181872853e-5, 0.0013400107779181628, 2.1225948454476555e-5, 0.0014692673845568258, 1.9691520241257505e-5, 1.9691520241257505e-5, 2.0719764820090228e-5, 2.071976482009024e-5, 0.0012814251851350068, 0.0012814251851350068, 0.0014076142737309428, 0.0014076142737309424, 0.9999409254392763, 0.9999409254392763, 0.9999378407055397, 0.9999378407055397]
     [5.8892121221065234e-5, 0.0019858348609738696, 6.600462640831481e-5, 0.0023951089488222126, 5.584377022957178e-5, 5.584377022957178e-5, 6.269911753894257e-5, 6.26991175389426e-5, 0.0018213519012766496, 0.0018213519012766496, 0.0022103171050747586, 0.002210317105074758, 0.9998324686893113, 0.9998324686893113, 0.9998119026473832, 0.9998119026473832]
     [0.0001298944252399789, 0.003168504429079342, 0.00015577121776709474, 0.0041508239092432645, 0.00011982185914803035, 0.00011982185914803035, 0.0001442479747417221, 0.00014424797474172211, 0.0028191114177272005, 0.0028191114177272005, 0.0037296032280434727, 0.0037296032280434727, 0.999640534422556, 0.999640534422556, 0.9995672560757748, 0.9995672560757748]
     [0.00027096472783730426, 0.0055300118310041176, 0.00034804951037921265, 0.007755298196541395, 0.00024387478479118746, 0.00024387478479118746, 0.00031514487109169406, 0.000315144871091694, 0.004825477419676674, 0.004825477419676674, 0.006842768222553834, 0.006842768222553833, 0.9992683756456265, 0.9992683756456265, 0.9990545653867249, 0.9990545653867249]
     [0.0005621271098670938, 0.010435564361159737, 0.0007686815999049803, 0.015384622669118676, 0.0004963215307090184, 0.0004963215307090184, 0.0006837083356613561, 0.000683708335661356, 0.009012405348190767, 0.009012405348190767, 0.013418470926378236, 0.013418470926378238, 0.998511035407873, 0.998511035407873, 0.9979488749930159, 0.9979488749930159]
     [0.0012000072668988339, 0.021189665070061387, 0.001727649611837305, 0.03224849689440693, 0.0010454870983983115, 0.0010454870983983115, 0.0015162914094760584, 0.0015162914094760576, 0.01820772394336698, 0.01820772394336698, 0.027910980868340006, 0.02791098086834002, 0.9968635387048052, 0.9968635387048052, 0.9954511257715718, 0.9954511257715718]
     [0.002666085085855431, 0.045513985939572364, 0.003979278578879939, 0.07018199578468828, 0.0023027305252073206, 0.0023027305252073206, 0.0034576534697216403, 0.0034576534697216372, 0.038969148924598525, 0.038969148924598525, 0.06033066048468166, 0.06033066048468168, 0.9930918084243782, 0.9930918084243782, 0.9896270395908351, 0.9896270395908351]
     [0.006199851804883094, 0.10103818491332611, 0.009409904826840287, 0.15426838920330418, 0.0053187391500540745, 0.0053187391500540745, 0.008101410274328586, 0.008101410274328586, 0.08596308011799295, 0.08596308011799295, 0.13127265293283014, 0.13127265293283014, 0.9840437825498379, 0.9840437825498379, 0.9756957691770143, 0.9756957691770143]
     [0.01512748819978776, 0.22232670577423974, 0.022731554721779904, 0.32395528009582036, 0.012852399000899066, 0.012852399000899066, 0.019309432129053294, 0.019309432129053294, 0.18604459797043132, 0.18604459797043132, 0.26944910630138696, 0.269449106301387, 0.961442802997303, 0.961442802997303, 0.9420717036128401, 0.9420717036128401]
     ⋮
     [0.9647709725665093, 0.02367669371352454, 0.9747668068418578, 0.022655089580772284, 0.24711174697878782, 0.24711174697878782, 0.24935537913906208, 0.2493553791390621, 6.783648828326034e-7, 6.783648828326034e-7, 3.798663813573771e-7, 3.798663813573752e-7, 0.2586647590636367, 0.2586647590636367, 0.2519338625828138, 0.25193386258281364]
     [0.9742804286821122, 0.014167263851585449, 0.9838659424614598, 0.013555959978682874, 0.24711189591054494, 0.24711189591054494, 0.24935546064904116, 0.24935546064904118, 1.0889151798329738e-7, 1.0889151798329738e-7, 5.984397766869613e-8, 5.984397766868803e-8, 0.2586643122683653, 0.2586643122683653, 0.2519336180528766, 0.25193361805287645]
     [0.9808540633546653, 0.007593633334013486, 0.9901559298738697, 0.007265973505871694, 0.24711191964767418, 0.24711191964767418, 0.2493554732155811, 0.24935547321558113, 1.809798222563234e-8, 1.809798222563234e-8, 1.0517416659235816e-8, 1.0517416659235227e-8, 0.2586642410569776, 0.2586642410569776, 0.25193358035325675, 0.2519335803532566]
     [0.9846124423191206, 0.0038352550299868325, 0.9937521372451956, 0.0036697662861085783, 0.24711192339169624, 0.24711192339169624, 0.2493554752709446, 0.24935547527094462, 3.782322678129574e-9, 3.782322678129574e-9, 2.4475255581793037e-9, 2.4475255581791825e-9, 0.25866422982491144, 0.25866422982491144, 0.25193357418716633, 0.25193357418716616]
     [0.9866223778656942, 0.001825319608677991, 0.9956753453293095, 0.0017465582315200586, 0.2471119240916565, 0.2471119240916565, 0.24935547568114064, 0.24935547568114066, 1.1077464537803462e-9, 1.1077464537803462e-9, 8.362667401515013e-10, 8.362667401514904e-10, 0.25866422772503067, 0.25866422772503067, 0.2519335729565782, 0.25193357295657803]
     [0.9876243184183611, 0.0008233790868122133, 0.9966340527653053, 0.0007878508029677505, 0.24711192426136824, 0.24711192426136824, 0.2493554757868034, 0.24935547578680342, 4.59700574299342e-10, 4.59700574299342e-10, 4.2105918345165767e-10, 4.2105918345163854e-10, 0.25866422721589544, 0.25866422721589544, 0.25193357263958993, 0.25193357263958976]
     [0.988098203868793, 0.00034949364420912277, 0.9970874903492782, 0.00033441322072749204, 0.2471119243065865, 0.2471119243065865, 0.2493554758094955, 0.24935547580949552, 2.866563847881473e-10, 2.866563847881473e-10, 3.32023532438109e-10, 3.320235324381219e-10, 0.2586642270802407, 0.2586642270802407, 0.25193357257151366, 0.2519335725715135]
     [0.9883098906375141, 0.0001378068733955106, 0.9972900429626289, 0.00013186060606428622, 0.2471119243056071, 0.2471119243056071, 0.2493554757812158, 0.24935547578121584, 2.884812941466322e-10, 2.884812941466322e-10, 4.4382983602782185e-10, 4.438298360278339e-10, 0.2586642270831788, 0.2586642270831788, 0.25193357265635274, 0.2519335726563526]
     [0.9883778713778645, 6.982614760133238e-5, 0.9973550903786643, 6.681319494251124e-5, 0.2471119243675555, 0.2471119243675555, 0.24935547586766163, 0.24935547586766166, 5.524394852132725e-11, 5.524394852132725e-11, 1.029602041297172e-10, 1.0296020412971173e-10, 0.25866422689733365, 0.25866422689733365, 0.25193357239701525, 0.2519335723970151]

### Extracting population trajectories

For Poisson PGFs, we can compute the susceptible fraction of each type
from the $\theta$ values. For type $l$:

$$S_l(t) = \psi_l\!\big(\theta_{1l}(t), \ldots, \theta_{Kl}(t)\big) = \exp\!\left(\sum_{k=1}^K \kappa_{lk}\big(\theta_{kl}(t) - 1\big)\right)$$

``` julia
# Extract θ trajectories
θ_YY = compartment(sol, result, :θ_Young_Young)
θ_OY = compartment(sol, result, :θ_Old_Young)
θ_YO = compartment(sol, result, :θ_Young_Old)
θ_OO = compartment(sol, result, :θ_Old_Old)

# Compute S for each type using the Poisson PGF formula
S_Young = exp.(κ_YY_val .* (θ_YY .- 1) .+ κ_YO_val .* (θ_OY .- 1))
S_Old   = exp.(κ_OY_val .* (θ_YO .- 1) .+ κ_OO_val .* (θ_OO .- 1))

# Extract R for each type
R_Young = compartment(sol, result, :R_Young)
R_Old   = compartment(sol, result, :R_Old)

# I = 1 - S - R
I_Young = 1.0 .- S_Young .- R_Young
I_Old   = 1.0 .- S_Old .- R_Old
```

    37-element Vector{Float64}:
     0.0
     0.00034037132919927663
     0.0009868806249166424
     0.002170805057546016
     0.004534817015885066
     0.009445567663913957
     0.020211044500091153
     0.044560998993279574
     0.10014322425823667
     0.22155819262152804
     ⋮
     0.023683685724189663
     0.014174255888536602
     0.007600625375122516
     0.0038422470717568435
     0.0018323116505734038
     0.0008303711287385163
     0.0003564856861432153
     0.000144798915327371
     7.681818954785591e-5

``` julia
plot(sol.t, S_Young, label="S Young", lw=2, color=1)
plot!(sol.t, I_Young, label="I Young", lw=2, color=2)
plot!(sol.t, R_Young, label="R Young", lw=2, color=3)
plot!(sol.t, S_Old, label="S Old", lw=2, ls=:dash, color=1)
plot!(sol.t, I_Old, label="I Old", lw=2, ls=:dash, color=2)
plot!(sol.t, R_Old, label="R Old", lw=2, ls=:dash, color=3)
xlabel!("Time")
ylabel!("Fraction")
title!("Two-type SIR: Young (solid) vs Old (dashed)")
```

<div id="fig-two-type-sir">

![](index_files/figure-commonmark/fig-two-type-sir-output-1.svg)

Figure 1: SIR dynamics in a two-type (Young/Old) population. Young
individuals have more contacts and experience a faster, larger epidemic.

</div>

The Young population (solid lines) experiences a faster epidemic wave
because they have more total contacts ($\kappa_{YY} + \kappa_{YO} = 8$)
compared to the Old population ($\kappa_{OY} + \kappa_{OO} = 6$, dashed
lines).

``` julia
plot(sol.t, I_Young, label="I Young", lw=2, color=1)
plot!(sol.t, I_Old, label="I Old", lw=2, color=2)
xlabel!("Time")
ylabel!("Prevalence")
title!("Infection prevalence by type")
```

<div id="fig-two-type-prevalence">

![](index_files/figure-commonmark/fig-two-type-prevalence-output-1.svg)

Figure 2: Prevalence (infected fraction) comparison between Young and
Old populations.

</div>

## Assortative mixing with a contact matrix

By default, the multi-type model assumes homogeneous mixing — the
transmission rate across an edge depends only on the disease state of
the infector. In reality, mixing is often **assortative**: individuals
preferentially contact others of the same type.

The `contact_matrix` parameter scales the transmission rate on each type
of edge. A value of 1.0 means the baseline transmission rate applies;
values less than 1.0 reduce cross-group transmission:

``` julia
model_assort = MultiTypeConfigurationModel(
    types = [:Young, :Old],
    pgfs = Dict(:Young => pgf_Y, :Old => pgf_O),
    progression = progression,
    contact_matrix = Dict(
        (:Young, :Young) => 1.0,
        (:Old, :Old) => 1.0,
        (:Young, :Old) => 0.5,
        (:Old, :Young) => 0.5,
    ),
)
result_assort = build_edge_system(model_assort)
```

    EdgeModelSystem(Model multitype_ebm:
    Equations (16):
      16 standard: see equations(multitype_ebm)
    Unknowns (16): see unknowns(multitype_ebm)
      pop_R_Old(t)
      pop_I_Old(t)
      pop_R_Young(t)
      pop_I_Young(t)
      ⋮
    Parameters (8): see parameters(multitype_ebm)
      κ_YY
      κ_YO
      ρ_Young
      κ_OO
      ⋮
    Observed (8): see observed(multitype_ebm), Dict{Symbol, Any}(:φ_I_Old_Old => φ_I_Old_Old(t), :θ_Young_Young => θ_Young_Young(t), :R_Young => pop_R_Young(t), :φ_I_Old_Young => φ_I_Old_Young(t), :θ_Old_Young => θ_Old_Young(t), :φ_R_Young_Young => φ_R_Young_Young(t), :pop_I_Old => pop_I_Old(t), :pop_R_Old => pop_R_Old(t), :pop_R_Young => pop_R_Young(t), :R_Old => pop_R_Old(t)…), Dict{Symbol, Any}(:edge_hazard_Young_Young => φ_I_Young_Young(t)*β, :excess_hazard_Young_Young => φ_I_Young_Young(t)*β*κ_YY + 0.5φ_I_Old_Young(t)*β*κ_YO, :φ_S_Young_Young => φ_S_Young_Young(t), :edge_hazard_Old_Old => φ_I_Old_Old(t)*β, :φ_S_Young_Old => φ_S_Young_Old(t), :excess_hazard_Old_Old => 0.5φ_I_Young_Old(t)*β*κ_OY + φ_I_Old_Old(t)*β*κ_OO, :excess_hazard_Young_Old => φ_I_Young_Young(t)*β*κ_YY + 0.5φ_I_Old_Young(t)*β*κ_YO, :I_Old => I_Old(t), :I_Young => I_Young(t), :S_Old => S_Old(t)…), Dict{Symbol, Any}(:rho_params => Any[ρ_Young, ρ_Old], :seed_groups => Any[(entry = pop_I_Young(t), susceptible_expr = exp((-1 + θ_Old_Young(t))*κ_YO + (-1 + θ_Young_Young(t))*κ_YY)), (entry = pop_I_Old(t), susceptible_expr = exp((-1 + θ_Old_Old(t))*κ_OO + (-1 + θ_Young_Old(t))*κ_OY))], :edge_seed_groups => Any[(entry = φ_I_Young_Young(t), phi_S_expr = exp((-1 + θ_Old_Young(t))*κ_YO + (-1 + θ_Young_Young(t))*κ_YY)*(1 - ρ_Young)), (entry = φ_I_Young_Old(t), phi_S_expr = exp((-1 + θ_Old_Young(t))*κ_YO + (-1 + θ_Young_Young(t))*κ_YY)*(1 - ρ_Young)), (entry = φ_I_Old_Young(t), phi_S_expr = exp((-1 + θ_Old_Old(t))*κ_OO + (-1 + θ_Young_Old(t))*κ_OY)*(1 - ρ_Old)), (entry = φ_I_Old_Old(t), phi_S_expr = exp((-1 + θ_Old_Old(t))*κ_OO + (-1 + θ_Young_Old(t))*κ_OY)*(1 - ρ_Old))]))

The contact matrix entry $c_{jl} = 0.5$ for cross-type edges means that
a Young infector transmits to an Old neighbor at half the baseline rate
(and vice versa). This models reduced cross-group transmission
efficiency due to shorter or less intimate contacts.

``` julia
ic_assort = default_initial_conditions(result_assort; ε = ε)
prob_assort = ODEProblem(result_assort.system, merge(ic_assort, params), tspan)
sol_assort = solve(prob_assort, Tsit5())
```

    retcode: Success
    Interpolation: specialized 4th order "free" interpolation
    t: 37-element Vector{Float64}:
      0.0
      0.07368261789469432
      0.17943780322772118
      0.30386782241451005
      0.4539173864545597
      0.6241808337924785
      0.8148962715660588
      1.0242085881691176
      1.2542398451445125
      1.5140874901636692
      ⋮
     18.395024886615687
     20.309485249067777
     22.527930604643622
     25.1219132616583
     28.025713564989786
     31.159000918138567
     34.563949958934636
     38.28748309861969
     40.0
    u: 37-element Vector{Vector{Float64}}:
     [0.0, 0.001, 0.0, 0.001, 0.0, 0.0, 0.0, 0.0, 0.0010000000000000009, 0.0010000000000000009, 0.0010000000000000009, 0.0010000000000000009, 1.0, 1.0, 1.0, 1.0]
     [2.0985692355937593e-5, 0.001289640383282528, 2.2171764886015106e-5, 0.0014283722506681445, 2.0443488150459962e-5, 2.071216077533212e-5, 2.188783519820554e-5, 2.160890312323203e-5, 0.0012288521230366264, 0.0012588456737001356, 0.0013958244275586464, 0.0013641084030612321, 0.9999386695355487, 0.999968931758837, 0.9999671682472027, 0.9999351732906303]
     [6.200017890389204e-5, 0.0018445631389567346, 7.079689720339291e-5, 0.002311733575280251, 5.845403001978747e-5, 6.018997607561222e-5, 6.88114750244143e-5, 6.690571849589143e-5, 0.0016727471977814772, 0.0017560883776715965, 0.0022105017849226084, 0.0021149075985000786, 0.9998246379099407, 0.9999097150358867, 0.9998967827874633, 0.9997992828445124]
     [0.00013322195258715937, 0.0028006907457823233, 0.00016619177413653314, 0.003955148807547016, 0.00012167750566269618, 0.0001272553972706926, 0.00015919820800123949, 0.00015264389099771885, 0.0024472026757186983, 0.0026157742051927525, 0.003723345061680452, 0.0035107650176926727, 0.999634967483012, 0.999809116904094, 0.9997612026879981, 0.9995420683270069]
     [0.0002699277795756952, 0.004646306260120455, 0.0003722337777488318, 0.007359001343647165, 0.0002393492267108104, 0.0002539198987717183, 0.0003518890466228168, 0.00033327859354167865, 0.003958837132852909, 0.0042814342927668565, 0.006851512504838957, 0.006398120747229282, 0.9992819523198676, 0.9996191201518425, 0.9994721664300656, 0.999000164219375]
     [0.0005381383154784359, 0.008320844295062257, 0.0008218816715552401, 0.014539796196030417, 0.00046598280993685677, 0.0004999159561814368, 0.0007687202053443826, 0.0007211462637663521, 0.006995051370793268, 0.007609192720087103, 0.0134398773542247, 0.012477092812520248, 0.9986020515701894, 0.9992501260657279, 0.9988469196919832, 0.997836561208701]
     [0.0011005087607542199, 0.016142935221834416, 0.001849969386428525, 0.030435567782219963, 0.0009370466988920464, 0.0010130481475435348, 0.00171625598074394, 0.0015988051970802926, 0.013495257187020458, 0.014710823613729811, 0.027994897216788633, 0.025890316380327315, 0.9971888599033238, 0.9984804277786848, 0.9974256160288839, 0.9952035844087592]
     [0.002345339747112935, 0.033513238797631587, 0.0042665661961765605, 0.06619012173190277, 0.0019762977519665837, 0.002146378420048868, 0.003933704706340874, 0.003645651928794801, 0.027953387536878187, 0.030492632494622366, 0.06062242616222713, 0.05587408021290014, 0.9940711067441003, 0.9967804323699269, 0.9940994429404885, 0.9890630442136157]
     [0.005277752678843633, 0.07326280717345574, 0.010101745302589603, 0.1455604440175953, 0.004417671976389368, 0.00481158579850602, 0.009261080987640384, 0.00854245551611728, 0.060869871946741906, 0.06651159535603435, 0.13250948685108396, 0.12149236725571577, 0.986746984070832, 0.9927826213022412, 0.9861083785185392, 0.9743726334516483]
     [0.012651322292384873, 0.16331422466551304, 0.024359871544616805, 0.30585965594121267, 0.010505761250072966, 0.011483573246023423, 0.022156453470147112, 0.020296773611887236, 0.1339425019576061, 0.14725661384283936, 0.2748283938104618, 0.24903243303828068, 0.9684827162497811, 0.982774640130965, 0.9667653197947791, 0.9391096791643384]
     ⋮
     [0.967165827079887, 0.01705345387851977, 0.9808032821453704, 0.015708645623889222, 0.2460544646820229, 0.3936683871804323, 0.3985910647255607, 0.249127874375241, 1.4222303149337797e-6, 4.831300732615574e-5, 3.4265955357376025e-5, 4.302682957339358e-7, 0.2618366059539314, 0.4094974192293519, 0.4021134029116586, 0.2526163768742774]
     [0.9736523633358565, 0.0105674439756725, 0.9867782185582095, 0.009733857259486233, 0.24605484987312998, 0.3936819602858771, 0.39860064734346634, 0.24912798896018154, 4.0781900896389677e-7, 1.4906596836363833e-5, 1.0457459029461536e-5, 1.1997696974361267e-7, 0.2618354503806102, 0.4094770595711847, 0.40209902898480016, 0.2526160331194558]
     [0.978150975889834, 0.00606900266763116, 0.9909219384635695, 0.005590186228662876, 0.24605496961076373, 0.3936864588595149, 0.398603787400046, 0.2491280238517034, 1.0011441008028474e-7, 3.831408678027632e-6, 2.656192117112018e-6, 2.9285418989821303e-8, 0.2618350911677089, 0.409470311710728, 0.40209431889993075, 0.2526159284448902]
     [0.9810468536316367, 0.003173171100291274, 0.9935893350726047, 0.00292280298899842, 0.24605500108529535, 0.393687691795659, 0.3986046373313488, 0.2491280330021124, 2.0390746313157946e-8, 7.952427806484819e-7, 5.447332308585772e-7, 6.053153803869125e-9, 0.26183499674411403, 0.4094684623065119, 0.4020930440029765, 0.25261590099366327]
     [0.9826845617103914, 0.0015354728237124186, 0.9950978231333862, 0.0014143178044595582, 0.24605500771418126, 0.39368795716992727, 0.39860481797072267, 0.24912803495006275, 3.6773785177456776e-9, 1.416092858201497e-7, 9.601103885533402e-8, 1.1375950863513859e-9, 0.26183497685745627, 0.40946806424510945, 0.4020927730439157, 0.25261589514981225]
     [0.9835184340154118, 0.0007016022777665663, 0.9958658990845359, 0.0006462423749963096, 0.24605500891033397, 0.3936880052753667, 0.39860485036164, 0.24912803530797314, 6.51842257713012e-10, 2.310476183716178e-8, 1.555543201926411e-8, 2.2764001451024912e-10, 0.26183497326899813, 0.4094679920869503, 0.40209272445753974, 0.2526158940760811]
     [0.9839204796645388, 0.0002995569169465489, 0.9962362212517549, 0.000275920293871224, 0.24605500910899664, 0.3936880132092932, 0.3986048556599449, 0.24912803536785785, 1.4549851492987676e-10, 3.5582524537279683e-9, 2.3957635814931365e-9, 7.419511803047385e-11, 0.2618349726730101, 0.4094679801860605, 0.4020927165100823, 0.252615893896427]
     [0.9841019090124073, 0.00011812761270941186, 0.996403334849559, 0.00010880670899791488, 0.24605500913669054, 0.3936880144280243, 0.39860485647125676, 0.2491280353723343, 7.835430090310202e-11, 5.550560366580329e-10, 3.804146777253449e-10, 6.922008575565667e-11, 0.2618349725899284, 0.40946797835796384, 0.4020927152931145, 0.2526158938829977]
     [0.984143049559691, 7.698707342175392e-5, 0.996441229185387, 7.091237559728318e-5, 0.24605500915384088, 0.3936880145753002, 0.3986048565716383, 0.2491280353867599, 1.774889725174806e-11, 1.948622419500047e-10, 1.3188830038912158e-10, 1.3945098282080431e-11, 0.2618349725384774, 0.40946797813705, 0.40209271514254225, 0.2526158938397209]

``` julia
# Extract trajectories for the assortative model
θ_YY_a = compartment(sol_assort, result_assort, :θ_Young_Young)
θ_OY_a = compartment(sol_assort, result_assort, :θ_Old_Young)
θ_YO_a = compartment(sol_assort, result_assort, :θ_Young_Old)
θ_OO_a = compartment(sol_assort, result_assort, :θ_Old_Old)

S_Young_a = exp.(κ_YY_val .* (θ_YY_a .- 1) .+ κ_YO_val .* (θ_OY_a .- 1))
S_Old_a   = exp.(κ_OY_val .* (θ_YO_a .- 1) .+ κ_OO_val .* (θ_OO_a .- 1))
R_Young_a = compartment(sol_assort, result_assort, :R_Young)
R_Old_a   = compartment(sol_assort, result_assort, :R_Old)
I_Young_a = 1.0 .- S_Young_a .- R_Young_a
I_Old_a   = 1.0 .- S_Old_a .- R_Old_a
```

    37-element Vector{Float64}:
     0.0
     0.00028995132010826985
     0.0008454706055230971
     0.0018026265629115022
     0.003650226137102853
     0.007328709125936313
     0.015159180222420427
     0.03254803102922676
     0.07233976966681004
     0.1624861135388882
     ⋮
     0.017044935868896327
     0.01055892649329726
     0.00606048535675241
     0.00316465383564446
     0.0015269555688782743
     0.0006930850246932296
     0.0002910396641618851
     0.00010961035996837065
     6.84698206886436e-5

``` julia
plot(sol.t, I_Young, label="I Young (homogeneous)", lw=2, color=1)
plot!(sol_assort.t, I_Young_a, label="I Young (assortative)", lw=2, ls=:dash, color=1)
plot!(sol.t, I_Old, label="I Old (homogeneous)", lw=2, color=2)
plot!(sol_assort.t, I_Old_a, label="I Old (assortative)", lw=2, ls=:dash, color=2)
xlabel!("Time")
ylabel!("Prevalence")
title!("Homogeneous (solid) vs assortative (dashed) mixing")
```

<div id="fig-assortative-comparison">

![](index_files/figure-commonmark/fig-assortative-comparison-output-1.svg)

Figure 3: Effect of assortative mixing on epidemic dynamics. Assortative
mixing (dashed) slows the epidemic and reduces final size compared to
homogeneous mixing (solid).

</div>

Assortative mixing tends to slow the epidemic because cross-group
transmission is a major driver of epidemic spread — reducing it isolates
the two populations, making the overall dynamics more like two separate,
smaller epidemics.

``` julia
final_R_Young_hom = R_Young[end]
final_R_Old_hom = R_Old[end]
final_R_Young_assort = R_Young_a[end]
final_R_Old_assort = R_Old_a[end]

bar_labels = ["Young\n(homogeneous)", "Young\n(assortative)", "Old\n(homogeneous)", "Old\n(assortative)"]
bar_vals = [final_R_Young_hom, final_R_Young_assort, final_R_Old_hom, final_R_Old_assort]
bar(bar_labels, bar_vals, legend=false, ylabel="Final size (R∞)",
    title="Final epidemic size by type and mixing", color=[1 1 2 2],
    ylim=(0, 1))
```

<div id="fig-final-size-comparison">

![](index_files/figure-commonmark/fig-final-size-comparison-output-1.svg)

Figure 4: Final epidemic size (recovered fraction) under homogeneous vs
assortative mixing.

</div>

## Scaling to more types

The multi-type framework scales to any number of population types. For
example, consider a three-type (Young/Middle/Old) SEIR model:

``` julia
@parameters σ

progression_seir = DiseaseProgression(
    [
        DiseaseStage(:E; transmission_rate = 0),
        DiseaseStage(:I; transmission_rate = β),
        DiseaseStage(:R; transmission_rate = 0),
    ],
    [
        DiseaseTransition(:E, :I, σ),
        DiseaseTransition(:I, :R, γ),
    ];
    entry = :E,
)
```

    DiseaseProgression(:S, :E, DiseaseStage[DiseaseStage(:E, 0), DiseaseStage(:I, β), DiseaseStage(:R, 0)], DiseaseTransition[DiseaseTransition(:E, :I, σ), DiseaseTransition(:I, :R, γ)])

``` julia
@parameters κ_YY3 κ_YM κ_YO3 κ_MY κ_MM κ_MO κ_OY3 κ_OM κ_OO3
types_3 = [:Y, :M, :O]

pgf_Y3 = multivariate_poisson_pgf(types_3, Dict(:Y => κ_YY3, :M => κ_YM, :O => κ_YO3))
pgf_M3 = multivariate_poisson_pgf(types_3, Dict(:Y => κ_MY, :M => κ_MM, :O => κ_MO))
pgf_O3 = multivariate_poisson_pgf(types_3, Dict(:Y => κ_OY3, :M => κ_OM, :O => κ_OO3))

model_3type = MultiTypeConfigurationModel(
    types = types_3,
    pgfs = Dict(:Y => pgf_Y3, :M => pgf_M3, :O => pgf_O3),
    progression = progression_seir,
)
result_3type = build_edge_system(model_3type)

n_eqs_3 = length(ModelingToolkit.equations(result_3type.system))
println("Three-type SEIR: $n_eqs_3 equations automatically generated")
```

    Three-type SEIR: 45 equations automatically generated

With $K = 3$ types and $M = 3$ stages (E, I, R), we expect
$K^2(1 + M) + K M = 9 \times 4 + 3 \times 3 = 45$ equations. Writing
these by hand would be impractical and error-prone — the package handles
all the symbolic bookkeeping automatically.

``` julia
println("\nState variables (", length(result_3type.variables), " total):")
for (name, _) in sort(collect(result_3type.variables), by = x -> string(x[1]))
    println("  ", name)
end
```


    State variables (48 total):
      R_M
      R_O
      R_Y
      pop_E_M
      pop_E_O
      pop_E_Y
      pop_I_M
      pop_I_O
      pop_I_Y
      pop_R_M
      pop_R_O
      pop_R_Y
      θ_M_M
      θ_M_O
      θ_M_Y
      θ_O_M
      θ_O_O
      θ_O_Y
      θ_Y_M
      θ_Y_O
      θ_Y_Y
      φ_E_M_M
      φ_E_M_O
      φ_E_M_Y
      φ_E_O_M
      φ_E_O_O
      φ_E_O_Y
      φ_E_Y_M
      φ_E_Y_O
      φ_E_Y_Y
      φ_I_M_M
      φ_I_M_O
      φ_I_M_Y
      φ_I_O_M
      φ_I_O_O
      φ_I_O_Y
      φ_I_Y_M
      φ_I_Y_O
      φ_I_Y_Y
      φ_R_M_M
      φ_R_M_O
      φ_R_M_Y
      φ_R_O_M
      φ_R_O_O
      φ_R_O_Y
      φ_R_Y_M
      φ_R_Y_O
      φ_R_Y_Y

## Summary

Multi-type edge-based models capture the essential features of
heterogeneous populations:

- **Structured contact patterns**: Different types can have different
  degree distributions and mixing preferences.
- **Type-specific dynamics**: Each population type experiences its own
  epidemic trajectory, determined by both its own contact structure and
  cross-group transmission.
- **Contact matrices**: Assortative or disassortative mixing can be
  specified to modulate cross-group transmission rates.
- **Automatic scaling**: The package generates $K^2(1+M) + K M$
  equations for any number of types $K$ and disease stages $M$, handling
  all the symbolic algebra and bookkeeping automatically.

## Simulation validation

We validate the deterministic two-type EBCM against direct stochastic
simulation on a stochastic block model whose within- and between-type
mean degrees match $\kappa_{YY}, \kappa_{YO}, \kappa_{OY}, \kappa_{OO}$.
Each node is assigned a type (1000 Young, 1000 Old). Within-type edges
are sampled at probability $\kappa_{ll}/(N_l-1)$ and between-type edges
at $\kappa_{lk}/N_k$, giving the prescribed mixing matrix in
expectation. We then run an ensemble of `NetworkOutbreaks.jl`
`DirectSSA` epidemics with the type-aware compartments
$\{S_l, I_l, R_l\}$ for $l \in \{Y, O\}$.

``` julia
include("../_validation.jl")

sbm = sbm_typed_graph_builder(
    [:Young => 1000, :Old => 1000],
    Dict((:Young, :Young) => κ_YY_val, (:Young, :Old) => κ_YO_val,
         (:Old,   :Young) => κ_OY_val, (:Old,   :Old) => κ_OO_val))

tgrid_v, mean_v, std_v = gillespie_multitype_ribbon(
    [:Young, :Old], sbm;
    β = β_val, γ = γ_val, n_graphs = 3, nsims_per_graph = 12,
    tspan = tspan, seed_fraction = ε,
    tgrid = collect(0.0:1.0:40.0))
```

    ([0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0  …  31.0, 32.0, 33.0, 34.0, 35.0, 36.0, 37.0, 38.0, 39.0, 40.0], Dict((:I, :Old) => [0.001, 0.04977777777777778, 0.5502777777777778, 0.6932777777777778, 0.5769722222222222, 0.45475000000000004, 0.3569722222222222, 0.2795555555555555, 0.22097222222222224, 0.1741388888888889  …  0.0006388888888888889, 0.0005833333333333334, 0.0004166666666666667, 0.00036111111111111115, 0.00025, 0.0001388888888888889, 0.00011111111111111112, 0.00011111111111111112, 0.00011111111111111112, 8.333333333333333e-5], (:S, :Old) => [0.9990000000000001, 0.947138888888889, 0.3770833333333333, 0.06786111111111111, 0.026250000000000002, 0.018027777777777778, 0.015583333333333334, 0.014888888888888889, 0.014444444444444446, 0.014361111111111111  …  0.014333333333333333, 0.014333333333333333, 0.014333333333333333, 0.014333333333333333, 0.014333333333333333, 0.014333333333333333, 0.014333333333333333, 0.014333333333333333, 0.014333333333333333, 0.014333333333333333], (:R, :Young) => [0.0, 0.004527777777777779, 0.09633333333333333, 0.2779166666666667, 0.4390555555555556, 0.5623055555555555, 0.6576944444444445, 0.7313055555555555, 0.7898333333333334, 0.8342222222222222  …  0.9963888888888888, 0.9966388888888889, 0.9968611111111111, 0.9969722222222221, 0.9970277777777778, 0.9970833333333332, 0.9971666666666665, 0.9971944444444445, 0.997222222222222, 0.9972499999999999], (:S, :Young) => [0.9990000000000001, 0.9164444444444444, 0.24208333333333332, 0.02288888888888889, 0.005722222222222222, 0.003416666666666667, 0.002916666666666667, 0.0026944444444444446, 0.0026666666666666666, 0.0026666666666666666  …  0.0026666666666666666, 0.0026666666666666666, 0.0026666666666666666, 0.0026666666666666666, 0.0026666666666666666, 0.0026666666666666666, 0.0026666666666666666, 0.0026666666666666666, 0.0026666666666666666, 0.0026666666666666666], (:I, :Young) => [0.001, 0.07902777777777778, 0.6615833333333333, 0.6991944444444445, 0.5552222222222222, 0.43427777777777776, 0.33938888888888896, 0.266, 0.2075, 0.16311111111111112  …  0.0009444444444444445, 0.0006944444444444445, 0.00047222222222222224, 0.00036111111111111115, 0.00030555555555555555, 0.00025, 0.00016666666666666666, 0.0001388888888888889, 0.00011111111111111112, 8.333333333333333e-5], (:R, :Old) => [0.0, 0.0030833333333333333, 0.07263888888888889, 0.2388611111111111, 0.39677777777777773, 0.5272222222222221, 0.6274444444444445, 0.7055555555555555, 0.7645833333333334, 0.8115000000000001  …  0.9850277777777777, 0.9850833333333332, 0.9852499999999998, 0.9853055555555557, 0.9854166666666667, 0.9855277777777778, 0.9855555555555555, 0.9855555555555555, 0.9855555555555555, 0.9855833333333334]), Dict((:I, :Old) => [0.0, 0.03965285874119552, 0.16213320997802325, 0.024516596257708596, 0.03619035870908249, 0.030768606449710124, 0.02701056524622605, 0.021398857705754084, 0.018797395125177946, 0.015640885575545316  …  0.0007616815149120597, 0.0007699721701835353, 0.0006491753010001008, 0.0005929479754475106, 0.0005, 0.0003507361872061008, 0.0003187276291558383, 0.0003187276291558383, 0.0003187276291558383, 0.00028030595529069405], (:S, :Old) => [1.1259716555514165e-16, 0.04218676351502939, 0.1918267633643886, 0.041646919129941326, 0.006482393737766055, 0.0034598605348532363, 0.0029796931769179576, 0.0029157481546915717, 0.0027510459771246955, 0.002840048065768081  …  0.002818307496150331, 0.002818307496150331, 0.002818307496150331, 0.002818307496150331, 0.002818307496150331, 0.002818307496150331, 0.002818307496150331, 0.002818307496150331, 0.002818307496150331, 0.002818307496150331], (:R, :Young) => [0.0, 0.004378428361939352, 0.040160392712934756, 0.0522228056367276, 0.04304147132671296, 0.03616376990813116, 0.029968382810121215, 0.025216569886195805, 0.018638669480410874, 0.0157808403019269  …  0.001777281676811575, 0.0017263136245070695, 0.0016239770895248467, 0.0014829721336580648, 0.0014635790009642445, 0.0014417251570848838, 0.001424279266355946, 0.0013694512862445416, 0.0013961398028873586, 0.0013809934312453698], (:S, :Young) => [1.1259716555514165e-16, 0.07121213558072986, 0.20234544366362334, 0.02406274865878528, 0.002668451783457014, 0.001662614120680356, 0.0014015297764534702, 0.0013484264786238695, 0.0013938641048743393, 0.0013938641048743393  …  0.0013938641048743393, 0.0013938641048743393, 0.0013938641048743393, 0.0013938641048743393, 0.0013938641048743393, 0.0013938641048743393, 0.0013938641048743393, 0.0013938641048743393, 0.0013938641048743393, 0.0013938641048743393], (:I, :Young) => [0.0, 0.06721755132663794, 0.16761697408078932, 0.03314023833386531, 0.04143367237343567, 0.036015561010771927, 0.029949746269163975, 0.02523489647294001, 0.018699885408357833, 0.015767557610989504  …  0.0010939951539314042, 0.001009085709072311, 0.0006540472290116195, 0.00048713610757321953, 0.0004671765921511567, 0.0004391550328268399, 0.0003779644730092273, 0.0003507361872061008, 0.0003187276291558383, 0.00028030595529069405], (:R, :Old) => [0.0, 0.0031110402486260813, 0.03380967974477789, 0.0493385695419359, 0.04056959530845807, 0.03168605922493912, 0.027126628398198852, 0.021594237914571348, 0.019244850888335985, 0.016097027232202993  …  0.002772168940544686, 0.002801785145224382, 0.0028322126635245077, 0.0027961140835548863, 0.0028322126635245072, 0.0028232312906729643, 0.002853012888103128, 0.002853012888103128, 0.002853012888103128, 0.0028119642346841594]))

``` julia
plot(sol.t, I_Young, label="I Young (EBM)", lw=2, color=:red)
plot!(tgrid_v, mean_v[(:I, :Young)],
      ribbon = std_v[(:I, :Young)],
      label = "I Young (SSA mean ± 1σ)",
      color = :red, fillalpha = 0.2, linealpha = 0.6, lw = 1)
plot!(sol.t, I_Old, label="I Old (EBM)", lw=2, color=:blue)
plot!(tgrid_v, mean_v[(:I, :Old)],
      ribbon = std_v[(:I, :Old)],
      label = "I Old (SSA mean ± 1σ)",
      color = :blue, fillalpha = 0.2, linealpha = 0.6, lw = 1)
xlabel!("Time")
ylabel!("Prevalence")
title!("Multi-type SIR: EBM vs SSA on SBM")
```

<div id="fig-multitype-validation">

![](index_files/figure-commonmark/fig-multitype-validation-output-1.svg)

Figure 5: EBM (lines) versus DirectSSA on a stochastic block model with
prescribed mixing matrix (ribbons = mean ± 1σ across 36 simulations on 3
graphs, N=2000).

</div>

The deterministic curves track the SSA ensemble means closely across
both populations, with the Young population peaking earlier and higher
because of its larger total mean degree ($\kappa_{YY} + \kappa_{YO} = 8$
vs. $\kappa_{OY} + \kappa_{OO} = 6$).
