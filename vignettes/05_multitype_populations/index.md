# Multi-type Populations
Simon Frost
2026-05-13

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
ε = 1e-2
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
    t: 36-element Vector{Float64}:
      0.0
      0.06003976573389654
      0.14282733861586352
      0.24274986797517922
      0.3640860348841155
      0.5060709234989875
      0.6734891209622932
      0.8786865142897698
      1.118660851060441
      1.382334630646394
      ⋮
     17.599213422798183
     19.977440508787417
     22.658507728824546
     25.556051173613156
     28.683405108036993
     32.03657348441811
     35.670043712566276
     39.66696121793301
     40.0
    u: 36-element Vector{Vector{Float64}}:
     [0.0, 0.01, 0.0, 0.01, 0.0, 0.0, 0.0, 0.0, 0.010000000000000009, 0.010000000000000009, 0.010000000000000009, 0.010000000000000009, 1.0, 1.0, 1.0, 1.0]
     [0.00017061674080834607, 0.012845098375940186, 0.00017817679932437838, 0.01391420229020848, 0.00016700646984314598, 0.00016700646984314598, 0.00017445804509715938, 0.00017445804509715938, 0.012347689237375958, 0.012347689237375958, 0.013394546909144229, 0.013394546909144229, 0.9994989805904706, 0.9994989805904706, 0.9994766258647085, 0.9994766258647085]
     [0.0004874181802830448, 0.01805149383853212, 0.000538131834492249, 0.02131092452037591, 0.00046489269848311543, 0.00046489269848311543, 0.0005139771650819497, 0.0005139771650819497, 0.01667934122488271, 0.01667934122488271, 0.01979314769454037, 0.01979314769454037, 0.9986053219045506, 0.9986053219045506, 0.9984580685047542, 0.9984580685047542]
     [0.0010438042331261496, 0.02708656040922116, 0.001224037329915107, 0.034526609396908, 0.0009698261768624914, 0.0009698261768624914, 0.0011408918939812159, 0.0011408918939812159, 0.02425105993489735, 0.02425105993489735, 0.031187079150898238, 0.031187079150898238, 0.9970905214694126, 0.9970905214694126, 0.9965773243180563, 0.9965773243180563]
     [0.002102689877925382, 0.044051127738900624, 0.002624533778474406, 0.05984424335654658, 0.0019050889311387367, 0.0019050889311387367, 0.002390239114365167, 0.002390239114365167, 0.03853346189227108, 0.03853346189227108, 0.05290782067756031, 0.05290782067756031, 0.9942847332065838, 0.9942847332065838, 0.9928292826569045, 0.9928292826569045]
     [0.004196161695303762, 0.07669902699762712, 0.005543600956025063, 0.10876767644465231, 0.003719163088060676, 0.003719163088060676, 0.004945784595156059, 0.004945784595156059, 0.06601853634068819, 0.06601853634068819, 0.09452813902005316, 0.09452813902005316, 0.988842510735818, 0.988842510735818, 0.9851626462145319, 0.9851626462145319]
     [0.00865040225193725, 0.1417444124206244, 0.011929811113655205, 0.20391628139757062, 0.007523316117623328, 0.007523316117623328, 0.010442122320927536, 0.010442122320927536, 0.12030155020206833, 0.12030155020206833, 0.17407760322751573, 0.17407760322751573, 0.97743005164713, 0.97743005164713, 0.9686736330372174, 0.9686736330372174]
     [0.018991040255172547, 0.2701514664916942, 0.026626059658259465, 0.37747415885970576, 0.016202107447083856, 0.016202107447083856, 0.02280094073875716, 0.02280094073875716, 0.2243340769585313, 0.2243340769585313, 0.31289645556293627, 0.31289645556293627, 0.9513936776587485, 0.9513936776587485, 0.9315971777837285, 0.9315971777837285]
     [0.04087378864614522, 0.46074417950061936, 0.05597956246207848, 0.5940321030249047, 0.0339739008039622, 0.0339739008039622, 0.046442204349802126, 0.046442204349802126, 0.3657223649309158, 0.3657223649309158, 0.46424284808777444, 0.46424284808777444, 0.8980782975881134, 0.8980782975881134, 0.8606733869505937, 0.8606733869505937]
     [0.07727110008239298, 0.6298674744023616, 0.10050970223097713, 0.7362109014896938, 0.061724632299575755, 0.061724632299575755, 0.07954656639954873, 0.07954656639954873, 0.4602400452864514, 0.4602400452864514, 0.5185343381224756, 0.5185343381224756, 0.8148261031012727, 0.8148261031012727, 0.7613603008013539, 0.7613603008013539]
     ⋮
     [0.9720360711767353, 0.016531014065338353, 0.9816043537589646, 0.015860885962117956, 0.2471417254156511, 0.2471417254156511, 0.24936628443870912, 0.24936628443870912, 1.835794691552242e-7, 1.835794691552242e-7, 1.0196624573052702e-7, 1.0196624573052702e-7, 0.25857482375304675, 0.25857482375304675, 0.25190114668387276, 0.25190114668387276]
     [0.9794450453183341, 0.009122046962477289, 0.9887129837717251, 0.008752257551576652, 0.24714176587272654, 0.24714176587272654, 0.24936630620464748, 0.24936630620464748, 2.878990513160736e-8, 2.878990513160736e-8, 1.650471155493446e-8, 1.650471155493446e-8, 0.2585747023818204, 0.2585747023818204, 0.2519010813860577, 0.2519010813860577]
     [0.9839003710770731, 0.004666722257965245, 0.9929876992341895, 0.00447754233029678, 0.24714177191618472, 0.24714177191618472, 0.24936630949664543, 0.24936630949664543, 5.670299339179423e-9, 5.670299339179423e-9, 3.577904269818271e-9, 3.577904269818271e-9, 0.25857468425144586, 0.25857468425144586, 0.25190107151006386, 0.25190107151006386]
     [0.9863053786936005, 0.0022617148349936495, 0.9952952123924839, 0.002170029217469249, 0.2471417730101142, 0.2471417730101142, 0.2493663101323525, 0.2493663101323525, 1.4881372525056386e-9, 1.4881372525056386e-9, 1.080542843346369e-9, 1.080542843346369e-9, 0.2585746809696574, 0.2585746809696574, 0.2519010696029427, 0.2519010696029427]
     [0.9875321189343043, 0.0010349746377994484, 0.9964722228907467, 0.000993018729704922, 0.24714177325235007, 0.24714177325235007, 0.24936631028259226, 0.24936631028259226, 5.627033088226144e-10, 5.627033088226144e-10, 4.900822681309971e-10, 4.900822681309971e-10, 0.2585746802429498, 0.2585746802429498, 0.2519010691522234, 0.2519010691522234]
     [0.9881194508088355, 0.00044764277499854336, 0.9970357454332888, 0.0004294961899349146, 0.2471417733184275, 0.2471417733184275, 0.24936631032155707, 0.24936631032155707, 3.10123863144964e-10, 3.10123863144964e-10, 3.3699512210557434e-10, 3.3699512210557434e-10, 0.25857468004471745, 0.25857468004471745, 0.25190106903532894, 0.25190106903532894]
     [0.9883865606029001, 0.0001805329814652635, 0.9972920270965151, 0.0001732145263112047, 0.24714177332832354, 0.24714177332832354, 0.24936631030951606, 0.24936631030951606, 2.7107097089715446e-10, 2.7107097089715446e-10, 3.847617880565842e-10, 3.847617880565842e-10, 0.25857468001502926, 0.25857468001502926, 0.25190106907145193, 0.25190106907145193]
     [0.9885005886193382, 6.650495217327531e-5, 0.9974014326281276, 6.380898913797434e-5, 0.24714177328922388, 0.24714177328922388, 0.2493663102002047, 0.2493663102002047, 4.146157442883999e-10, 4.146157442883999e-10, 8.16446548029662e-10, 8.16446548029662e-10, 0.25857468013232826, 0.25857468013232826, 0.251901069399386, 0.251901069399386]
     [0.9885059015561801, 6.119202337161398e-5, 0.9974065301901142, 5.871143023431761e-5, 0.24714177331890017, 0.24714177331890017, 0.24936631025814193, 0.24936631025814193, 3.0395083113483007e-10, 3.0395083113483007e-10, 5.877804586668547e-10, 5.877804586668547e-10, 0.2585746800432994, 0.2585746800432994, 0.25190106922557426, 0.25190106922557426]

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

    36-element Vector{Float64}:
      0.0
      0.0028755601275356176
      0.0081377451919941
      0.017269693266252235
      0.03441630122532625
      0.06741503478371039
      0.13316197368578997
      0.2629696294017459
      0.4557110283117928
      0.6269002820387685
      ⋮
      0.016423494838608832
      0.009014527806844641
      0.00455920311298097
      0.002154195691964511
      0.0009274554952097835
      0.0003401236325273338
      7.301383899949165e-5
     -4.101419042235044e-5
     -4.6327119142874906e-5

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
    t: 35-element Vector{Float64}:
      0.0
      0.06309194293588453
      0.15518114446885634
      0.2650483578237706
      0.40084076888262965
      0.5601325273621369
      0.7489955757295323
      0.9795372155732923
      1.2560479793654462
      1.5541195967806871
      ⋮
     17.293558431035045
     19.13729898133455
     21.26228044093317
     23.748545480062603
     26.582640437384583
     29.64666803245552
     32.97412240481453
     36.59835456681955
     40.0
    u: 35-element Vector{Vector{Float64}}:
     [0.0, 0.01, 0.0, 0.01, 0.0, 0.0, 0.0, 0.0, 0.010000000000000009, 0.010000000000000009, 0.010000000000000009, 0.010000000000000009, 1.0, 1.0, 1.0, 1.0]
     [0.00017611162505556173, 0.012407883336372846, 0.000184510845865112, 0.013541225922849556, 0.00017217623735439939, 0.00017412876854066954, 0.00018246443531959563, 0.0001804490798868021, 0.01189529001201082, 0.012148673040076741, 0.013269575680415684, 0.013003940449167467, 0.9994834712879368, 0.999738806847189, 0.9997263033470206, 0.9994586527603396]
     [0.0005107899557458583, 0.016879317428765087, 0.0005720843695279228, 0.0205390354801317, 0.00048493510343480784, 0.0004976259904307922, 0.0005578447596360535, 0.0005441073274019214, 0.015450366970771727, 0.01614604240843397, 0.01971650795056949, 0.01893469054005194, 0.9985451946896956, 0.9992535610143538, 0.999163232860546, 0.9983676780177942]
     [0.0010692971439301485, 0.024211200050781086, 0.0012929847631462787, 0.03278414963090177, 0.0009853897452458643, 0.0010260890430180184, 0.0012435083645312881, 0.0011968161113071508, 0.021338938213727784, 0.02271527458716618, 0.03096836348271983, 0.029289869948819453, 0.9970438307642624, 0.9984608664354729, 0.9981347374532031, 0.9964095516660786]
     [0.0021024060233171137, 0.03760710801929742, 0.0027759277437838853, 0.05646155281665524, 0.0018806166721928625, 0.0019867796133007398, 0.002633902359759549, 0.0025029906256580654, 0.0321870473538431, 0.03474256500936268, 0.05265272466104025, 0.04922551805780685, 0.9943581499834214, 0.9970198305800488, 0.9960491464603607, 0.9924910281230258]
     [0.004056461702881903, 0.06254535808368321, 0.0058572115811865175, 0.10212640008988638, 0.0035334939489685096, 0.003780475229285893, 0.005490359902482059, 0.00515993227654734, 0.052467843990691106, 0.05715063171335041, 0.09425771191486776, 0.08734388256488351, 0.9893995181530945, 0.9943292871560712, 0.991764460146277, 0.984520203170358]
     [0.00807087130360951, 0.11172454282785116, 0.012619485666443558, 0.19142256374115213, 0.006872017137086822, 0.007430801197078271, 0.011695346640464127, 0.010881382870056452, 0.09230734558311343, 0.10121841113876502, 0.17480368280643546, 0.16051651792737, 0.9793839485887396, 0.9888537982043826, 0.9824569800393038, 0.9673558513898307]
     [0.01714729408959914, 0.21086702966848545, 0.02812481056842392, 0.35495623292060885, 0.014294871089321188, 0.015607522177113071, 0.025733008597935557, 0.023674563192204838, 0.17083483940079985, 0.1889955183153019, 0.3187485219941936, 0.2883827907202133, 0.9571153867320364, 0.9765887167343303, 0.9614004871030967, 0.9289763104233856]
     [0.037307662316766015, 0.37762724643953455, 0.06026525736873552, 0.5689113617611292, 0.03030228884649377, 0.03348395355678794, 0.05411884884301885, 0.04897373397511722, 0.29372575337032547, 0.33122502486433075, 0.49387949702231737, 0.43328168322939575, 0.9090931334605187, 0.949774069664818, 0.9188217267354717, 0.8530787980746484]
     [0.07215815800862171, 0.5495222777183052, 0.10868321144904866, 0.7106012854471992, 0.05641782659706967, 0.06345684840008549, 0.09497947001484372, 0.08390907300995887, 0.396009129338648, 0.463038314726713, 0.5818358218591384, 0.48364820485641236, 0.830746520208791, 0.9048147273998717, 0.8575307949777344, 0.7482727809701234]
     ⋮
     [0.9651606818955317, 0.019208179931967977, 0.9787315479670317, 0.017827537430031487, 0.24609172532871754, 0.39372164796804215, 0.3986049240084043, 0.24913962211724747, 1.9605126292263828e-6, 6.474190739406303e-5, 4.677537605221957e-5, 5.969280734310598e-7, 0.2617248240138474, 0.4094175280479367, 0.4020926139873934, 0.25258113364825785]
     [0.9722545255135835, 0.012115034768497273, 0.9853153947834551, 0.01124388356903432, 0.24609224444160122, 0.39373948157220445, 0.39861774949867884, 0.24913977689873842, 5.825156755515408e-7, 2.0856351569389833e-5, 1.4904605792080235e-5, 1.7075753591360037e-7, 0.26172326667519635, 0.40939077764169324, 0.40207337575198154, 0.25258066930378503]
     [0.977247490975839, 0.00712230631359978, 0.9899492915192234, 0.006610053276603067, 0.24609241178850488, 0.39374565185176746, 0.3986221369534273, 0.24913982534452922, 1.5013541881871094e-7, 5.667660019809957e-6, 4.002412257975838e-6, 4.3417709796141674e-8, 0.2617227646344853, 0.4093815222223487, 0.4020667945698589, 0.2525805239664127]
     [0.9805443452152104, 0.0038255198543174548, 0.993009014399835, 0.0035503496765892997, 0.24609245822026693, 0.3937474467561913, 0.3986233974114099, 0.24913983867204517, 3.2188459729781625e-8, 1.2481790494738053e-6, 8.705478993594412e-7, 9.388243764086949e-9, 0.2617226253391991, 0.409378829865713, 0.402064903882885, 0.2525804839838648]
     [0.9824862140385825, 0.0018836664197423455, 0.9948112007259439, 0.0017481677900852415, 0.24609246863130374, 0.3937478604123341, 0.3986236841100388, 0.24913984168170897, 5.933109446752879e-9, 2.2942748940779155e-7, 1.5824093194522139e-7, 1.7891933595109228e-9, 0.26172259410608867, 0.40937820938149877, 0.4020644738349417, 0.2525804749548734]
     [0.9834941606175704, 0.0008757226945516769, 0.9957466414974985, 0.000812727851529338, 0.24609247056704153, 0.39374793799820024, 0.3986237372571095, 0.24913984225108937, 1.0439555545105137e-9, 3.8316621409176464e-8, 2.6206253902881563e-8, 3.446704456598285e-10, 0.2617225882988753, 0.4093780930026996, 0.4020643941143357, 0.2525804732467322]
     [0.9839886803253605, 0.0003812034660832048, 0.9962055879449154, 0.00035378154523539173, 0.24609247089585884, 0.3937479511314219, 0.3986237461688814, 0.2491398423493906, 2.0800788270640009e-10, 5.962888742907263e-9, 4.067947060166621e-9, 9.258850515900184e-11, 0.26172258731242337, 0.4093780733028671, 0.40206438074667783, 0.25258047295182856]
     [0.9842157909851124, 0.00015409288056566413, 0.9964163613444526, 0.00014300816754160794, 0.24609247094613929, 0.39374795317911193, 0.39862374755166025, 0.24913984236212203, 8.112039422731175e-11, 9.178980210826275e-10, 6.328432534052354e-10, 6.35061001982231e-11, 0.261722587161582, 0.40937807023133205, 0.40206437867250955, 0.2525804729136343]
     [0.9843040379567242, 6.584592161778135e-5, 0.9964982602418259, 6.110927378762873e-5, 0.2460924709596559, 0.39374795349620567, 0.3986237477677978, 0.2491398423679308, 3.971790124114483e-11, 1.3782765486217007e-10, 9.611862474385797e-11, 4.38903192399519e-11, 0.26172258712103214, 0.40937806975569146, 0.4020643783483032, 0.252580472896208]

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

    35-element Vector{Float64}:
      0.0
      0.0024339842900055553
      0.006953964849552543
      0.01436554760616001
      0.027907196600209253
      0.05311704446697316
      0.10283329119624385
      0.2030680494411372
      0.3717187849980235
      0.5456957597410426
      ⋮
      0.019057795456768556
      0.01196465734894303
      0.006971931288185407
      0.0036751455135713984
      0.001733292234440298
      0.0007253485380759317
      0.00023082931444906585
      3.7187296814122917e-6
     -8.452822913862512e-5

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

This vignette focuses on a scenario for which `NetworkOutbreaks.jl` does
not yet provide an out-of-the-box stochastic ground truth (multi-type
host graphs with prescribed mixing matrices, time-varying networks via
the EBCM rewiring schedule, multiplex layers, degree-correlated
configuration models, clustered graphs with prescribed triangle counts,
or final-size sweeps over $R_0$).

A future revision will add the missing primitives to NetworkOutbreaks.jl
and overlay the corresponding Gillespie SSA ribbon here. Until then, see
[vignette 01](../01_sir_basics/index.html) for the validation pattern on
a single-layer Poisson configuration-model network with the same
canonical parameters.
