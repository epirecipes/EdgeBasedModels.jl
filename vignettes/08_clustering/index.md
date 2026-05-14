# Clustering and Triangle Motifs
Simon Frost
2026-05-13

- [Introduction](#introduction)
- [Setup](#setup)
- [Clustered networks](#clustered-networks)
- [Building a clustered SIR model](#building-a-clustered-sir-model)
- [Comparing clustered vs unclustered
  epidemics](#comparing-clustered-vs-unclustered-epidemics)
- [Varying the clustering
  coefficient](#varying-the-clustering-coefficient)
- [Clustering coefficient and $R_0$](#clustering-coefficient-and-r_0)
- [SEIR with clustering](#seir-with-clustering)
- [Summary](#summary)
- [Simulation validation](#simulation-validation)

## Introduction

Real contact networks exhibit **clustering** — the tendency for two
people who share a mutual contact to also be connected to each other,
forming triangles. This property, also called triadic closure, is
ubiquitous in social networks but absent from the standard configuration
model in the large-$N$ limit.

Clustering has important epidemiological consequences. When transmission
can travel around a triangle, one of the three edges is “redundant”: if
$A$ infects $B$ and $B$ infects $C$, the edge from $A$ to $C$ cannot
cause a *new* infection. This correlation means that clustering
**reduces** epidemic severity compared to a tree-like network with the
same degree distribution.

The edge-based compartmental model framework handles clustering by
introducing a **bivariate probability generating function** $g(x, y)$
where $x$ tracks single-edge stubs and $y$ tracks triangle-edge stubs.
This approach follows Volz (2011) and Miller (2009).

In this vignette we show how to:

1.  Build clustered network models using `ClusteredPGF`
2.  Compare clustered and unclustered epidemics
3.  Explore how increasing clustering reduces $R_0$ and epidemic
    severity

## Setup

``` julia
using EdgeBasedModels
using ModelingToolkit
using OrdinaryDiffEq
using Symbolics
using Plots
```

## Clustered networks

In a clustered network each node has two types of half-edges:

- **Single-edge stubs** ($s$): connect to a random partner (tree-like)
- **Triangle-edge stubs** ($t$): connect in groups of three to form
  triangles

The joint degree distribution is encoded by a bivariate PGF:

$$g(x, y) = \sum_{s,t} p_{s,t}\, x^s\, y^t$$

where $p_{s,t}$ is the probability that a node has $s$ single-edge stubs
and $t$ triangle-edge stubs. The mean single degree is
$\langle s \rangle = g_x(1,1)$ and the mean triangle degree is
$\langle t \rangle = g_y(1,1)$.

The **clustering coefficient** measures the fraction of connected
triples that are closed into triangles:

$$C = \frac{2\langle t \rangle}{2\langle t \rangle + \langle s \rangle}$$

For a Poisson clustered network with mean single-edge degree $\kappa_s$
and mean triangle-edge degree $\kappa_t$:

$$g(x, y) = e^{\kappa_s(x - 1) + \kappa_t(y - 1)}$$

``` julia
κ_s = 3.0
κ_t = 1.0
cpgf = clustered_poisson_pgf(κ_s, κ_t)
println("Mean single-edge degree: ", mean_single_degree(cpgf))
println("Mean triangle-edge degree: ", mean_triangle_degree(cpgf))
println("Clustering coefficient: ", clustering_coefficient(cpgf))
```

    Mean single-edge degree: 3.0exp(0.0)
    Mean triangle-edge degree: exp(0.0)
    Clustering coefficient: 0.4

Each triangle-edge stub participates in one triangle with two partners,
so the total mean degree (number of distinct neighbours) is
$\langle s \rangle + 2\langle t \rangle$.

## Building a clustered SIR model

The key insight of the clustered EBCM is that we need **two** survival
probabilities:

- $\theta_2(t)$: probability a single-edge partner has not transmitted
  infection
- $\theta_3(t)$: probability a triangle-edge partner has not transmitted
  infection

The susceptible fraction is then $S(t) = g(\theta_2, \theta_3^2)$, where
the square on $\theta_3$ accounts for the two triangle partners per
triangle stub.

Let us build both an unclustered and a clustered SIR model with
comparable mean degrees.

``` julia
@parameters β γ

# Universal anchors: γ=0.25, R₀=2, β derived per scenario (see plan.md)
γ_val = 0.25
R0_target = 2.0
κ_total = 5.0
T_unclustered = R0_target / κ_total
β_val = T_unclustered * γ_val / (1 - T_unclustered)

# Unclustered: all edges are single-stubs, mean degree 5
pgf_unclustered = poisson_pgf(κ_total)
model_unclustered = build_sir(pgf_unclustered, β, γ; form = :expanded)

# Clustered: κ_s=3, κ_t=1 → total mean degree = 3 + 2(1) = 5
cpgf = clustered_poisson_pgf(3.0, 1.0)
model_clustered = build_clustered_sir(cpgf, β, γ)
```

    EdgeModelSystem(Model clustered_sir:
    Equations (8):
      8 standard: see equations(clustered_sir)
    Unknowns (8): see unknowns(clustered_sir)
      pop_R(t)
      pop_I(t)
      φ3_R(t)
      φ3_I(t)
      ⋮
    Parameters (3): see parameters(clustered_sir)
      ρ
      β
      γ
    Observed (4): see observed(clustered_sir), Dict{Symbol, Any}(:θ₃ => θ₃(t), :φ3_I => φ3_I(t), :φ3_R => φ3_R(t), :φ2_I => φ2_I(t), :pop_I => pop_I(t), :R => pop_R(t), :pop_R => pop_R(t), :φ2_R => φ2_R(t), :θ₂ => θ₂(t)), Dict{Symbol, Any}(:I => I(t), :φ2_S => φ2_S(t), :edge_hazard3 => φ3_I(t)*β, :edge_hazard2 => φ2_I(t)*β, :S => S(t), :φ3_S => φ3_S(t)), Dict{Symbol, Any}(:seed_groups => Any[(entry = pop_I(t), susceptible_expr = exp(-1 + 3.0(-1 + θ₂(t)) + θ₃(t)^2))], :rho_param => ρ, :edge_seed_groups => Any[(entry = φ2_I(t), theta = θ₂(t), phi_S_expr = (exp(-1 + 3.0(-1 + θ₂(t)) + θ₃(t)^2) - exp(-1 + 3.0(-1 + θ₂(t)) + θ₃(t)^2)*ρ) / exp(0.0)), (entry = φ3_I(t), theta = θ₃(t), phi_S_expr = (θ₃(t)*exp(-1 + 3.0(-1 + θ₂(t)) + θ₃(t)^2)*(1 - ρ)) / exp(0.0))]))

The clustered model tracks more state variables due to the separate
single-edge and triangle-edge dynamics:

``` julia
println("Unclustered variables: ", keys(model_unclustered.variables))
println("Clustered variables:   ", keys(model_clustered.variables))
```

    Unclustered variables: [:R, :φ_I, :pop_I, :pop_R, :φ_R, :θ]
    Clustered variables:   [:θ₃, :φ3_I, :φ3_R, :φ2_I, :pop_I, :R, :pop_R, :φ2_R, :θ₂]

## Comparing clustered vs unclustered epidemics

We now solve both models with the unclustered Poisson baseline anchored
at $R_0 = 2$ ($\beta = 1/6$, $\gamma = 0.25$), and compare the epidemic
curves.

``` julia
tspan = (0.0, 40.0)
params = Dict(β => β_val, γ => γ_val)

# Unclustered
ic1 = merge(default_initial_conditions(model_unclustered), params)
prob1 = ODEProblem(model_unclustered.system, ic1, tspan)
sol1 = solve(prob1, Tsit5(); saveat = 0.5)

# Clustered
ic2 = merge(default_initial_conditions(model_clustered), params)
prob2 = ODEProblem(model_clustered.system, ic2, tspan)
sol2 = solve(prob2, Tsit5(); saveat = 0.5)
```

    retcode: Success
    Interpolation: 1st order linear
    t: 81-element Vector{Float64}:
      0.0
      0.5
      1.0
      1.5
      2.0
      2.5
      3.0
      3.5
      4.0
      4.5
      ⋮
     36.0
     36.5
     37.0
     37.5
     38.0
     38.5
     39.0
     39.5
     40.0
    u: 81-element Vector{Vector{Float64}}:
     [0.0, 0.001, 0.0, 0.0010000000000000009, 0.0, 0.0010000000000000009, 1.0, 1.0]
     [0.000144623672614379, 0.001326107805807947, 0.00014461643846619562, 0.001325973247055298, 0.00013925055241075892, 0.001238647224404395, 0.9999035890410225, 0.9999071662983928]
     [0.00033497795415506396, 0.0017352069162356533, 0.0003349379878670594, 0.0017347846265559207, 0.00031264810372536516, 0.0015491046975151096, 0.9997767080080886, 0.9997915679308498]
     [0.0005828644053464031, 0.0022510324558243327, 0.0005827405493116342, 0.002250055298484182, 0.0005302916488085122, 0.0019500774464898828, 0.9996115063004589, 0.9996464722341276]
     [0.0009034147604395979, 0.0029034455012692355, 0.0009031116558782131, 0.002901456725756914, 0.0008049188765299209, 0.002465328800825632, 0.9993979255627479, 0.9994633874156467]
     [0.0013159697685541298, 0.0037299981287621455, 0.0013153165442927257, 0.0037262259677345697, 0.0011526283367719805, 0.003124920669362975, 0.9991231223038047, 0.9992315811088187]
     [0.001845104935954855, 0.004777700564948291, 0.0018438057262388148, 0.004770859951768346, 0.0015937170953358993, 0.00396661034200998, 0.9987707961825074, 0.9989375219364427]
     [0.0025220405153348123, 0.00610529737504897, 0.0025195880956793057, 0.0060932557069970986, 0.002153822733974818, 0.005037633333759084, 0.9983202746028803, 0.9985641181773501]
     [0.0033860764081957277, 0.007785467336545977, 0.0033816217012115767, 0.007764739705640867, 0.0028650798927143833, 0.006396410590217731, 0.9977455855325255, 0.9980899467381904]
     [0.004486804708450796, 0.009907869260592578, 0.004478935779073265, 0.009872758398233766, 0.003767889207824383, 0.008114858622669401, 0.997014042813951, 0.9974880738614504]
     ⋮
     [0.7684924194637379, 0.007192733932296931, 0.5103843458746748, 0.0013664247117114415, 0.46449153199027526, 0.0015326000789094595, 0.6597437694168831, 0.6903389786731499]
     [0.7693445792642608, 0.006452802328367567, 0.5105445393464301, 0.0011974197922827636, 0.4646713106641779, 0.00134519715233194, 0.6596369737690463, 0.6902191262238815]
     [0.7701087548816637, 0.005786927653077036, 0.5106847513725135, 0.0010495222828236022, 0.4648289390852569, 0.0011807840593127791, 0.6595434990849907, 0.6901140406098287]
     [0.7707938267003962, 0.005187961768522474, 0.5108074749911291, 0.0009201003717910553, 0.46496713884520846, 0.0010365570602379932, 0.6594616833392469, 0.6900219074365277]
     [0.7714078772463105, 0.004649395858668374, 0.5109149871101936, 0.0008067432479673713, 0.4650883861784953, 0.0009099628074868937, 0.659390008593204, 0.6899410758810032]
     [0.7719581911297007, 0.004165360386799442, 0.5110093483369407, 0.0007072612939204892, 0.465194911812177, 0.0007986984962052435, 0.6593271011087058, 0.689870058791882]
     [0.7724512024872386, 0.003730549318561273, 0.5110921803987606, 0.0006199402285695773, 0.4652885065500611, 0.0007009075556981971, 0.6592718797341591, 0.6898076622999593]
     [0.7728926785078177, 0.0033401151108894125, 0.511164784159956, 0.0005434150928230247, 0.46537063744677826, 0.000615064540743387, 0.6592234772266955, 0.6897529083688145]
     [0.7732878931740367, 0.0029896659767265237, 0.5112284260589087, 0.00047634766958477864, 0.4654427075922083, 0.0005397131637494885, 0.6591810492940604, 0.6897048616051945]

Extract the epidemic compartments using the PGFs:

``` julia
S1 = compartment(sol1, model_unclustered, :S)
I1 = compartment(sol1, model_unclustered, :I)
R1 = compartment(sol1, model_unclustered, :R)

S2 = compartment(sol2, model_clustered, :S)
I2 = compartment(sol2, model_clustered, :I)
R2 = compartment(sol2, model_clustered, :R)
```

    81-element Vector{Float64}:
     0.0
     0.000144623672614379
     0.00033497795415506396
     0.0005828644053464031
     0.0009034147604395979
     0.0013159697685541298
     0.001845104935954855
     0.0025220405153348123
     0.0033860764081957277
     0.004486804708450796
     ⋮
     0.7684924194637379
     0.7693445792642608
     0.7701087548816637
     0.7707938267003962
     0.7714078772463105
     0.7719581911297007
     0.7724512024872386
     0.7728926785078177
     0.7732878931740367

``` julia
plot(sol1.t, S1, label = "S (unclustered)", linewidth = 2, color = :blue)
plot!(sol1.t, I1, label = "I (unclustered)", linewidth = 2, color = :red)
plot!(sol1.t, R1, label = "R (unclustered)", linewidth = 2, color = :green)
plot!(sol2.t, S2, label = "S (clustered)", linewidth = 2, color = :blue, linestyle = :dash)
plot!(sol2.t, I2, label = "I (clustered)", linewidth = 2, color = :red, linestyle = :dash)
plot!(sol2.t, R2, label = "R (clustered)", linewidth = 2, color = :green, linestyle = :dash)
xlabel!("Time")
ylabel!("Fraction of population")
title!("Clustered vs Unclustered SIR (R₀=2 unclustered baseline)")
```

<div id="fig-clustered-vs-unclustered">

![](index_files/figure-commonmark/fig-clustered-vs-unclustered-output-1.svg)

Figure 1: Clustering reduces peak prevalence and delays the epidemic
peak. Both networks have mean degree 5.

</div>

The dashed (clustered) epidemic has a lower peak prevalence and a
delayed peak compared to the solid (unclustered) curves. The final
epidemic size is also smaller with clustering.

## Varying the clustering coefficient

We fix the total mean degree at 5 and vary the fraction of edges that
come from triangles. As clustering increases, more edges are “wasted” on
redundant triangle paths.

``` julia
fracs = [0.0, 0.2, 0.4, 0.6]
results = []

for frac in fracs
    κ_s_i = 5.0 * (1 - frac)
    κ_t_i = 5.0 * frac / 2  # each triangle stub contributes 2 neighbours
    cpgf_i = clustered_poisson_pgf(κ_s_i, κ_t_i)
    model_i = build_clustered_sir(cpgf_i, β, γ)
    ic_i = merge(default_initial_conditions(model_i), params)
    prob_i = ODEProblem(model_i.system, ic_i, tspan)
    sol_i = solve(prob_i, Tsit5(); saveat = 0.5)

    S_i = compartment(sol_i, model_i, :S)
    I_i = compartment(sol_i, model_i, :I)
    R_i_vals = compartment(sol_i, model_i, :R)
    C_i = 2κ_t_i / (2κ_t_i + κ_s_i)

    push!(results, (frac = frac, C = C_i, t = sol_i.t, I = I_i, S = S_i, R = R_i_vals))
end
```

``` julia
p = plot(xlabel = "Time", ylabel = "Fraction infected",
         title = "Effect of clustering on epidemic dynamics")
colors = [:red, :orange, :purple, :blue]
for (i, res) in enumerate(results)
    plot!(p, res.t, res.I,
          label = "C = $(round(res.C; digits=2)) (frac = $(res.frac))",
          linewidth = 2, color = colors[i])
end
p
```

<div id="fig-varying-clustering">

![](index_files/figure-commonmark/fig-varying-clustering-output-1.svg)

Figure 2: Increasing the fraction of triangle edges reduces epidemic
severity while keeping total mean degree = 5.

</div>

As the clustering coefficient $C$ increases, the peak prevalence
decreases and the epidemic is delayed.

## Clustering coefficient and $R_0$

The basic reproduction number $R_0$ for a clustered network accounts for
the redundant transmission paths within triangles. We can compute it
using `basic_reproduction_number`:

``` julia
using EdgeBasedModels: ClusteredConfigurationModel, DiseaseProgression, DiseaseStage, DiseaseTransition

fracs_fine = 0.0:0.05:0.8
C_vals = Float64[]
R0_vals = Float64[]

for frac in fracs_fine
    κ_s_i = 5.0 * (1 - frac)
    κ_t_i = 5.0 * frac / 2
    cpgf_i = clustered_poisson_pgf(κ_s_i, κ_t_i)
    C_i = 2κ_t_i / (2κ_t_i + κ_s_i)
    push!(C_vals, C_i)

    prog = DiseaseProgression(
        [DiseaseStage(:I; transmission_rate = β_val),
         DiseaseStage(:R; transmission_rate = 0)],
        [DiseaseTransition(:I, :R, γ_val)]; entry = :I)
    cm = ClusteredConfigurationModel(cpgf_i, prog)
    R0_i = basic_reproduction_number(cm)
    push!(R0_vals, Float64(Symbolics.value(R0_i)))
end
```

``` julia
plot(C_vals, R0_vals, linewidth = 2, color = :darkred, marker = :circle, markersize = 3,
     label = "R₀")
xlabel!("Clustering coefficient C")
ylabel!("R₀")
title!("R₀ vs Clustering (total mean degree = 5, anchored β, γ)")
hline!([1.0], linestyle = :dash, color = :gray, label = "R₀ = 1")
```

<div id="fig-clustering-r0">

![](index_files/figure-commonmark/fig-clustering-r0-output-1.svg)

Figure 3: R₀ decreases as the clustering coefficient increases,
reflecting the redundancy of triangle edges.

</div>

As the clustering coefficient rises from 0 toward 1, $R_0$ decreases.
This quantifies the protective effect of clustering: triangles create
correlated transmission paths that reduce the effective number of
secondary infections.

## SEIR with clustering

The clustered EBCM framework extends to arbitrary disease progressions.
Here we add a latent (exposed) period using `build_clustered_seir`:

``` julia
@parameters σ

cpgf_seir = clustered_poisson_pgf(3.0, 1.0)
model_seir = build_clustered_seir(cpgf_seir, σ, β, γ)
println("SEIR clustered variables: ", keys(model_seir.variables))
```

    SEIR clustered variables: [:θ₃, :φ3_I, :φ3_R, :φ2_I, :pop_I, :R, :θ₂, :φ2_E, :φ3_E, :pop_R, :φ2_R, :pop_E]

``` julia
params_seir = Dict(β => β_val, γ => γ_val, σ => 0.2)
ic_seir = merge(default_initial_conditions(model_seir), params_seir)
prob_seir = ODEProblem(model_seir.system, ic_seir, tspan)
sol_seir = solve(prob_seir, Tsit5(); saveat = 0.5)

S_seir = compartment(sol_seir, model_seir, :S)
R_seir_vals = compartment(sol_seir, model_seir, :R)
I_seir = 1.0 .- S_seir .- R_seir_vals
```

    81-element Vector{Float64}:
     0.0010000000000000009
     0.0010130454905676778
     0.00104717512584005
     0.0010968014650383033
     0.0011582546048606796
     0.0012291684860312529
     0.0013080987956067896
     0.0013942005315523895
     0.0014870910042569122
     0.0015866444132882913
     ⋮
     0.07593289690599012
     0.07978103926137754
     0.08374450570741221
     0.08781939417069416
     0.09200168706017353
     0.09628717125938369
     0.10066838862572111
     0.10513033548489154
     0.10966182705534845

``` julia
plot(sol_seir.t, S_seir, label = "S", linewidth = 2, color = :blue)
plot!(sol_seir.t, I_seir, label = "E + I", linewidth = 2, color = :red)
plot!(sol_seir.t, R_seir_vals, label = "R", linewidth = 2, color = :green)
xlabel!("Time")
ylabel!("Fraction of population")
title!("Clustered SEIR (κ_s=3, κ_t=1, σ=0.2, anchored β, γ)")
```

<div id="fig-seir-clustered">

![](index_files/figure-commonmark/fig-seir-clustered-output-1.svg)

Figure 4: SEIR epidemic on a clustered network with a latent period
(σ=0.2).

</div>

The latent period further delays and flattens the epidemic curve on top
of the clustering effect.

## Summary

- **Clustering** (triadic closure) is a key structural property of real
  contact networks that is absent from the standard configuration model.
- Triangles create **redundant transmission paths**: if two of three
  triangle edges transmit, the third cannot cause a new infection.
- The clustered EBCM uses a **bivariate PGF** $g(x, y)$ and tracks
  separate survival probabilities for single-edge ($\theta_2$) and
  triangle-edge ($\theta_3$) partners.
- Increasing clustering **reduces $R_0$** and lowers epidemic peak
  prevalence while keeping the mean degree fixed.
- The `EdgeBasedModels.jl` package provides `clustered_poisson_pgf`,
  `build_clustered_sir`, and `build_clustered_seir` for modelling
  clustered networks with arbitrary disease progressions.

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
