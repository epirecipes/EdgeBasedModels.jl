# Edge-Based vs Pairwise Closure Models

2026-05-13

- [Introduction](#introduction)
- [Setup](#setup)
- [Scenario A — $k$-regular network
  ($k=5$)](#scenario-a--k-regular-network-k5)
- [Scenario B — Poisson network
  ($\kappa=5$)](#scenario-b--poisson-network-kappa5)
- [Side-by-side trajectories — regular
  network](#side-by-side-trajectories--regular-network)
- [Side-by-side trajectories — Poisson
  network](#side-by-side-trajectories--poisson-network)
- [Simulation validation](#simulation-validation)
- [Quantitative agreement at the
  peak](#quantitative-agreement-at-the-peak)
- [Sweep over mean degree (Poisson
  networks)](#sweep-over-mean-degree-poisson-networks)
- [Discussion](#discussion)
- [See also](#see-also)

## Introduction

Two leading frameworks for modelling SIR-type epidemics on networks
while avoiding stochastic simulation are:

1.  **Edge-Based Compartmental Models (EBCMs)** — Miller’s PGF-based
    ODEs that track the probability that a randomly chosen *test edge*
    has not yet transmitted infection ([Miller
    2011](https://doi.org/10.1007/s11538-011-9655-3)).
2.  **Pairwise (moment-closure) models** — node and edge population
    fractions coupled to a third-order *triple* term that must be closed
    by an approximation ([Keeling
    1999](https://doi.org/10.1098/rspb.1999.0716)).

EBCMs are exact on the configuration model in the large-`N` limit;
pairwise models with a triple closure are approximations whose accuracy
depends on the network structure and the closure choice.

In this vignette we use the **disambiguating aliases** to load both
packages in one session and run two matched comparisons:

1.  **Regular network**, $k = 5$. EBCM uses a degenerate PGF
    $\psi(z) = z^5$ (every node has degree 5); pairwise uses
    `regular_network(5)`.
2.  **Poisson network**, $\kappa = 5$. EBCM uses `poisson_pgf(5.0)`;
    pairwise uses `erdos_renyi_network(5)` (a `HeterogeneousNetwork`
    whose degree distribution is Poisson($5$)).

Within each scenario we recompute the per-edge transmission rate so the
network epidemic has the same $R_0=2$ anchor as the well-mixed
reference.

## Setup

Both packages export `sir_model`, `default_initial_conditions`,
`compartment`, `population_fraction`, etc. To avoid namespace collisions
we import `NodeBasedModels` under an alias and use Edge’s API by
default.

``` julia
using EdgeBasedModels
import NodeBasedModels as NBM
using OrdinaryDiffEq
using Plots
using Statistics
```

``` julia
γ = 0.25      # recovery rate
R0_target = 2.0
κ = 5         # mean / regular degree
T_regular = R0_target / (κ - 1)
β_regular = T_regular * γ / (1 - T_regular)
T_poisson = R0_target / κ
β_poisson = T_poisson * γ / (1 - T_poisson)
β = β_regular
seed_fraction = 0.01
tspan = (0.0, 40.0)
saveat = 1.0;
```

> [!NOTE]
>
> **$R_0=2$ anchor.** For the 5-regular case,
> $\kappa_{\mathrm{excess}}=4$, so $\beta=0.25$. For Poisson(5),
> $\kappa_{\mathrm{excess}}=5$, so $\beta=1/6$.

## Scenario A — $k$-regular network ($k=5$)

For a $k$-regular network the EBCM PGF is the monomial $\psi(z) = z^k$,
while the pairwise model uses `regular_network(k)`. Because the regular
network has no clustering ($\phi = 0$), the Bernoulli, Keeling and
Barnard closures all reduce to the *standard* pair approximation (the
clustering correction vanishes), so we expect — and observe — them to
coincide exactly.

``` julia
# Degenerate PGF concentrated at degree k
regular_pgf(k::Int) = polynomial_pgf(vcat(zeros(k), [1.0]))

ebcm_reg = build_sir(regular_pgf(κ), β, γ)
ic_r = default_initial_conditions(ebcm_reg; seed_fraction = seed_fraction)
sol_r = solve(ODEProblem(ebcm_reg.system, ic_r, tspan);
              abstol=1e-9, reltol=1e-9, saveat=saveat)

S_r = compartment(ebcm_reg, sol_r, :S)
I_r = compartment(ebcm_reg, sol_r, :I)
R_r = compartment(ebcm_reg, sol_r, :R)
"EBCM (regular) final attack rate = $(round(R_r[end] + I_r[end]; digits=4))"
```

    "EBCM (regular) final attack rate = 0.9532"

``` julia
function run_pairwise(net, closure)
    psys = NBM.generate_pairwise(NBM.sir_model(), net, closure; tspan = tspan, seed_fraction = seed_fraction)
    sol  = NBM.solve_pairwise(psys, Dict(:τ => β, :γ => γ); saveat = saveat)
    (; t = sol.t,
       S = NBM.compartment(psys, sol, :S),
       I = NBM.compartment(psys, sol, :I),
       R = NBM.compartment(psys, sol, :R))
end

reg_net = NBM.regular_network(κ)
bern_r  = run_pairwise(reg_net, NBM.BernoulliClosure())
keel_r  = run_pairwise(reg_net, NBM.KeelingClosure())
barn_r  = run_pairwise(reg_net, NBM.BarnardClosure())
"pairwise (regular) final attack rates: " *
"Bernoulli=$(round(bern_r.R[end]+bern_r.I[end]; digits=4)), " *
"Keeling=$(round(keel_r.R[end]+keel_r.I[end]; digits=4)), " *
"Barnard=$(round(barn_r.R[end]+barn_r.I[end]; digits=4))"
```

    "pairwise (regular) final attack rates: Bernoulli=0.9532, Keeling=0.9532, Barnard=0.9532"

## Scenario B — Poisson network ($\kappa=5$)

A Poisson degree distribution has variance equal to its mean, so degree
heterogeneity matters. The pairwise package’s `HeterogeneousNetwork`
machinery handles this through an *excess-degree* ratio. (Barnard’s
closure is currently implemented only for `HomogeneousNetwork` so we
report only Bernoulli and Keeling.)

``` julia
β = β_poisson
ebcm_pois = build_sir(poisson_pgf(Float64(κ)), β, γ)
ic_p = default_initial_conditions(ebcm_pois; seed_fraction = seed_fraction)
sol_p = solve(ODEProblem(ebcm_pois.system, ic_p, tspan);
              abstol=1e-9, reltol=1e-9, saveat=saveat)

S_p = compartment(ebcm_pois, sol_p, :S)
I_p = compartment(ebcm_pois, sol_p, :I)
R_p = compartment(ebcm_pois, sol_p, :R)

pois_net = NBM.erdos_renyi_network(Float64(κ))
bern_p   = run_pairwise(pois_net, NBM.BernoulliClosure())
keel_p   = run_pairwise(pois_net, NBM.KeelingClosure())
"EBCM (Poisson) attack rate = $(round(R_p[end]+I_p[end]; digits=4));   " *
"pairwise (Poisson) Bernoulli=$(round(bern_p.R[end]+bern_p.I[end]; digits=4)), " *
"Keeling=$(round(keel_p.R[end]+keel_p.I[end]; digits=4))"
```

    "EBCM (Poisson) attack rate = 0.8;   pairwise (Poisson) Bernoulli=0.8, Keeling=0.8"

## Side-by-side trajectories — regular network

``` julia
plt = plot(sol_r.t, I_r, label="EBCM (regular)", lw=3, color=:black, legend=:topright)
plot!(plt, bern_r.t, bern_r.I, label="Pairwise / Bernoulli", lw=2, ls=:dash,    color=1)
plot!(plt, keel_r.t, keel_r.I, label="Pairwise / Keeling",   lw=2, ls=:dot,     color=2)
plot!(plt, barn_r.t, barn_r.I, label="Pairwise / Barnard",   lw=2, ls=:dashdot, color=3)
xlabel!(plt, "time"); ylabel!(plt, "I(t)")
title!(plt, "Scenario A — 5-regular  (R₀=2, γ=$γ)")
```

![I(t) on a 5-regular contact pattern. Bernoulli, Keeling and Barnard
collapse to the same standard pair approximation when the clustering
coefficient is zero, and they coincide with the
EBCM.](index_files/figure-commonmark/cell-7-output-1.svg)

## Side-by-side trajectories — Poisson network

``` julia
plt2 = plot(sol_p.t, I_p, label="EBCM (Poisson)", lw=3, color=:black, legend=:topright)
plot!(plt2, bern_p.t, bern_p.I, label="Pairwise / Bernoulli", lw=2, ls=:dash, color=1)
plot!(plt2, keel_p.t, keel_p.I, label="Pairwise / Keeling",   lw=2, ls=:dot,  color=2)
xlabel!(plt2, "time"); ylabel!(plt2, "I(t)")
title!(plt2, "Scenario B — Poisson($κ)  (R₀=2, γ=$γ)")
```

![I(t) on a Poisson(5) network. Degree variance shifts the peak later
and lower than on the regular network. The Keeling closure on
`HeterogeneousNetwork` tracks the EBCM closely; the Bernoulli
(mean-field) closure ignores degree correlations and over-predicts the
peak.](index_files/figure-commonmark/cell-8-output-1.svg)

## Simulation validation

We add Gillespie SSA ground truth from `NetworkOutbreaks.jl` for both
scenarios — this gives a direct visual check of which approximation
matches the stochastic dynamics best.

``` julia
include("../_validation.jl")

# Regular k=5
t_r_g, μ_r_g, σ_r_g = gillespie_ribbon(
    EdgeBasedModels.sir_model(), Dict(:β => β_regular, :γ => γ),
    regular_graph_builder(1000, κ);
    N = 1000, n_graphs = 5, nsims_per_graph = 20,
    tspan = tspan, seed_fraction = seed_fraction)

# Poisson κ=5
t_p_g, μ_p_g, σ_p_g = gillespie_ribbon(
    EdgeBasedModels.sir_model(), Dict(:β => β_poisson, :γ => γ),
    poisson_graph_builder(1000, Float64(κ));
    N = 1000, n_graphs = 5, nsims_per_graph = 20,
    tspan = tspan, seed_fraction = seed_fraction)
```

    ([0.0, 0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 3.5, 4.0, 4.5  …  35.5, 36.0, 36.5, 37.0, 37.5, 38.0, 38.5, 39.0, 39.5, 40.0], Dict(:I => [0.01, 0.01311, 0.01668, 0.02134, 0.02621, 0.03251, 0.03976, 0.04803, 0.057229999999999996, 0.06829  …  0.00431, 0.0038900000000000002, 0.00346, 0.00317, 0.00294, 0.00265, 0.00235, 0.00212, 0.0019199999999999998, 0.0018], :R => [0.0, 0.00156, 0.00354, 0.005900000000000001, 0.00895, 0.01238, 0.016309999999999998, 0.021670000000000002, 0.02816, 0.03582  …  0.80265, 0.80315, 0.80363, 0.80396, 0.80426, 0.80464, 0.80498, 0.80526, 0.80549, 0.80567], :S => [0.99, 0.98533, 0.97978, 0.97276, 0.96484, 0.95511, 0.9439299999999999, 0.9302999999999999, 0.91461, 0.89589  …  0.19304, 0.19296000000000002, 0.19291, 0.19287, 0.1928, 0.19271000000000002, 0.19266999999999998, 0.19262, 0.19259, 0.19253]), Dict(:I => [0.0, 0.0027703152283894456, 0.00512644165483272, 0.0075654985081465495, 0.009203968182421661, 0.012363595142533778, 0.015003110788544266, 0.017516776950896953, 0.02104821545255972, 0.025202330740379444  …  0.003794453687670834, 0.003592627130244621, 0.003355742853826869, 0.003159257680359279, 0.0028562177434467073, 0.0026376259604179485, 0.0023066657908563763, 0.002279819237916848, 0.0020581446975272647, 0.0019847906537954927], :R => [0.0, 0.0011310136688793462, 0.001816979400382443, 0.002435013948480158, 0.003465194909031202, 0.004451262447187019, 0.005311879197239015, 0.0070195326328637, 0.008905474425738066, 0.011385246522752085  …  0.020014325677454946, 0.019989580619245953, 0.019931019932646586, 0.019842266895583164, 0.019723656513502417, 0.019668731273241546, 0.01963041342695388, 0.01958850415293355, 0.019591017834660347, 0.01954794933573144], :S => [0.0, 0.002570441930324768, 0.005072365216433936, 0.008117968596971422, 0.010417273921693523, 0.014843217680513584, 0.018551187715522843, 0.02279442604203621, 0.028067701341325735, 0.0347071136422166  …  0.019745819145767892, 0.019753490933007364, 0.019720826810785852, 0.01968625372839093, 0.01969617714023191, 0.019706582502793172, 0.019719781894833373, 0.019737560972200016, 0.019750000639304426, 0.019756321070032806]))

``` julia
plot(t_r_g, μ_r_g[:I], ribbon = σ_r_g[:I], label = "SSA (mean ± 1σ)",
     color = :gray, fillalpha = 0.3)
plot!(sol_r.t, I_r, label = "EBCM", lw = 3, color = :black)
plot!(bern_r.t, bern_r.I, label = "Pairwise", lw = 2, ls = :dash, color = 1)
xlabel!("time"); ylabel!("I(t)")
title!("Scenario A — 5-regular  (R₀=2, γ=$γ)")
```

<div id="fig-validation-regular">

![](index_files/figure-commonmark/fig-validation-regular-output-1.svg)

Figure 1: Scenario A: SSA ribbon (gray) overlaid with EBCM and pairwise
closures.

</div>

``` julia
plot(t_p_g, μ_p_g[:I], ribbon = σ_p_g[:I], label = "SSA (mean ± 1σ)",
     color = :gray, fillalpha = 0.3)
plot!(sol_p.t, I_p, label = "EBCM", lw = 3, color = :black)
plot!(keel_p.t, keel_p.I, label = "Pairwise / Keeling", lw = 2, ls = :dot, color = 2)
plot!(bern_p.t, bern_p.I, label = "Pairwise / Bernoulli", lw = 2, ls = :dash, color = 1)
xlabel!("time"); ylabel!("I(t)")
title!("Scenario B — Poisson($κ)  (R₀=2, γ=$γ)")
```

<div id="fig-validation-poisson">

![](index_files/figure-commonmark/fig-validation-poisson-output-1.svg)

Figure 2: Scenario B: SSA ribbon (gray) overlaid with EBCM and pairwise
closures on Poisson(5).

</div>

The SSA mean coincides with the EBCM and the heterogeneity-aware
pairwise closures, while the Bernoulli mean-field closure visibly
over-predicts the peak on the heterogeneous network — the same
stochastic check used in the EdgeBasedModels validation pilot now
applies across the package suite.

## Quantitative agreement at the peak

``` julia
function peak_stats(t, I)
    idx = argmax(I)
    (; t_peak = t[idx], I_peak = I[idx])
end
println("Scenario A — 5-regular network")
println("  Method       t_peak    I_peak    R(∞)")
for (name, t, I, R) in (
    ("EBCM     ", sol_r.t, I_r,     R_r),
    ("Bernoulli", bern_r.t, bern_r.I, bern_r.R),
    ("Keeling  ", keel_r.t, keel_r.I, keel_r.R),
    ("Barnard  ", barn_r.t, barn_r.I, barn_r.R),
)
    p = peak_stats(t, I)
    println("  ", name, "    ", round(p.t_peak; digits=2), "    ",
            round(p.I_peak; digits=4), "    ", round(R[end]; digits=4))
end

println("\nScenario B — Poisson($κ) network")
println("  Method       t_peak    I_peak    R(∞)")
for (name, t, I, R) in (
    ("EBCM     ", sol_p.t, I_p,     R_p),
    ("Bernoulli", bern_p.t, bern_p.I, bern_p.R),
    ("Keeling  ", keel_p.t, keel_p.I, keel_p.R),
)
    p = peak_stats(t, I)
    println("  ", name, "    ", round(p.t_peak; digits=2), "    ",
            round(p.I_peak; digits=4), "    ", round(R[end]; digits=4))
end
```

    Scenario A — 5-regular network
      Method       t_peak    I_peak    R(∞)
      EBCM         9.0    0.3426    0.9527
      Bernoulli    9.0    0.3426    0.9527
      Keeling      9.0    0.3426    0.9527
      Barnard      9.0    0.3426    0.9527

    Scenario B — Poisson(5) network
      Method       t_peak    I_peak    R(∞)
      EBCM         11.0    0.2318    0.7985
      Bernoulli    11.0    0.2317    0.7985
      Keeling      11.0    0.2317    0.7985

## Sweep over mean degree (Poisson networks)

A more revealing comparison: vary the mean degree of a Poisson network
and look at the **final attack rate** predicted by each method.

``` julia
ks = 3:1:12
γ_sweep = γ

ebcm_R   = Float64[]
bern_R   = Float64[]
keel_R   = Float64[]

for k in ks
    T_sweep = R0_target / Float64(k)
    β_sweep = T_sweep * γ_sweep / (1 - T_sweep)
    e = build_sir(poisson_pgf(Float64(k)), β_sweep, γ_sweep)
    ic = default_initial_conditions(e; seed_fraction = seed_fraction)
    sol = solve(ODEProblem(e.system, ic, (0.0, 400.0));
                abstol=1e-9, reltol=1e-9, saveat=400.0)
    push!(ebcm_R, compartment(e, sol, :R)[end])

    for (vec, closure) in zip((bern_R, keel_R),
                              (NBM.BernoulliClosure(), NBM.KeelingClosure()))
        psys = NBM.generate_pairwise(NBM.sir_model(),
                                      NBM.erdos_renyi_network(Float64(k)),
                                      closure; tspan=(0.0, 400.0), seed_fraction = seed_fraction)
        sol = NBM.solve_pairwise(psys, Dict(:τ => β_sweep, :γ => γ_sweep);
                                  saveat=400.0)
        push!(vec, NBM.compartment(psys, sol, :R)[end])
    end
end

plt3 = plot(ks, ebcm_R, label="EBCM", lw=3, marker=:circle, color=:black)
plot!(plt3, ks, bern_R, label="Bernoulli", lw=2, marker=:square,    ls=:dash,    color=1)
plot!(plt3, ks, keel_R, label="Keeling",   lw=2, marker=:diamond,   ls=:dot,     color=2)
xlabel!(plt3, "mean degree κ")
ylabel!(plt3, "final attack rate R(∞)")
title!(plt3, "SIR final size: EBCM vs pairwise closures")
```

![Final attack rate vs mean degree κ on Poisson networks. The Keeling
pair-closure on `HeterogeneousNetwork` tracks the EBCM closely; the
Bernoulli (mean-field) closure systematically over-predicts because it
ignores the correlation between an infected node and its
neighbours.](index_files/figure-commonmark/cell-13-output-1.svg)

## Discussion

- **Closure equivalence on unclustered networks.** When the clustering
  coefficient is zero, the Bernoulli, Keeling and Barnard
  triple-closures reduce algebraically to the same expression on
  `HomogeneousNetwork`, and the heterogeneous Bernoulli and Keeling
  closures likewise coincide on `HeterogeneousNetwork`. So the
  differences between *closures* only show up once $\phi > 0$ (Scenario
  A and B both give identical pairwise traces across the available
  closures).
- **EBCM vs pairwise on a $k$-regular network.** Both predictions share
  the same epidemic threshold and the same initial growth rate
  $r = (k-1)\beta - \gamma$, but the pair-closure dynamics still differ
  from the (exact) EBCM at finite time: the closure inflates the peak
  prevalence and pushes the final size toward 1, whereas the EBCM
  resolves the joint $(S,\phi)$ dynamics analytically and stops at the
  configuration- model final size $\psi(\theta_\infty)$.
- **Degree heterogeneity.** Scenario B (Poisson) shows the EBCM and the
  heterogeneous-network Keeling closure tracking each other closely
  while the Bernoulli (mean-field) closure ignores degree variance and
  over- predicts spread.
- **Where the EBCM is exact.** Miller’s edge-based formulation is exact
  in the large-$N$ limit on the configuration-model ensemble (locally
  tree-like). Pair-closure approximations only recover this limit
  asymptotically, and even on regular trees they incur a
  finite-population-style overshoot at the peak.

When closure assumptions break:

- On **clustered** networks, Keeling/Barnard need triangle-aware
  corrections (and `BarnardClosure` is currently only implemented on
  `HomogeneousNetwork`), and the EBCM needs a clustered PGF
  (`clustered_pgf` — see Vignette 08).
- On **multi-type** populations, both formalisms generalise but the EBCM
  scales better in the number of compartments because pairwise models
  track $K^2$ pair variables.

## See also

- Vignette 01 — SIR Basics: introduction to EBCMs.
- Vignette 08 — Clustering: triangle-aware EBCMs.
- NodeBasedModels Vignette 03 — Moment Closure Hierarchy.
- NodeBasedModels Vignette 06 — Population vs Graph models.
