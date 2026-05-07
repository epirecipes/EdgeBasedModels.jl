# Method of Stages: Non-Exponential Distributions
Simon Frost
2026-03-30

- [Introduction](#introduction)
- [Setup](#setup)
- [Exponential vs Erlang
  distributions](#exponential-vs-erlang-distributions)
- [Building an Erlang SIR model](#building-an-erlang-sir-model)
- [Comparing exponential vs Erlang
  epidemics](#comparing-exponential-vs-erlang-epidemics)
- [Varying the number of stages](#varying-the-number-of-stages)
- [GammaApproxStage: matching a target
  CV](#gammaapproxstage-matching-a-target-cv)
- [SEIR with Erlang stages](#seir-with-erlang-stages)
- [Summary](#summary)

## Introduction

Standard edge-based compartmental models assume **exponentially
distributed** sojourn times in each disease compartment. The exponential
distribution is memoryless, leading to simple ODE systems, but it is
often unrealistic: real infectious periods tend to be concentrated
around a mean value rather than broadly spread.

The **method of stages** (also called the **linear chain trick**) offers
a simple fix. Replace a single compartment with a chain of $n$ identical
sub-compartments, each with rate $n\gamma$. The total sojourn time then
follows an **Erlang distribution** $\text{Erlang}(n, n\gamma)$, which
has:

- **Mean**: $1/\gamma$ (same as the original exponential)
- **Variance**: $1/(n\gamma^2)$ (decreasing with $n$)
- **Coefficient of variation**: $\text{CV} = 1/\sqrt{n}$

As $n \to \infty$, the Erlang distribution concentrates at the mean,
approaching a fixed (deterministic) sojourn time. Because the mean is
preserved, the basic reproduction number $R_0$ and the final epidemic
size remain unchanged — only the transient dynamics (peak height and
timing) are affected.

This approach was described by Lloyd (2001) for compartmental models and
by Sherborne et al. (2018) for edge-based models on networks.

## Setup

``` julia
using EdgeBasedModels
using ModelingToolkit
using OrdinaryDiffEq
using Symbolics
using Plots
```

``` julia
@parameters β γ κ
pgf = poisson_pgf(κ)
κ_val = 5.0
β_val = 0.5
γ_val = 0.1
ψ(x) = exp(κ_val * (x - 1))
tspan = (0.0, 120.0)
```

    (0.0, 120.0)

## Exponential vs Erlang distributions

Before building epidemic models, let us visualize how the Erlang
distribution compares to the exponential. All distributions below have
the same mean sojourn time $1/\gamma = 10$, but different shapes.

``` julia
function erlang_pdf(x, n, total_rate)
    λ = n * total_rate
    return λ^n * x^(n - 1) * exp(-λ * x) / factorial(n - 1)
end

x = range(0, 40, length = 500)
p = plot(xlabel = "Sojourn time", ylabel = "Density",
         title = "Erlang distributions (mean = $(1/γ_val))")
for (n, ls) in [(1, :solid), (2, :dash), (5, :dashdot), (20, :dot)]
    label = n == 1 ? "Exp(γ)  [CV=1.00]" : "Erlang($n, $(n)γ)  [CV=$(round(1/√n; digits=2))]"
    plot!(p, x, erlang_pdf.(x, n, γ_val), label = label, linewidth = 2, linestyle = ls)
end
vline!(p, [1 / γ_val], label = "Mean = 1/γ", color = :black, linestyle = :dash, linewidth = 1)
p
```

<div id="fig-distributions">

![](index_files/figure-commonmark/fig-distributions-output-1.svg)

Figure 1: Erlang distributions with the same mean (1/γ = 10) but
increasing shape parameter n. As n increases, the distribution
concentrates around the mean.

</div>

The exponential ($n = 1$) has $\text{CV} = 1$ — its standard deviation
equals its mean. As $n$ increases, the distribution narrows: by
$n = 20$, the CV is only $0.22$, and the density is tightly concentrated
around the mean of $10$.

## Building an Erlang SIR model

EdgeBasedModels provides `ErlangStage` to define a stage with
Erlang-distributed sojourn time, and `expand_erlang_stages` to convert
it into a standard `DiseaseProgression`.

An `ErlangStage(:I, n, γ; transmission_rate = β)` represents an
infectious period that is Erlang-distributed with shape $n$ and overall
rate $\gamma$. When expanded, it produces $n$ sub-stages
$I_1, I_2, \ldots, I_n$, each inheriting the transmission rate $\beta$
and connected by transitions at rate $n\gamma$:

$$I_1 \xrightarrow{n\gamma} I_2 \xrightarrow{n\gamma} \cdots \xrightarrow{n\gamma} I_n \xrightarrow{n\gamma} R$$

``` julia
# Standard exponential SIR (n = 1)
model_exp = build_sir(pgf, β, γ; form = :expanded)
println("Exponential SIR: ", length(ModelingToolkit.equations(model_exp.system)), " ODEs")
```

    Exponential SIR: 4 ODEs

``` julia
# Erlang SIR with n = 5 sub-stages for the infectious period
n_stages = 5
erlang_I = ErlangStage(:I, n_stages, γ; transmission_rate = β)
prog_erlang = expand_erlang_stages(
    [erlang_I, DiseaseStage(:R)],
    [DiseaseTransition(:I, :R, n_stages * γ)];
    entry = :I,
)
model_erlang = build_edge_system(
    StaticConfigurationModel(pgf, prog_erlang);
    form = :expanded,
)
println("Erlang SIR (n=$n_stages): ", length(ModelingToolkit.equations(model_erlang.system)), " ODEs")
```

    Erlang SIR (n=5): 8 ODEs

> [!NOTE]
>
> The exit transition from `I` to `R` must use the sub-stage rate
> $n\gamma$, not the overall rate $\gamma$. This ensures all sub-stages
> — including the last one — have identical sojourn-time distributions,
> which is required for the total to be Erlang.

Let us inspect the expanded ODE system:

``` julia
for eq in ModelingToolkit.equations(model_erlang.system)
    println("  ", eq)
end
```

      Differential(t, 1)(R(t)) ~ 5(1 - exp((-1 + θ(t))*κ) - R(t))*γ
      Differential(t, 1)(phi_R(t)) ~ 5phi_I_5(t)*γ
      Differential(t, 1)(phi_I_5(t)) ~ 5phi_I_4(t)*γ - phi_I_5(t)*β - 5phi_I_5(t)*γ
      Differential(t, 1)(phi_I_4(t)) ~ 5phi_I_3(t)*γ - phi_I_4(t)*β - 5phi_I_4(t)*γ
      Differential(t, 1)(phi_I_3(t)) ~ -phi_I_3(t)*β - 5phi_I_3(t)*γ + 5phi_I_2(t)*γ
      Differential(t, 1)(phi_I_2(t)) ~ -phi_I_2(t)*β - 5phi_I_2(t)*γ + 5phi_I_1(t)*γ
      Differential(t, 1)(phi_I_1(t)) ~ -phi_I_1(t)*β - 5phi_I_1(t)*γ + phi_S(t)*(phi_I_3(t) + phi_I_2(t) + phi_I_4(t) + phi_I_5(t) + phi_I_1(t))*β*κ
      Differential(t, 1)(θ(t)) ~ -(phi_I_3(t) + phi_I_2(t) + phi_I_4(t) + phi_I_5(t) + phi_I_1(t))*β

## Comparing exponential vs Erlang epidemics

Both models have the same mean infectious period ($1/\gamma$) and
per-edge transmission rate ($\beta$), so $R_0$ is identical. Let us
compare the dynamics.

``` julia
# Solve exponential SIR
ic_exp = default_initial_conditions(model_exp)
prob_exp = ODEProblem(
    model_exp.system,
    merge(ic_exp, Dict(β => β_val, γ => γ_val, κ => κ_val)),
    tspan,
)
sol_exp = solve(prob_exp, Tsit5(); saveat = 0.5)

state_names_exp = string.(ModelingToolkit.unknowns(model_exp.system))
θ_idx_exp = findfirst(s -> startswith(s, "θ"), state_names_exp)
R_idx_exp = findfirst(s -> startswith(s, "R"), state_names_exp)
θ_exp = sol_exp[θ_idx_exp, :]
R_exp = sol_exp[R_idx_exp, :]
S_exp = ψ.(θ_exp)
I_exp = 1.0 .- S_exp .- R_exp
```

    241-element Vector{Float64}:
     0.00498752080731768
     0.0047442765291545504
     0.0045128954494401685
     0.004292798828178263
     0.004083436019791223
     0.00388428450359447
     0.0036948461339441543
     0.0035146465844452203
     0.003343234715160879
     0.0031801816282027466
     ⋮
     6.211918420536561e-8
     6.187977976811893e-8
     6.153985682762902e-8
     6.103506919926532e-8
     6.029835240145553e-8
     5.925992364961413e-8
     5.784728186047916e-8
     5.598520765124487e-8
     5.359576333782701e-8

``` julia
# Solve Erlang SIR
ic_erlang = default_initial_conditions(model_erlang)
prob_erlang = ODEProblem(
    model_erlang.system,
    merge(ic_erlang, Dict(β => β_val, γ => γ_val, κ => κ_val)),
    tspan,
)
sol_erlang = solve(prob_erlang, Tsit5(); saveat = 0.5)

state_names_erlang = string.(ModelingToolkit.unknowns(model_erlang.system))
θ_idx_erl = findfirst(s -> startswith(s, "θ"), state_names_erlang)
R_idx_erl = findfirst(s -> startswith(s, "R"), state_names_erlang)
θ_erl = sol_erlang[θ_idx_erl, :]
R_erl = sol_erlang[R_idx_erl, :]
S_erl = ψ.(θ_erl)
I_erl = 1.0 .- S_erl .- R_erl
```

    241-element Vector{Float64}:
      0.00498752080731768
      0.0038842850659281617
      0.003025084461361214
      0.002355934190755476
      0.0018347991295662963
      0.001428942517067842
      0.00111285684093625
      0.0008666800893511618
      0.000674998253958393
      0.0005256350977320993
      ⋮
     -3.864336028561871e-6
     -3.6590918507913364e-6
     -2.822148442652682e-6
     -1.4574009076602154e-6
      2.5330181381826716e-7
      2.0501569445649515e-6
      3.595407870505933e-6
      4.473344140716422e-6
      4.1903014674207414e-6

``` julia
plot(sol_exp.t, I_exp, label = "I (exponential)", linewidth = 2, color = :red)
plot!(sol_erlang.t, I_erl, label = "I (Erlang, n=5)", linewidth = 2, color = :blue)
plot!(sol_exp.t, R_exp, label = "R (exponential)", linewidth = 1, color = :red,
      linestyle = :dash)
plot!(sol_erlang.t, R_erl, label = "R (Erlang, n=5)", linewidth = 1, color = :blue,
      linestyle = :dash)
xlabel!("Time")
ylabel!("Fraction of population")
title!("Exponential vs Erlang SIR (β=$β_val, γ=$γ_val)")
```

<div id="fig-exp-vs-erlang">

![](index_files/figure-commonmark/fig-exp-vs-erlang-output-1.svg)

Figure 2: Exponential vs Erlang (n=5) SIR. The Erlang model produces a
sharper, higher, earlier peak but converges to the same final size.

</div>

The final sizes converge to the same value — both epidemics infect the
same total fraction of the population. However, the Erlang model
produces a sharper, higher peak that arrives earlier. This is because a
more concentrated infectious period means individuals transmit infection
over a narrower time window, leading to more synchronised dynamics.

## Varying the number of stages

Let us sweep over $n = 1, 2, 5, 10, 20$ to see how the epidemic curve
changes as the infectious period distribution narrows.

``` julia
p = plot(xlabel = "Time", ylabel = "Fraction infected",
         title = "SIR with Erlang infectious period (varying n)")

for n in [1, 2, 5, 10, 20]
    if n == 1
        model_n = build_sir(pgf, β, γ; form = :expanded)
    else
        erl = ErlangStage(:I, n, γ; transmission_rate = β)
        prog_n = expand_erlang_stages(
            [erl, DiseaseStage(:R)],
            [DiseaseTransition(:I, :R, n * γ)];
            entry = :I,
        )
        model_n = build_edge_system(
            StaticConfigurationModel(pgf, prog_n);
            form = :expanded,
        )
    end

    ic_n = default_initial_conditions(model_n)
    prob_n = ODEProblem(
        model_n.system,
        merge(ic_n, Dict(β => β_val, γ => γ_val, κ => κ_val)),
        tspan,
    )
    sol_n = solve(prob_n, Tsit5(); saveat = 0.5)

    sn = string.(ModelingToolkit.unknowns(model_n.system))
    θ_n = sol_n[findfirst(s -> startswith(s, "θ"), sn), :]
    R_n = sol_n[findfirst(s -> startswith(s, "R"), sn), :]
    I_n = 1.0 .- ψ.(θ_n) .- R_n

    cv = round(1 / √n; digits = 2)
    plot!(p, sol_n.t, I_n, label = "n=$n (CV=$cv)", linewidth = 2)
end
p
```

<div id="fig-varying-n">

![](index_files/figure-commonmark/fig-varying-n-output-1.svg)

Figure 3: Effect of the number of Erlang stages on the infected curve.
More stages → sharper peak, same final size.

</div>

As $n$ increases, the epidemic peak becomes taller and narrower. The
curve approaches the limiting behaviour of a model with a fixed
infectious period of exactly $1/\gamma$. All curves converge to the same
final size, confirming that $R_0$ — and hence the final size — depends
only on the mean infectious period, not its variance.

## GammaApproxStage: matching a target CV

Instead of choosing $n$ directly, it can be more natural to specify the
desired **coefficient of variation** (CV) of the sojourn time.
`GammaApproxStage` does this automatically by selecting:

$$n = \text{round}(1 / \text{CV}^2)$$

This approximates a Gamma distribution with the specified mean and CV
using an Erlang distribution with the closest integer shape parameter.

``` julia
# Demonstrate the mapping from CV to number of sub-stages
println("CV → n sub-stages (mean sojourn = $(1/γ_val))")
println("─" ^ 35)
for cv in [1.0, 0.7, 0.5, 0.3, 0.2, 0.1]
    stage = GammaApproxStage(:I, 1 / γ_val, cv; transmission_rate = β_val)
    actual_cv = round(1 / √stage.n_substages; digits = 3)
    println("  CV = $cv → n = $(stage.n_substages)  (actual CV = $actual_cv)")
end
```

    CV → n sub-stages (mean sojourn = 10.0)
    ───────────────────────────────────
      CV = 1.0 → n = 1  (actual CV = 1.0)
      CV = 0.7 → n = 2  (actual CV = 0.707)
      CV = 0.5 → n = 4  (actual CV = 0.5)
      CV = 0.3 → n = 11  (actual CV = 0.302)
      CV = 0.2 → n = 25  (actual CV = 0.2)
      CV = 0.1 → n = 100  (actual CV = 0.1)

> [!TIP]
>
> Use `GammaApproxStage` when you have empirical estimates of the mean
> and CV of the infectious period (e.g., from clinical data), and
> `ErlangStage` when you want direct control over the number of
> sub-stages.

``` julia
p = plot(xlabel = "Time", ylabel = "Fraction infected",
         title = "SIR parameterised by CV of infectious period")

for cv in [1.0, 0.5, 0.3, 0.2]
    # Use GammaApproxStage to determine n, then build with symbolic params
    n = GammaApproxStage(:I, 1 / γ_val, cv).n_substages
    erl_cv = ErlangStage(:I, n, γ; transmission_rate = β)
    prog_cv = expand_erlang_stages(
        [erl_cv, DiseaseStage(:R)],
        [DiseaseTransition(:I, :R, n * γ)];
        entry = :I,
    )
    model_cv = build_edge_system(
        StaticConfigurationModel(pgf, prog_cv);
        form = :expanded,
    )
    ic_cv = default_initial_conditions(model_cv)
    prob_cv = ODEProblem(
        model_cv.system,
        merge(ic_cv, Dict(β => β_val, γ => γ_val, κ => κ_val)),
        tspan,
    )
    sol_cv = solve(prob_cv, Tsit5(); saveat = 0.5)

    sn = string.(ModelingToolkit.unknowns(model_cv.system))
    θ_cv = sol_cv[findfirst(s -> startswith(s, "θ"), sn), :]
    R_cv = sol_cv[findfirst(s -> startswith(s, "R"), sn), :]
    I_cv = 1.0 .- ψ.(θ_cv) .- R_cv

    plot!(p, sol_cv.t, I_cv, label = "CV=$cv (n=$n)", linewidth = 2)
end
p
```

<div id="fig-cv-sweep">

![](index_files/figure-commonmark/fig-cv-sweep-output-1.svg)

Figure 4: Epidemic curves parameterised by the CV of the infectious
period.

</div>

## SEIR with Erlang stages

Both the latent ($E$) and infectious ($I$) periods can independently use
Erlang distributions. Here we model an SEIR epidemic with
Erlang-distributed $E$ ($n_E = 3$ sub-stages) and Erlang-distributed $I$
($n_I = 5$ sub-stages):

$$S \xrightarrow{\text{infection}} E_1 \to E_2 \to E_3 \xrightarrow{} I_1 \to I_2 \to \cdots \to I_5 \xrightarrow{} R$$

``` julia
@parameters σ
n_E = 3
n_I = 5

erlang_E = ErlangStage(:E, n_E, σ; transmission_rate = 0)
erlang_I_seir = ErlangStage(:I, n_I, γ; transmission_rate = β)

prog_seir_erlang = expand_erlang_stages(
    [erlang_E, erlang_I_seir, DiseaseStage(:R)],
    [
        DiseaseTransition(:E, :I, n_E * σ),
        DiseaseTransition(:I, :R, n_I * γ),
    ];
    entry = :E,
)

model_seir_erlang = build_edge_system(
    StaticConfigurationModel(pgf, prog_seir_erlang);
    form = :expanded,
)
println("Erlang SEIR: ", length(ModelingToolkit.equations(model_seir_erlang.system)), " ODEs")
```

    Erlang SEIR: 11 ODEs

For comparison, the standard exponential SEIR:

``` julia
model_seir_exp = build_seir(pgf, σ, β, γ)
println("Exponential SEIR: ", length(ModelingToolkit.equations(model_seir_exp.system)), " ODEs")
```

    Exponential SEIR: 5 ODEs

``` julia
σ_val = 0.2  # mean latent period = 5 days

# Solve exponential SEIR
ic_seir_exp = default_initial_conditions(model_seir_exp)
prob_seir_exp = ODEProblem(
    model_seir_exp.system,
    merge(ic_seir_exp, Dict(β => β_val, γ => γ_val, σ => σ_val, κ => κ_val)),
    tspan,
)
sol_seir_exp = solve(prob_seir_exp, Tsit5(); saveat = 0.5)

sn_se = string.(ModelingToolkit.unknowns(model_seir_exp.system))
θ_se = sol_seir_exp[findfirst(s -> startswith(s, "θ"), sn_se), :]
R_se = sol_seir_exp[findfirst(s -> startswith(s, "R"), sn_se), :]
S_se = ψ.(θ_se)
EI_se = 1.0 .- S_se .- R_se
```

    241-element Vector{Float64}:
     0.00498752080731768
     0.0047442765271789675
     0.0045128954484631376
     0.004292798850391892
     0.004083435971888061
     0.0038842843802593743
     0.003694846041310686
     0.0035146465838806424
     0.00334323494085032
     0.0031801816899232407
     ⋮
     5.818145546593323e-8
     5.6189005359121025e-8
     5.427839099014786e-8
     5.2420291235359684e-8
     5.058429138841275e-8
     4.8738883158538915e-8
     4.685146467141299e-8
     4.488834047088747e-8
     4.281472151552307e-8

``` julia
# Solve Erlang SEIR
ic_seir_erl = default_initial_conditions(model_seir_erlang)
prob_seir_erl = ODEProblem(
    model_seir_erlang.system,
    merge(ic_seir_erl, Dict(β => β_val, γ => γ_val, σ => σ_val, κ => κ_val)),
    tspan,
)
sol_seir_erl = solve(prob_seir_erl, Tsit5(); saveat = 0.5)

sn_sel = string.(ModelingToolkit.unknowns(model_seir_erlang.system))
θ_sel = sol_seir_erl[findfirst(s -> startswith(s, "θ"), sn_sel), :]
R_sel = sol_seir_erl[findfirst(s -> startswith(s, "R"), sn_sel), :]
S_sel = ψ.(θ_sel)
EI_sel = 1.0 .- S_sel .- R_sel
```

    241-element Vector{Float64}:
      0.00498752080731768
      0.002131732043857496
      0.0009111445611480057
      0.0003894353537581231
      0.00016646603946954795
      7.119891080761137e-5
      3.036189659632628e-5
      1.295819578973293e-5
      5.606061643502816e-6
      2.3290472590887026e-6
      ⋮
     -3.94197407106462e-6
     -3.343180877428756e-6
      3.6093133108511255e-6
      3.6599397101747325e-6
     -3.3783189967266647e-6
     -3.912234521440475e-6
      2.738193365969463e-6
      4.611537840814271e-6
      1.9722442448520325e-6

``` julia
plot(sol_seir_exp.t, EI_se, label = "E+I (exponential)", linewidth = 2, color = :red)
plot!(sol_seir_erl.t, EI_sel, label = "E+I (Erlang)", linewidth = 2, color = :blue)
plot!(sol_seir_exp.t, R_se, label = "R (exponential)", linewidth = 1, color = :red,
      linestyle = :dash)
plot!(sol_seir_erl.t, R_sel, label = "R (Erlang)", linewidth = 1, color = :blue,
      linestyle = :dash)
xlabel!("Time")
ylabel!("Fraction of population")
title!("Exponential vs Erlang SEIR (nE=$n_E, nI=$n_I)")
```

<div id="fig-seir-erlang">

![](index_files/figure-commonmark/fig-seir-erlang-output-1.svg)

Figure 5: Exponential vs Erlang SEIR. Erlang stages produce sharper
dynamics for both the latent and infectious periods.

</div>

The Erlang SEIR produces a sharper epidemic curve with a higher, earlier
peak. As with SIR, the final epidemic size is the same for both models
since it depends only on $R_0$ and the degree distribution.

## Summary

- The **method of stages** replaces a single compartment with $n$
  identical sub-compartments, giving an Erlang-distributed sojourn time
  with the same mean but reduced variance.
- **Same mean → same $R_0$ and final epidemic size**; different variance
  → different peak timing and height.
- More stages → sharper, more peaked epidemics, approaching the
  fixed-duration limit.
- `ErlangStage(name, n, γ)` creates an Erlang stage with $n$ sub-stages
  and overall rate $\gamma$.
- `GammaApproxStage(name, mean, cv)` automatically selects
  $n = \text{round}(1/\text{CV}^2)$ to match a target coefficient of
  variation.
- `expand_erlang_stages` converts Erlang stages into a standard
  `DiseaseProgression` compatible with the full edge-based framework.
- Multiple compartments ($E$, $I$, etc.) can each independently use
  Erlang distributions.
