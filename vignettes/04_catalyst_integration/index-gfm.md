

- [Catalyst.jl Integration](#catalystjl-integration)
  - [Introduction](#introduction)
  - [Setup](#setup)
  - [SIR via Catalyst](#sir-via-catalyst)
    - [Building and solving the model](#building-and-solving-the-model)
    - [Comparison with `build_sir`](#comparison-with-build_sir)
  - [SEIR via Catalyst](#seir-via-catalyst)
  - [Custom multi-stage model via
    Catalyst](#custom-multi-stage-model-via-catalyst)
    - [Symbolic $R_0$](#symbolic-r_0)
  - [Simulation validation](#simulation-validation)
  - [Benefits of the Catalyst
    adapter](#benefits-of-the-catalyst-adapter)

# Catalyst.jl Integration

Simon Frost 2026-05-14

- [Introduction](#introduction)
- [Setup](#setup)
- [SIR via Catalyst](#sir-via-catalyst)
  - [Building and solving the model](#building-and-solving-the-model)
  - [Comparison with `build_sir`](#comparison-with-build_sir)
- [SEIR via Catalyst](#seir-via-catalyst)
- [Custom multi-stage model via
  Catalyst](#custom-multi-stage-model-via-catalyst)
  - [Symbolic $R_0$](#symbolic-r_0)
- [Simulation validation](#simulation-validation)
- [Benefits of the Catalyst adapter](#benefits-of-the-catalyst-adapter)

## Introduction

For users already familiar with
[Catalyst.jl](https://github.com/SciML/Catalyst.jl)’s reaction network
DSL, EdgeBasedModels.jl provides a convenient bridge: the
`progression_from_catalyst` function converts a Catalyst
`ReactionSystem` into a `DiseaseProgression` that can be plugged
directly into any edge-based configuration model. This lets you leverage
Catalyst’s expressive chemical kinetics notation for specifying disease
compartment transitions, while EdgeBasedModels handles the network
epidemic equations automatically.

## Setup

``` julia
using EdgeBasedModels
using ModelingToolkit
using Symbolics
using OrdinaryDiffEq
using Plots
import Catalyst
```

We use `import Catalyst` rather than `using Catalyst` to avoid namespace
collisions with ModelingToolkit (both packages export symbols like
`@parameters`).

## SIR via Catalyst

In the standard edge-based SIR model, the disease progression is simply
$I \xrightarrow{\gamma} R$. We can express this as a Catalyst reaction
network:

``` julia
@parameters β γ γ_cat
rn = Catalyst.@reaction_network begin
    γ_cat, I --> R
end; nothing
```

Now we convert this `ReactionSystem` into a `DiseaseProgression`. The
`transmission_rates` dictionary specifies which compartments can
transmit infection across an edge, and at what rate:

``` julia
progression = progression_from_catalyst(
    rn;
    transmission_rates = Dict(:I => β, :R => 0),
    entry = :I
)
```

    DiseaseProgression(:S, :I, DiseaseStage[DiseaseStage(:I, β), DiseaseStage(:R, 0)], DiseaseTransition[DiseaseTransition(:I, :R, γ_cat)])

The `entry = :I` argument tells the model that newly infected nodes
enter the $I$ compartment (as opposed to an exposed class).

### Building and solving the model

We pair the progression with a Poisson degree distribution to build a
`StaticConfigurationModel`:

``` julia
@parameters κ
pgf = poisson_pgf(κ)
scm = StaticConfigurationModel(pgf, progression)
result = build_edge_system(scm)
```

    EdgeModelSystem(Model edge_based_model:
    Equations (5):
      5 standard: see equations(edge_based_model)
    Unknowns (5): see unknowns(edge_based_model)
      pop_R(t)
      pop_I(t)
      phi_R(t)
      phi_I(t)
      ⋮
    Parameters (4): see parameters(edge_based_model)
      κ
      ρ
      β
      γ_cat
    Observed (3): see observed(edge_based_model), Dict{Symbol, Any}(:R => pop_R(t), :φ_I => phi_I(t), :pop_I => pop_I(t), :pop_R => pop_R(t), :φ_R => phi_R(t), :θ => θ(t)), Dict{Symbol, Any}(:I => I(t), :φ_S => phi_S(t), :S => S(t), :edge_hazard => phi_I(t)*β, :excess_hazard => phi_I(t)*β*κ), Dict{Symbol, Any}(:seed_groups => Any[(entry = pop_I(t), susceptible_expr = exp((-1 + θ(t))*κ))], :rho_param => ρ, :edge_seed_groups => Any[(entry = phi_I(t), theta = θ(t), phi_S_expr = (exp((-1 + θ(t))*κ)*(1 - ρ)) / exp(0))]))

Set up numeric parameters and solve:

> \[!NOTE\]
>
> **$R_0=2$ anchor.** For the Poisson($\kappa=10$) SIR example, $T=2/10$
> and with $\gamma=0.25$ the comparable per-edge rate is $\beta=0.0625$.
> We seed 1% of the population.

``` julia
κ_val = 10.0
γ_val = 0.25
R0_target = 2.0
T_val = R0_target / κ_val
β_val = T_val * γ_val / (1 - T_val)
ε = 0.01
tspan = (0.0, 40.0)

ic = default_initial_conditions(result; ε = ε)
params = Dict(κ => κ_val, β => β_val, γ_cat => γ_val)
prob = ODEProblem(result.system, merge(ic, params), tspan)
sol = solve(prob, Tsit5())
```

    retcode: Success
    Interpolation: specialized 4th order "free" interpolation
    t: 17-element Vector{Float64}:
      0.0
      0.09110688895572071
      0.5464977499579222
      1.3639750905714887
      2.4358712145705024
      3.819573557953353
      5.549782633207902
      7.741359444944836
     10.361491907175683
     13.261960455673645
     16.74345967150911
     20.34204427921308
     24.501337657464553
     28.96873925624184
     33.7077794456598
     38.24231483234168
     40.0
    u: 17-element Vector{Vector{Float64}}:
     [0.0, 0.01, 0.0, 0.010000000000000009, 1.0]
     [0.00023162286685069586, 0.010339870914217042, 0.0002309732511789605, 0.010282777217094046, 0.9999422566872053]
     [0.0015105347512930213, 0.012162756886651385, 0.0014869184741195078, 0.011814643545295031, 0.9996282703814702]
     [0.004377154768673389, 0.016027986228427847, 0.004226346418613679, 0.015122207973834149, 0.9989434133953466]
     [0.009502040650055719, 0.02252234184876684, 0.008999217559171888, 0.020775360549857704, 0.9977501956102071]
     [0.019164859891338808, 0.03399767621529163, 0.01783099598097689, 0.030873791130409327, 0.9955422510047558]
     [0.038053859000017114, 0.05461394951854508, 0.03487850239097236, 0.04906968052984674, 0.9912803744022569]
     [0.07763095975449598, 0.09180464948086249, 0.07023970154433137, 0.08163598230494423, 0.9824400746139171]
     [0.15512949324070988, 0.14477574662660353, 0.138595823422467, 0.12666046058922964, 0.9653510441443832]
     [0.2768382093965426, 0.18472909540394505, 0.2436146103221423, 0.1570490418978097, 0.9390963474194644]
     [0.43831076432928434, 0.17661155614704308, 0.3777009408615125, 0.14279614439943666, 0.9055747647846218]
     [0.5772464737007437, 0.12959004146676004, 0.4867928063362821, 0.09834550724715099, 0.8783017984159295]
     [0.6826581074742273, 0.07568564425106337, 0.5640776745798669, 0.05324665850045702, 0.8589805813550333]
     [0.7442379064865149, 0.038131281481120535, 0.6059672724623802, 0.024910097389660157, 0.848508181884405]
     [0.775603460468506, 0.017322283399000108, 0.6258590556956601, 0.010601924247931056, 0.843535236076085]
     [0.7892206780848599, 0.007880545128275357, 0.6340077606976434, 0.004591522341081063, 0.8414980598255892]
     [0.7921976077411619, 0.005774772713549698, 0.6357289180967921, 0.0033112328337215526, 0.8410677704758021]

``` julia
κ_val_num = 10.0
ψ(x) = exp(κ_val_num * (x - 1))
θ_vals = compartment(sol, result, :θ)
S_vals = compartment(sol, result, :S)
R_vals = compartment(sol, result, :R)
I_vals = compartment(sol, result, :I)

plot(sol.t, S_vals, label="S", lw=2)
plot!(sol.t, I_vals, label="I", lw=2)
plot!(sol.t, R_vals, label="R", lw=2)
xlabel!("Time")
ylabel!("Fraction")
title!("SIR (Catalyst-defined progression)")
```

<div id="fig-sir-catalyst">

![](index_files/figure-commonmark/fig-sir-catalyst-output-1.svg)

Figure 1: Figure 1: SIR epidemic on a Poisson network, defined via
Catalyst.jl.

</div>

### Comparison with `build_sir`

To verify that the Catalyst pathway produces identical results, we can
compare against the built-in `build_sir`:

``` julia
result_builtin = build_sir(pgf, β, γ)
ic_builtin = default_initial_conditions(result_builtin; ε = ε)
params_builtin = Dict(κ => κ_val, β => β_val, γ => γ_val)
prob_builtin = ODEProblem(result_builtin.system, merge(ic_builtin, params_builtin), tspan)
sol_builtin = solve(prob_builtin, Tsit5())

θ_builtin = compartment(sol_builtin, result_builtin, :θ)
S_builtin = ψ.(θ_builtin)
```

    17-element Vector{Float64}:
     1.0
     0.9994227335544771
     0.9962896044070031
     0.989489756643127
     0.9777531497764266
     0.9564014857164544
     0.9164972099261603
     0.8389541236050947
     0.7071662030849121
     0.543874625888061
     0.3889702750044135
     0.2961225127566232
     0.24409587843889705
     0.21982617003511232
     0.2091617005661999
     0.20494381681073356
     0.20406385993200743

``` julia
R_builtin = compartment(sol_builtin, result_builtin, :R)
I_builtin = 1.0 .- S_builtin .- R_builtin

plot(sol.t, S_vals, label="S (Catalyst)", lw=2, color=1)
plot!(sol_builtin.t, S_builtin, label="S (built-in)", lw=2, ls=:dash, color=1)
plot!(sol.t, I_vals, label="I (Catalyst)", lw=2, color=2)
plot!(sol_builtin.t, I_builtin, label="I (built-in)", lw=2, ls=:dash, color=2)
plot!(sol.t, R_vals, label="R (Catalyst)", lw=2, color=3)
plot!(sol_builtin.t, R_builtin, label="R (built-in)", lw=2, ls=:dash, color=3)
xlabel!("Time")
ylabel!("Fraction")
title!("Catalyst vs built-in SIR")
```

<div id="fig-sir-comparison">

![](index_files/figure-commonmark/fig-sir-comparison-output-1.svg)

Figure 2: Figure 2: Comparison of Catalyst-defined SIR (solid) and
built-in build_sir (dashed). The curves overlap exactly.

</div>

The solid and dashed lines overlap perfectly, confirming that both
approaches produce the same ODE system.

## SEIR via Catalyst

The SEIR model adds a latent (exposed) period before infectiousness. The
compartment transitions are:

$$E \xrightarrow{\sigma} I \xrightarrow{\gamma} R$$

In Catalyst notation:

``` julia
@parameters σ_cat
rn_seir = Catalyst.@reaction_network begin
    σ_cat, E --> I
    γ_cat, I --> R
end; nothing
```

Converting to a `DiseaseProgression`, we specify that the $E$ and $R$
compartments do not transmit ($\beta = 0$), only $I$ does:

``` julia
progression_seir = progression_from_catalyst(
    rn_seir;
    transmission_rates = Dict(:E => 0, :I => β, :R => 0),
    entry = :E
)
```

    DiseaseProgression(:S, :E, DiseaseStage[DiseaseStage(:E, 0), DiseaseStage(:I, β), DiseaseStage(:R, 0)], DiseaseTransition[DiseaseTransition(:E, :I, σ_cat), DiseaseTransition(:I, :R, γ_cat)])

``` julia
scm_seir = StaticConfigurationModel(pgf, progression_seir)
result_seir = build_edge_system(scm_seir)
```

    EdgeModelSystem(Model edge_based_model:
    Equations (7):
      7 standard: see equations(edge_based_model)
    Unknowns (7): see unknowns(edge_based_model)
      pop_R(t)
      pop_I(t)
      pop_E(t)
      phi_R(t)
      ⋮
    Parameters (5): see parameters(edge_based_model)
      κ
      ρ
      β
      σ_cat
      ⋮
    Observed (3): see observed(edge_based_model), Dict{Symbol, Any}(:R => pop_R(t), :φ_I => phi_I(t), :pop_I => pop_I(t), :pop_R => pop_R(t), :φ_R => phi_R(t), :θ => θ(t), :φ_E => phi_E(t), :pop_E => pop_E(t)), Dict{Symbol, Any}(:I => I(t), :φ_S => phi_S(t), :S => S(t), :edge_hazard => phi_I(t)*β, :excess_hazard => phi_I(t)*β*κ), Dict{Symbol, Any}(:seed_groups => Any[(entry = pop_E(t), susceptible_expr = exp((-1 + θ(t))*κ))], :rho_param => ρ, :edge_seed_groups => Any[(entry = phi_E(t), theta = θ(t), phi_S_expr = (exp((-1 + θ(t))*κ)*(1 - ρ)) / exp(0))]))

Let’s inspect the system. The SEIR edge-based model has 7 differential
equations: $\theta$, $\phi_E$, $\phi_I$, $\phi_R$, plus per-stage
population trackers ($\mathrm{pop}_E$, $\mathrm{pop}_I$,
$\mathrm{pop}_R$), plus algebraic observables for $\phi_S$, $S$, $E$,
$I$, and $R$:

``` julia
println("Number of equations: ", length(ModelingToolkit.equations(result_seir.system)))
println("\nVariables: ", keys(result_seir.variables))
println("\nObservables: ", keys(result_seir.observables))
```

    Number of equations: 7

    Variables: [:R, :φ_I, :pop_I, :pop_R, :φ_R, :θ, :φ_E, :pop_E]

    Observables: [:I, :φ_S, :S, :edge_hazard, :excess_hazard]

Solve and plot:

``` julia
σ_val = 0.2

ic_seir = default_initial_conditions(result_seir; ε = ε)
params_seir = Dict(κ => κ_val, β => β_val, σ_cat => σ_val, γ_cat => γ_val)
prob_seir = ODEProblem(result_seir.system, merge(ic_seir, params_seir), tspan)
sol_seir = solve(prob_seir, Tsit5())
```

    retcode: Success
    Interpolation: specialized 4th order "free" interpolation
    t: 19-element Vector{Float64}:
      0.0
      0.098592381985361
      0.42655546536664324
      0.917295230518782
      1.5185043184797968
      2.2956054631883225
      3.238351229993599
      4.39526875860142
      5.789967169199533
      7.488917416356898
      9.573501642200249
     12.198470204596731
     15.70219936684111
     20.053534055868617
     24.197820877163963
     28.80107760261609
     33.44590762368407
     38.31081304157407
     40.0
    u: 19-element Vector{Vector{Float64}}:
     [0.0, 0.0, 0.01, 0.0, 0.0, 0.010000000000000009, 1.0]
     [2.3947132769561177e-6, 0.00019289752158125747, 0.009810622538059033, 2.38981437834139e-6, 0.00019230496688528705, 0.009810622538059042, 0.9999994025464054]
     [4.27581734879625e-5, 0.0007779470965802289, 0.009284192061745182, 4.238500600642627e-5, 0.0007677240125601591, 0.00928419206174519, 0.9999894037484984]
     [0.0001850796439820982, 0.0015182627500049143, 0.008746221809116002, 0.00018168335878542872, 0.0014762381955052278, 0.00874622180911601, 0.9999545791603037]
     [0.00047095384147178345, 0.0022602451514632813, 0.008399395331914973, 0.00045706683116853185, 0.0021598654539744023, 0.00839939533191498, 0.999885733292208]
     [0.0009881995169844626, 0.0030373249689153578, 0.008312901232154024, 0.0009459360993976816, 0.0028431043616527225, 0.00831290123215403, 0.9997635159751507]
     [0.0017982276655028665, 0.0038142834592989326, 0.008574743739808023, 0.0016954081152292298, 0.003493250980765266, 0.008574743739808027, 0.9995761479711928]
     [0.0030235700473812627, 0.0046449526416024525, 0.00924865576279498, 0.002804629109956706, 0.004162736301537837, 0.009248655762794983, 0.9992988427225109]
     [0.004808674647319991, 0.005592919575037304, 0.010398753367488953, 0.0043877545887952545, 0.004916900986363235, 0.010398753367488953, 0.9989030613528013]
     [0.007435062858319723, 0.006789540353966164, 0.012164088491934762, 0.0066771146813260724, 0.005878209860628305, 0.012164088491934762, 0.9983307213296686]
     [0.01139215136688713, 0.008437449093584662, 0.014811894076500118, 0.01008216102027056, 0.007226899185133601, 0.014811894076500118, 0.9974794597449325]
     [0.01771785732201631, 0.010929102349780584, 0.018931833850011837, 0.015479024832775785, 0.009298178630827169, 0.018931833850011837, 0.9961302437918061]
     [0.029073462428966045, 0.015198948288486063, 0.025979231613290545, 0.02511638954609047, 0.012876923784839026, 0.025979231613290545, 0.9937209026134775]
     [0.049301972767027344, 0.022366958811077222, 0.0375090922418668, 0.042224129124753464, 0.01888877017216274, 0.0375090922418668, 0.9894439677188117]
     [0.07694787449418125, 0.03135621472996431, 0.05129546133404554, 0.06553056908454877, 0.026390877868459606, 0.05129546133404554, 0.9836173577288629]
     [0.11986488755150423, 0.04355185818853497, 0.06856862760504812, 0.10155846960637932, 0.036468658732065055, 0.06856862760504812, 0.9746103825984053]
     [0.17815334418733228, 0.05682073739405983, 0.0849327534692118, 0.15019006798840479, 0.047236496595886135, 0.0849327534692118, 0.9624524830028989]
     [0.25491710885403235, 0.06879574415805678, 0.09601303187368652, 0.21368164561821631, 0.05661079598931878, 0.09601303187368652, 0.946579588595446]
     [0.28463430485398733, 0.0718220067402375, 0.09761144561058473, 0.2380839332850149, 0.058851394987956246, 0.09761144561058473, 0.9404790166787463]

``` julia
θ_seir = compartment(sol_seir, result_seir, :θ)
S_seir = ψ.(θ_seir)
R_seir = compartment(sol_seir, result_seir, :R)
I_seir = 1.0 .- S_seir .- R_seir

plot(sol_seir.t, S_seir, label="S", lw=2)
plot!(sol_seir.t, I_seir, label="E + I", lw=2)
plot!(sol_seir.t, R_seir, label="R", lw=2)
xlabel!("Time")
ylabel!("Fraction")
title!("SEIR (Catalyst-defined progression)")
```

<div id="fig-seir-catalyst">

![](index_files/figure-commonmark/fig-seir-catalyst-output-1.svg)

Figure 3: Figure 3: SEIR epidemic on a Poisson network, defined via
Catalyst.jl. The exposed class delays the onset of infectiousness.

</div>

## Custom multi-stage model via Catalyst

Catalyst’s flexibility really shines when defining non-standard disease
progressions. Consider a model with two sequential infectious stages,
$I_1$ and $I_2$, each with different transmission rates:

$$I_1 \xrightarrow{\gamma_1} I_2 \xrightarrow{\gamma_2} R$$

This could represent an initial acute phase ($I_1$, high transmission)
followed by a chronic phase ($I_2$, lower transmission).

``` julia
@parameters β₁ β₂ γ₁_cat γ₂_cat
rn_multi = Catalyst.@reaction_network begin
    γ₁_cat, I1 --> I2
    γ₂_cat, I2 --> R
end; nothing
```

``` julia
progression_multi = progression_from_catalyst(
    rn_multi;
    transmission_rates = Dict(:I1 => β₁, :I2 => β₂, :R => 0),
    entry = :I1
)
```

    DiseaseProgression(:S, :I1, DiseaseStage[DiseaseStage(:I1, β₁), DiseaseStage(:I2, β₂), DiseaseStage(:R, 0)], DiseaseTransition[DiseaseTransition(:I1, :I2, γ₁_cat), DiseaseTransition(:I2, :R, γ₂_cat)])

``` julia
scm_multi = StaticConfigurationModel(pgf, progression_multi)
result_multi = build_edge_system(scm_multi)
println("Number of equations: ", length(ModelingToolkit.equations(result_multi.system)))
println("Variables: ", keys(result_multi.variables))
```

    Number of equations: 7
    Variables: [:R, :pop_I2, :φ_I2, :pop_I1, :pop_R, :φ_R, :θ, :φ_I1]

Solve with the acute phase having higher transmissibility:

``` julia
β₁_val = 0.5   # high transmission in acute phase
β₂_val = 0.1   # lower transmission in chronic phase
γ₁_val = 0.3   # fast progression out of acute phase
γ₂_val = 0.05  # slow recovery from chronic phase

ic_multi = default_initial_conditions(result_multi; ε = ε)
params_multi = Dict(
    κ => κ_val,
    β₁ => β₁_val, β₂ => β₂_val,
    γ₁_cat => γ₁_val, γ₂_cat => γ₂_val
)
prob_multi = ODEProblem(result_multi.system, merge(ic_multi, params_multi), tspan)
sol_multi = solve(prob_multi, Tsit5())
```

    retcode: Success
    Interpolation: specialized 4th order "free" interpolation
    t: 35-element Vector{Float64}:
      0.0
      0.06163014075864835
      0.14784979235917267
      0.25158051020772304
      0.3780700429078955
      0.5260267253549517
      0.7001370710983181
      0.910849244860522
      1.1644945194623462
      1.4335539237614046
      ⋮
     18.782759785217237
     21.0767394970459
     23.5638818325584
     26.250582021739874
     29.155922584424623
     32.34467220561181
     35.906313991898976
     39.960813009328135
     40.0
    u: 35-element Vector{Vector{Float64}}:
     [0.0, 0.0, 0.01, 0.0, 0.0, 0.010000000000000009, 1.0]
     [3.1358976681975906e-7, 0.00021346383214410907, 0.01326259394529581, 3.0986037223736306e-7, 0.00020975854285724252, 0.012914536369942869, 0.9996482334059656]
     [2.075253925989347e-6, 0.0006301817737292225, 0.019457372828231456, 2.0189809345513254e-6, 0.0006061503307376494, 0.0184570771264432, 0.9989756165822288]
     [7.167205931346077e-6, 0.0013893983329728297, 0.030419963755823176, 6.856440050949855e-6, 0.0013082029991704095, 0.02827313644319867, 0.9977716665876927]
     [2.0310169802824718e-5, 0.0028980183533542044, 0.051486381712079754, 1.908463783248978e-5, 0.002673259299050764, 0.0471233416684415, 0.9954109753700879]
     [5.205574334367352e-5, 0.005983081277923565, 0.09251539226490921, 4.806106892210159e-5, 0.0054201879370089304, 0.08371220623610917, 0.9906299259558637]
     [0.00013027619121133485, 0.012685674869382138, 0.17399973382371456, 0.000118261322425157, 0.011308054821577112, 0.15571478144736783, 0.9803254127070621]
     [0.0003364649914911229, 0.028057254712772258, 0.328032547718105, 0.0003002708858569891, 0.024578721919594936, 0.2884808418832593, 0.9569335672663429]
     [0.0008828616323051696, 0.06079999507367797, 0.5434827532762717, 0.0007724002385767066, 0.051910665348752376, 0.4605579671436348, 0.9080754227487091]
     [0.002021488050354003, 0.11039488926617094, 0.6941112014865434, 0.0017252936249280118, 0.09070546700282726, 0.5508439844627715, 0.8367471662874585]
     ⋮
     [0.5051430343255509, 0.4895884712378037, 0.0050631907350294, 0.11409979394735126, 0.03261936979470652, 1.1358600356518277e-5, 0.14693582604403008]
     [0.5583523010060514, 0.4389016649990648, 0.002552735172494866, 0.11726573022753776, 0.023127695371698363, 7.005032779938651e-6, 0.14059372945440474]
     [0.6097654100425901, 0.38883342436271, 0.0012164745752109003, 0.11966650566565885, 0.01592955218603407, 4.4578258159541115e-6, 0.1357852066969976]
     [0.6586918677106921, 0.3405820758379108, 0.0005474222074826305, 0.12142791603583099, 0.010648201375819122, 2.833800586608683e-6, 0.13225758545615093]
     [0.7047667306492212, 0.294827094786259, 0.00023172362248822956, 0.12268188489027364, 0.006888261591595077, 1.7723581925379112e-6, 0.1297463697820925]
     [0.7482298938825446, 0.2515076795898575, 9.082644782701112e-5, 0.12355488622871413, 0.004270588507181074, 1.0740713664454497e-6, 0.12799814888703234]
     [0.789263315811449, 0.21053463930057514, 3.234102913525147e-5, 0.12414413661681128, 0.0025037185143446977, 6.20501749984127e-7, 0.12681817949174623]
     [0.8278984493588643, 0.17192279230588275, 1.0266517235797678e-5, 0.1245244599853955, 0.0013633098590545552, 3.3534133991155777e-7, 0.12605659700380692]
     [0.8282349765247978, 0.17158638517700495, 1.0154935513322814e-5, 0.12452712335441528, 0.0013553236823804042, 3.33315646117093e-7, 0.12605126371512546]

``` julia
θ_multi = compartment(sol_multi, result_multi, :θ)
S_multi = compartment(sol_multi, result_multi, :S)
R_multi = compartment(sol_multi, result_multi, :R)
I_multi = compartment(sol_multi, result_multi, :I)

plot(sol_multi.t, S_multi, label="S", lw=2)
plot!(sol_multi.t, I_multi, label="I₁ + I₂", lw=2)
plot!(sol_multi.t, R_multi, label="R", lw=2)
xlabel!("Time")
ylabel!("Fraction")
title!("Two-stage infection (Catalyst-defined)")
```

<div id="fig-multistage-catalyst">

![](index_files/figure-commonmark/fig-multistage-catalyst-output-1.svg)

Figure 4: Figure 4: Two-stage infectious disease on a Poisson network.
The acute phase (I₁) has higher transmissibility than the chronic phase
(I₂).

</div>

### Symbolic $R_0$

We can also compute the basic reproduction number symbolically for the
multi-stage model:

``` julia
R0_multi = basic_reproduction_number(scm_multi)
println("R₀ = ", R0_multi)
```

    R₀ = (((β₁ + γ₁_cat)*(β₂ + γ₂_cat) - γ₁_cat*γ₂_cat)*κ) / ((β₁ + γ₁_cat)*(β₂ + γ₂_cat))

For two infectious stages with transmission rates $\beta_1, \beta_2$ and
progression rates $\gamma_1, \gamma_2$, the transmissibility across an
edge is:

$$T = 1 - \frac{\gamma_1}{\beta_1 + \gamma_1} \cdot \frac{\gamma_2}{\beta_2 + \gamma_2}$$

and $R_0 = T \cdot \psi''(1) / \psi'(1)$, where the excess degree ratio
$\psi''(1)/\psi'(1) = \kappa$ for a Poisson distribution.

## Simulation validation

We verify the ODE prediction against Gillespie SSA on Erdős–Rényi
networks with mean degree $\kappa = 10$, using `NetworkOutbreaks.jl`.

``` julia
include("../_validation.jl")

t_g, μ_g, σ_g = gillespie_ribbon(
    sir_model(), Dict(:β => β_val, :γ => γ_val),
    poisson_graph_builder(1000, κ_val);
    N = 1000, n_graphs = 5, nsims_per_graph = 20,
    tspan = tspan, seed_fraction = ε)
```

    ([0.0, 0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 3.5, 4.0, 4.5  …  35.5, 36.0, 36.5, 37.0, 37.5, 38.0, 38.5, 39.0, 39.5, 40.0], Dict(:I => [0.01, 0.01185, 0.01393, 0.01641, 0.01954, 0.023039999999999998, 0.026350000000000002, 0.031100000000000003, 0.03557, 0.041030000000000004  …  0.01599, 0.01482, 0.013439999999999999, 0.0123, 0.01108, 0.010060000000000001, 0.00906, 0.00836, 0.00754, 0.0068], :R => [0.0, 0.0014, 0.0032, 0.00513, 0.00741, 0.0099, 0.01292, 0.016329999999999997, 0.02044, 0.02523  …  0.78188, 0.78361, 0.78552, 0.78716, 0.78876, 0.7901699999999999, 0.79153, 0.7925399999999999, 0.7936, 0.7945800000000001], :S => [0.99, 0.98675, 0.98287, 0.97846, 0.97305, 0.9670599999999999, 0.96073, 0.95257, 0.94399, 0.93374  …  0.20213, 0.20157, 0.20104, 0.20054, 0.20016, 0.19977, 0.19941, 0.1991, 0.19886, 0.19862]), Dict(:I => [0.0, 0.0021290439833005523, 0.0034909840585384657, 0.005091277944790592, 0.006842263196966751, 0.008867053990173198, 0.010643321992230764, 0.012617528292103023, 0.01492557631325599, 0.01763344790018347  …  0.009399650756460813, 0.009147920225080914, 0.008247827996913289, 0.00790281882966739, 0.00739052081925205, 0.007226242859092536, 0.006711696409021246, 0.006330174650916918, 0.005710914590023691, 0.005365433699886598], :R => [0.0, 0.001063632046956621, 0.0016391670710664873, 0.0022322475877306473, 0.0025309997226312764, 0.003388930286218423, 0.004181923582334432, 0.005210818195123129, 0.006429603252129791, 0.007835241547074991  …  0.025681137203807936, 0.02548594185670273, 0.025072613736823682, 0.025032794651832387, 0.024881180263667785, 0.02471087561656555, 0.02451075006373466, 0.024330394176997644, 0.024309037268663954, 0.024179538891593882], :S => [0.0, 0.0019765033914885288, 0.0033864107514856756, 0.005005895514190234, 0.0070929969731141195, 0.00961776554826609, 0.01231723355401863, 0.015445083556284376, 0.019290179110132963, 0.023640668605629835  …  0.02377531824341701, 0.02362726339967403, 0.023652330271512936, 0.023454843784806945, 0.023331480445912125, 0.023348417202426933, 0.023419794355988007, 0.02323985604712106, 0.023228343884055952, 0.02310222342703679]))

``` julia
plot(t_g, μ_g[:I], ribbon = σ_g[:I], label = "SSA (mean ± 1σ)",
     color = :red, fillalpha = 0.2, linealpha = 0.6)
plot!(sol.t, I_vals, label = "EBCM Catalyst",
      color = :red, linewidth = 2)
xlabel!("Time"); ylabel!("Fraction infected")
title!("Catalyst-defined EBCM vs SSA")
```

<div id="fig-sir-validation-04">

![](index_files/figure-commonmark/fig-sir-validation-04-output-1.svg)

Figure 5: Figure 5: Catalyst-defined EBCM (red line) vs Gillespie SSA
mean ± 1σ (red ribbon) on Poisson κ=10.

</div>

## Benefits of the Catalyst adapter

The `progression_from_catalyst` function provides several advantages:

1.  **Familiar syntax**: Users of Catalyst.jl can specify disease
    compartment transitions using the same `@reaction_network` macro
    they use for chemical kinetics.
2.  **Validation**: Catalyst’s reaction parsing catches malformed
    transitions (e.g., bimolecular reactions, which are not supported in
    the edge-based framework).
3.  **Ecosystem integration**: Models defined in Catalyst can be
    analyzed with Catalyst’s own tools (e.g., species graphs,
    conservation laws) before converting to edge-based form.
4.  **Rapid prototyping**: Complex multi-stage progressions can be
    written in a few lines of Catalyst DSL, rather than manually
    constructing `DiseaseStage` and `DiseaseTransition` vectors.

The key constraint is that only **unimolecular** reactions are supported
— each reaction must have exactly one substrate and one product,
representing the progression of a single individual between disease
compartments.
