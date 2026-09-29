# EdgeBasedModels.jl vignettes


- [Overview](#overview)
- [Pages](#pages)
- [Reference ensembles used by the
  pages](#reference-ensembles-used-by-the-pages)
- [Getting started](#getting-started)
- [How to cite](#how-to-cite)
- [References](#references)

## Overview

[EdgeBasedModels.jl](https://github.com/epirecipes/EdgeBasedModels.jl)
lifts a typed reaction network (a `ContactModel` from NetworkEpiCore.jl,
written in Catalyst, ModelingToolkit or plain Julia) and a network
descriptor to an **edge-based compartmental model** (EBCM): a small ODE
system for θ, the probability that a random edge has not yet
transmitted, closed by the probability generating function of the degree
distribution. The method is due to Volz (Volz 2008) and Miller (Miller
2011), and was set out in general form by Miller, Slim and Volz (Miller
et al. 2012) and Miller and Volz (Miller and Volz 2013).

Every page follows the same rules:

- each model is built twice, first at the low level (reaction network →
  `contact_model` → `edge_based`) and then with the factory, and the two
  vector fields are checked equal;
- every comparison with stochastic simulation uses a committed
  NetworkOutbreaks ensemble (`scenario_summary(sc)`), is drawn with the
  shared `comparisonplot`, is summarised with `compare`, and states N,
  the number of runs, the conditioning rule and the fraction of runs it
  keeps (P(major) for `MajorOutbreak`, P(survival) for `Survival()`);
- every number in the prose is printed by code on the same page;
- Lean theorems are cited only by names listed in NetworkEpiCore’s
  `proofs/CITABLE.txt`.

Unless a scenario says otherwise, the anchors are R₀ = 2, recovery rate
γ = 1/4 and per-contact transmission rate τ = 1/6.

## Pages

| \# | Page | Summary |
|----|----|----|
| E01 | [From a reaction network to an edge-based model](E01_reaction_network_to_ebm/index.md) | SIR as a Catalyst network, lifted to an EBCM on Poisson(5) and 6-regular networks, against NetworkOutbreaks. |
| E02 | [Writing models: Catalyst, ModelingToolkit, plain Julia](E02_writing_models/index.md) | Three front ends, one `ContactModel`: typing reports, rate conventions, and the errors for models an EBCM cannot represent. |
| E03 | [Degree heterogeneity](E03_degree_heterogeneity/index.md) | Five degree distributions with the same R₀ and growth rate give different epidemics. |
| E04 | [Natural history](E04_natural_history/index.md) | Latency, Erlang stages, branching, two strains and vaccination as reaction networks. |
| E05 | [Three roads back to mass action](E05_mass_action/index.md) | The well-mixed unit law, the Rempała identity and the dense-network ladder, with `mass_action` and `verify`. |
| E06 | [Edge-based and pairwise](E06_edge_based_and_pairwise/index.md) | The EBCM as a pairwise model (`pairwise_image`); when the constant closure is exact. |
| E07 | [Final size, R₀ and the probability of a major outbreak](E07_final_size/index.md) | `final_size`, infector-side P(major), small seeds, and aligned versus unaligned ensembles. |
| E08 | [Clustered networks](E08_clustering/index.md) | Triangle-clustered EBCMs for SIR and beyond (SEIR, SEAIR), against NetworkOutbreaks and the pairwise Keeling closure. |
| E09 | [Dynamic partnerships](E09_dynamic_partnerships/index.md) | Neighbour exchange at rate η; the η-sweep and its well-mixed limit. |
| E10 | [Multitype populations, stratification and heterogeneous susceptibility](E10_multitype/index.md) | Typed networks, `stratify`, reciprocity, and susceptible classes with different susceptibility. |
| E11 | [Multiplex networks](E11_multiplex/index.md) | Several contact layers on the same nodes; the spectral R₀ against the additive one. |
| E12 | [Composition](E12_composition/index.md) | Open models, gluing and stratification, with the naturality checks and what fails. |
| E13 | [Where edge-based models stop: SIS and SIRS](E13_sis_sirs/index.md) | Why SIS and SIRS are refused, and what the pairwise approximations give instead. |
| E14 | [Validation methodology](E14_validation/index.md) | How the reference ensembles are built and compared; N-scaling of the exact-limit scenarios. |
| E15 | [Degree correlations](E15_degree_correlations/index.md) | `DegreeCorrelatedNetwork` and its EBCM, validated against the 2K sampler for assortative and disassortative mixing. |
| E16 | [Dormant contacts and fleeting heterogeneous contacts](E16_dormant_fleeting/index.md) | Dormant-contact (DVD) partnerships and their fast limit, the mean-field social heterogeneity (MFSH) model. |

## Reference ensembles used by the pages

The comparisons use the summaries committed in NetworkOutbreaks.jl
(`data/scenarios/`). This page loads them under the strict cache
(`NETEPI_STRICT_CACHE=1`), so a missing or stale summary stops the
render instead of falling back to a fresh simulation.

<details class="code-fold">
<summary>Code</summary>

``` julia
include(joinpath(@__DIR__, "_shared", "setup.jl"))
using NetworkEpiCore, NetworkOutbreaks

pages = [
    "E01" => [:sir_pois5, :sir_reg6],
    "E02" => [:sir_pois5, :seir_pois5, :sir_wm5, :sis_reg3],
    "E03" => [:sir_reg6, :sir_pois5, :sir_nb4, :sir_bim, :sir_pl, :sir_pl_N1000, :sir_pl_N100000],
    "E04" => [:seir_pois5, :sir_erl3_pois5, :seair_pois5, :twostrain_pois5, :sir_vax_pois5],
    "E05" => [:sir_wm5, :sir_pois5, :sir_dense_pois5, :sir_dense_pois20, :sir_dense_pois100],
    "E06" => [:sir_reg6, :sir_pois5, :sir_nb4, :sir_bim, :sir_pl, :seair_pois5],
    "E07" => [:sir_pois5, :sir_bim, :seair_pois5, :sir_pois5_5seeds, :sir_pois5_1seed,
              :sir_pois5_5seeds_unaligned, :sir_pois5_1seed_unaligned],
    "E08" => [:sir_clust_s2t2, :sir_reg6, :sir_clust_pois12, :seir_clust_s2t2, :seair_clust_s2t2,
              :sir_clust_s2t2_N1000, :sir_clust_s2t2_N100000],
    "E09" => [:sir_ne_reg6_eta01, :sir_ne_reg6_eta1, :sir_ne_reg6_eta10, :sir_wm5, :sir_ne_pois5_eta10],
    "E10" => [:sir_sbm2, :sir_unstr2, :sir_hetsus_bim, :seirv_hetsus_pois5],
    "E11" => [:sir_mpx],
    "E12" => [:seir_pois5, :sir_sbm2],
    "E13" => [:sis_reg3, :sirs_pois5],
    "E14" => [:sir_pois5, :sir_pois5_N1000, :sir_pois5_N100000, :sir_bim, :sir_bim_N1000,
              :sir_bim_N100000, :sir_pl, :sir_pl_N1000, :sir_pl_N100000, :sir_clust_s2t2,
              :sir_clust_s2t2_N1000, :sir_clust_s2t2_N100000],
    "E15" => [:sir_dc_bim_r0, :sir_dc_bim_r05, :sir_dc_bim_rn05],
    "E16" => [:sir_dormant_dvd, :sir_dormant_fast, :sir_dormant_msv, :sir_mfsh_pois5, :sir_mfsh_msv],
]

# `<id>_unaligned` is the unaligned companion of the time-aligned scenario `<id>`
# (`unaligned_scenario`), summarised from the same ensemble.
function page_scenario(id)
    s = string(id)
    endswith(s, "_unaligned") || return scenario(id)
    return unaligned_scenario(scenario(Symbol(chop(s; tail = length("_unaligned")))))
end

ids = unique(reduce(vcat, last.(pages)))
used_on(id) = join([p for (p, s) in pages if id in s], ", ")
rows = map(ids) do id
    sc = page_scenario(id)
    ref = scenario_summary(sc)
    runs, prob = kept_label(sc.sim.condition)
    (string("`:", id, "`"), ref.N, ref.nsims, condition_label(sc.sim.condition),
     string(ref.n_major, " ", runs), @sprintf("%s = %.3f", prob, ref.p_major), used_on(id))
end
mdtable(["scenario", "N", "runs", "conditioning", "runs kept by the rule", "fraction kept", "pages"], rows)
```

</details>

| scenario | N | runs | conditioning | runs kept by the rule | fraction kept | pages |
|---:|---:|---:|---:|---:|---:|---:|
| `:sir_pois5` | 10000 | 200 | MajorOutbreak(0.05) | 200 major runs | P(major) = 1.000 | E01, E02, E03, E05, E06, E07, E14 |
| `:sir_reg6` | 10000 | 200 | MajorOutbreak(0.05) | 200 major runs | P(major) = 1.000 | E01, E03, E06, E08 |
| `:seir_pois5` | 10000 | 200 | MajorOutbreak(0.05) | 200 major runs | P(major) = 1.000 | E02, E04, E12 |
| `:sir_wm5` | 10000 | 200 | MajorOutbreak(0.05) | 200 major runs | P(major) = 1.000 | E02, E05, E09 |
| `:sis_reg3` | 10000 | 200 | Survival() | 200 surviving runs | P(survival) = 1.000 | E02, E13 |
| `:sir_nb4` | 10000 | 200 | MajorOutbreak(0.05) | 200 major runs | P(major) = 1.000 | E03, E06 |
| `:sir_bim` | 10000 | 200 | MajorOutbreak(0.05) | 200 major runs | P(major) = 1.000 | E03, E06, E07, E14 |
| `:sir_pl` | 10000 | 200 | MajorOutbreak(0.05) | 200 major runs | P(major) = 1.000 | E03, E06, E14 |
| `:sir_pl_N1000` | 1000 | 2000 | MajorOutbreak(0.05) | 1712 major runs | P(major) = 0.856 | E03, E14 |
| `:sir_pl_N100000` | 100000 | 20 | MajorOutbreak(0.05) | 20 major runs | P(major) = 1.000 | E03, E14 |
| `:sir_erl3_pois5` | 10000 | 200 | MajorOutbreak(0.05) | 200 major runs | P(major) = 1.000 | E04 |
| `:seair_pois5` | 10000 | 200 | MajorOutbreak(0.05) | 200 major runs | P(major) = 1.000 | E04, E06, E07 |
| `:twostrain_pois5` | 10000 | 200 | MajorOutbreak(0.05) | 200 major runs | P(major) = 1.000 | E04 |
| `:sir_vax_pois5` | 10000 | 200 | MajorOutbreak(0.05) | 200 major runs | P(major) = 1.000 | E04 |
| `:sir_dense_pois5` | 10000 | 200 | MajorOutbreak(0.05) | 200 major runs | P(major) = 1.000 | E05 |
| `:sir_dense_pois20` | 10000 | 200 | MajorOutbreak(0.05) | 200 major runs | P(major) = 1.000 | E05 |
| `:sir_dense_pois100` | 10000 | 200 | MajorOutbreak(0.05) | 200 major runs | P(major) = 1.000 | E05 |
| `:sir_pois5_5seeds` | 10000 | 1000 | MajorOutbreak(0.05) | 990 major runs | P(major) = 0.990 | E07 |
| `:sir_pois5_1seed` | 10000 | 2000 | MajorOutbreak(0.05) | 1191 major runs | P(major) = 0.596 | E07 |
| `:sir_pois5_5seeds_unaligned` | 10000 | 1000 | MajorOutbreak(0.05) | 990 major runs | P(major) = 0.990 | E07 |
| `:sir_pois5_1seed_unaligned` | 10000 | 2000 | MajorOutbreak(0.05) | 1191 major runs | P(major) = 0.596 | E07 |
| `:sir_clust_s2t2` | 10000 | 200 | MajorOutbreak(0.05) | 200 major runs | P(major) = 1.000 | E08, E14 |
| `:sir_clust_pois12` | 10000 | 200 | MajorOutbreak(0.05) | 200 major runs | P(major) = 1.000 | E08 |
| `:seir_clust_s2t2` | 10000 | 200 | MajorOutbreak(0.05) | 200 major runs | P(major) = 1.000 | E08 |
| `:seair_clust_s2t2` | 10000 | 200 | MajorOutbreak(0.05) | 200 major runs | P(major) = 1.000 | E08 |
| `:sir_clust_s2t2_N1000` | 1000 | 2000 | MajorOutbreak(0.05) | 2000 major runs | P(major) = 1.000 | E08, E14 |
| `:sir_clust_s2t2_N100000` | 100000 | 20 | MajorOutbreak(0.05) | 20 major runs | P(major) = 1.000 | E08, E14 |
| `:sir_ne_reg6_eta01` | 5000 | 100 | MajorOutbreak(0.05) | 100 major runs | P(major) = 1.000 | E09 |
| `:sir_ne_reg6_eta1` | 5000 | 100 | MajorOutbreak(0.05) | 100 major runs | P(major) = 1.000 | E09 |
| `:sir_ne_reg6_eta10` | 5000 | 100 | MajorOutbreak(0.05) | 100 major runs | P(major) = 1.000 | E09 |
| `:sir_ne_pois5_eta10` | 5000 | 100 | MajorOutbreak(0.05) | 100 major runs | P(major) = 1.000 | E09 |
| `:sir_sbm2` | 10000 | 200 | MajorOutbreak(0.05) | 200 major runs | P(major) = 1.000 | E10, E12 |
| `:sir_unstr2` | 10000 | 200 | MajorOutbreak(0.05) | 200 major runs | P(major) = 1.000 | E10 |
| `:sir_hetsus_bim` | 10000 | 200 | MajorOutbreak(0.05) | 200 major runs | P(major) = 1.000 | E10 |
| `:seirv_hetsus_pois5` | 10000 | 200 | MajorOutbreak(0.05) | 200 major runs | P(major) = 1.000 | E10 |
| `:sir_mpx` | 10000 | 200 | MajorOutbreak(0.05) | 200 major runs | P(major) = 1.000 | E11 |
| `:sirs_pois5` | 10000 | 200 | Survival() | 198 surviving runs | P(survival) = 0.990 | E13 |
| `:sir_pois5_N1000` | 1000 | 2000 | MajorOutbreak(0.05) | 1999 major runs | P(major) = 1.000 | E14 |
| `:sir_pois5_N100000` | 100000 | 20 | MajorOutbreak(0.05) | 20 major runs | P(major) = 1.000 | E14 |
| `:sir_bim_N1000` | 1000 | 2000 | MajorOutbreak(0.05) | 1972 major runs | P(major) = 0.986 | E14 |
| `:sir_bim_N100000` | 100000 | 20 | MajorOutbreak(0.05) | 20 major runs | P(major) = 1.000 | E14 |
| `:sir_dc_bim_r0` | 10000 | 200 | MajorOutbreak(0.05) | 200 major runs | P(major) = 1.000 | E15 |
| `:sir_dc_bim_r05` | 10000 | 200 | MajorOutbreak(0.05) | 200 major runs | P(major) = 1.000 | E15 |
| `:sir_dc_bim_rn05` | 10000 | 200 | MajorOutbreak(0.05) | 200 major runs | P(major) = 1.000 | E15 |
| `:sir_dormant_dvd` | 10000 | 200 | MajorOutbreak(0.05) | 200 major runs | P(major) = 1.000 | E16 |
| `:sir_dormant_fast` | 10000 | 200 | MajorOutbreak(0.05) | 200 major runs | P(major) = 1.000 | E16 |
| `:sir_dormant_msv` | 10000 | 200 | MajorOutbreak(0.05) | 200 major runs | P(major) = 1.000 | E16 |
| `:sir_mfsh_pois5` | 10000 | 200 | MajorOutbreak(0.05) | 200 major runs | P(major) = 1.000 | E16 |
| `:sir_mfsh_msv` | 10000 | 200 | MajorOutbreak(0.05) | 200 major runs | P(major) = 1.000 | E16 |

<details class="code-fold">
<summary>Code</summary>

``` julia
println(length(ids), " scenarios, each with a committed summary; ",
        length(citable_names()), " citable Lean theorem names in CITABLE.txt.")
```

</details>

    49 scenarios, each with a committed summary; 90 citable Lean theorem names in CITABLE.txt.

## Getting started

The vignette environment path-develops NetworkEpiCore.jl,
EdgeBasedModels.jl, NodeBasedModels.jl and NetworkOutbreaks.jl
(`[sources]` in `Project.toml`: `..` and `../../NetworkEpiCore.jl`,
`../../NodeBasedModels.jl`, `../../NetworkOutbreaks.jl`). A clone of
EdgeBasedModels.jl on its own therefore will not instantiate. Check out
all four repositories side by side in one parent directory first:

``` bash
mkdir netepi && cd netepi
for pkg in NetworkEpiCore EdgeBasedModels NodeBasedModels NetworkOutbreaks; do
    git clone https://github.com/epirecipes/$pkg.jl.git
done
cd EdgeBasedModels.jl/vignettes
julia --project=. -e 'using Pkg; Pkg.instantiate()'
NETEPI_STRICT_CACHE=1 quarto render
```

The reference summaries are read from
`NetworkOutbreaks.jl/data/scenarios/`, so that checkout is also where
the committed ensembles come from.

## How to cite

If you use the edge-based method, please cite:

- Miller, J. C., Slim, A. C. and Volz, E. M. (2012). Edge-based
  compartmental modelling for infectious disease spread. *Journal of the
  Royal Society Interface* 9(70):890–906.
  [doi:10.1098/rsif.2011.0403](https://doi.org/10.1098/rsif.2011.0403)
- Miller, J. C. and Volz, E. M. (2013). Incorporating disease and
  population structure into models of SIR disease in contact networks.
  *PLoS ONE* 8(8):e69162.
  [doi:10.1371/journal.pone.0069162](https://doi.org/10.1371/journal.pone.0069162)

## References

<div id="refs" class="references csl-bib-body hanging-indent">

<div id="ref-miller2011note" class="csl-entry">

Miller, Joel C. 2011. “A Note on a Paper by Erik Volz: SIR Dynamics in
Random Networks.” *Journal of Mathematical Biology* 62 (3): 349–58.
<https://doi.org/10.1007/s00285-010-0337-9>.

</div>

<div id="ref-miller2012edge" class="csl-entry">

Miller, Joel C., Anja C. Slim, and Erik M. Volz. 2012. “Edge-Based
Compartmental Modelling for Infectious Disease Spread.” *Journal of the
Royal Society Interface* 9 (70): 890–906.
<https://doi.org/10.1098/rsif.2011.0403>.

</div>

<div id="ref-miller2013incorporating" class="csl-entry">

Miller, Joel C., and Erik M. Volz. 2013. “Incorporating Disease and
Population Structure into Models of SIR Disease in Contact Networks.”
*PLoS ONE* 8 (8): e69162.
<https://doi.org/10.1371/journal.pone.0069162>.

</div>

<div id="ref-volz2008sir" class="csl-entry">

Volz, Erik. 2008. “SIR Dynamics in Random Networks with Heterogeneous
Connectivity.” *Journal of Mathematical Biology* 56 (3): 293–310.
<https://doi.org/10.1007/s00285-007-0116-4>.

</div>

</div>
