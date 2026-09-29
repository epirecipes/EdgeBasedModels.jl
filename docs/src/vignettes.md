# Vignettes

The vignettes are Quarto pages under `vignettes/` in the repository. They are rendered with the
strict scenario cache (`NETEPI_STRICT_CACHE=1`), so a missing or stale reference ensemble is an
error. Every number on a page is printed by code on that page, and Lean is cited only from
NetworkEpiCore's `CITABLE.txt`. Each page opens with the shared first cell: a Catalyst model,
`contact_model`, a shared scenario and its committed NetworkOutbreaks summary, then the low-level
`edge_based` call next to the factory. The cell ends with `comparisonplot` and `compare` against
the ensemble.

- [E01. From a reaction network to an edge-based model](vignettes/E01_reaction_network_to_ebm/index.html): SIR written as a Catalyst network, lifted to an edge-based model on Poisson(5) and 6-regular networks, and checked against NetworkOutbreaks
- [E02. Writing models: Catalyst, ModelingToolkit, plain Julia](vignettes/E02_writing_models/index.html): three front ends, one ContactModel: typing reports, rate conventions, and the errors for models an edge-based model cannot represent
- [E03. Degree heterogeneity: same R₀, different epidemics](vignettes/E03_degree_heterogeneity/index.html): five degree distributions with R₀ = 2, lifted and compared with NetworkOutbreaks, with an N-scaling check on the heavy-tailed network
- [E04. Natural history: latency, stages, branching, strains, vaccination](vignettes/E04_natural_history/index.html): five natural histories as reaction networks, lifted reaction by reaction, with the transmissibility from the absorption formula, against NetworkOutbreaks
- [E05. Three roads back to mass action](vignettes/E05_mass_action/index.html): the well-mixed unit law, Rempała's identity on Poisson networks, and the dense-network limit, with the mass_action maps, verify and pushforward
- [E06. Edge-based and pairwise](vignettes/E06_edge_based_and_pairwise/index.html): the edge-based model as an S-anchored pairwise model (pairwise_image, verify); when the constant pairwise closure is exact
- [E07. Final size, R₀ and the probability of a major outbreak](vignettes/E07_final_size/index.html): final_size with a seed fraction, the infector-side probability of a major outbreak, Ball's central limit theorem, and aligned versus unaligned small-seed ensembles
- [E08. Clustered networks](vignettes/E08_clustering/index.html): the triangle-clustered edge-based model of Volz et al. for SIR, SEIR and SEAIR, against NetworkOutbreaks and the Keeling pairwise closure, with an N-scaling check
- [E09. Dynamic partnerships](vignettes/E09_dynamic_partnerships/index.html): neighbour exchange at rate η: the dynamic fixed-degree (DFD) edge-based model, the η-sweep, and its limits
- [E10. Multitype populations, stratification and heterogeneous susceptibility](vignettes/E10_multitype/index.html): typed edge-based models on stochastic block models and unstructured networks, reciprocity, the unit law, and susceptible classes
- [E11. Multiplex networks](vignettes/E11_multiplex/index.html): contacts on several layers of the same nodes: layer metadata, the multiplex EBCM, and R₀ = ρ(K)
- [E12. Composition: open models, gluing, stratification](vignettes/E12_composition/index.html): build models from pieces, lift the pieces, and check which laws hold: H1 and H2 hold for the edge-based lift, F2 and F7 fail
- [E13. Where edge-based models stop: SIS and SIRS](vignettes/E13_sis_sirs/index.html): why an edge-based model cannot represent reinfection, and what the node-based approximations give against simulation
- [E14. Validation methodology](vignettes/E14_validation/index.html): how the reference ensembles are built, hashed and cached; what the comparison statistics mean; and how the error scales with N
- [E15. Degree correlations](vignettes/E15_degree_correlations/index.html): the joint-degree (2K) edge-based model, its sampler, and how assortative mixing changes R₀ and the epidemic
- [E16. Dormant contacts and fleeting heterogeneous contacts (DVD, MFSH)](vignettes/E16_dormant_fleeting/index.html): partnerships that pause and resume, and their fast limit: mean-field social heterogeneity

The pages are also rendered as Markdown (`vignettes/<page>/index.md`) and PDF.
