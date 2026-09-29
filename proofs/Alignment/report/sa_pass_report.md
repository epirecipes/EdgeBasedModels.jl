# SA-PASS report (EBCMCategory)

Generated 2026-09-26 18:45 from `Alignment/report/sa_pass_audit.json` (Lean 4.29.0-rc4) and `Alignment/claims.yaml`.

Trusted modules loaded by the audit: `EBCMCategory.CategoricalComposition`, `EBCMCategory.ClosureTheorem`, `EBCMCategory.ClusteringExtension`, `EBCMCategory.CoarseGrain`, `EBCMCategory.ConvergenceTheorems`, `EBCMCategory.DegreeCorrelation`, `EBCMCategory.DynamicLimits`, `EBCMCategory.EpiCategory`, `EBCMCategory.GaloisPair`, `EBCMCategory.Hierarchy`, `EBCMCategory.InvariantRegion`, `EBCMCategory.MarginalisationCharacterization`, `EBCMCategory.MarginalisationDynamicalGap`, `EBCMCategory.MarginalisationFunctor`, `EBCMCategory.MessagePassingBridge`, `EBCMCategory.MethodOfStages`, `EBCMCategory.Obstructions`, `EBCMCategory.PairwiseClosureConditions`, `EBCMCategory.SEIREquations`, `EBCMCategory.SurvivalBridge`, `EBCMCategory.VolzMeyersEquations`

Tool sanity: 3/3 worked-example claims (`EXAMPLE.*`) pass every check (run `bash scripts/sa_pass.sh --self-test` for the full self-test).

## Summary

| quantity | value |
|---|---|
| claims in registry | 711 |
| claims registered in Lean | 557 |
| registry claims not registered in Lean | 154 |
| required claims (status implemented) | 467 |
| SA-PASS = 1 (all / required) | 182 / 182 |
| mean SA-PASS_soft (registered claims) | 0.4674 |
| required failures | 285 |
| check statuses | fail: 667, missing: 351, pass: 768, vacuous: 10 |
| bridges | reviewed: 2 |
| hints (not scored) | backward_unused_shadows: 150, witness_missing: 8 |
| trusted-free shadows (by review status) | reviewed: 16, unreviewed: 142 |
| tautological shadows (by review status) | none |
| claims with a refuted implementation hypothesis | 3 |

## Per group

| group | registry | registered | required | SA-PASS=1 | mean soft | forward pass | backward pass | required failures |
|---|---|---|---|---|---|---|---|---|
| CategoricalComposition | 69 | 49 | 35 | 14 | 0.3622 | 29/111 | 19/49 | 21 |
| ClosureTheorem | 29 | 26 | 26 | 4 | 0.1731 | 12/47 | 6/26 | 22 |
| ClusteringExtension | 18 | 16 | 13 | 3 | 0.25 | 12/37 | 6/16 | 10 |
| CoarseGrain | 10 | 9 | 9 | 7 | 0.8889 | 13/13 | 7/9 | 2 |
| ConvergenceTheorems | 46 | 33 | 27 | 13 | 0.548 | 29/56 | 18/33 | 14 |
| DegreeCorrelation | 44 | 35 | 33 | 20 | 0.616 | 39/74 | 22/35 | 13 |
| Docs | 64 | 43 | 25 | 10 | 0.3283 | 32/114 | 15/43 | 15 |
| DynamicLimits | 40 | 38 | 32 | 11 | 0.589 | 42/110 | 27/38 | 21 |
| EpiCategory | 10 | 9 | 7 | 7 | 0.7778 | 14/22 | 7/9 | 0 |
| GaloisPair | 26 | 24 | 22 | 17 | 0.8368 | 27/38 | 21/24 | 5 |
| Hierarchy | 18 | 17 | 16 | 8 | 0.6784 | 14/44 | 16/17 | 8 |
| InvariantRegion | 51 | 41 | 31 | 6 | 0.2789 | 18/79 | 11/41 | 25 |
| MarginalisationCharacterization | 26 | 21 | 17 | 5 | 0.4036 | 20/53 | 9/21 | 12 |
| MarginalisationDynamicalGap | 31 | 26 | 24 | 7 | 0.4343 | 22/56 | 15/26 | 17 |
| MarginalisationFunctor | 12 | 9 | 8 | 4 | 0.5926 | 12/17 | 5/9 | 4 |
| MessagePassingBridge | 42 | 25 | 24 | 8 | 0.468 | 21/62 | 14/25 | 16 |
| MethodOfStages | 16 | 11 | 10 | 1 | 0.3409 | 5/20 | 9/11 | 9 |
| Obstructions | 46 | 37 | 32 | 13 | 0.5914 | 48/93 | 24/37 | 19 |
| PairwiseClosureConditions | 20 | 19 | 18 | 10 | 0.6947 | 24/37 | 13/19 | 8 |
| SEIREquations | 18 | 14 | 14 | 3 | 0.5238 | 9/22 | 8/14 | 11 |
| SurvivalBridge | 46 | 31 | 24 | 3 | 0.2393 | 20/94 | 14/31 | 21 |
| VolzMeyersEquations | 29 | 24 | 20 | 8 | 0.3958 | 10/40 | 10/24 | 12 |

## Claims

| id | req | n | forward | backward | SA-PASS | soft | flags |
|---|---|---|---|---|---|---|---|
| `CategoricalComposition.R100.monoidal` | no | 6 | missing missing missing missing missing missing | missing | 0 | 0.0 | gap, shadow_trusted_free |
| `CategoricalComposition.R100a` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `CategoricalComposition.R100b` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `CategoricalComposition.R100c` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `CategoricalComposition.R100d` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `CategoricalComposition.R100e` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [0]) |
| `CategoricalComposition.R100f.1` | yes | 2 | pass pass | pass | 0 | 0.0 | shadow_trusted_free (identical to impl: [0]) |
| `CategoricalComposition.R101a` | yes | 1 | fail | fail | 0 | 0.0 |  |
| `CategoricalComposition.R101b` | yes | 1 | pass | fail | 0 | 0.5 |  |
| `CategoricalComposition.R101c` | yes | 1 | pass | fail | 0 | 0.5 |  |
| `CategoricalComposition.R101d` | yes | 1 | pass | fail | 0 | 0.5 |  |
| `CategoricalComposition.R101e` | yes | 2 | pass fail | pass | 0 | 0.0 | shadow_trusted_free (hints: backward_unused_shadows) |
| `CategoricalComposition.R102.terminal` | no | 4 | missing missing missing missing | missing | 0 | 0.0 | gap |
| `CategoricalComposition.R102a.1` | no | 4 | missing missing missing missing | missing | 0 | 0.0 | gap |
| `CategoricalComposition.R102a.3` | yes | 1 | fail | fail | 0 | 0.0 |  |
| `CategoricalComposition.R102b` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `CategoricalComposition.R102c.1` | no | 4 | missing missing missing missing | missing | 0 | 0.0 | gap |
| `CategoricalComposition.R102c.2` | yes | 4 | pass pass pass pass | fail | 0 | 0.5 |  |
| `CategoricalComposition.R102d.1` | no | 3 | missing missing missing | missing | 0 | 0.0 | gap |
| `CategoricalComposition.R102d.2` | yes | 1 | fail | fail | 0 | 0.0 |  |
| `CategoricalComposition.R102e.1` | yes | 2 | fail fail | fail | 0 | 0.0 |  |
| `CategoricalComposition.R102e.2` | no | 5 | missing missing missing missing missing | missing | 0 | 0.0 | gap |
| `CategoricalComposition.R95a.2` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `CategoricalComposition.R96a` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `CategoricalComposition.R96b` | no | 3 | missing missing missing | missing | 0 | 0.0 | gap |
| `CategoricalComposition.R96c` | no | 11 | missing missing missing missing missing missing missing missing missing missing missing | missing | 0 | 0.0 | gap |
| `CategoricalComposition.R96d` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `CategoricalComposition.R96e` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `CategoricalComposition.R96f` | yes | 4 | pass fail fail fail | pass | 0 | 0.625 |  (hints: backward_unused_shadows) |
| `CategoricalComposition.R96g` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `CategoricalComposition.R97a.2` | no | 1 | missing | missing | 0 | 0.0 | gap |
| `CategoricalComposition.R97b` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `CategoricalComposition.R97c` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `CategoricalComposition.R97d.1` | yes | 1 | fail | vacuous | 0 | 0.0 |  |
| `CategoricalComposition.R98.keyProperty` | no | 5 | missing missing missing missing missing | missing | 0 | 0.0 | gap |
| `CategoricalComposition.R98a` | yes | 2 | fail fail | fail | 0 | 0.0 |  |
| `CategoricalComposition.R98b.1` | yes | 1 | fail | fail | 0 | 0.0 |  |
| `CategoricalComposition.R98b.3` | no | 3 | missing missing missing | missing | 0 | 0.0 | gap |
| `CategoricalComposition.R98c.1` | yes | 1 | fail | fail | 0 | 0.0 |  |
| `CategoricalComposition.R98c.2` | no | 2 | missing missing | missing | 0 | 0.0 | gap |
| `CategoricalComposition.R98d.1` | yes | 0 | - | fail | 0 | 0.0 | incomplete |
| `CategoricalComposition.R99a.2` | no | 3 | missing missing missing | missing | 0 | 0.0 | gap |
| `CategoricalComposition.R99a.3` | yes | 2 | fail fail | pass | 0 | 0.5 |  (hints: backward_unused_shadows) |
| `CategoricalComposition.R99b.1` | yes | 1 | fail | fail | 0 | 0.0 |  |
| `CategoricalComposition.R99b.2` | no | 2 | missing missing | missing | 0 | 0.0 | gap |
| `CategoricalComposition.meanDegPos` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `CategoricalComposition.multiplexR0SumNeSpectral` | yes | 5 | fail fail fail fail fail | fail | 0 | 0.0 |  |
| `CategoricalComposition.r0SumEqTrace` | yes | 1 | fail | fail | 0 | 0.0 |  |
| `CategoricalComposition.stagesChangeTransmissibility` | yes | 4 | pass fail fail fail | pass | 0 | 0.625 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `ClosureTheorem.R51` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `ClosureTheorem.R52` | yes | 2 | pass fail | fail | 0 | 0.0 | shadow_trusted_free |
| `ClosureTheorem.R53` | yes | 2 | pass fail | fail | 0 | 0.0 | shadow_trusted_free |
| `ClosureTheorem.R54` | yes | 2 | fail fail | fail | 0 | 0.0 | shadow_trusted_free |
| `ClosureTheorem.R55` | yes | 2 | fail fail | fail | 0 | 0.0 | shadow_trusted_free |
| `ClosureTheorem.R56` | yes | 2 | fail fail | fail | 0 | 0.0 | shadow_trusted_free |
| `ClosureTheorem.R57` | yes | 3 | pass fail fail | fail | 0 | 0.0 | shadow_trusted_free |
| `ClosureTheorem.R58` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `ClosureTheorem.R59` | yes | 1 | fail | pass | 0 | 0.0 | shadow_trusted_free |
| `ClosureTheorem.binomialClosureRatio` | yes | 2 | fail fail | fail | 0 | 0.0 | shadow_trusted_free |
| `ClosureTheorem.binomialKappaDeterminesN` | yes | 2 | fail fail | fail | 0 | 0.0 | shadow_trusted_free |
| `ClosureTheorem.binomialRecoverN` | yes | 1 | fail | fail | 0 | 0.0 | shadow_trusted_free |
| `ClosureTheorem.header.verificationStrategy` | yes | 4 | pass fail fail pass | fail | 0 | 0.0 | shadow_trusted_free |
| `ClosureTheorem.negbin2ClosureRatio` | yes | 2 | fail fail | fail | 0 | 0.0 | shadow_trusted_free |
| `ClosureTheorem.negbin3ClosureRatio` | yes | 2 | fail fail | fail | 0 | 0.0 | shadow_trusted_free |
| `ClosureTheorem.negbinKappaDeterminesR` | yes | 2 | pass fail | pass | 0 | 0.0 | shadow_trusted_free (hints: backward_unused_shadows) |
| `ClosureTheorem.poissonClosureRatio` | yes | 2 | pass fail | fail | 0 | 0.0 | shadow_trusted_free |
| `ClosureTheorem.poissonKappaIsOne` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `ClosureTheorem.table.R52` | yes | 2 | fail fail | fail | 0 | 0.0 | shadow_trusted_free |
| `ClosureTheorem.table.R53` | yes | 2 | fail fail | fail | 0 | 0.0 | shadow_trusted_free |
| `ClosureTheorem.table.R54` | yes | 2 | fail fail | fail | 0 | 0.0 | shadow_trusted_free |
| `ClosureTheorem.table.R55` | yes | 2 | fail fail | fail | 0 | 0.0 | shadow_trusted_free |
| `ClosureTheorem.table.R56` | yes | 1 | fail | fail | 0 | 0.0 | shadow_trusted_free |
| `ClosureTheorem.table.R57` | yes | 1 | pass | fail | 0 | 0.5 |  |
| `ClosureTheorem.table.R58` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `ClosureTheorem.table.R59` | yes | 2 | fail fail | fail | 0 | 0.0 |  |
| `ClusteringExtension.R69` | no | 4 | missing missing missing missing | missing | 0 | 0.0 | gap, shadow_trusted_free |
| `ClusteringExtension.R70` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `ClusteringExtension.R71-sec-a` | yes | 2 | fail pass | fail | 0 | 0.0 | shadow_trusted_free |
| `ClusteringExtension.R71-sec-b` | yes | 3 | fail fail fail | fail | 0 | 0.0 | shadow_trusted_free |
| `ClusteringExtension.R71a` | yes | 1 | pass | fail | 0 | 0.0 | shadow_trusted_free |
| `ClusteringExtension.R71b` | yes | 3 | pass fail fail | pass | 0 | 0.0 | shadow_trusted_free (identical to impl: [1]) (hints: backward_unused_shadows) |
| `ClusteringExtension.R72` | no | 2 | missing missing | missing | 0 | 0.0 | gap |
| `ClusteringExtension.R73` | yes | 1 | pass | pass | 0 | 0.0 | shadow_trusted_free (identical to impl: [0, 1]) |
| `ClusteringExtension.R73-sec-a` | no | 3 | missing missing missing | missing | 0 | 0.0 | gap, shadow_trusted_free |
| `ClusteringExtension.R73-sec-b` | yes | 5 | pass fail fail fail fail | pass | 0 | 0.0 | shadow_trusted_free (identical to impl: [1]) (hints: backward_unused_shadows) |
| `ClusteringExtension.R75` | yes | 2 | fail fail | fail | 0 | 0.0 | shadow_trusted_free |
| `ClusteringExtension.R75-sec` | yes | 4 | fail fail fail fail | fail | 0 | 0.0 | shadow_trusted_free |
| `ClusteringExtension.R76` | yes | 1 | pass | fail | 0 | 0.5 |  |
| `ClusteringExtension.R76-sec` | yes | 1 | pass | fail | 0 | 0.5 |  |
| `ClusteringExtension.clusteringInUnitInterval` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [0]) |
| `ClusteringExtension.meanDegreePositive` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `CoarseGrain.R5` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0]) |
| `CoarseGrain.R6` | yes | 1 | pass | fail | 0 | 0.5 |  |
| `CoarseGrain.R7` | yes | 2 | pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows) |
| `CoarseGrain.R8` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `CoarseGrain.coarseGrainPreservesR0` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `CoarseGrain.table.R5` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0]) |
| `CoarseGrain.table.R6` | yes | 1 | pass | fail | 0 | 0.5 |  |
| `CoarseGrain.table.R7` | yes | 2 | pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows) |
| `CoarseGrain.table.R8` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `ConvergenceTheorems.R105` | no | 2 | missing missing | missing | 0 | 0.0 | gap |
| `ConvergenceTheorems.R105.keyIdentity` | no | 2 | missing missing | missing | 0 | 0.0 | gap |
| `ConvergenceTheorems.R105c.1` | no | 1 | missing | missing | 0 | 0.0 | gap |
| `ConvergenceTheorems.R105c.2` | no | 2 | missing missing | missing | 0 | 0.0 | gap |
| `ConvergenceTheorems.R105c.3` | no | 1 | missing | missing | 0 | 0.0 | gap |
| `ConvergenceTheorems.R105c.4` | yes | 1 | fail | fail | 0 | 0.0 |  |
| `ConvergenceTheorems.R105d.2` | yes | 2 | fail pass | pass | 0 | 0.75 |  (hints: backward_unused_shadows) |
| `ConvergenceTheorems.R105e.2` | yes | 0 | - | fail | 0 | 0.0 | incomplete |
| `ConvergenceTheorems.R107a` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `ConvergenceTheorems.R107b` | yes | 1 | fail | fail | 0 | 0.0 |  |
| `ConvergenceTheorems.R107c` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `ConvergenceTheorems.R108a` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `ConvergenceTheorems.R108b` | yes | 2 | pass fail | pass | 0 | 0.75 |  (hints: backward_unused_shadows) |
| `ConvergenceTheorems.R108c` | yes | 4 | pass pass pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows) |
| `ConvergenceTheorems.R109a` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `ConvergenceTheorems.R109b` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `ConvergenceTheorems.R110.stability` | yes | 2 | fail fail | fail | 0 | 0.0 |  |
| `ConvergenceTheorems.R110a` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `ConvergenceTheorems.R110b.2` | no | 2 | missing missing | missing | 0 | 0.0 | gap |
| `ConvergenceTheorems.R110b.3` | yes | 0 | - | fail | 0 | 0.0 | incomplete |
| `ConvergenceTheorems.R110c.2` | yes | 4 | fail fail fail fail | vacuous | 0 | 0.0 |  |
| `ConvergenceTheorems.R110d` | yes | 2 | pass pass | fail | 0 | 0.5 |  |
| `ConvergenceTheorems.R112a` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `ConvergenceTheorems.R112b` | yes | 5 | fail fail fail fail fail | pass | 0 | 0.5 |  (hints: backward_unused_shadows) |
| `ConvergenceTheorems.R112c` | yes | 3 | pass fail pass | pass | 0 | 0.8333 |  (identical to impl: [3]) (hints: backward_unused_shadows) |
| `ConvergenceTheorems.R112d` | yes | 1 | pass | fail | 0 | 0.5 |  |
| `ConvergenceTheorems.R112e` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `ConvergenceTheorems.dfeDerivativeAbsLeOneIff` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [0]) |
| `ConvergenceTheorems.effectiveBetaPos` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `ConvergenceTheorems.effectiveGammaPos` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `ConvergenceTheorems.finalSizeMapHasDerivAt` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `ConvergenceTheorems.r0MassActionEqEdge` | yes | 2 | pass fail | pass | 0 | 0.75 |  (hints: backward_unused_shadows) |
| `ConvergenceTheorems.sThetaChainRule` | yes | 1 | pass | fail | 0 | 0.5 |  |
| `DegreeCorrelation.R79-sec` | yes | 5 | fail fail fail fail fail | fail | 0 | 0.0 | shadow_trusted_free |
| `DegreeCorrelation.R79b` | yes | 2 | fail fail | fail | 0 | 0.0 |  |
| `DegreeCorrelation.R80-sec` | yes | 2 | fail fail | fail | 0 | 0.0 |  |
| `DegreeCorrelation.R82` | no | 5 | missing missing missing missing missing | missing | 0 | 0.0 | gap |
| `DegreeCorrelation.R83-sec` | yes | 8 | pass pass pass pass pass pass pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows) |
| `DegreeCorrelation.R83a` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `DegreeCorrelation.R83b` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `DegreeCorrelation.R83c` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `DegreeCorrelation.R83d` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `DegreeCorrelation.R83e` | yes | 3 | pass fail fail | pass | 0 | 0.6667 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `DegreeCorrelation.R83f` | yes | 2 | pass fail | fail | 0 | 0.25 |  |
| `DegreeCorrelation.R84` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `DegreeCorrelation.R84-sec` | yes | 3 | fail pass pass | pass | 0 | 0.0 | shadow_trusted_free (hints: backward_unused_shadows) |
| `DegreeCorrelation.R84b` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `DegreeCorrelation.R85-sec` | yes | 4 | pass pass pass pass | pass | 1 | 1.0 |  |
| `DegreeCorrelation.R85a` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `DegreeCorrelation.R85b` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `DegreeCorrelation.R85c` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `DegreeCorrelation.R85d` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `DegreeCorrelation.R86-sec` | no | 3 | missing missing missing | missing | 0 | 0.0 | gap |
| `DegreeCorrelation.R86a` | yes | 1 | fail | fail | 0 | 0.0 |  |
| `DegreeCorrelation.R86b` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `DegreeCorrelation.R86c` | yes | 1 | pass | fail | 0 | 0.5 |  |
| `DegreeCorrelation.R86d-1` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `DegreeCorrelation.R86d-2` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `DegreeCorrelation.R86e` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `DegreeCorrelation.R86f-1` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `DegreeCorrelation.R86g-1` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `DegreeCorrelation.R86h-1` | yes | 7 | fail fail pass pass fail fail fail | fail | 0 | 0.1429 |  |
| `DegreeCorrelation.R86h-2` | yes | 3 | fail fail fail | fail | 0 | 0.0 | shadow_trusted_free |
| `DegreeCorrelation.meanDegPos` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `DegreeCorrelation.neutralDetK` | yes | 2 | fail fail | fail | 0 | 0.0 |  |
| `DegreeCorrelation.neutralTraceCSubTraceK` | yes | 2 | fail fail | fail | 0 | 0.0 |  |
| `DegreeCorrelation.neutralTraceK` | yes | 1 | fail | fail | 0 | 0.0 |  |
| `DegreeCorrelation.uncorrelatedR0Formula` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `Docs.cf.coarseGrainDef` | no | 1 | missing | missing | 0 | 0.0 | gap |
| `Docs.cf.cor4_2-FG` | yes | 2 | pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows) |
| `Docs.cf.cor4_2-FGF` | yes | 3 | pass pass pass | pass | 1 | 1.0 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `Docs.cf.cor4_2-GF` | yes | 2 | pass fail | fail | 0 | 0.25 |  |
| `Docs.cf.cor4_2-GFG` | yes | 3 | pass pass pass | pass | 1 | 1.0 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `Docs.cf.dispersionSingleScalar` | no | 1 | missing | missing | 0 | 0.0 | gap |
| `Docs.cf.liftDef` | no | 2 | missing missing | missing | 0 | 0.0 | gap, shadow_trusted_free |
| `Docs.cf.liftNotUnique` | no | 3 | missing missing missing | missing | 0 | 0.0 | gap, shadow_trusted_free |
| `Docs.cf.localisedObstruction` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [2]) (hints: backward_unused_shadows) |
| `Docs.cf.nonMarkovObstruction` | yes | 3 | pass pass fail | pass | 0 | 0.8333 |  (identical to impl: [2]) (hints: backward_unused_shadows) |
| `Docs.cf.pgfClosureTreeLike` | no | 1 | missing | missing | 0 | 0.0 | gap |
| `Docs.cf.poissonEquivMassAction` | no | 1 | missing | missing | 0 | 0.0 | gap |
| `Docs.cf.poissonUniqueSection` | no | 4 | missing missing missing missing | missing | 0 | 0.0 | gap, shadow_trusted_free |
| `Docs.cf.subcategoryInclusions` | no | 2 | missing missing | missing | 0 | 0.0 | gap |
| `Docs.cf.thetaNonincreasing` | yes | 1 | fail | fail | 0 | 0.0 | shadow_trusted_free |
| `Docs.cf.thm3_2` | yes | 2 | fail pass | fail | 0 | 0.0 | shadow_trusted_free |
| `Docs.cf.thm3_3-lostInformation` | no | 1 | missing | missing | 0 | 0.0 | gap |
| `Docs.cf.thm4_1` | no | 5 | missing missing missing missing missing | missing | 0 | 0.0 | gap |
| `Docs.cf.thm4_3` | yes | 8 | fail fail pass fail fail fail fail fail | fail | 0 | 0.0 | shadow_trusted_free |
| `Docs.cf.thm4_3-massAction` | no | 3 | missing missing missing | missing | 0 | 0.0 | gap, shadow_trusted_free |
| `Docs.cf.thm7_1` | no | 2 | missing missing | missing | 0 | 0.0 | gap, shadow_trusted_free |
| `Docs.cf.thm8_1` | yes | 2 | fail fail | fail | 0 | 0.0 |  |
| `Docs.cf.thm8_1-factor` | no | 2 | missing missing | missing | 0 | 0.0 | gap |
| `Docs.cf.thm8_1-poisson` | yes | 5 | fail fail fail fail fail | fail | 0 | 0.0 | shadow_trusted_free |
| `Docs.cf.validityDomain` | yes | 4 | pass fail fail fail | pass | 0 | 0.625 |  (hints: backward_unused_shadows) |
| `Docs.ms.T1` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `Docs.ms.T2` | yes | 5 | pass fail fail fail fail | pass | 0 | 0.6 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `Docs.ms.T2-smallestWitness` | no | 2 | missing missing | missing | 0 | 0.0 | gap |
| `Docs.ms.T3` | yes | 3 | pass pass fail | pass | 0 | 0.8333 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `Docs.ms.T3-kkr` | yes | 2 | pass fail | fail | 0 | 0.25 |  |
| `Docs.ms.T3-linearEquivariant` | yes | 3 | fail fail fail | fail | 0 | 0.0 |  |
| `Docs.ms.T4` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `Docs.ms.T4-companion` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `Docs.ms.T5` | yes | 2 | pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows, witness_missing) |
| `Docs.ms.T5-rateTwo` | yes | 2 | fail fail | fail | 0 | 0.0 | hypothesis_refuted |
| `Docs.ms.T5-witnessGap` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `Docs.ms.T6` | yes | 5 | pass fail fail fail fail | pass | 0 | 0.6 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `Docs.ms.T6-phaseReversal` | no | 4 | missing missing missing missing | missing | 0 | 0.0 | gap |
| `Docs.ms.T6-values` | yes | 4 | fail fail fail pass | fail | 0 | 0.125 |  |
| `Docs.ms.T7` | yes | 2 | pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows, witness_missing) |
| `Docs.ms.T7-witness` | no | 3 | missing missing missing | missing | 0 | 0.0 | gap |
| `Docs.ms.flowDef` | no | 3 | missing missing missing | missing | 0 | 0.0 | gap |
| `Docs.ms.flowHypothesised` | no | 3 | missing missing missing | missing | 0 | 0.0 | gap |
| `DynamicLimits.R29` | yes | 5 | pass pass fail fail fail | pass | 0 | 0.7 |  (identical to impl: [2]) (hints: backward_unused_shadows) |
| `DynamicLimits.R30` | yes | 4 | pass pass fail fail | pass | 0 | 0.75 |  (identical to impl: [2]) (hints: backward_unused_shadows) |
| `DynamicLimits.R31a` | yes | 5 | fail fail pass fail fail | pass | 0 | 0.6 |  (identical to impl: [3]) (hints: backward_unused_shadows) |
| `DynamicLimits.R32a` | yes | 3 | pass fail fail | pass | 0 | 0.6667 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `DynamicLimits.R32b` | no | 2 | missing missing | missing | 0 | 0.0 | gap |
| `DynamicLimits.R33a` | yes | 2 | pass fail | pass | 0 | 0.75 |  (hints: backward_unused_shadows) |
| `DynamicLimits.R33b` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `DynamicLimits.R33c` | no | 1 | missing | missing | 0 | 0.0 | gap |
| `DynamicLimits.R34` | yes | 4 | pass pass fail fail | pass | 0 | 0.75 |  (hints: backward_unused_shadows) |
| `DynamicLimits.R35a` | yes | 3 | pass fail fail | pass | 0 | 0.6667 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `DynamicLimits.R35b` | yes | 3 | fail fail fail | fail | 0 | 0.0 |  |
| `DynamicLimits.R36a` | yes | 2 | fail pass | pass | 0 | 0.75 |  (hints: backward_unused_shadows) |
| `DynamicLimits.R36b` | yes | 3 | pass pass pass | pass | 1 | 1.0 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `DynamicLimits.R37a` | yes | 3 | fail pass fail | pass | 0 | 0.6667 |  (hints: backward_unused_shadows) |
| `DynamicLimits.R37b` | no | 5 | missing missing missing missing missing | missing | 0 | 0.0 | gap |
| `DynamicLimits.R38` | yes | 6 | pass fail fail fail fail fail | pass | 0 | 0.5833 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `DynamicLimits.R39` | yes | 3 | pass fail fail | pass | 0 | 0.6667 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `DynamicLimits.R40a` | yes | 2 | fail fail | fail | 0 | 0.0 |  |
| `DynamicLimits.R40b` | no | 10 | missing missing missing missing missing missing missing missing missing missing | missing | 0 | 0.0 | gap |
| `DynamicLimits.fastRewiringR0MeanDegree` | no | 4 | missing missing missing missing | missing | 0 | 0.0 | gap |
| `DynamicLimits.header.fastRewiringCollapse` | no | 2 | missing missing | missing | 0 | 0.0 | gap |
| `DynamicLimits.header.interpolation` | yes | 4 | pass fail fail pass | fail | 0 | 0.25 |  |
| `DynamicLimits.r0EdgeSwapTendstoMfsh` | yes | 1 | fail | fail | 0 | 0.0 |  |
| `DynamicLimits.r0EdgeSwapZero` | yes | 2 | pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows) |
| `DynamicLimits.r0MfshPoisson` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `DynamicLimits.r0StaticLtMfsh` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `DynamicLimits.table.R29` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [2]) (hints: backward_unused_shadows) |
| `DynamicLimits.table.R30` | yes | 4 | pass pass pass pass | pass | 1 | 1.0 |  (identical to impl: [4]) (hints: backward_unused_shadows) |
| `DynamicLimits.table.R31` | yes | 3 | fail fail pass | pass | 0 | 0.6667 |  (identical to impl: [3]) (hints: backward_unused_shadows) |
| `DynamicLimits.table.R32` | yes | 3 | fail fail pass | pass | 0 | 0.6667 |  (identical to impl: [3]) (hints: backward_unused_shadows) |
| `DynamicLimits.table.R33` | yes | 3 | pass pass fail | pass | 0 | 0.8333 |  (hints: backward_unused_shadows) |
| `DynamicLimits.table.R34` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [0]) |
| `DynamicLimits.table.R35` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `DynamicLimits.table.R36` | yes | 2 | fail pass | pass | 0 | 0.75 |  (hints: backward_unused_shadows) |
| `DynamicLimits.table.R37` | yes | 3 | fail pass fail | pass | 0 | 0.6667 |  (hints: backward_unused_shadows) |
| `DynamicLimits.table.R38` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `DynamicLimits.table.R39` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `DynamicLimits.table.R40` | yes | 2 | fail fail | fail | 0 | 0.0 |  |
| `EpiCategory.R1` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `EpiCategory.R2` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `EpiCategory.R3` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `EpiCategory.R4` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `EpiCategory.dispersionIndexEqOneIff` | yes | 4 | pass pass pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows) |
| `EpiCategory.dispersionIndexOneIffPoisson` | no | 6 | missing missing missing missing missing missing | missing | 0 | 0.0 | gap, shadow_trusted_free |
| `EpiCategory.header.refinementPreorder` | no | 2 | missing missing | missing | 0 | 0.0 | gap |
| `EpiCategory.transmissibilityLtOne` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `EpiCategory.transmissibilityPos` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `GaloisPair.R10` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `GaloisPair.R11` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `GaloisPair.R12` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `GaloisPair.R13` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `GaloisPair.R14a` | yes | 2 | pass fail | pass | 0 | 0.75 |  (hints: backward_unused_shadows) |
| `GaloisPair.R14b` | no | 1 | missing | missing | 0 | 0.0 | gap |
| `GaloisPair.R15` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `GaloisPair.R9` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0]) |
| `GaloisPair.coarseGrainR0` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `GaloisPair.fgEqSelfOfDimThree` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `GaloisPair.header.FGPreservesR0` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `GaloisPair.header.GFLossy` | yes | 2 | pass fail | pass | 0 | 0.75 |  (hints: backward_unused_shadows) |
| `GaloisPair.header.galoisConnection` | no | 3 | missing missing missing | missing | 0 | 0.0 | gap |
| `GaloisPair.header.idempotency` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `GaloisPair.notGaloisConnectionCoarseGrainPoissonLift` | yes | 3 | pass fail fail | pass | 0 | 0.6667 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `GaloisPair.notGaloisConnectionPoissonLiftCoarseGrain` | yes | 3 | pass fail fail | pass | 0 | 0.6667 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `GaloisPair.poissonLiftR0` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `GaloisPair.table.R10` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `GaloisPair.table.R11` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `GaloisPair.table.R12` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `GaloisPair.table.R13` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `GaloisPair.table.R14` | yes | 2 | pass fail | fail | 0 | 0.25 |  |
| `GaloisPair.table.R15` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `GaloisPair.table.R9` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0]) |
| `Hierarchy.R23` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `Hierarchy.R24` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `Hierarchy.R25` | yes | 3 | pass fail fail | pass | 0 | 0.0 | shadow_trusted_free (identical to impl: [1]) (hints: backward_unused_shadows) |
| `Hierarchy.R26` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `Hierarchy.R27` | yes | 5 | fail fail fail fail fail | pass | 0 | 0.0 | shadow_trusted_free (hints: backward_unused_shadows) |
| `Hierarchy.R28` | yes | 6 | fail fail fail fail fail fail | pass | 0 | 0.5 |  (hints: backward_unused_shadows) |
| `Hierarchy.edgeLiftR0EqIff` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `Hierarchy.fullLtPairThree` | yes | 3 | pass fail fail | pass | 0 | 0.6667 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `Hierarchy.header.fullGtPair` | no | 5 | missing missing missing missing missing | missing | 0 | 0.0 | gap |
| `Hierarchy.header.pairGtEbcmGtMeanField` | yes | 5 | pass pass fail fail fail | pass | 0 | 0.7 |  (hints: backward_unused_shadows) |
| `Hierarchy.pairLtFull` | yes | 3 | pass fail fail | pass | 0 | 0.6667 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `Hierarchy.table.R23` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `Hierarchy.table.R24` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `Hierarchy.table.R25` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `Hierarchy.table.R26` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `Hierarchy.table.R27` | yes | 1 | fail | pass | 0 | 0.5 |  |
| `Hierarchy.table.R28` | yes | 4 | fail fail fail fail | pass | 0 | 0.5 |  (hints: backward_unused_shadows) |
| `InvariantRegion.R113` | yes | 1 | pass | fail | 0 | 0.5 |  |
| `InvariantRegion.R114` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `InvariantRegion.R115` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [0]) |
| `InvariantRegion.R116a` | yes | 1 | fail | fail | 0 | 0.0 |  |
| `InvariantRegion.R117a` | yes | 1 | fail | fail | 0 | 0.0 |  |
| `InvariantRegion.R118a` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `InvariantRegion.R119a` | yes | 1 | pass | fail | 0 | 0.5 |  |
| `InvariantRegion.R120` | yes | 1 | pass | fail | 0 | 0.5 |  |
| `InvariantRegion.R120b` | yes | 3 | fail fail fail | pass | 0 | 0.5 |  (hints: backward_unused_shadows) |
| `InvariantRegion.R120b.guard` | yes | 1 | fail | pass | 0 | 0.5 |  |
| `InvariantRegion.R121` | yes | 2 | pass pass | fail | 0 | 0.5 |  |
| `InvariantRegion.R122a` | yes | 2 | fail fail | fail | 0 | 0.0 |  |
| `InvariantRegion.R123a` | yes | 6 | fail fail pass fail fail fail | fail | 0 | 0.0833 |  |
| `InvariantRegion.R123b` | yes | 3 | fail fail fail | fail | 0 | 0.0 |  |
| `InvariantRegion.R123c` | no | 3 | missing missing missing | missing | 0 | 0.0 | gap, shadow_trusted_free |
| `InvariantRegion.R123d` | yes | 1 | pass | fail | 0 | 0.5 |  |
| `InvariantRegion.R123e` | yes | 1 | fail | pass | 0 | 0.5 |  |
| `InvariantRegion.R123f` | yes | 4 | fail fail fail fail | fail | 0 | 0.0 |  |
| `InvariantRegion.header.faceConditions` | yes | 5 | fail fail fail pass fail | fail | 0 | 0.1 |  |
| `InvariantRegion.header.invariance.I` | no | 1 | missing | missing | 0 | 0.0 | gap |
| `InvariantRegion.header.invariance.R` | no | 2 | missing missing | missing | 0 | 0.0 | gap |
| `InvariantRegion.header.invariance.S` | no | 2 | missing missing | missing | 0 | 0.0 | gap |
| `InvariantRegion.header.invariance.phi` | no | 2 | missing missing | missing | 0 | 0.0 | gap |
| `InvariantRegion.header.invariance.theta` | no | 2 | missing missing | missing | 0 | 0.0 | gap |
| `InvariantRegion.header.model` | no | 1 | missing | missing | 0 | 0.0 | gap |
| `InvariantRegion.header.thetaFace.a` | yes | 2 | fail fail | fail | 0 | 0.0 |  |
| `InvariantRegion.header.thetaFace.b` | no | 1 | missing | missing | 0 | 0.0 | gap, shadow_trusted_free |
| `InvariantRegion.header.thetaFace.c` | no | 2 | missing missing | missing | 0 | 0.0 | gap |
| `InvariantRegion.iDotAtZero` | yes | 2 | fail fail | fail | 0 | 0.0 |  |
| `InvariantRegion.iDotGeneral.a` | yes | 1 | fail | vacuous | 0 | 0.0 |  |
| `InvariantRegion.iDotGeneral.b` | yes | 2 | fail fail | fail | 0 | 0.0 |  |
| `InvariantRegion.iNonnegFromRegion` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [2]) (hints: backward_unused_shadows) |
| `InvariantRegion.missingSeedFactorOvercounts` | yes | 2 | fail fail | pass | 0 | 0.5 |  (hints: backward_unused_shadows) |
| `InvariantRegion.pgfEvalOne` | yes | 2 | pass fail | pass | 0 | 0.75 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `InvariantRegion.phiIDotCorrectFactors` | yes | 3 | fail fail fail | fail | 0 | 0.0 |  |
| `InvariantRegion.phiIDotCorrectZeroAtBoundary` | yes | 1 | fail | fail | 0 | 0.0 |  |
| `InvariantRegion.phiIDotFactors.a` | yes | 1 | fail | fail | 0 | 0.0 |  |
| `InvariantRegion.phiIDotFactors.b` | no | 4 | missing missing missing missing | missing | 0 | 0.0 | gap |
| `InvariantRegion.phiILeTheta` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `InvariantRegion.sFromRegion` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [0]) |
| `InvariantRegion.thetaLowerBoundaryAbsorbing` | yes | 1 | fail | fail | 0 | 0.0 |  |
| `MarginalisationCharacterization.c4RealIsKirkwoodForm` | yes | 7 | pass pass fail fail fail fail fail | pass | 0 | 0.6429 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `MarginalisationCharacterization.closureFamilies.linear` | no | 4 | missing missing missing missing | missing | 0 | 0.0 | gap, shadow_trusted_free |
| `MarginalisationCharacterization.existsEquivariantIffFibrewise` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `MarginalisationCharacterization.existsKirkwoodFormEquivariant` | yes | 2 | fail fail | pass | 0 | 0.5 |  |
| `MarginalisationCharacterization.header.T1forces` | yes | 3 | pass fail fail | fail | 0 | 0.1667 |  |
| `MarginalisationCharacterization.header.T2witness` | yes | 1 | pass | fail | 0 | 0.5 |  |
| `MarginalisationCharacterization.header.T3` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `MarginalisationCharacterization.header.interLevel` | yes | 2 | fail fail | fail | 0 | 0.0 |  |
| `MarginalisationCharacterization.header.kkrNotSufficient` | yes | 2 | pass pass | fail | 0 | 0.5 |  |
| `MarginalisationCharacterization.header.onlyTrivial` | no | 4 | missing missing missing missing | missing | 0 | 0.0 | gap |
| `MarginalisationCharacterization.isLinearAdmitsEquivariant` | yes | 3 | fail fail fail | fail | 0 | 0.0 |  |
| `MarginalisationCharacterization.kirkwoodFormNotEquivariant` | yes | 1 | fail | pass | 0 | 0.5 |  |
| `MarginalisationCharacterization.kkrNecessaryNotSufficient.concretely` | no | 4 | missing missing missing missing | missing | 0 | 0.0 | gap |
| `MarginalisationCharacterization.kkrNecessaryNotSufficient.formal` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `MarginalisationCharacterization.kkrNecessaryNotSufficient.notSufficient` | yes | 3 | pass fail fail | fail | 0 | 0.1667 |  |
| `MarginalisationCharacterization.linearAdmitsEquivariantIff` | yes | 3 | pass pass fail | pass | 0 | 0.0 | shadow_trusted_free (hints: backward_unused_shadows) |
| `MarginalisationCharacterization.linearClosureEquivariant.a` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `MarginalisationCharacterization.linearClosureEquivariant.b` | no | 1 | missing | missing | 0 | 0.0 | gap |
| `MarginalisationCharacterization.table.T3a` | yes | 2 | fail fail | fail | 0 | 0.0 |  |
| `MarginalisationCharacterization.table.T3b` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `MarginalisationCharacterization.table.T3c.b` | yes | 2 | pass pass | fail | 0 | 0.5 |  |
| `MarginalisationDynamicalGap.algebraicGapAtWitness.a` | yes | 2 | pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows) |
| `MarginalisationDynamicalGap.algebraicGapWitness` | yes | 4 | pass fail fail fail | pass | 0 | 0.625 |  (hints: backward_unused_shadows) |
| `MarginalisationDynamicalGap.f3RealIsKirkwoodForm` | yes | 4 | pass pass fail fail | pass | 0 | 0.75 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `MarginalisationDynamicalGap.fibreCollapseObstruction` | yes | 1 | pass | vacuous | 0 | 0.5 |  |
| `MarginalisationDynamicalGap.header.T6.a` | yes | 1 | fail | fail | 0 | 0.0 |  |
| `MarginalisationDynamicalGap.header.T6.b` | no | 4 | missing missing missing missing | missing | 0 | 0.0 | gap |
| `MarginalisationDynamicalGap.header.overview` | yes | 4 | fail fail fail fail | fail | 0 | 0.0 | hypothesis_refuted |
| `MarginalisationDynamicalGap.kirkwoodFormMatchesAtWitness` | yes | 3 | pass fail fail | fail | 0 | 0.1667 |  |
| `MarginalisationDynamicalGap.kirkwoodNotEquivariantViaT4` | yes | 2 | pass fail | pass | 0 | 0.75 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `MarginalisationDynamicalGap.localGapHasDerivAtZero` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `MarginalisationDynamicalGap.localGapNormGeHalfEpsT` | yes | 1 | fail | fail | 0 | 0.0 |  |
| `MarginalisationDynamicalGap.mRealLinCLMApply` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `MarginalisationDynamicalGap.noFlowF3Real` | yes | 2 | pass fail | pass | 0 | 0.75 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `MarginalisationDynamicalGap.noGlobalSolutionSqDivFour` | yes | 4 | pass fail fail fail | pass | 0 | 0.0 | shadow_trusted_free (hints: backward_unused_shadows) |
| `MarginalisationDynamicalGap.normGeHalfEpsTOfHasDerivAt` | yes | 1 | fail | fail | 0 | 0.0 | shadow_trusted_free |
| `MarginalisationDynamicalGap.refinementFailureExists.a` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `MarginalisationDynamicalGap.refinementFailureExists.b` | yes | 3 | fail fail fail | fail | 0 | 0.0 |  |
| `MarginalisationDynamicalGap.refinementFailureExists.c` | no | 1 | missing | missing | 0 | 0.0 | gap |
| `MarginalisationDynamicalGap.trajectoryGapAtZero` | yes | 2 | pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows, witness_missing) |
| `MarginalisationDynamicalGap.trajectoryGapHasDerivAtZero` | yes | 2 | pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows, witness_missing) |
| `MarginalisationDynamicalGap.trajectoryGapNormGeHalfEpsT` | yes | 1 | fail | fail | 0 | 0.0 |  (hints: witness_missing) |
| `MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.a` | yes | 2 | pass pass | pass | 0 | 0.0 | hypothesis_refuted (hints: backward_unused_shadows) |
| `MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.b` | yes | 3 | pass fail fail | pass | 0 | 0.0 | shadow_trusted_free (identical to impl: [1]) (hints: backward_unused_shadows) |
| `MarginalisationDynamicalGap.witnessLocalGapGe` | yes | 2 | pass fail | pass | 0 | 0.75 |  (hints: backward_unused_shadows) |
| `MarginalisationDynamicalGap.witnessLocalGapHasDerivAt` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `MarginalisationDynamicalGap.witnessLocalSolutionsExist` | yes | 3 | fail fail fail | fail | 0 | 0.0 |  |
| `MarginalisationFunctor.RM1` | yes | 3 | pass pass fail | pass | 0 | 0.8333 |  (hints: backward_unused_shadows) |
| `MarginalisationFunctor.RM2` | yes | 1 | pass | pass | 1 | 1.0 |  (hints: witness_missing) |
| `MarginalisationFunctor.RM3` | yes | 1 | pass | pass | 1 | 1.0 |  (hints: witness_missing) |
| `MarginalisationFunctor.RM4a` | yes | 2 | pass pass | pass | 1 | 1.0 |  (hints: witness_missing) |
| `MarginalisationFunctor.RM4b` | yes | 3 | pass pass fail | fail | 0 | 0.3333 |  |
| `MarginalisationFunctor.header.T1` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `MarginalisationFunctor.header.closedNeedNotCommute` | yes | 3 | fail fail pass | fail | 0 | 0.1667 |  |
| `MarginalisationFunctor.rhsCommuteOfLocalTrajCommute` | yes | 1 | pass | fail | 0 | 0.0 | shadow_trusted_free |
| `MarginalisationFunctor.table.M1` | no | 1 | missing | missing | 0 | 0.0 | gap |
| `MessagePassingBridge.R60` | yes | 3 | pass fail pass | pass | 0 | 0.8333 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `MessagePassingBridge.R61a` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `MessagePassingBridge.R61b` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `MessagePassingBridge.R62d` | yes | 2 | fail fail | pass | 0 | 0.0 | shadow_trusted_free (hints: backward_unused_shadows) |
| `MessagePassingBridge.R63d` | yes | 2 | pass fail | pass | 0 | 0.75 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `MessagePassingBridge.R64` | yes | 5 | pass fail fail fail fail | pass | 0 | 0.6 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `MessagePassingBridge.R65` | yes | 3 | fail pass fail | fail | 0 | 0.1667 |  |
| `MessagePassingBridge.R66a` | yes | 1 | fail | fail | 0 | 0.0 | shadow_trusted_free |
| `MessagePassingBridge.R66e` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `MessagePassingBridge.R67` | yes | 5 | fail fail fail fail pass | pass | 0 | 0.6 |  (identical to impl: [5]) (hints: backward_unused_shadows) |
| `MessagePassingBridge.R68a` | yes | 2 | fail fail | fail | 0 | 0.0 |  |
| `MessagePassingBridge.R68b` | no | 6 | missing missing missing missing missing missing | missing | 0 | 0.0 | gap |
| `MessagePassingBridge.ebcmMpRoundtrip` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `MessagePassingBridge.markovEbcmDim` | yes | 1 | fail | vacuous | 0 | 0.0 |  |
| `MessagePassingBridge.pdeToOdeReduction` | yes | 1 | fail | fail | 0 | 0.0 |  |
| `MessagePassingBridge.poissonMarkovR0Agree` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `MessagePassingBridge.table.R60` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `MessagePassingBridge.table.R61` | yes | 4 | pass pass pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows) |
| `MessagePassingBridge.table.R62` | yes | 1 | fail | fail | 0 | 0.0 | shadow_trusted_free |
| `MessagePassingBridge.table.R63` | yes | 5 | fail fail fail fail fail | vacuous | 0 | 0.0 |  |
| `MessagePassingBridge.table.R64` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `MessagePassingBridge.table.R65` | yes | 6 | fail fail fail pass pass pass | pass | 0 | 0.75 |  (hints: backward_unused_shadows) |
| `MessagePassingBridge.table.R66` | yes | 1 | fail | fail | 0 | 0.0 | shadow_trusted_free |
| `MessagePassingBridge.table.R67` | yes | 4 | fail fail fail fail | fail | 0 | 0.0 |  |
| `MessagePassingBridge.table.R68` | yes | 2 | fail fail | fail | 0 | 0.0 |  |
| `MethodOfStages.R87` | yes | 3 | fail fail fail | pass | 0 | 0.0 | shadow_trusted_free (hints: backward_unused_shadows) |
| `MethodOfStages.R88` | yes | 2 | fail fail | pass | 0 | 0.5 |  (hints: backward_unused_shadows) |
| `MethodOfStages.R89a` | yes | 2 | fail fail | pass | 0 | 0.5 |  (hints: backward_unused_shadows) |
| `MethodOfStages.R90a` | yes | 2 | fail fail | pass | 0 | 0.5 |  (hints: backward_unused_shadows) |
| `MethodOfStages.R91a` | yes | 2 | pass fail | pass | 0 | 0.0 | shadow_trusted_free (identical to impl: [1]) (hints: backward_unused_shadows) |
| `MethodOfStages.R92` | yes | 1 | fail | vacuous | 0 | 0.0 | shadow_trusted_free |
| `MethodOfStages.R93a` | no | 1 | missing | missing | 0 | 0.0 | gap |
| `MethodOfStages.R93c` | yes | 2 | fail pass | pass | 0 | 0.0 | shadow_trusted_free (identical to impl: [2]) (hints: backward_unused_shadows) |
| `MethodOfStages.R94b` | yes | 1 | fail | pass | 0 | 0.5 |  |
| `MethodOfStages.erlangTransmissibilityOneLtTwo` | yes | 2 | pass fail | pass | 0 | 0.75 |  (hints: backward_unused_shadows) |
| `MethodOfStages.erlangTransmissibilityValues` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `Obstructions.R17` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `Obstructions.R18a` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `Obstructions.R18b` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `Obstructions.R18c` | yes | 2 | fail fail | fail | 0 | 0.0 |  |
| `Obstructions.R19a` | yes | 3 | pass fail fail | pass | 0 | 0.6667 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `Obstructions.R19b` | yes | 4 | pass pass fail fail | pass | 0 | 0.75 |  (identical to impl: [2]) (hints: backward_unused_shadows) |
| `Obstructions.R20a` | yes | 2 | pass fail | pass | 0 | 0.75 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `Obstructions.R20b` | yes | 4 | pass pass pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows) |
| `Obstructions.R21a` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `Obstructions.R21b` | yes | 3 | pass fail fail | pass | 0 | 0.6667 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `Obstructions.R22a` | yes | 3 | fail fail pass | pass | 0 | 0.6667 |  (hints: backward_unused_shadows) |
| `Obstructions.R23a` | yes | 4 | pass pass pass pass | pass | 1 | 1.0 |  |
| `Obstructions.R23b` | yes | 4 | pass pass fail fail | fail | 0 | 0.25 |  |
| `Obstructions.R23c` | yes | 3 | pass fail fail | fail | 0 | 0.1667 |  |
| `Obstructions.R23d` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `Obstructions.R24a` | yes | 3 | pass fail fail | fail | 0 | 0.1667 |  |
| `Obstructions.R24b` | no | 2 | missing missing | missing | 0 | 0.0 | gap |
| `Obstructions.R24c` | yes | 1 | fail | fail | 0 | 0.0 |  |
| `Obstructions.R25a` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `Obstructions.R25b` | yes | 3 | fail fail pass | pass | 0 | 0.6667 |  (hints: backward_unused_shadows) |
| `Obstructions.erlangIsOde` | yes | 2 | pass fail | pass | 0 | 0.75 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `Obstructions.header.T1ImpliesTrajectoryFailure` | no | 2 | missing missing | missing | 0 | 0.0 | gap |
| `Obstructions.header.kirkwoodHierarchyInconsistent` | yes | 3 | fail pass fail | pass | 0 | 0.6667 |  (identical to impl: [2]) (hints: backward_unused_shadows) |
| `Obstructions.header.networkNotObstruction` | yes | 2 | pass fail | pass | 0 | 0.75 |  (hints: backward_unused_shadows) |
| `Obstructions.header.smallestFaithfulWitness` | no | 3 | missing missing missing | missing | 0 | 0.0 | gap |
| `Obstructions.header.surrogateForms` | no | 3 | missing missing missing | missing | 0 | 0.0 | gap |
| `Obstructions.kirkwoodObstructionWitnessValue-a` | yes | 2 | pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows) |
| `Obstructions.markovIsOde` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `Obstructions.standardMostCompact` | yes | 3 | fail fail fail | fail | 0 | 0.0 |  |
| `Obstructions.table.R17` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `Obstructions.table.R18` | yes | 3 | pass pass fail | pass | 0 | 0.8333 |  (hints: backward_unused_shadows) |
| `Obstructions.table.R19` | yes | 5 | pass fail fail pass pass | fail | 0 | 0.3 |  |
| `Obstructions.table.R20` | yes | 3 | pass pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows) |
| `Obstructions.table.R21` | yes | 3 | pass fail fail | pass | 0 | 0.6667 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `Obstructions.table.R22` | yes | 3 | fail fail pass | fail | 0 | 0.1667 |  |
| `Obstructions.table.R23` | yes | 4 | pass pass pass pass | pass | 1 | 1.0 |  |
| `Obstructions.table.R24` | no | 1 | missing | missing | 0 | 0.0 | gap |
| `PairwiseClosureConditions.barnardStyleClosureSafe` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `PairwiseClosureConditions.barnardWeightsNonneg` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `PairwiseClosureConditions.barnardWeightsNormalized.a` | yes | 1 | pass | fail | 0 | 0.5 |  |
| `PairwiseClosureConditions.barnardWeightsNormalized.b` | no | 2 | missing missing | missing | 0 | 0.0 | gap |
| `PairwiseClosureConditions.convexMixNonneg` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `PairwiseClosureConditions.header.conservationNotPositivity` | yes | 2 | fail fail | fail | 0 | 0.0 |  |
| `PairwiseClosureConditions.header.nonnegNeedsPointwise` | yes | 2 | pass fail | fail | 0 | 0.25 |  |
| `PairwiseClosureConditions.header.normalizationOnly` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [2]) (hints: backward_unused_shadows) |
| `PairwiseClosureConditions.header.safeRegime` | yes | 4 | pass pass pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows) |
| `PairwiseClosureConditions.keelingFactorNonneg` | yes | 2 | pass fail | pass | 0 | 0.75 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `PairwiseClosureConditions.keelingStyleClosureSafe.a` | yes | 5 | pass pass fail fail fail | pass | 0 | 0.7 |  (hints: backward_unused_shadows) |
| `PairwiseClosureConditions.keelingStyleClosureSafe.b` | yes | 2 | pass fail | fail | 0 | 0.25 |  |
| `PairwiseClosureConditions.keelingWeightsNonneg` | yes | 2 | pass fail | pass | 0 | 0.75 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `PairwiseClosureConditions.negativeWeightGivesNegativeTriple.a` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `PairwiseClosureConditions.negativeWeightGivesNegativeTriple.b` | yes | 2 | fail fail | fail | 0 | 0.0 |  |
| `PairwiseClosureConditions.normalizedNonnegativeClosureSafe` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `PairwiseClosureConditions.tripleMassConserved` | yes | 2 | pass pass | pass | 1 | 1.0 |  (identical to impl: [2]) (hints: backward_unused_shadows) |
| `PairwiseClosureConditions.tripleTermNonneg` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `PairwiseClosureConditions.weightInUnitInterval` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `SEIREquations.dTheta` | yes | 2 | fail fail | fail | 0 | 0.0 |  |
| `SEIREquations.edgeHazard` | yes | 3 | pass pass fail | pass | 0 | 0.8333 |  (identical to impl: [2]) (hints: backward_unused_shadows) |
| `SEIREquations.edgeHazardIndependentOfE` | yes | 1 | pass | fail | 0 | 0.5 |  |
| `SEIREquations.iPopLeWrong` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `SEIREquations.iPopWrongNonzeroAtSeed` | yes | 2 | fail pass | pass | 0 | 0.75 |  (hints: backward_unused_shadows) |
| `SEIREquations.iPopZeroAtSeed-a` | yes | 1 | fail | pass | 0 | 0.5 |  |
| `SEIREquations.iPopZeroAtSeed-b` | yes | 2 | fail fail | fail | 0 | 0.0 |  |
| `SEIREquations.seirIGrowthBounded-a` | yes | 2 | pass fail | pass | 0 | 0.75 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `SEIREquations.seirPopulationConservation` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `SEIREquations.seirThetaNonincreasing` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `SEIREquations.table.SEIR1` | yes | 2 | fail fail | pass | 0 | 0.5 |  (hints: backward_unused_shadows) |
| `SEIREquations.table.SEIR2` | yes | 1 | pass | fail | 0 | 0.5 |  |
| `SEIREquations.table.SEIR3` | yes | 1 | fail | fail | 0 | 0.0 |  |
| `SEIREquations.table.SEIR4` | yes | 2 | fail fail | fail | 0 | 0.0 |  |
| `SurvivalBridge.R42` | yes | 3 | pass fail fail | pass | 0 | 0.6667 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `SurvivalBridge.R43a` | yes | 2 | fail fail | vacuous | 0 | 0.0 |  |
| `SurvivalBridge.R44a` | yes | 2 | fail fail | pass | 0 | 0.5 |  (hints: backward_unused_shadows) |
| `SurvivalBridge.R45a` | yes | 3 | pass pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows) |
| `SurvivalBridge.R45b` | yes | 3 | fail pass fail | pass | 0 | 0.6667 |  (hints: backward_unused_shadows) |
| `SurvivalBridge.R46b` | no | 1 | missing | missing | 0 | 0.0 | gap, shadow_trusted_free |
| `SurvivalBridge.R46c` | yes | 3 | pass fail fail | pass | 0 | 0.6667 |  (hints: backward_unused_shadows) |
| `SurvivalBridge.R47a` | yes | 3 | pass fail fail | pass | 0 | 0.0 | shadow_trusted_free (identical to impl: [1]) (hints: backward_unused_shadows) |
| `SurvivalBridge.R47b` | yes | 1 | fail | fail | 0 | 0.0 | shadow_trusted_free |
| `SurvivalBridge.R48a` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `SurvivalBridge.R48c` | no | 6 | missing missing missing missing missing missing | missing | 0 | 0.0 | gap |
| `SurvivalBridge.R49a` | yes | 4 | pass fail fail fail | pass | 0 | 0.0 | shadow_trusted_free (identical to impl: [1]) (hints: backward_unused_shadows) |
| `SurvivalBridge.R49b` | no | 7 | missing missing missing missing missing missing missing | missing | 0 | 0.0 | gap, shadow_trusted_free |
| `SurvivalBridge.R50a` | yes | 5 | pass fail fail fail fail | fail | 0 | 0.0 | shadow_trusted_free |
| `SurvivalBridge.R50b` | yes | 3 | fail pass fail | fail | 0 | 0.1667 |  |
| `SurvivalBridge.R50e` | yes | 1 | fail | fail | 0 | 0.0 |  |
| `SurvivalBridge.closureKappa-c` | no | 4 | missing missing missing missing | missing | 0 | 0.0 | gap, shadow_trusted_free |
| `SurvivalBridge.dsaVolzRoundtrip` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `SurvivalBridge.header.categorical.eta` | no | 4 | missing missing missing missing | missing | 0 | 0.0 | gap |
| `SurvivalBridge.header.kappaInvariant-b` | yes | 6 | fail fail fail fail fail fail | fail | 0 | 0.0 | shadow_trusted_free |
| `SurvivalBridge.table.R42` | yes | 3 | pass fail fail | pass | 0 | 0.0 | shadow_trusted_free (identical to impl: [1]) (hints: backward_unused_shadows) |
| `SurvivalBridge.table.R43` | yes | 3 | pass fail fail | pass | 0 | 0.0 | shadow_trusted_free (identical to impl: [1]) (hints: backward_unused_shadows) |
| `SurvivalBridge.table.R44` | yes | 3 | pass fail fail | pass | 0 | 0.0 | shadow_trusted_free (hints: backward_unused_shadows) |
| `SurvivalBridge.table.R45` | yes | 4 | pass fail pass fail | pass | 0 | 0.75 |  (hints: backward_unused_shadows) |
| `SurvivalBridge.table.R46` | no | 1 | missing | missing | 0 | 0.0 | gap, shadow_trusted_free |
| `SurvivalBridge.table.R47` | yes | 2 | pass fail | pass | 0 | 0.75 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `SurvivalBridge.table.R48` | yes | 2 | fail fail | vacuous | 0 | 0.0 |  |
| `SurvivalBridge.table.R49` | yes | 2 | fail fail | vacuous | 0 | 0.0 | shadow_trusted_free |
| `SurvivalBridge.table.R50` | yes | 5 | pass fail fail fail fail | fail | 0 | 0.0 | shadow_trusted_free |
| `SurvivalBridge.volzState-a` | no | 4 | missing missing missing missing | missing | 0 | 0.0 | gap |
| `SurvivalBridge.volzState-b` | yes | 2 | pass fail | fail | 0 | 0.25 |  |
| `VolzMeyersEquations.edgePartition` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `VolzMeyersEquations.fastMixingP1Equilibrium-a` | yes | 1 | fail | fail | 0 | 0.0 |  |
| `VolzMeyersEquations.fastMixingP1Equilibrium-b` | no | 1 | missing | missing | 0 | 0.0 | gap |
| `VolzMeyersEquations.fastMixingP1Equilibrium-d` | yes | 2 | fail fail | fail | 0 | 0.0 |  |
| `VolzMeyersEquations.header.popIEquation` | no | 3 | missing missing missing | missing | 0 | 0.0 | gap |
| `VolzMeyersEquations.icEdgePartition` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `VolzMeyersEquations.icPopulation` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `VolzMeyersEquations.icTheta` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `VolzMeyersEquations.massActionIncidence-a` | yes | 4 | fail fail fail fail | fail | 0 | 0.0 |  |
| `VolzMeyersEquations.massActionIncidence-b` | yes | 1 | fail | fail | 0 | 0.0 |  |
| `VolzMeyersEquations.populationInflux-a` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `VolzMeyersEquations.populationInflux-b` | no | 2 | missing missing | missing | 0 | 0.0 | gap |
| `VolzMeyersEquations.sNonincreasing-a` | yes | 2 | fail fail | fail | 0 | 0.0 |  |
| `VolzMeyersEquations.sNonincreasing-b` | yes | 2 | fail fail | fail | 0 | 0.0 |  |
| `VolzMeyersEquations.staticThetaEq-a` | yes | 2 | fail fail | fail | 0 | 0.0 |  |
| `VolzMeyersEquations.table.VM1` | yes | 2 | pass fail | pass | 0 | 0.75 |  (identical to impl: [1]) (hints: backward_unused_shadows) |
| `VolzMeyersEquations.table.VM2` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `VolzMeyersEquations.table.VM3` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `VolzMeyersEquations.table.VM4` | yes | 2 | fail fail | fail | 0 | 0.0 |  |
| `VolzMeyersEquations.table.VM5` | yes | 1 | fail | fail | 0 | 0.0 |  |
| `VolzMeyersEquations.table.VM6` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `VolzMeyersEquations.table.VM7` | no | 2 | missing missing | missing | 0 | 0.0 | gap |
| `VolzMeyersEquations.table.VM8` | yes | 3 | fail fail fail | fail | 0 | 0.0 |  |
| `VolzMeyersEquations.thetaNonincreasing` | yes | 2 | pass fail | pass | 0 | 0.75 |  (identical to impl: [1]) (hints: backward_unused_shadows) |

## Registry claims without a Lean registration

| id | group | required | status | impl | registry problems |
|---|---|---|---|---|---|
| `CategoricalComposition.R100.unitObject` | CategoricalComposition | no | missing |  |  |
| `CategoricalComposition.R100f.2` | CategoricalComposition | no | informal |  |  |
| `CategoricalComposition.R101.natTrans` | CategoricalComposition | no | missing |  |  |
| `CategoricalComposition.R102.pullback` | CategoricalComposition | no | missing |  |  |
| `CategoricalComposition.R102a.2` | CategoricalComposition | no | missing |  |  |
| `CategoricalComposition.R95.functor` | CategoricalComposition | no | missing |  |  |
| `CategoricalComposition.R95a.1` | CategoricalComposition | no | missing |  |  |
| `CategoricalComposition.R95b` | CategoricalComposition | no | informal |  |  |
| `CategoricalComposition.R95c` | CategoricalComposition | no | informal |  |  |
| `CategoricalComposition.R96.product` | CategoricalComposition | no | missing |  |  |
| `CategoricalComposition.R97.coproduct` | CategoricalComposition | no | missing |  |  |
| `CategoricalComposition.R97a.1` | CategoricalComposition | no | informal |  |  |
| `CategoricalComposition.R97d.2` | CategoricalComposition | no | missing |  |  |
| `CategoricalComposition.R98.natTrans` | CategoricalComposition | no | missing |  |  |
| `CategoricalComposition.R98b.2` | CategoricalComposition | no | missing |  |  |
| `CategoricalComposition.R98d.2` | CategoricalComposition | no | informal |  |  |
| `CategoricalComposition.R99.natTrans` | CategoricalComposition | no | missing |  |  |
| `CategoricalComposition.R99a.1` | CategoricalComposition | no | missing |  |  |
| `CategoricalComposition.R99c` | CategoricalComposition | no | informal |  |  |
| `CategoricalComposition.header.scope` | CategoricalComposition | no | missing |  |  |
| `ClosureTheorem.header.closureExact` | ClosureTheorem | no | missing |  |  |
| `ClosureTheorem.header.paperProofCorrect` | ClosureTheorem | no | missing |  |  |
| `ClosureTheorem.header.sorryFree` | ClosureTheorem | no | informal |  |  |
| `ClusteringExtension.R70-sec` | ClusteringExtension | no | missing |  |  |
| `ClusteringExtension.R74` | ClusteringExtension | no | informal |  |  |
| `CoarseGrain.header.coarseGrainMap` | CoarseGrain | no | missing |  |  |
| `ConvergenceTheorems.R105a` | ConvergenceTheorems | no | informal |  |  |
| `ConvergenceTheorems.R105b` | ConvergenceTheorems | no | informal |  |  |
| `ConvergenceTheorems.R105d.1` | ConvergenceTheorems | no | missing |  |  |
| `ConvergenceTheorems.R105e.1` | ConvergenceTheorems | no | missing |  |  |
| `ConvergenceTheorems.R106` | ConvergenceTheorems | no | informal |  |  |
| `ConvergenceTheorems.R106.header` | ConvergenceTheorems | no | missing |  |  |
| `ConvergenceTheorems.R110.header` | ConvergenceTheorems | no | missing |  |  |
| `ConvergenceTheorems.R110b.1` | ConvergenceTheorems | no | missing |  |  |
| `ConvergenceTheorems.R110c.1` | ConvergenceTheorems | no | missing |  |  |
| `ConvergenceTheorems.R111a` | ConvergenceTheorems | no | missing |  |  |
| `ConvergenceTheorems.R111b` | ConvergenceTheorems | no | missing |  |  |
| `ConvergenceTheorems.R111c` | ConvergenceTheorems | no | informal |  |  |
| `ConvergenceTheorems.header.scope` | ConvergenceTheorems | no | informal |  |  |
| `DegreeCorrelation.R79a` | DegreeCorrelation | no | informal |  |  |
| `DegreeCorrelation.R80` | DegreeCorrelation | no | informal |  |  |
| `DegreeCorrelation.R81` | DegreeCorrelation | no | informal |  |  |
| `DegreeCorrelation.R81-sec` | DegreeCorrelation | no | missing |  |  |
| `DegreeCorrelation.R81-sec.2` | DegreeCorrelation | no | missing |  |  |
| `DegreeCorrelation.R81-sec.3` | DegreeCorrelation | no | missing |  |  |
| `DegreeCorrelation.R81-sec.4` | DegreeCorrelation | no | missing |  |  |
| `DegreeCorrelation.R86f-2` | DegreeCorrelation | no | missing |  |  |
| `DegreeCorrelation.R86g-2` | DegreeCorrelation | no | informal |  |  |
| `Docs.cf.ambientODE` | Docs | no | missing |  |  |
| `Docs.cf.conj6_1` | Docs | no | informal |  |  |
| `Docs.cf.edgeCategory` | Docs | no | missing |  |  |
| `Docs.cf.edgeTreeFunctor` | Docs | no | missing |  |  |
| `Docs.cf.nodeCategory` | Docs | no | missing |  |  |
| `Docs.cf.prop3_1` | Docs | no | missing |  |  |
| `Docs.cf.thm3_3` | Docs | no | missing |  |  |
| `Docs.cf.thm8_1-overdispersed` | Docs | no | missing |  |  |
| `Docs.cf.thm8_1-underdispersed` | Docs | no | missing |  |  |
| `Docs.ms.T1-proofStatus` | Docs | no | informal |  |  |
| `Docs.ms.T2-proofStatus` | Docs | no | informal |  |  |
| `Docs.ms.T3-proofStatus` | Docs | no | informal |  |  |
| `Docs.ms.T5-empiricalBridge` | Docs | no | informal |  |  |
| `Docs.ms.exactInvariant` | Docs | no | informal |  |  |
| `Docs.ms.marginalisationLinearMap` | Docs | no | informal |  |  |
| `Docs.ms.overdetermined` | Docs | no | informal |  |  |
| `Docs.ms.realVsRational` | Docs | no | informal |  |  |
| `Docs.readme.leanScope` | Docs | no | informal |  |  |
| `Docs.readme.legacy` | Docs | no | informal |  |  |
| `Docs.readme.notSolutions` | Docs | no | informal |  |  |
| `Docs.vignettes.leanMarginalisation` | Docs | no | informal |  |  |
| `DynamicLimits.R31b` | DynamicLimits | no | missing |  |  |
| `DynamicLimits.header.staticLimitCollapse` | DynamicLimits | no | missing |  |  |
| `EpiCategory.header.twoCategories` | EpiCategory | no | missing |  |  |
| `GaloisPair.R14c` | GaloisPair | no | informal |  |  |
| `GaloisPair.poissonLiftPoisson` | GaloisPair | no | missing |  |  |
| `Hierarchy.header.stepsAreCoarseGrainings` | Hierarchy | no | missing |  |  |
| `InvariantRegion.R116b` | InvariantRegion | no | missing |  |  |
| `InvariantRegion.R116c` | InvariantRegion | no | missing |  |  |
| `InvariantRegion.R117b` | InvariantRegion | no | missing |  |  |
| `InvariantRegion.R118b` | InvariantRegion | no | missing |  |  |
| `InvariantRegion.R119b` | InvariantRegion | no | missing |  |  |
| `InvariantRegion.R122b` | InvariantRegion | no | informal |  |  |
| `InvariantRegion.R122c` | InvariantRegion | no | missing |  |  |
| `InvariantRegion.R122d` | InvariantRegion | no | missing |  |  |
| `InvariantRegion.R123g` | InvariantRegion | no | missing |  |  |
| `InvariantRegion.header.nagumoConditional` | InvariantRegion | no | missing |  |  |
| `MarginalisationCharacterization.closureFamilies.kirkwood` | MarginalisationCharacterization | no | informal |  |  |
| `MarginalisationCharacterization.header.kkrCharacterization` | MarginalisationCharacterization | no | informal |  |  |
| `MarginalisationCharacterization.header.kkrNecessary` | MarginalisationCharacterization | no | missing |  |  |
| `MarginalisationCharacterization.kkrNecessaryNotSufficient.necessary` | MarginalisationCharacterization | no | missing |  |  |
| `MarginalisationCharacterization.table.T3c.a` | MarginalisationCharacterization | no | informal |  |  |
| `MarginalisationDynamicalGap.algebraicGapAtWitness.b` | MarginalisationDynamicalGap | no | informal |  |  |
| `MarginalisationDynamicalGap.header.T6.c` | MarginalisationDynamicalGap | no | informal |  |  |
| `MarginalisationDynamicalGap.header.bridge` | MarginalisationDynamicalGap | no | informal |  |  |
| `MarginalisationDynamicalGap.noFlowF3Real.b` | MarginalisationDynamicalGap | no | informal |  |  |
| `MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.c` | MarginalisationDynamicalGap | no | informal |  |  |
| `MarginalisationFunctor.header.exactMarginalises` | MarginalisationFunctor | no | missing |  |  |
| `MarginalisationFunctor.header.scaffolding` | MarginalisationFunctor | no | informal |  |  |
| `MarginalisationFunctor.uniqueFlow.c1` | MarginalisationFunctor | no | missing |  |  |
| `MessagePassingBridge.R60b` | MessagePassingBridge | no | informal |  |  |
| `MessagePassingBridge.R62a` | MessagePassingBridge | no | missing |  |  |
| `MessagePassingBridge.R62b` | MessagePassingBridge | no | missing |  |  |
| `MessagePassingBridge.R62c` | MessagePassingBridge | no | missing |  |  |
| `MessagePassingBridge.R63a` | MessagePassingBridge | no | missing |  |  |
| `MessagePassingBridge.R63b` | MessagePassingBridge | no | missing |  |  |
| `MessagePassingBridge.R63c` | MessagePassingBridge | no | missing |  |  |
| `MessagePassingBridge.R66b` | MessagePassingBridge | no | missing |  |  |
| `MessagePassingBridge.R66c` | MessagePassingBridge | no | missing |  |  |
| `MessagePassingBridge.R66d` | MessagePassingBridge | no | missing |  |  |
| `MessagePassingBridge.R68c` | MessagePassingBridge | no | missing |  |  |
| `MessagePassingBridge.ebcmState` | MessagePassingBridge | no | missing |  |  |
| `MessagePassingBridge.header.hierarchy` | MessagePassingBridge | no | missing |  |  |
| `MessagePassingBridge.header.kkrThm2` | MessagePassingBridge | no | missing |  |  |
| `MessagePassingBridge.header.sherborneThm1` | MessagePassingBridge | no | missing |  |  |
| `MessagePassingBridge.summary.nonPT` | MessagePassingBridge | no | missing |  |  |
| `MessagePassingBridge.summary.ptDecouples` | MessagePassingBridge | no | missing |  |  |
| `MethodOfStages.R89b` | MethodOfStages | no | missing |  |  |
| `MethodOfStages.R90b` | MethodOfStages | no | missing |  |  |
| `MethodOfStages.R91b` | MethodOfStages | no | missing |  |  |
| `MethodOfStages.R93b` | MethodOfStages | no | missing |  |  |
| `MethodOfStages.R94a` | MethodOfStages | no | missing |  |  |
| `Obstructions.R19c` | Obstructions | no | informal |  |  |
| `Obstructions.R19d` | Obstructions | no | missing |  |  |
| `Obstructions.R20c` | Obstructions | no | informal |  |  |
| `Obstructions.R22b` | Obstructions | no | informal |  |  |
| `Obstructions.header.clusteringAddsVariables` | Obstructions | no | missing |  |  |
| `Obstructions.header.pdeCollapsesToOde` | Obstructions | no | missing |  |  |
| `Obstructions.header.standardAssumptions` | Obstructions | no | informal |  |  |
| `Obstructions.header.witnessCollapse` | Obstructions | no | missing |  |  |
| `Obstructions.kirkwoodObstructionWitnessValue-b` | Obstructions | no | informal |  |  |
| `PairwiseClosureConditions.keelingStyleClosureSafe.c` | PairwiseClosureConditions | no | missing |  |  |
| `SEIREquations.iPop` | SEIREquations | no | informal |  |  |
| `SEIREquations.seirIGrowthBounded-b` | SEIREquations | no | missing |  |  |
| `SEIREquations.table.SEIR5` | SEIREquations | no | missing |  |  |
| `SEIREquations.table.SEIR6` | SEIREquations | no | missing |  |  |
| `SurvivalBridge.R43b` | SurvivalBridge | no | informal |  |  |
| `SurvivalBridge.R44b` | SurvivalBridge | no | informal |  |  |
| `SurvivalBridge.R46a` | SurvivalBridge | no | missing |  |  |
| `SurvivalBridge.R48b` | SurvivalBridge | no | missing |  |  |
| `SurvivalBridge.R50c` | SurvivalBridge | no | missing |  |  |
| `SurvivalBridge.R50d` | SurvivalBridge | no | missing |  |  |
| `SurvivalBridge.closureKappa-b` | SurvivalBridge | no | missing |  |  |
| `SurvivalBridge.header.categorical.colimit` | SurvivalBridge | no | missing |  |  |
| `SurvivalBridge.header.categorical.naturalIso` | SurvivalBridge | no | missing |  |  |
| `SurvivalBridge.header.categorical.pairwiseIso` | SurvivalBridge | no | missing |  |  |
| `SurvivalBridge.header.kappaInvariant-a` | SurvivalBridge | no | missing |  |  |
| `SurvivalBridge.header.ptCharacterisation` | SurvivalBridge | no | missing |  |  |
| `SurvivalBridge.header.survivalEquation` | SurvivalBridge | no | missing |  |  |
| `SurvivalBridge.header.threeModelEquivalence` | SurvivalBridge | no | missing |  |  |
| `SurvivalBridge.table.R41` | SurvivalBridge | no | missing |  |  |
| `VolzMeyersEquations.fastMixingP1Equilibrium-c` | VolzMeyersEquations | no | missing |  |  |
| `VolzMeyersEquations.header.equationLevel` | VolzMeyersEquations | no | missing |  |  |
| `VolzMeyersEquations.header.table4System` | VolzMeyersEquations | no | missing |  |  |
| `VolzMeyersEquations.staticThetaEq-b` | VolzMeyersEquations | no | missing |  |  |
| `VolzMeyersEquations.staticThetaEq-c` | VolzMeyersEquations | no | missing |  |  |

## Required failures

* `CategoricalComposition.R96f`: forward 2: fail; forward 3: fail; forward 4: fail
* `CategoricalComposition.R97d.1`: forward 1: fail; backward: vacuous
* `CategoricalComposition.R98a`: forward 1: fail; forward 2: fail; backward: fail
* `CategoricalComposition.R98b.1`: forward 1: fail; backward: fail
* `CategoricalComposition.R98c.1`: forward 1: fail; backward: fail
* `CategoricalComposition.R98d.1`: incomplete: no sa_reference; no shadows; backward: fail; no shadows
* `CategoricalComposition.R99a.3`: forward 1: fail; forward 2: fail
* `CategoricalComposition.R99b.1`: forward 1: fail; backward: fail
* `CategoricalComposition.R100f.1`: shadow_trusted_free: S1 (Alignment.Shadows.CategoricalComposition.R100f_1.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 4645710261415564671; review: unreviewed); S2 (Alignment.Shadows.CategoricalComposition.R100f_1.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 2614311514533656700; review: unreviewed)
* `CategoricalComposition.R101a`: forward 1: fail; backward: fail
* `CategoricalComposition.R101b`: backward: fail
* `CategoricalComposition.R101c`: backward: fail
* `CategoricalComposition.R101d`: backward: fail
* `CategoricalComposition.R101e`: shadow_trusted_free: S1 (Alignment.Shadows.CategoricalComposition.R101e.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 11345656827471733963; review: unreviewed); forward 2: fail
* `CategoricalComposition.R102a.3`: forward 1: fail; backward: fail
* `CategoricalComposition.R102c.2`: backward: fail
* `CategoricalComposition.R102d.2`: forward 1: fail; backward: fail
* `CategoricalComposition.R102e.1`: forward 1: fail; forward 2: fail; backward: fail
* `CategoricalComposition.r0SumEqTrace`: forward 1: fail; backward: fail
* `CategoricalComposition.multiplexR0SumNeSpectral`: forward 1: fail; forward 2: fail; forward 3: fail; forward 4: fail; forward 5: fail; backward: fail
* `CategoricalComposition.stagesChangeTransmissibility`: forward 2: fail; forward 3: fail; forward 4: fail
* `ClosureTheorem.header.verificationStrategy`: shadow_trusted_free: S1 (Alignment.Shadows.ClosureTheorem.header_verificationStrategy.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 3137840644093547994; review: unreviewed); S2 (Alignment.Shadows.ClosureTheorem.header_verificationStrategy.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 1234849908418522215; review: unreviewed); S3 (Alignment.Shadows.ClosureTheorem.header_verificationStrategy.S3) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 2512323839188433664; review: unreviewed); forward 2: fail; forward 3: fail; backward: fail
* `ClosureTheorem.table.R52`: shadow_trusted_free: S1 (Alignment.Shadows.ClosureTheorem.table_R52.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 158470926229173236; review: unreviewed); S2 (Alignment.Shadows.ClosureTheorem.table_R52.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 17680666234752013126; review: unreviewed); forward 1: fail; forward 2: fail; backward: fail
* `ClosureTheorem.table.R53`: shadow_trusted_free: S1 (Alignment.Shadows.ClosureTheorem.table_R53.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 9961840620573049331; review: unreviewed); S2 (Alignment.Shadows.ClosureTheorem.table_R53.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 14054725648801240648; review: unreviewed); forward 1: fail; forward 2: fail; backward: fail
* `ClosureTheorem.table.R54`: shadow_trusted_free: S1 (Alignment.Shadows.ClosureTheorem.table_R54.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 4991563090386846176; review: unreviewed); S2 (Alignment.Shadows.ClosureTheorem.table_R54.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 8233478868788664652; review: unreviewed); forward 1: fail; forward 2: fail; backward: fail
* `ClosureTheorem.table.R55`: shadow_trusted_free: S1 (Alignment.Shadows.ClosureTheorem.table_R55.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 8937008213658706485; review: unreviewed); S2 (Alignment.Shadows.ClosureTheorem.table_R55.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 12963147099206911679; review: unreviewed); forward 1: fail; forward 2: fail; backward: fail
* `ClosureTheorem.table.R56`: shadow_trusted_free: S1 (Alignment.Shadows.ClosureTheorem.table_R56.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 14833468798300432852; review: unreviewed); forward 1: fail; backward: fail
* `ClosureTheorem.table.R57`: backward: fail
* `ClosureTheorem.table.R59`: forward 1: fail; forward 2: fail; backward: fail
* `ClosureTheorem.R52`: shadow_trusted_free: S1 (Alignment.Shadows.ClosureTheorem.R52.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 5736442423597233535; review: unreviewed); S2 (Alignment.Shadows.ClosureTheorem.R52.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 12489734717761764471; review: unreviewed); forward 2: fail; backward: fail
* `ClosureTheorem.poissonClosureRatio`: shadow_trusted_free: S2 (Alignment.Shadows.ClosureTheorem.poissonClosureRatio.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 7787854828244810692; review: unreviewed); forward 2: fail; backward: fail
* `ClosureTheorem.R53`: shadow_trusted_free: S1 (Alignment.Shadows.ClosureTheorem.R53.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 8102201160637063098; review: unreviewed); S2 (Alignment.Shadows.ClosureTheorem.R53.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 3800242781666044695; review: unreviewed); forward 2: fail; backward: fail
* `ClosureTheorem.binomialClosureRatio`: shadow_trusted_free: S2 (Alignment.Shadows.ClosureTheorem.binomialClosureRatio.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 5522051591303715438; review: unreviewed); forward 1: fail; forward 2: fail; backward: fail
* `ClosureTheorem.R54`: shadow_trusted_free: S1 (Alignment.Shadows.ClosureTheorem.R54.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 11984815519717754417; review: unreviewed); S2 (Alignment.Shadows.ClosureTheorem.R54.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 5535807201988576959; review: unreviewed); forward 1: fail; forward 2: fail; backward: fail
* `ClosureTheorem.negbin2ClosureRatio`: shadow_trusted_free: S2 (Alignment.Shadows.ClosureTheorem.negbin2ClosureRatio.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 15996686828414596910; review: unreviewed); forward 1: fail; forward 2: fail; backward: fail
* `ClosureTheorem.R55`: shadow_trusted_free: S1 (Alignment.Shadows.ClosureTheorem.R55.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 9395387580549500412; review: unreviewed); S2 (Alignment.Shadows.ClosureTheorem.R55.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 13520616302085932718; review: unreviewed); forward 1: fail; forward 2: fail; backward: fail
* `ClosureTheorem.negbin3ClosureRatio`: shadow_trusted_free: S2 (Alignment.Shadows.ClosureTheorem.negbin3ClosureRatio.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 564299106612444687; review: unreviewed); forward 1: fail; forward 2: fail; backward: fail
* `ClosureTheorem.R56`: shadow_trusted_free: S1 (Alignment.Shadows.ClosureTheorem.R56.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 10824917823408188949; review: unreviewed); S2 (Alignment.Shadows.ClosureTheorem.R56.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 660383570758253160; review: unreviewed); forward 1: fail; forward 2: fail; backward: fail
* `ClosureTheorem.R57`: shadow_trusted_free: S2 (Alignment.Shadows.ClosureTheorem.R57.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 3373795397357900506; review: unreviewed); S3 (Alignment.Shadows.ClosureTheorem.R57.S3) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 15027029890531176574; review: unreviewed); forward 2: fail; forward 3: fail; backward: fail
* `ClosureTheorem.R59`: shadow_trusted_free: S1 (Alignment.Shadows.ClosureTheorem.R59.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 16292072948732100427; review: unreviewed); forward 1: fail
* `ClosureTheorem.binomialKappaDeterminesN`: shadow_trusted_free: S2 (Alignment.Shadows.ClosureTheorem.binomialKappaDeterminesN.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 5777466738936095210; review: unreviewed); forward 1: fail; forward 2: fail; backward: fail
* `ClosureTheorem.binomialRecoverN`: shadow_trusted_free: S1 (Alignment.Shadows.ClosureTheorem.binomialRecoverN.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 3667473968810287908; review: unreviewed); forward 1: fail; backward: fail
* `ClosureTheorem.negbinKappaDeterminesR`: shadow_trusted_free: S1 (Alignment.Shadows.ClosureTheorem.negbinKappaDeterminesR.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 6859366675205680798; review: unreviewed); S2 (Alignment.Shadows.ClosureTheorem.negbinKappaDeterminesR.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 15160479782507934200; review: unreviewed); forward 2: fail
* `ClusteringExtension.R71-sec-a`: shadow_trusted_free: S1 (Alignment.Shadows.ClusteringExtension.R71_sec_a.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 8741874897961290610; review: unreviewed); S2 (Alignment.Shadows.ClusteringExtension.R71_sec_a.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 15635824020244536499; review: unreviewed); forward 1: fail; backward: fail
* `ClusteringExtension.R71-sec-b`: shadow_trusted_free: S1 (Alignment.Shadows.ClusteringExtension.R71_sec_b.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 8301577312851019754; review: unreviewed); S2 (Alignment.Shadows.ClusteringExtension.R71_sec_b.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 17891639165235094217; review: unreviewed); S3 (Alignment.Shadows.ClusteringExtension.R71_sec_b.S3) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 7798069742285525242; review: unreviewed); forward 1: fail; forward 2: fail; forward 3: fail; backward: fail
* `ClusteringExtension.R71a`: shadow_trusted_free: S1 (Alignment.Shadows.ClusteringExtension.R71a.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 2848181122043229357; review: unreviewed); backward: fail
* `ClusteringExtension.R71b`: shadow_trusted_free: S1 (Alignment.Shadows.ClusteringExtension.R71b.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 1527543137634270157; review: unreviewed); S2 (Alignment.Shadows.ClusteringExtension.R71b.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 12524949695741934103; review: unreviewed); S3 (Alignment.Shadows.ClusteringExtension.R71b.S3) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 13139182004517702821; review: unreviewed); forward 2: fail; forward 3: fail
* `ClusteringExtension.R73-sec-b`: shadow_trusted_free: S1 (Alignment.Shadows.ClusteringExtension.R73_sec_b.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 7354373933624218626; review: unreviewed); S2 (Alignment.Shadows.ClusteringExtension.R73_sec_b.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 130496183441507227; review: unreviewed); S3 (Alignment.Shadows.ClusteringExtension.R73_sec_b.S3) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 12839298447089389154; review: unreviewed); S4 (Alignment.Shadows.ClusteringExtension.R73_sec_b.S4) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 3693278195670602350; review: unreviewed); S5 (Alignment.Shadows.ClusteringExtension.R73_sec_b.S5) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 8641011339768408277; review: unreviewed); forward 2: fail; forward 3: fail; forward 4: fail; forward 5: fail
* `ClusteringExtension.R73`: shadow_trusted_free: S1 (Alignment.Shadows.ClusteringExtension.R73.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 2397481539701400779; review: unreviewed)
* `ClusteringExtension.R75-sec`: shadow_trusted_free: S1 (Alignment.Shadows.ClusteringExtension.R75_sec.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 16255756126079489805; review: unreviewed); S2 (Alignment.Shadows.ClusteringExtension.R75_sec.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 14490751464226690499; review: unreviewed); S4 (Alignment.Shadows.ClusteringExtension.R75_sec.S4) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 2459365703473738911; review: unreviewed); forward 1: fail; forward 2: fail; forward 3: fail; forward 4: fail; backward: fail
* `ClusteringExtension.R75`: shadow_trusted_free: S2 (Alignment.Shadows.ClusteringExtension.R75.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 3226202868403386447; review: unreviewed); forward 1: fail; forward 2: fail; backward: fail
* `ClusteringExtension.R76-sec`: backward: fail
* `ClusteringExtension.R76`: backward: fail
* `CoarseGrain.table.R6`: backward: fail
* `CoarseGrain.R6`: backward: fail
* `ConvergenceTheorems.R105c.4`: forward 1: fail; backward: fail
* `ConvergenceTheorems.R105d.2`: forward 1: fail
* `ConvergenceTheorems.R105e.2`: incomplete: no sa_reference; no shadows; backward: fail; no shadows
* `ConvergenceTheorems.R107b`: forward 1: fail; backward: fail
* `ConvergenceTheorems.R108b`: forward 2: fail
* `ConvergenceTheorems.R110.stability`: forward 1: fail; forward 2: fail; backward: fail
* `ConvergenceTheorems.R110b.3`: incomplete: no sa_reference; no shadows; backward: fail; no shadows
* `ConvergenceTheorems.R110c.2`: forward 1: fail; forward 2: fail; forward 3: fail; forward 4: fail; backward: vacuous
* `ConvergenceTheorems.R110d`: backward: fail
* `ConvergenceTheorems.R112b`: forward 1: fail; forward 2: fail; forward 3: fail; forward 4: fail; forward 5: fail
* `ConvergenceTheorems.R112c`: forward 2: fail
* `ConvergenceTheorems.R112d`: backward: fail
* `ConvergenceTheorems.r0MassActionEqEdge`: forward 2: fail
* `ConvergenceTheorems.sThetaChainRule`: backward: fail
* `DegreeCorrelation.R79-sec`: shadow_trusted_free: S1 (Alignment.Shadows.DegreeCorrelation.R79_sec.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 10496674773217584345; review: unreviewed); S2 (Alignment.Shadows.DegreeCorrelation.R79_sec.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 3987878779773114042; review: unreviewed); forward 1: fail; forward 2: fail; forward 3: fail; forward 4: fail; forward 5: fail; backward: fail
* `DegreeCorrelation.R79b`: forward 1: fail; forward 2: fail; backward: fail
* `DegreeCorrelation.R80-sec`: forward 1: fail; forward 2: fail; backward: fail
* `DegreeCorrelation.R83e`: forward 2: fail; forward 3: fail
* `DegreeCorrelation.R83f`: forward 2: fail; backward: fail
* `DegreeCorrelation.R84-sec`: shadow_trusted_free: S1 (Alignment.Shadows.DegreeCorrelation.R84_sec.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 6499021519330164613; review: unreviewed); forward 1: fail
* `DegreeCorrelation.R86a`: forward 1: fail; backward: fail
* `DegreeCorrelation.R86c`: backward: fail
* `DegreeCorrelation.R86h-1`: forward 1: fail; forward 2: fail; forward 5: fail; forward 6: fail; forward 7: fail; backward: fail
* `DegreeCorrelation.R86h-2`: shadow_trusted_free: S1 (Alignment.Shadows.DegreeCorrelation.R86h_2.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 14417567082359161917; review: unreviewed); S2 (Alignment.Shadows.DegreeCorrelation.R86h_2.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 6693015741707976227; review: unreviewed); S3 (Alignment.Shadows.DegreeCorrelation.R86h_2.S3) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 7675396514764475528; review: unreviewed); forward 1: fail; forward 2: fail; forward 3: fail; backward: fail
* `DegreeCorrelation.neutralDetK`: forward 1: fail; forward 2: fail; backward: fail
* `DegreeCorrelation.neutralTraceK`: forward 1: fail; backward: fail
* `DegreeCorrelation.neutralTraceCSubTraceK`: forward 1: fail; forward 2: fail; backward: fail
* `Docs.cf.thm3_2`: shadow_trusted_free: S1 (Alignment.Shadows.Docs.cf_thm3_2.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 15429395924667692775; review: unreviewed); forward 1: fail; backward: fail
* `Docs.cf.cor4_2-GF`: forward 2: fail; backward: fail
* `Docs.cf.thm4_3`: shadow_trusted_free: S4 (Alignment.Shadows.Docs.cf_thm4_3.S4) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 16644653117622581947; review: unreviewed); S5 (Alignment.Shadows.Docs.cf_thm4_3.S5) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 6206690150405442008; review: unreviewed); S6 (Alignment.Shadows.Docs.cf_thm4_3.S6) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 18064114354052800026; review: unreviewed); S7 (Alignment.Shadows.Docs.cf_thm4_3.S7) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 1164084204777216966; review: unreviewed); S8 (Alignment.Shadows.Docs.cf_thm4_3.S8) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 3729984076407844400; review: unreviewed); forward 1: fail; forward 2: fail; forward 4: fail; forward 5: fail; forward 6: fail; forward 7: fail; forward 8: fail; backward: fail
* `Docs.cf.nonMarkovObstruction`: forward 3: fail
* `Docs.cf.validityDomain`: forward 2: fail; forward 3: fail; forward 4: fail
* `Docs.cf.thetaNonincreasing`: shadow_trusted_free: S1 (Alignment.Shadows.Docs.cf_thetaNonincreasing.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 2667673506868623642; review: unreviewed); forward 1: fail; backward: fail
* `Docs.cf.thm8_1`: forward 1: fail; forward 2: fail; backward: fail
* `Docs.cf.thm8_1-poisson`: shadow_trusted_free: S4 (Alignment.Shadows.Docs.cf_thm8_1_poisson.S4) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 18048839259459195058; review: unreviewed); S5 (Alignment.Shadows.Docs.cf_thm8_1_poisson.S5) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 11629983299048506476; review: unreviewed); forward 1: fail; forward 2: fail; forward 3: fail; forward 4: fail; forward 5: fail; backward: fail
* `Docs.ms.T2`: forward 2: fail; forward 3: fail; forward 4: fail; forward 5: fail
* `Docs.ms.T3`: forward 3: fail
* `Docs.ms.T3-linearEquivariant`: forward 1: fail; forward 2: fail; forward 3: fail; backward: fail
* `Docs.ms.T3-kkr`: forward 2: fail; backward: fail
* `Docs.ms.T5-rateTwo`: hypothesis_refuted: EBCMCategory.MarginalisationDynamicalGap.trajectoryGap_rate_two_at_witness: hypothesis h₃ : EBCMCategory.Marginalisation.IsFlow EBCMCategory.MarginalisationDynamicalGap.F3Kℝ φ₃ refuted by EBCMCategory.MarginalisationDynamicalGap.no_flow_F3Kℝ (trusted); forward 1: fail; forward 2: fail; backward: fail
* `Docs.ms.T6`: forward 2: fail; forward 3: fail; forward 4: fail; forward 5: fail
* `Docs.ms.T6-values`: forward 1: fail; forward 2: fail; forward 3: fail; backward: fail
* `DynamicLimits.header.interpolation`: forward 2: fail; forward 3: fail; backward: fail
* `DynamicLimits.table.R31`: forward 1: fail; forward 2: fail
* `DynamicLimits.table.R32`: forward 1: fail; forward 2: fail
* `DynamicLimits.table.R33`: forward 3: fail
* `DynamicLimits.table.R36`: forward 1: fail
* `DynamicLimits.table.R37`: forward 1: fail; forward 3: fail
* `DynamicLimits.table.R40`: forward 1: fail; forward 2: fail; backward: fail
* `DynamicLimits.R29`: forward 3: fail; forward 4: fail; forward 5: fail
* `DynamicLimits.R30`: forward 3: fail; forward 4: fail
* `DynamicLimits.R31a`: forward 1: fail; forward 2: fail; forward 4: fail; forward 5: fail
* `DynamicLimits.R32a`: forward 2: fail; forward 3: fail
* `DynamicLimits.R33a`: forward 2: fail
* `DynamicLimits.R34`: forward 3: fail; forward 4: fail
* `DynamicLimits.R35a`: forward 2: fail; forward 3: fail
* `DynamicLimits.R35b`: forward 1: fail; forward 2: fail; forward 3: fail; backward: fail
* `DynamicLimits.R36a`: forward 1: fail
* `DynamicLimits.R37a`: forward 1: fail; forward 3: fail
* `DynamicLimits.R38`: forward 2: fail; forward 3: fail; forward 4: fail; forward 5: fail; forward 6: fail
* `DynamicLimits.R39`: forward 2: fail; forward 3: fail
* `DynamicLimits.R40a`: forward 1: fail; forward 2: fail; backward: fail
* `DynamicLimits.r0EdgeSwapTendstoMfsh`: forward 1: fail; backward: fail
* `GaloisPair.header.GFLossy`: forward 2: fail
* `GaloisPair.table.R14`: forward 2: fail; backward: fail
* `GaloisPair.R14a`: forward 2: fail
* `GaloisPair.notGaloisConnectionCoarseGrainPoissonLift`: forward 2: fail; forward 3: fail
* `GaloisPair.notGaloisConnectionPoissonLiftCoarseGrain`: forward 2: fail; forward 3: fail
* `Hierarchy.header.pairGtEbcmGtMeanField`: forward 3: fail; forward 4: fail; forward 5: fail
* `Hierarchy.table.R27`: forward 1: fail
* `Hierarchy.table.R28`: forward 1: fail; forward 2: fail; forward 3: fail; forward 4: fail
* `Hierarchy.R25`: shadow_trusted_free: S3 (Alignment.Shadows.Hierarchy.R25.S3) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 97897990587558479; review: unreviewed); forward 2: fail; forward 3: fail
* `Hierarchy.R27`: shadow_trusted_free: S3 (Alignment.Shadows.Hierarchy.R27.S3) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 380570508930210522; review: unreviewed); S4 (Alignment.Shadows.Hierarchy.R27.S4) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 9344111523977439499; review: unreviewed); S5 (Alignment.Shadows.Hierarchy.R27.S5) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 16433037668216630849; review: unreviewed); forward 1: fail; forward 2: fail; forward 3: fail; forward 4: fail; forward 5: fail
* `Hierarchy.R28`: forward 1: fail; forward 2: fail; forward 3: fail; forward 4: fail; forward 5: fail; forward 6: fail
* `Hierarchy.pairLtFull`: forward 2: fail; forward 3: fail
* `Hierarchy.fullLtPairThree`: forward 2: fail; forward 3: fail
* `InvariantRegion.header.faceConditions`: forward 1: fail; forward 2: fail; forward 3: fail; forward 5: fail; backward: fail
* `InvariantRegion.pgfEvalOne`: forward 2: fail
* `InvariantRegion.R113`: backward: fail
* `InvariantRegion.R116a`: forward 1: fail; backward: fail
* `InvariantRegion.R117a`: forward 1: fail; backward: fail
* `InvariantRegion.phiIDotFactors.a`: forward 1: fail; backward: fail
* `InvariantRegion.R119a`: backward: fail
* `InvariantRegion.R120`: backward: fail
* `InvariantRegion.R120b`: forward 1: fail; forward 2: fail; forward 3: fail
* `InvariantRegion.R120b.guard`: forward 1: fail
* `InvariantRegion.missingSeedFactorOvercounts`: forward 1: fail; forward 2: fail
* `InvariantRegion.R121`: backward: fail
* `InvariantRegion.R122a`: forward 1: fail; forward 2: fail; backward: fail
* `InvariantRegion.iDotGeneral.a`: forward 1: fail; backward: vacuous
* `InvariantRegion.iDotGeneral.b`: forward 1: fail; forward 2: fail; backward: fail
* `InvariantRegion.iDotAtZero`: forward 1: fail; forward 2: fail; backward: fail
* `InvariantRegion.R123a`: forward 1: fail; forward 2: fail; forward 4: fail; forward 5: fail; forward 6: fail; backward: fail
* `InvariantRegion.R123b`: forward 1: fail; forward 2: fail; forward 3: fail; backward: fail
* `InvariantRegion.R123d`: backward: fail
* `InvariantRegion.R123e`: forward 1: fail
* `InvariantRegion.R123f`: forward 1: fail; forward 2: fail; forward 3: fail; forward 4: fail; backward: fail
* `InvariantRegion.header.thetaFace.a`: forward 1: fail; forward 2: fail; backward: fail
* `InvariantRegion.thetaLowerBoundaryAbsorbing`: forward 1: fail; backward: fail
* `InvariantRegion.phiIDotCorrectZeroAtBoundary`: forward 1: fail; backward: fail
* `InvariantRegion.phiIDotCorrectFactors`: forward 1: fail; forward 2: fail; forward 3: fail; backward: fail
* `MarginalisationCharacterization.header.T2witness`: backward: fail
* `MarginalisationCharacterization.header.T1forces`: forward 2: fail; forward 3: fail; backward: fail
* `MarginalisationCharacterization.header.interLevel`: forward 1: fail; forward 2: fail; backward: fail
* `MarginalisationCharacterization.header.kkrNotSufficient`: backward: fail
* `MarginalisationCharacterization.table.T3a`: forward 1: fail; forward 2: fail; backward: fail
* `MarginalisationCharacterization.table.T3c.b`: backward: fail
* `MarginalisationCharacterization.isLinearAdmitsEquivariant`: forward 1: fail; forward 2: fail; forward 3: fail; backward: fail
* `MarginalisationCharacterization.c4RealIsKirkwoodForm`: forward 3: fail; forward 4: fail; forward 5: fail; forward 6: fail; forward 7: fail
* `MarginalisationCharacterization.kirkwoodFormNotEquivariant`: forward 1: fail
* `MarginalisationCharacterization.kkrNecessaryNotSufficient.notSufficient`: forward 2: fail; forward 3: fail; backward: fail
* `MarginalisationCharacterization.linearAdmitsEquivariantIff`: shadow_trusted_free: S1 (Alignment.Shadows.MarginalisationCharacterization.linearAdmitsEquivariantIff.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 4078019246639920170; review: unreviewed); S2 (Alignment.Shadows.MarginalisationCharacterization.linearAdmitsEquivariantIff.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 12130700592282499896; review: unreviewed); S3 (Alignment.Shadows.MarginalisationCharacterization.linearAdmitsEquivariantIff.S3) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 5133793807900686558; review: unreviewed); forward 3: fail
* `MarginalisationCharacterization.existsKirkwoodFormEquivariant`: forward 1: fail; forward 2: fail
* `MarginalisationDynamicalGap.header.overview`: hypothesis_refuted: EBCMCategory.MarginalisationDynamicalGap.trajectoryGap_rate_two_at_witness: hypothesis h₃ : EBCMCategory.Marginalisation.IsFlow EBCMCategory.MarginalisationDynamicalGap.F3Kℝ φ₃ refuted by EBCMCategory.MarginalisationDynamicalGap.no_flow_F3Kℝ (trusted); forward 1: fail; forward 2: fail; forward 3: fail; forward 4: fail; backward: fail
* `MarginalisationDynamicalGap.header.T6.a`: forward 1: fail; backward: fail
* `MarginalisationDynamicalGap.fibreCollapseObstruction`: backward: vacuous
* `MarginalisationDynamicalGap.kirkwoodNotEquivariantViaT4`: forward 2: fail
* `MarginalisationDynamicalGap.trajectoryGapNormGeHalfEpsT`: forward 1: fail; backward: fail
* `MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.a`: hypothesis_refuted: EBCMCategory.MarginalisationDynamicalGap.trajectoryGap_rate_two_at_witness: hypothesis h₃ : EBCMCategory.Marginalisation.IsFlow EBCMCategory.MarginalisationDynamicalGap.F3Kℝ φ₃ refuted by EBCMCategory.MarginalisationDynamicalGap.no_flow_F3Kℝ (trusted)
* `MarginalisationDynamicalGap.f3RealIsKirkwoodForm`: forward 3: fail; forward 4: fail
* `MarginalisationDynamicalGap.refinementFailureExists.b`: forward 1: fail; forward 2: fail; forward 3: fail; backward: fail
* `MarginalisationDynamicalGap.normGeHalfEpsTOfHasDerivAt`: shadow_trusted_free: S1 (Alignment.Shadows.MarginalisationDynamicalGap.normGeHalfEpsTOfHasDerivAt.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 9646603772153485512; review: unreviewed); forward 1: fail; backward: fail
* `MarginalisationDynamicalGap.localGapNormGeHalfEpsT`: forward 1: fail; backward: fail
* `MarginalisationDynamicalGap.algebraicGapWitness`: forward 2: fail; forward 3: fail; forward 4: fail
* `MarginalisationDynamicalGap.kirkwoodFormMatchesAtWitness`: forward 2: fail; forward 3: fail; backward: fail
* `MarginalisationDynamicalGap.witnessLocalSolutionsExist`: forward 1: fail; forward 2: fail; forward 3: fail; backward: fail
* `MarginalisationDynamicalGap.witnessLocalGapGe`: forward 2: fail
* `MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.b`: shadow_trusted_free: S2 (Alignment.Shadows.MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness_b.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 5544687249140376120; review: unreviewed); S3 (Alignment.Shadows.MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness_b.S3) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 8157836920290940122; review: unreviewed); forward 2: fail; forward 3: fail
* `MarginalisationDynamicalGap.noGlobalSolutionSqDivFour`: shadow_trusted_free: S1 (Alignment.Shadows.MarginalisationDynamicalGap.noGlobalSolutionSqDivFour.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 8196236047846007684; review: unreviewed); S2 (Alignment.Shadows.MarginalisationDynamicalGap.noGlobalSolutionSqDivFour.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 5129660957717886767; review: unreviewed); S3 (Alignment.Shadows.MarginalisationDynamicalGap.noGlobalSolutionSqDivFour.S3) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 10544433766813641099; review: unreviewed); S4 (Alignment.Shadows.MarginalisationDynamicalGap.noGlobalSolutionSqDivFour.S4) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 6801411969706087453; review: unreviewed); forward 2: fail; forward 3: fail; forward 4: fail
* `MarginalisationDynamicalGap.noFlowF3Real`: forward 2: fail
* `MarginalisationFunctor.header.closedNeedNotCommute`: forward 1: fail; forward 2: fail; backward: fail
* `MarginalisationFunctor.RM1`: forward 3: fail
* `MarginalisationFunctor.RM4b`: forward 3: fail; backward: fail
* `MarginalisationFunctor.rhsCommuteOfLocalTrajCommute`: shadow_trusted_free: S1 (Alignment.Shadows.MarginalisationFunctor.rhsCommuteOfLocalTrajCommute.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 1942754957992540291; review: unreviewed); backward: fail
* `MessagePassingBridge.table.R62`: shadow_trusted_free: S1 (Alignment.Shadows.MessagePassingBridge.table_R62.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 3026395228859435690; review: unreviewed); forward 1: fail; backward: fail
* `MessagePassingBridge.table.R63`: forward 1: fail; forward 2: fail; forward 3: fail; forward 4: fail; forward 5: fail; backward: vacuous
* `MessagePassingBridge.table.R65`: forward 1: fail; forward 2: fail; forward 3: fail
* `MessagePassingBridge.table.R66`: shadow_trusted_free: S1 (Alignment.Shadows.MessagePassingBridge.table_R66.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 15979788211800390070; review: unreviewed); forward 1: fail; backward: fail
* `MessagePassingBridge.table.R67`: forward 1: fail; forward 2: fail; forward 3: fail; forward 4: fail; backward: fail
* `MessagePassingBridge.table.R68`: forward 1: fail; forward 2: fail; backward: fail
* `MessagePassingBridge.R64`: forward 2: fail; forward 3: fail; forward 4: fail; forward 5: fail
* `MessagePassingBridge.R60`: forward 2: fail
* `MessagePassingBridge.R62d`: shadow_trusted_free: S1 (Alignment.Shadows.MessagePassingBridge.R62d.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 17984503144793547209; review: unreviewed); S2 (Alignment.Shadows.MessagePassingBridge.R62d.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 3686825374707651492; review: unreviewed); forward 1: fail; forward 2: fail
* `MessagePassingBridge.R63d`: forward 2: fail
* `MessagePassingBridge.markovEbcmDim`: forward 1: fail; backward: vacuous
* `MessagePassingBridge.pdeToOdeReduction`: forward 1: fail; backward: fail
* `MessagePassingBridge.R65`: forward 1: fail; forward 3: fail; backward: fail
* `MessagePassingBridge.R66a`: shadow_trusted_free: S1 (Alignment.Shadows.MessagePassingBridge.R66a.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 16695688466509539996; review: unreviewed); forward 1: fail; backward: fail
* `MessagePassingBridge.R67`: forward 1: fail; forward 2: fail; forward 3: fail; forward 4: fail
* `MessagePassingBridge.R68a`: forward 1: fail; forward 2: fail; backward: fail
* `MethodOfStages.R87`: shadow_trusted_free: S2 (Alignment.Shadows.MethodOfStages.R87.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 9793455247961484286; review: unreviewed); S3 (Alignment.Shadows.MethodOfStages.R87.S3) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 16190401507582013625; review: unreviewed); forward 1: fail; forward 2: fail; forward 3: fail
* `MethodOfStages.R88`: forward 1: fail; forward 2: fail
* `MethodOfStages.R89a`: forward 1: fail; forward 2: fail
* `MethodOfStages.R90a`: forward 1: fail; forward 2: fail
* `MethodOfStages.R91a`: shadow_trusted_free: S1 (Alignment.Shadows.MethodOfStages.R91a.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 11347689737676604337; review: unreviewed); S2 (Alignment.Shadows.MethodOfStages.R91a.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 6396324146758978060; review: unreviewed); forward 2: fail
* `MethodOfStages.R92`: shadow_trusted_free: S1 (Alignment.Shadows.MethodOfStages.R92.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 658428605520415641; review: unreviewed); forward 1: fail; backward: vacuous
* `MethodOfStages.R93c`: shadow_trusted_free: S1 (Alignment.Shadows.MethodOfStages.R93c.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 1171519756853779018; review: unreviewed); S2 (Alignment.Shadows.MethodOfStages.R93c.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 11981603910784286201; review: unreviewed); forward 1: fail
* `MethodOfStages.R94b`: forward 1: fail
* `MethodOfStages.erlangTransmissibilityOneLtTwo`: forward 2: fail
* `Obstructions.header.networkNotObstruction`: forward 2: fail
* `Obstructions.table.R18`: forward 3: fail
* `Obstructions.table.R19`: forward 2: fail; forward 3: fail; backward: fail
* `Obstructions.table.R21`: forward 2: fail; forward 3: fail
* `Obstructions.table.R22`: forward 1: fail; forward 2: fail; backward: fail
* `Obstructions.R18c`: forward 1: fail; forward 2: fail; backward: fail
* `Obstructions.R21b`: forward 2: fail; forward 3: fail
* `Obstructions.R19a`: forward 2: fail; forward 3: fail
* `Obstructions.R19b`: forward 3: fail; forward 4: fail
* `Obstructions.erlangIsOde`: forward 2: fail
* `Obstructions.R20a`: forward 2: fail
* `Obstructions.R22a`: forward 1: fail; forward 2: fail
* `Obstructions.standardMostCompact`: forward 1: fail; forward 2: fail; forward 3: fail; backward: fail
* `Obstructions.R24a`: forward 2: fail; forward 3: fail; backward: fail
* `Obstructions.R24c`: forward 1: fail; backward: fail
* `Obstructions.R23b`: forward 3: fail; forward 4: fail; backward: fail
* `Obstructions.R23c`: forward 2: fail; forward 3: fail; backward: fail
* `Obstructions.header.kirkwoodHierarchyInconsistent`: forward 1: fail; forward 3: fail
* `Obstructions.R25b`: forward 1: fail; forward 2: fail
* `PairwiseClosureConditions.header.nonnegNeedsPointwise`: forward 2: fail; backward: fail
* `PairwiseClosureConditions.header.conservationNotPositivity`: forward 1: fail; forward 2: fail; backward: fail
* `PairwiseClosureConditions.negativeWeightGivesNegativeTriple.b`: forward 1: fail; forward 2: fail; backward: fail
* `PairwiseClosureConditions.barnardWeightsNormalized.a`: backward: fail
* `PairwiseClosureConditions.keelingFactorNonneg`: forward 2: fail
* `PairwiseClosureConditions.keelingWeightsNonneg`: forward 2: fail
* `PairwiseClosureConditions.keelingStyleClosureSafe.a`: forward 3: fail; forward 4: fail; forward 5: fail
* `PairwiseClosureConditions.keelingStyleClosureSafe.b`: forward 2: fail; backward: fail
* `SEIREquations.table.SEIR1`: forward 1: fail; forward 2: fail
* `SEIREquations.table.SEIR2`: backward: fail
* `SEIREquations.table.SEIR3`: forward 1: fail; backward: fail
* `SEIREquations.table.SEIR4`: forward 1: fail; forward 2: fail; backward: fail
* `SEIREquations.edgeHazard`: forward 3: fail
* `SEIREquations.dTheta`: forward 1: fail; forward 2: fail; backward: fail
* `SEIREquations.iPopZeroAtSeed-a`: forward 1: fail
* `SEIREquations.iPopZeroAtSeed-b`: forward 1: fail; forward 2: fail; backward: fail
* `SEIREquations.iPopWrongNonzeroAtSeed`: forward 1: fail
* `SEIREquations.edgeHazardIndependentOfE`: backward: fail
* `SEIREquations.seirIGrowthBounded-a`: forward 2: fail
* `SurvivalBridge.header.kappaInvariant-b`: shadow_trusted_free: S1 (Alignment.Shadows.SurvivalBridge.header_kappaInvariant_b.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 18136052394246737765; review: unreviewed); S2 (Alignment.Shadows.SurvivalBridge.header_kappaInvariant_b.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 2088136917368670874; review: unreviewed); S3 (Alignment.Shadows.SurvivalBridge.header_kappaInvariant_b.S3) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 4079142737166344163; review: unreviewed); forward 1: fail; forward 2: fail; forward 3: fail; forward 4: fail; forward 5: fail; forward 6: fail; backward: fail
* `SurvivalBridge.table.R42`: shadow_trusted_free: S2 (Alignment.Shadows.SurvivalBridge.table_R42.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 4478200644341556262; review: unreviewed); S3 (Alignment.Shadows.SurvivalBridge.table_R42.S3) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 8416891768802004460; review: unreviewed); forward 2: fail; forward 3: fail
* `SurvivalBridge.table.R43`: shadow_trusted_free: S2 (Alignment.Shadows.SurvivalBridge.table_R43.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 4496524544225396250; review: unreviewed); forward 2: fail; forward 3: fail
* `SurvivalBridge.table.R44`: shadow_trusted_free: S2 (Alignment.Shadows.SurvivalBridge.table_R44.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 6243796909787637318; review: unreviewed); forward 2: fail; forward 3: fail
* `SurvivalBridge.table.R45`: forward 2: fail; forward 4: fail
* `SurvivalBridge.table.R47`: forward 2: fail
* `SurvivalBridge.table.R48`: forward 1: fail; forward 2: fail; backward: vacuous
* `SurvivalBridge.table.R49`: shadow_trusted_free: S1 (Alignment.Shadows.SurvivalBridge.table_R49.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 10823801428713371447; review: unreviewed); S2 (Alignment.Shadows.SurvivalBridge.table_R49.S2) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 3846847698532795088; review: unreviewed); forward 1: fail; forward 2: fail; backward: vacuous
* `SurvivalBridge.table.R50`: shadow_trusted_free: S3 (Alignment.Shadows.SurvivalBridge.table_R50.S3) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 8030604248267453373; review: unreviewed); S4 (Alignment.Shadows.SurvivalBridge.table_R50.S4) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 3240607034056983751; review: unreviewed); S5 (Alignment.Shadows.SurvivalBridge.table_R50.S5) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 17715426519102687964; review: unreviewed); forward 2: fail; forward 3: fail; forward 4: fail; forward 5: fail; backward: fail
* `SurvivalBridge.volzState-b`: forward 2: fail; backward: fail
* `SurvivalBridge.R42`: forward 2: fail; forward 3: fail
* `SurvivalBridge.R43a`: forward 1: fail; forward 2: fail; backward: vacuous
* `SurvivalBridge.R44a`: forward 1: fail; forward 2: fail
* `SurvivalBridge.R45b`: forward 1: fail; forward 3: fail
* `SurvivalBridge.R46c`: forward 2: fail; forward 3: fail
* `SurvivalBridge.R47a`: shadow_trusted_free: S3 (Alignment.Shadows.SurvivalBridge.R47a.S3) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 5262980823421386273; review: unreviewed); forward 2: fail; forward 3: fail
* `SurvivalBridge.R47b`: shadow_trusted_free: S1 (Alignment.Shadows.SurvivalBridge.R47b.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 6056720407993818802; review: unreviewed); forward 1: fail; backward: fail
* `SurvivalBridge.R49a`: shadow_trusted_free: S3 (Alignment.Shadows.SurvivalBridge.R49a.S3) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 14794979786512434332; review: unreviewed); S4 (Alignment.Shadows.SurvivalBridge.R49a.S4) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 5921752440457201276; review: unreviewed); forward 2: fail; forward 3: fail; forward 4: fail
* `SurvivalBridge.R50a`: shadow_trusted_free: S3 (Alignment.Shadows.SurvivalBridge.R50a.S3) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 527990334137464407; review: unreviewed); S4 (Alignment.Shadows.SurvivalBridge.R50a.S4) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 109660018130293259; review: unreviewed); S5 (Alignment.Shadows.SurvivalBridge.R50a.S5) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 4822892061238026736; review: unreviewed); forward 2: fail; forward 3: fail; forward 4: fail; forward 5: fail; backward: fail
* `SurvivalBridge.R50b`: forward 1: fail; forward 3: fail; backward: fail
* `SurvivalBridge.R50e`: forward 1: fail; backward: fail
* `VolzMeyersEquations.table.VM1`: forward 2: fail
* `VolzMeyersEquations.thetaNonincreasing`: forward 2: fail
* `VolzMeyersEquations.table.VM4`: forward 1: fail; forward 2: fail; backward: fail
* `VolzMeyersEquations.sNonincreasing-a`: forward 1: fail; forward 2: fail; backward: fail
* `VolzMeyersEquations.sNonincreasing-b`: forward 1: fail; forward 2: fail; backward: fail
* `VolzMeyersEquations.table.VM5`: forward 1: fail; backward: fail
* `VolzMeyersEquations.staticThetaEq-a`: forward 1: fail; forward 2: fail; backward: fail
* `VolzMeyersEquations.fastMixingP1Equilibrium-a`: forward 1: fail; backward: fail
* `VolzMeyersEquations.fastMixingP1Equilibrium-d`: forward 1: fail; forward 2: fail; backward: fail
* `VolzMeyersEquations.table.VM8`: forward 1: fail; forward 2: fail; forward 3: fail; backward: fail
* `VolzMeyersEquations.massActionIncidence-a`: forward 1: fail; forward 2: fail; forward 3: fail; forward 4: fail; backward: fail
* `VolzMeyersEquations.massActionIncidence-b`: forward 1: fail; backward: fail

## Bridges

| bridge | claims | status | hash | statement | notes |
|---|---|---|---|---|---|
| `Alignment.Shadows.SurvivalBridge.R46c.bridge_edgeModel` | SurvivalBridge.R46c | reviewed | `12900344808292493412` | `∀ (p : SIRParams) (ψ : PGFData), edgeModel p ψ = { dim := 4, R0 := p.β / (p.β + p.γ) * ψ.secondFactorial / ψ.mean }` | The R46c text (EBCMCategory/SurvivalBridge.lean:170-172) says 'the EBCM uses T·ψ''(1)/ψ'(1)'. EpiCategory.lean defines edgeModel p ψ = ⟨4, transmissibility p * excessDegree ψ⟩ with T = β/(β+γ) (line 79), excessDegree = secondFactorial/mean, and PGFData's docstring gives mean = ψ'(1) and secondFactorial = ψ''(1). So the RHS ⟨4, ((β/(β+γ))·ψ''(1))/ψ'(1)⟩ is exactly the text's per-edge-transmissibility-times-mean-excess-degree R₀. The only step is mul_div_assoc, which holds in ℚ with no hypotheses (and mean > 0, β+γ > 0 by the structure invariants in any case), and dim := 4 is the definition's own value. No Poisson content (κ²/κ = κ) and no impl theorem are used. |
| `Alignment.Shadows.SurvivalBridge.R46c.bridge_nodeModel` | SurvivalBridge.R46c | reviewed | `1686206359287332404` | `∀ (p : SIRParams) (κ : ℚ), nodeModel p κ = { dim := 3, R0 := p.β * κ / (p.β + p.γ) }` | The R46c text says 'DSA uses β·μ/(β+γ) where μ = mean degree'. EpiCategory.lean defines nodeModel p κ = ⟨3, transmissibility p * κ⟩ = ⟨3, (β/(β+γ))·κ⟩, where κ is the mean degree (edge_refines_node instantiates it with ψ.mean, and the checker uses the Poisson mean, which is definitionally κ). So the RHS ⟨3, β·κ/(β+γ)⟩ is exactly the text's DSA formula with μ = κ. The only step is div_mul_eq_mul_div, which is unconditional in ℚ and needs no sign or nonzero side condition on κ, and dim := 3 is the definition's own value. The bridge carries no theorem content and uses no impl theorem. |

## Refuted implementation hypotheses (`hypothesis_refuted`)

The implementation theorem assumes a hypothesis that a sound theorem refutes, so it is vacuously true (and so is every shadow that shares the hypothesis). The refutation is kernel-checked.

* `Docs.ms.T5-rateTwo`: EBCMCategory.MarginalisationDynamicalGap.trajectoryGap_rate_two_at_witness: hypothesis h₃ : EBCMCategory.Marginalisation.IsFlow EBCMCategory.MarginalisationDynamicalGap.F3Kℝ φ₃ refuted by EBCMCategory.MarginalisationDynamicalGap.no_flow_F3Kℝ (trusted)
* `MarginalisationDynamicalGap.header.overview`: EBCMCategory.MarginalisationDynamicalGap.trajectoryGap_rate_two_at_witness: hypothesis h₃ : EBCMCategory.Marginalisation.IsFlow EBCMCategory.MarginalisationDynamicalGap.F3Kℝ φ₃ refuted by EBCMCategory.MarginalisationDynamicalGap.no_flow_F3Kℝ (trusted)
* `MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.a` (all checks pass: this pass is withdrawn by the flag): EBCMCategory.MarginalisationDynamicalGap.trajectoryGap_rate_two_at_witness: hypothesis h₃ : EBCMCategory.Marginalisation.IsFlow EBCMCategory.MarginalisationDynamicalGap.F3Kℝ φ₃ refuted by EBCMCategory.MarginalisationDynamicalGap.no_flow_F3Kℝ (trusted)

## Trusted-free shadows (`shadow_trusted_free`)

These shadows mention no trusted-library constant after inlining alignment helpers, so they are closed statements of logic or arithmetic. The flag zeroes the claim until an independent reviewer confirms that the source text is itself such a statement, with `sa_shadow_reviewed <shadow> "<hash>" "<reason>"` in `Alignment/ReviewedBridges.lean`.

| claim | shadow | content hash | review |
|---|---|---|---|
| `CategoricalComposition.R100a` | S1 `Alignment.Shadows.CategoricalComposition.R100a.S1` | `8006581057523220641` | reviewed |
| `CategoricalComposition.R100b` | S1 `Alignment.Shadows.CategoricalComposition.R100b.S1` | `12227782950718836910` | reviewed |
| `CategoricalComposition.R100c` | S1 `Alignment.Shadows.CategoricalComposition.R100c.S1` | `8966180171648085440` | reviewed |
| `CategoricalComposition.R100d` | S1 `Alignment.Shadows.CategoricalComposition.R100d.S1` | `3921892068967338273` | reviewed |
| `CategoricalComposition.R100e` | S1 `Alignment.Shadows.CategoricalComposition.R100e.S1` | `10859786292137398121` | reviewed |
| `CategoricalComposition.R100e` | S2 `Alignment.Shadows.CategoricalComposition.R100e.S2` | `4420622397373677444` | reviewed |
| `CategoricalComposition.R96a` | S1 `Alignment.Shadows.CategoricalComposition.R96a.S1` | `18118268704599918753` | reviewed |
| `CategoricalComposition.R96a` | S2 `Alignment.Shadows.CategoricalComposition.R96a.S2` | `16452762903075868917` | reviewed |
| `ConvergenceTheorems.dfeDerivativeAbsLeOneIff` | S1 `Alignment.Shadows.ConvergenceTheorems.dfeDerivativeAbsLeOneIff.S1` | `18405518961620889407` | reviewed |
| `ConvergenceTheorems.dfeDerivativeAbsLeOneIff` | S2 `Alignment.Shadows.ConvergenceTheorems.dfeDerivativeAbsLeOneIff.S2` | `12647593375326244056` | reviewed |
| `InvariantRegion.phiILeTheta` | S1 `Alignment.Shadows.InvariantRegion.phiILeTheta.S1` | `9010931585015679052` | reviewed |
| `MarginalisationCharacterization.existsEquivariantIffFibrewise` | S1 `Alignment.Shadows.MarginalisationCharacterization.existsEquivariantIffFibrewise.S1` | `3630059095103699796` | reviewed |
| `MarginalisationCharacterization.existsEquivariantIffFibrewise` | S2 `Alignment.Shadows.MarginalisationCharacterization.existsEquivariantIffFibrewise.S2` | `9673709430542453181` | reviewed |
| `PairwiseClosureConditions.header.safeRegime` | S3 `Alignment.Shadows.PairwiseClosureConditions.header_safeRegime.S3` | `15140977414827178178` | reviewed |
| `PairwiseClosureConditions.header.safeRegime` | S4 `Alignment.Shadows.PairwiseClosureConditions.header_safeRegime.S4` | `1806753512647260405` | reviewed |
| `PairwiseClosureConditions.weightInUnitInterval` | S1 `Alignment.Shadows.PairwiseClosureConditions.weightInUnitInterval.S1` | `12901778656111795673` | reviewed |
| `CategoricalComposition.R100.monoidal` | S1 `Alignment.Shadows.CategoricalComposition.R100_monoidal.S1` | `17004486307455099508` | unreviewed |
| `CategoricalComposition.R100.monoidal` | S2 `Alignment.Shadows.CategoricalComposition.R100_monoidal.S2` | `11187242852896608051` | unreviewed |
| `CategoricalComposition.R100.monoidal` | S3 `Alignment.Shadows.CategoricalComposition.R100_monoidal.S3` | `4066740869024288118` | unreviewed |
| `CategoricalComposition.R100f.1` | S1 `Alignment.Shadows.CategoricalComposition.R100f_1.S1` | `4645710261415564671` | unreviewed |
| `CategoricalComposition.R100f.1` | S2 `Alignment.Shadows.CategoricalComposition.R100f_1.S2` | `2614311514533656700` | unreviewed |
| `CategoricalComposition.R101e` | S1 `Alignment.Shadows.CategoricalComposition.R101e.S1` | `11345656827471733963` | unreviewed |
| `ClosureTheorem.R52` | S1 `Alignment.Shadows.ClosureTheorem.R52.S1` | `5736442423597233535` | unreviewed |
| `ClosureTheorem.R52` | S2 `Alignment.Shadows.ClosureTheorem.R52.S2` | `12489734717761764471` | unreviewed |
| `ClosureTheorem.R53` | S1 `Alignment.Shadows.ClosureTheorem.R53.S1` | `8102201160637063098` | unreviewed |
| `ClosureTheorem.R53` | S2 `Alignment.Shadows.ClosureTheorem.R53.S2` | `3800242781666044695` | unreviewed |
| `ClosureTheorem.R54` | S1 `Alignment.Shadows.ClosureTheorem.R54.S1` | `11984815519717754417` | unreviewed |
| `ClosureTheorem.R54` | S2 `Alignment.Shadows.ClosureTheorem.R54.S2` | `5535807201988576959` | unreviewed |
| `ClosureTheorem.R55` | S1 `Alignment.Shadows.ClosureTheorem.R55.S1` | `9395387580549500412` | unreviewed |
| `ClosureTheorem.R55` | S2 `Alignment.Shadows.ClosureTheorem.R55.S2` | `13520616302085932718` | unreviewed |
| `ClosureTheorem.R56` | S1 `Alignment.Shadows.ClosureTheorem.R56.S1` | `10824917823408188949` | unreviewed |
| `ClosureTheorem.R56` | S2 `Alignment.Shadows.ClosureTheorem.R56.S2` | `660383570758253160` | unreviewed |
| `ClosureTheorem.R57` | S2 `Alignment.Shadows.ClosureTheorem.R57.S2` | `3373795397357900506` | unreviewed |
| `ClosureTheorem.R57` | S3 `Alignment.Shadows.ClosureTheorem.R57.S3` | `15027029890531176574` | unreviewed |
| `ClosureTheorem.R59` | S1 `Alignment.Shadows.ClosureTheorem.R59.S1` | `16292072948732100427` | unreviewed |
| `ClosureTheorem.binomialClosureRatio` | S2 `Alignment.Shadows.ClosureTheorem.binomialClosureRatio.S2` | `5522051591303715438` | unreviewed |
| `ClosureTheorem.binomialKappaDeterminesN` | S2 `Alignment.Shadows.ClosureTheorem.binomialKappaDeterminesN.S2` | `5777466738936095210` | unreviewed |
| `ClosureTheorem.binomialRecoverN` | S1 `Alignment.Shadows.ClosureTheorem.binomialRecoverN.S1` | `3667473968810287908` | unreviewed |
| `ClosureTheorem.header.verificationStrategy` | S1 `Alignment.Shadows.ClosureTheorem.header_verificationStrategy.S1` | `3137840644093547994` | unreviewed |
| `ClosureTheorem.header.verificationStrategy` | S2 `Alignment.Shadows.ClosureTheorem.header_verificationStrategy.S2` | `1234849908418522215` | unreviewed |
| `ClosureTheorem.header.verificationStrategy` | S3 `Alignment.Shadows.ClosureTheorem.header_verificationStrategy.S3` | `2512323839188433664` | unreviewed |
| `ClosureTheorem.negbin2ClosureRatio` | S2 `Alignment.Shadows.ClosureTheorem.negbin2ClosureRatio.S2` | `15996686828414596910` | unreviewed |
| `ClosureTheorem.negbin3ClosureRatio` | S2 `Alignment.Shadows.ClosureTheorem.negbin3ClosureRatio.S2` | `564299106612444687` | unreviewed |
| `ClosureTheorem.negbinKappaDeterminesR` | S1 `Alignment.Shadows.ClosureTheorem.negbinKappaDeterminesR.S1` | `6859366675205680798` | unreviewed |
| `ClosureTheorem.negbinKappaDeterminesR` | S2 `Alignment.Shadows.ClosureTheorem.negbinKappaDeterminesR.S2` | `15160479782507934200` | unreviewed |
| `ClosureTheorem.poissonClosureRatio` | S2 `Alignment.Shadows.ClosureTheorem.poissonClosureRatio.S2` | `7787854828244810692` | unreviewed |
| `ClosureTheorem.table.R52` | S1 `Alignment.Shadows.ClosureTheorem.table_R52.S1` | `158470926229173236` | unreviewed |
| `ClosureTheorem.table.R52` | S2 `Alignment.Shadows.ClosureTheorem.table_R52.S2` | `17680666234752013126` | unreviewed |
| `ClosureTheorem.table.R53` | S1 `Alignment.Shadows.ClosureTheorem.table_R53.S1` | `9961840620573049331` | unreviewed |
| `ClosureTheorem.table.R53` | S2 `Alignment.Shadows.ClosureTheorem.table_R53.S2` | `14054725648801240648` | unreviewed |
| `ClosureTheorem.table.R54` | S1 `Alignment.Shadows.ClosureTheorem.table_R54.S1` | `4991563090386846176` | unreviewed |
| `ClosureTheorem.table.R54` | S2 `Alignment.Shadows.ClosureTheorem.table_R54.S2` | `8233478868788664652` | unreviewed |
| `ClosureTheorem.table.R55` | S1 `Alignment.Shadows.ClosureTheorem.table_R55.S1` | `8937008213658706485` | unreviewed |
| `ClosureTheorem.table.R55` | S2 `Alignment.Shadows.ClosureTheorem.table_R55.S2` | `12963147099206911679` | unreviewed |
| `ClosureTheorem.table.R56` | S1 `Alignment.Shadows.ClosureTheorem.table_R56.S1` | `14833468798300432852` | unreviewed |
| `ClusteringExtension.R69` | S3 `Alignment.Shadows.ClusteringExtension.R69.S3` | `17003994300335183523` | unreviewed |
| `ClusteringExtension.R71-sec-a` | S1 `Alignment.Shadows.ClusteringExtension.R71_sec_a.S1` | `8741874897961290610` | unreviewed |
| `ClusteringExtension.R71-sec-a` | S2 `Alignment.Shadows.ClusteringExtension.R71_sec_a.S2` | `15635824020244536499` | unreviewed |
| `ClusteringExtension.R71-sec-b` | S1 `Alignment.Shadows.ClusteringExtension.R71_sec_b.S1` | `8301577312851019754` | unreviewed |
| `ClusteringExtension.R71-sec-b` | S2 `Alignment.Shadows.ClusteringExtension.R71_sec_b.S2` | `17891639165235094217` | unreviewed |
| `ClusteringExtension.R71-sec-b` | S3 `Alignment.Shadows.ClusteringExtension.R71_sec_b.S3` | `7798069742285525242` | unreviewed |
| `ClusteringExtension.R71a` | S1 `Alignment.Shadows.ClusteringExtension.R71a.S1` | `2848181122043229357` | unreviewed |
| `ClusteringExtension.R71b` | S1 `Alignment.Shadows.ClusteringExtension.R71b.S1` | `1527543137634270157` | unreviewed |
| `ClusteringExtension.R71b` | S2 `Alignment.Shadows.ClusteringExtension.R71b.S2` | `12524949695741934103` | unreviewed |
| `ClusteringExtension.R71b` | S3 `Alignment.Shadows.ClusteringExtension.R71b.S3` | `13139182004517702821` | unreviewed |
| `ClusteringExtension.R73` | S1 `Alignment.Shadows.ClusteringExtension.R73.S1` | `2397481539701400779` | unreviewed |
| `ClusteringExtension.R73-sec-a` | S3 `Alignment.Shadows.ClusteringExtension.R73_sec_a.S3` | `11061940440754222947` | unreviewed |
| `ClusteringExtension.R73-sec-b` | S1 `Alignment.Shadows.ClusteringExtension.R73_sec_b.S1` | `7354373933624218626` | unreviewed |
| `ClusteringExtension.R73-sec-b` | S2 `Alignment.Shadows.ClusteringExtension.R73_sec_b.S2` | `130496183441507227` | unreviewed |
| `ClusteringExtension.R73-sec-b` | S3 `Alignment.Shadows.ClusteringExtension.R73_sec_b.S3` | `12839298447089389154` | unreviewed |
| `ClusteringExtension.R73-sec-b` | S4 `Alignment.Shadows.ClusteringExtension.R73_sec_b.S4` | `3693278195670602350` | unreviewed |
| `ClusteringExtension.R73-sec-b` | S5 `Alignment.Shadows.ClusteringExtension.R73_sec_b.S5` | `8641011339768408277` | unreviewed |
| `ClusteringExtension.R75` | S2 `Alignment.Shadows.ClusteringExtension.R75.S2` | `3226202868403386447` | unreviewed |
| `ClusteringExtension.R75-sec` | S1 `Alignment.Shadows.ClusteringExtension.R75_sec.S1` | `16255756126079489805` | unreviewed |
| `ClusteringExtension.R75-sec` | S2 `Alignment.Shadows.ClusteringExtension.R75_sec.S2` | `14490751464226690499` | unreviewed |
| `ClusteringExtension.R75-sec` | S4 `Alignment.Shadows.ClusteringExtension.R75_sec.S4` | `2459365703473738911` | unreviewed |
| `DegreeCorrelation.R79-sec` | S1 `Alignment.Shadows.DegreeCorrelation.R79_sec.S1` | `10496674773217584345` | unreviewed |
| `DegreeCorrelation.R79-sec` | S2 `Alignment.Shadows.DegreeCorrelation.R79_sec.S2` | `3987878779773114042` | unreviewed |
| `DegreeCorrelation.R84-sec` | S1 `Alignment.Shadows.DegreeCorrelation.R84_sec.S1` | `6499021519330164613` | unreviewed |
| `DegreeCorrelation.R86h-2` | S1 `Alignment.Shadows.DegreeCorrelation.R86h_2.S1` | `14417567082359161917` | unreviewed |
| `DegreeCorrelation.R86h-2` | S2 `Alignment.Shadows.DegreeCorrelation.R86h_2.S2` | `6693015741707976227` | unreviewed |
| `DegreeCorrelation.R86h-2` | S3 `Alignment.Shadows.DegreeCorrelation.R86h_2.S3` | `7675396514764475528` | unreviewed |
| `Docs.cf.liftDef` | S1 `Alignment.Shadows.Docs.cf_liftDef.S1` | `13188018100104406519` | unreviewed |
| `Docs.cf.liftNotUnique` | S3 `Alignment.Shadows.Docs.cf_liftNotUnique.S3` | `10615672184546078462` | unreviewed |
| `Docs.cf.poissonUniqueSection` | S4 `Alignment.Shadows.Docs.cf_poissonUniqueSection.S4` | `13256523891039714127` | unreviewed |
| `Docs.cf.thetaNonincreasing` | S1 `Alignment.Shadows.Docs.cf_thetaNonincreasing.S1` | `2667673506868623642` | unreviewed |
| `Docs.cf.thm3_2` | S1 `Alignment.Shadows.Docs.cf_thm3_2.S1` | `15429395924667692775` | unreviewed |
| `Docs.cf.thm4_3` | S4 `Alignment.Shadows.Docs.cf_thm4_3.S4` | `16644653117622581947` | unreviewed |
| `Docs.cf.thm4_3` | S5 `Alignment.Shadows.Docs.cf_thm4_3.S5` | `6206690150405442008` | unreviewed |
| `Docs.cf.thm4_3` | S6 `Alignment.Shadows.Docs.cf_thm4_3.S6` | `18064114354052800026` | unreviewed |
| `Docs.cf.thm4_3` | S7 `Alignment.Shadows.Docs.cf_thm4_3.S7` | `1164084204777216966` | unreviewed |
| `Docs.cf.thm4_3` | S8 `Alignment.Shadows.Docs.cf_thm4_3.S8` | `3729984076407844400` | unreviewed |
| `Docs.cf.thm4_3-massAction` | S1 `Alignment.Shadows.Docs.cf_thm4_3_massAction.S1` | `17555428417863862265` | unreviewed |
| `Docs.cf.thm4_3-massAction` | S2 `Alignment.Shadows.Docs.cf_thm4_3_massAction.S2` | `3789710977042613763` | unreviewed |
| `Docs.cf.thm7_1` | S1 `Alignment.Shadows.Docs.cf_thm7_1.S1` | `1766798228870029672` | unreviewed |
| `Docs.cf.thm8_1-poisson` | S4 `Alignment.Shadows.Docs.cf_thm8_1_poisson.S4` | `18048839259459195058` | unreviewed |
| `Docs.cf.thm8_1-poisson` | S5 `Alignment.Shadows.Docs.cf_thm8_1_poisson.S5` | `11629983299048506476` | unreviewed |
| `EpiCategory.dispersionIndexOneIffPoisson` | S3 `Alignment.Shadows.EpiCategory.dispersionIndexOneIffPoisson.S3` | `16442924393894332800` | unreviewed |
| `EpiCategory.dispersionIndexOneIffPoisson` | S4 `Alignment.Shadows.EpiCategory.dispersionIndexOneIffPoisson.S4` | `2281541815242083472` | unreviewed |
| `EpiCategory.dispersionIndexOneIffPoisson` | S6 `Alignment.Shadows.EpiCategory.dispersionIndexOneIffPoisson.S6` | `16562816912598356856` | unreviewed |
| `Hierarchy.R25` | S3 `Alignment.Shadows.Hierarchy.R25.S3` | `97897990587558479` | unreviewed |
| `Hierarchy.R27` | S3 `Alignment.Shadows.Hierarchy.R27.S3` | `380570508930210522` | unreviewed |
| `Hierarchy.R27` | S4 `Alignment.Shadows.Hierarchy.R27.S4` | `9344111523977439499` | unreviewed |
| `Hierarchy.R27` | S5 `Alignment.Shadows.Hierarchy.R27.S5` | `16433037668216630849` | unreviewed |
| `InvariantRegion.R123c` | S3 `Alignment.Shadows.InvariantRegion.R123c.S3` | `17590874711526371350` | unreviewed |
| `InvariantRegion.header.thetaFace.b` | S1 `Alignment.Shadows.InvariantRegion.header_thetaFace_b.S1` | `1146043274182688729` | unreviewed |
| `MarginalisationCharacterization.closureFamilies.linear` | S4 `Alignment.Shadows.MarginalisationCharacterization.closureFamilies_linear.S4` | `2349370451500214205` | unreviewed |
| `MarginalisationCharacterization.linearAdmitsEquivariantIff` | S1 `Alignment.Shadows.MarginalisationCharacterization.linearAdmitsEquivariantIff.S1` | `4078019246639920170` | unreviewed |
| `MarginalisationCharacterization.linearAdmitsEquivariantIff` | S2 `Alignment.Shadows.MarginalisationCharacterization.linearAdmitsEquivariantIff.S2` | `12130700592282499896` | unreviewed |
| `MarginalisationCharacterization.linearAdmitsEquivariantIff` | S3 `Alignment.Shadows.MarginalisationCharacterization.linearAdmitsEquivariantIff.S3` | `5133793807900686558` | unreviewed |
| `MarginalisationDynamicalGap.noGlobalSolutionSqDivFour` | S1 `Alignment.Shadows.MarginalisationDynamicalGap.noGlobalSolutionSqDivFour.S1` | `8196236047846007684` | unreviewed |
| `MarginalisationDynamicalGap.noGlobalSolutionSqDivFour` | S2 `Alignment.Shadows.MarginalisationDynamicalGap.noGlobalSolutionSqDivFour.S2` | `5129660957717886767` | unreviewed |
| `MarginalisationDynamicalGap.noGlobalSolutionSqDivFour` | S3 `Alignment.Shadows.MarginalisationDynamicalGap.noGlobalSolutionSqDivFour.S3` | `10544433766813641099` | unreviewed |
| `MarginalisationDynamicalGap.noGlobalSolutionSqDivFour` | S4 `Alignment.Shadows.MarginalisationDynamicalGap.noGlobalSolutionSqDivFour.S4` | `6801411969706087453` | unreviewed |
| `MarginalisationDynamicalGap.normGeHalfEpsTOfHasDerivAt` | S1 `Alignment.Shadows.MarginalisationDynamicalGap.normGeHalfEpsTOfHasDerivAt.S1` | `9646603772153485512` | unreviewed |
| `MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.b` | S2 `Alignment.Shadows.MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness_b.S2` | `5544687249140376120` | unreviewed |
| `MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.b` | S3 `Alignment.Shadows.MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness_b.S3` | `8157836920290940122` | unreviewed |
| `MarginalisationFunctor.rhsCommuteOfLocalTrajCommute` | S1 `Alignment.Shadows.MarginalisationFunctor.rhsCommuteOfLocalTrajCommute.S1` | `1942754957992540291` | unreviewed |
| `MessagePassingBridge.R62d` | S1 `Alignment.Shadows.MessagePassingBridge.R62d.S1` | `17984503144793547209` | unreviewed |
| `MessagePassingBridge.R62d` | S2 `Alignment.Shadows.MessagePassingBridge.R62d.S2` | `3686825374707651492` | unreviewed |
| `MessagePassingBridge.R66a` | S1 `Alignment.Shadows.MessagePassingBridge.R66a.S1` | `16695688466509539996` | unreviewed |
| `MessagePassingBridge.table.R62` | S1 `Alignment.Shadows.MessagePassingBridge.table_R62.S1` | `3026395228859435690` | unreviewed |
| `MessagePassingBridge.table.R66` | S1 `Alignment.Shadows.MessagePassingBridge.table_R66.S1` | `15979788211800390070` | unreviewed |
| `MethodOfStages.R87` | S2 `Alignment.Shadows.MethodOfStages.R87.S2` | `9793455247961484286` | unreviewed |
| `MethodOfStages.R87` | S3 `Alignment.Shadows.MethodOfStages.R87.S3` | `16190401507582013625` | unreviewed |
| `MethodOfStages.R91a` | S1 `Alignment.Shadows.MethodOfStages.R91a.S1` | `11347689737676604337` | unreviewed |
| `MethodOfStages.R91a` | S2 `Alignment.Shadows.MethodOfStages.R91a.S2` | `6396324146758978060` | unreviewed |
| `MethodOfStages.R92` | S1 `Alignment.Shadows.MethodOfStages.R92.S1` | `658428605520415641` | unreviewed |
| `MethodOfStages.R93c` | S1 `Alignment.Shadows.MethodOfStages.R93c.S1` | `1171519756853779018` | unreviewed |
| `MethodOfStages.R93c` | S2 `Alignment.Shadows.MethodOfStages.R93c.S2` | `11981603910784286201` | unreviewed |
| `SurvivalBridge.R46b` | S1 `Alignment.Shadows.SurvivalBridge.R46b.S1` | `3533362574123242016` | unreviewed |
| `SurvivalBridge.R47a` | S3 `Alignment.Shadows.SurvivalBridge.R47a.S3` | `5262980823421386273` | unreviewed |
| `SurvivalBridge.R47b` | S1 `Alignment.Shadows.SurvivalBridge.R47b.S1` | `6056720407993818802` | unreviewed |
| `SurvivalBridge.R49a` | S3 `Alignment.Shadows.SurvivalBridge.R49a.S3` | `14794979786512434332` | unreviewed |
| `SurvivalBridge.R49a` | S4 `Alignment.Shadows.SurvivalBridge.R49a.S4` | `5921752440457201276` | unreviewed |
| `SurvivalBridge.R49b` | S3 `Alignment.Shadows.SurvivalBridge.R49b.S3` | `12215839855542911442` | unreviewed |
| `SurvivalBridge.R49b` | S4 `Alignment.Shadows.SurvivalBridge.R49b.S4` | `6100976651095405087` | unreviewed |
| `SurvivalBridge.R49b` | S5 `Alignment.Shadows.SurvivalBridge.R49b.S5` | `1881993758862135957` | unreviewed |
| `SurvivalBridge.R49b` | S6 `Alignment.Shadows.SurvivalBridge.R49b.S6` | `15852953902680977192` | unreviewed |
| `SurvivalBridge.R49b` | S7 `Alignment.Shadows.SurvivalBridge.R49b.S7` | `9184717181154393743` | unreviewed |
| `SurvivalBridge.R50a` | S3 `Alignment.Shadows.SurvivalBridge.R50a.S3` | `527990334137464407` | unreviewed |
| `SurvivalBridge.R50a` | S4 `Alignment.Shadows.SurvivalBridge.R50a.S4` | `109660018130293259` | unreviewed |
| `SurvivalBridge.R50a` | S5 `Alignment.Shadows.SurvivalBridge.R50a.S5` | `4822892061238026736` | unreviewed |
| `SurvivalBridge.closureKappa-c` | S2 `Alignment.Shadows.SurvivalBridge.closureKappa_c.S2` | `8056942235816920691` | unreviewed |
| `SurvivalBridge.closureKappa-c` | S3 `Alignment.Shadows.SurvivalBridge.closureKappa_c.S3` | `124430430158536312` | unreviewed |
| `SurvivalBridge.header.kappaInvariant-b` | S1 `Alignment.Shadows.SurvivalBridge.header_kappaInvariant_b.S1` | `18136052394246737765` | unreviewed |
| `SurvivalBridge.header.kappaInvariant-b` | S2 `Alignment.Shadows.SurvivalBridge.header_kappaInvariant_b.S2` | `2088136917368670874` | unreviewed |
| `SurvivalBridge.header.kappaInvariant-b` | S3 `Alignment.Shadows.SurvivalBridge.header_kappaInvariant_b.S3` | `4079142737166344163` | unreviewed |
| `SurvivalBridge.table.R42` | S2 `Alignment.Shadows.SurvivalBridge.table_R42.S2` | `4478200644341556262` | unreviewed |
| `SurvivalBridge.table.R42` | S3 `Alignment.Shadows.SurvivalBridge.table_R42.S3` | `8416891768802004460` | unreviewed |
| `SurvivalBridge.table.R43` | S2 `Alignment.Shadows.SurvivalBridge.table_R43.S2` | `4496524544225396250` | unreviewed |
| `SurvivalBridge.table.R44` | S2 `Alignment.Shadows.SurvivalBridge.table_R44.S2` | `6243796909787637318` | unreviewed |
| `SurvivalBridge.table.R46` | S1 `Alignment.Shadows.SurvivalBridge.table_R46.S1` | `13649131194988457723` | unreviewed |
| `SurvivalBridge.table.R49` | S1 `Alignment.Shadows.SurvivalBridge.table_R49.S1` | `10823801428713371447` | unreviewed |
| `SurvivalBridge.table.R49` | S2 `Alignment.Shadows.SurvivalBridge.table_R49.S2` | `3846847698532795088` | unreviewed |
| `SurvivalBridge.table.R50` | S3 `Alignment.Shadows.SurvivalBridge.table_R50.S3` | `8030604248267453373` | unreviewed |
| `SurvivalBridge.table.R50` | S4 `Alignment.Shadows.SurvivalBridge.table_R50.S4` | `3240607034056983751` | unreviewed |
| `SurvivalBridge.table.R50` | S5 `Alignment.Shadows.SurvivalBridge.table_R50.S5` | `17715426519102687964` | unreviewed |

## Tautological shadows (`shadow_tautology`)

These shadows hold by reflexivity or by assumption at reducible transparency after inlining alignment helpers, so they say nothing whatever constants they mention. The flag is lifted by the same hash-pinned `sa_shadow_reviewed` record.

| claim | shadow | content hash | review |
|---|---|---|---|
| none | | | |

## Hints (not scored)

`witness_missing`: an implementation hypothesis headed by a trusted predicate is shared by every shadow, and no `@[sa_witness]` certificate shows it can hold. `backward_unused_shadows`: the backward checker does not use some shadows (they may be redundant).

* `CategoricalComposition.R101e` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `CategoricalComposition.R96f` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3, 4] (redundant given the others?)
* `CategoricalComposition.R99a.3` backward_unused_shadows: the backward checker does not use shadow(s) [1] (redundant given the others?)
* `CategoricalComposition.stagesChangeTransmissibility` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3, 4] (redundant given the others?)
* `ClosureTheorem.negbinKappaDeterminesR` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `ClusteringExtension.R71b` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3] (redundant given the others?)
* `ClusteringExtension.R73-sec-b` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3, 4, 5] (redundant given the others?)
* `CoarseGrain.R7` backward_unused_shadows: the backward checker does not use shadow(s) [1] (redundant given the others?)
* `CoarseGrain.R8` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `CoarseGrain.table.R7` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `CoarseGrain.table.R8` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `ConvergenceTheorems.R105d.2` backward_unused_shadows: the backward checker does not use shadow(s) [1] (redundant given the others?)
* `ConvergenceTheorems.R107a` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `ConvergenceTheorems.R108b` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `ConvergenceTheorems.R108c` backward_unused_shadows: the backward checker does not use shadow(s) [1, 2] (redundant given the others?)
* `ConvergenceTheorems.R109a` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `ConvergenceTheorems.R110a` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `ConvergenceTheorems.R112b` backward_unused_shadows: the backward checker does not use shadow(s) [3, 4, 5] (redundant given the others?)
* `ConvergenceTheorems.R112c` backward_unused_shadows: the backward checker does not use shadow(s) [1, 2] (redundant given the others?)
* `ConvergenceTheorems.r0MassActionEqEdge` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `DegreeCorrelation.R83-sec` backward_unused_shadows: the backward checker does not use shadow(s) [5, 6, 7, 8] (redundant given the others?)
* `DegreeCorrelation.R83e` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3] (redundant given the others?)
* `DegreeCorrelation.R84-sec` backward_unused_shadows: the backward checker does not use shadow(s) [1] (redundant given the others?)
* `Docs.cf.cor4_2-FG` backward_unused_shadows: the backward checker does not use shadow(s) [1] (redundant given the others?)
* `Docs.cf.cor4_2-FGF` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3] (redundant given the others?)
* `Docs.cf.cor4_2-GFG` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3] (redundant given the others?)
* `Docs.cf.localisedObstruction` backward_unused_shadows: the backward checker does not use shadow(s) [1] (redundant given the others?)
* `Docs.cf.nonMarkovObstruction` backward_unused_shadows: the backward checker does not use shadow(s) [1, 3] (redundant given the others?)
* `Docs.cf.validityDomain` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3, 4] (redundant given the others?)
* `Docs.ms.T2` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3, 4, 5] (redundant given the others?)
* `Docs.ms.T3` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3] (redundant given the others?)
* `Docs.ms.T4-companion` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `Docs.ms.T5` witness_missing: impl 1 (EBCMCategory.MarginalisationDynamicalGap.trajectoryGap_hasDerivAt_zero): its hypotheses headed by [EBCMCategory.Marginalisation.IsFlow] are also assumed by every shadow, and no @[sa_witness "Docs.ms.T5" 1] certificate shows they can hold
* `Docs.ms.T5` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `Docs.ms.T6` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3, 4, 5] (redundant given the others?)
* `Docs.ms.T7` witness_missing: impl 1 (EBCMCategory.MarginalisationDynamicalGap.trajectoryGap_norm_ge_half_eps_t): its hypotheses headed by [EBCMCategory.Marginalisation.IsFlow] are also assumed by every shadow, and no @[sa_witness "Docs.ms.T7" 1] certificate shows they can hold
* `Docs.ms.T7` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `DynamicLimits.R29` backward_unused_shadows: the backward checker does not use shadow(s) [1, 3, 4, 5] (redundant given the others?)
* `DynamicLimits.R30` backward_unused_shadows: the backward checker does not use shadow(s) [1, 3, 4] (redundant given the others?)
* `DynamicLimits.R31a` backward_unused_shadows: the backward checker does not use shadow(s) [1, 2, 4, 5] (redundant given the others?)
* `DynamicLimits.R32a` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3] (redundant given the others?)
* `DynamicLimits.R33a` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `DynamicLimits.R33b` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `DynamicLimits.R34` backward_unused_shadows: the backward checker does not use shadow(s) [3, 4] (redundant given the others?)
* `DynamicLimits.R35a` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3] (redundant given the others?)
* `DynamicLimits.R36a` backward_unused_shadows: the backward checker does not use shadow(s) [1] (redundant given the others?)
* `DynamicLimits.R36b` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3] (redundant given the others?)
* `DynamicLimits.R37a` backward_unused_shadows: the backward checker does not use shadow(s) [1, 3] (redundant given the others?)
* `DynamicLimits.R38` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3, 4, 5, 6] (redundant given the others?)
* `DynamicLimits.R39` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3] (redundant given the others?)
* `DynamicLimits.r0EdgeSwapZero` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `DynamicLimits.table.R29` backward_unused_shadows: the backward checker does not use shadow(s) [1] (redundant given the others?)
* `DynamicLimits.table.R30` backward_unused_shadows: the backward checker does not use shadow(s) [1, 2, 3] (redundant given the others?)
* `DynamicLimits.table.R31` backward_unused_shadows: the backward checker does not use shadow(s) [1, 2] (redundant given the others?)
* `DynamicLimits.table.R32` backward_unused_shadows: the backward checker does not use shadow(s) [1, 2] (redundant given the others?)
* `DynamicLimits.table.R33` backward_unused_shadows: the backward checker does not use shadow(s) [1, 3] (redundant given the others?)
* `DynamicLimits.table.R36` backward_unused_shadows: the backward checker does not use shadow(s) [1] (redundant given the others?)
* `DynamicLimits.table.R37` backward_unused_shadows: the backward checker does not use shadow(s) [1, 3] (redundant given the others?)
* `EpiCategory.R1` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `EpiCategory.R2` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `EpiCategory.R3` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `EpiCategory.R4` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `EpiCategory.dispersionIndexEqOneIff` backward_unused_shadows: the backward checker does not use shadow(s) [3, 4] (redundant given the others?)
* `GaloisPair.R10` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `GaloisPair.R11` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `GaloisPair.R14a` backward_unused_shadows: the backward checker does not use shadow(s) [1] (redundant given the others?)
* `GaloisPair.header.GFLossy` backward_unused_shadows: the backward checker does not use shadow(s) [1] (redundant given the others?)
* `GaloisPair.notGaloisConnectionCoarseGrainPoissonLift` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3] (redundant given the others?)
* `GaloisPair.notGaloisConnectionPoissonLiftCoarseGrain` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3] (redundant given the others?)
* `GaloisPair.table.R10` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `GaloisPair.table.R11` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `Hierarchy.R25` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3] (redundant given the others?)
* `Hierarchy.R27` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3, 4, 5] (redundant given the others?)
* `Hierarchy.R28` backward_unused_shadows: the backward checker does not use shadow(s) [3, 4, 5, 6] (redundant given the others?)
* `Hierarchy.fullLtPairThree` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3] (redundant given the others?)
* `Hierarchy.header.pairGtEbcmGtMeanField` backward_unused_shadows: the backward checker does not use shadow(s) [3, 4, 5] (redundant given the others?)
* `Hierarchy.pairLtFull` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3] (redundant given the others?)
* `Hierarchy.table.R28` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3] (redundant given the others?)
* `InvariantRegion.R120b` backward_unused_shadows: the backward checker does not use shadow(s) [3] (redundant given the others?)
* `InvariantRegion.iNonnegFromRegion` backward_unused_shadows: the backward checker does not use shadow(s) [1] (redundant given the others?)
* `InvariantRegion.missingSeedFactorOvercounts` backward_unused_shadows: the backward checker does not use shadow(s) [1] (redundant given the others?)
* `InvariantRegion.pgfEvalOne` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `MarginalisationCharacterization.c4RealIsKirkwoodForm` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3, 4, 5, 6, 7] (redundant given the others?)
* `MarginalisationCharacterization.header.T3` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `MarginalisationCharacterization.linearAdmitsEquivariantIff` backward_unused_shadows: the backward checker does not use shadow(s) [3] (redundant given the others?)
* `MarginalisationCharacterization.table.T3b` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `MarginalisationDynamicalGap.algebraicGapAtWitness.a` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `MarginalisationDynamicalGap.algebraicGapWitness` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3, 4] (redundant given the others?)
* `MarginalisationDynamicalGap.f3RealIsKirkwoodForm` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3, 4] (redundant given the others?)
* `MarginalisationDynamicalGap.kirkwoodNotEquivariantViaT4` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `MarginalisationDynamicalGap.noFlowF3Real` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `MarginalisationDynamicalGap.noGlobalSolutionSqDivFour` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3, 4] (redundant given the others?)
* `MarginalisationDynamicalGap.trajectoryGapAtZero` witness_missing: impl 1 (EBCMCategory.MarginalisationDynamicalGap.trajectoryGap_at_zero): its hypotheses headed by [EBCMCategory.Marginalisation.IsFlow] are also assumed by every shadow, and no @[sa_witness "MarginalisationDynamicalGap.trajectoryGapAtZero" 1] certificate shows they can hold
* `MarginalisationDynamicalGap.trajectoryGapAtZero` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `MarginalisationDynamicalGap.trajectoryGapHasDerivAtZero` witness_missing: impl 1 (EBCMCategory.MarginalisationDynamicalGap.trajectoryGap_hasDerivAt_zero): its hypotheses headed by [EBCMCategory.Marginalisation.IsFlow] are also assumed by every shadow, and no @[sa_witness "MarginalisationDynamicalGap.trajectoryGapHasDerivAtZero" 1] certificate shows they can hold
* `MarginalisationDynamicalGap.trajectoryGapHasDerivAtZero` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `MarginalisationDynamicalGap.trajectoryGapNormGeHalfEpsT` witness_missing: impl 1 (EBCMCategory.MarginalisationDynamicalGap.trajectoryGap_norm_ge_half_eps_t): its hypotheses headed by [EBCMCategory.Marginalisation.IsFlow] are also assumed by every shadow, and no @[sa_witness "MarginalisationDynamicalGap.trajectoryGapNormGeHalfEpsT" 1] certificate shows they can hold
* `MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.a` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.b` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3] (redundant given the others?)
* `MarginalisationDynamicalGap.witnessLocalGapGe` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `MarginalisationFunctor.RM1` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3] (redundant given the others?)
* `MarginalisationFunctor.RM2` witness_missing: impl 1 (EBCMCategory.Marginalisation.traj_commute_of_rhs_commute): its hypotheses headed by [EBCMCategory.Marginalisation.IsFlow, EBCMCategory.Marginalisation.UniqueFlow] are also assumed by every shadow, and no @[sa_witness "MarginalisationFunctor.RM2" 1] certificate shows they can hold
* `MarginalisationFunctor.RM3` witness_missing: impl 1 (EBCMCategory.Marginalisation.rhs_commute_of_traj_commute): its hypotheses headed by [EBCMCategory.Marginalisation.IsFlow] are also assumed by every shadow, and no @[sa_witness "MarginalisationFunctor.RM3" 1] certificate shows they can hold
* `MarginalisationFunctor.RM4a` witness_missing: impl 1 (EBCMCategory.Marginalisation.dynamic_marginalisation_iff_equivariance): its hypotheses headed by [EBCMCategory.Marginalisation.IsFlow, EBCMCategory.Marginalisation.UniqueFlow] are also assumed by every shadow, and no @[sa_witness "MarginalisationFunctor.RM4a" 1] certificate shows they can hold
* `MessagePassingBridge.R60` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3] (redundant given the others?)
* `MessagePassingBridge.R62d` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `MessagePassingBridge.R63d` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `MessagePassingBridge.R64` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3, 4, 5] (redundant given the others?)
* `MessagePassingBridge.R67` backward_unused_shadows: the backward checker does not use shadow(s) [1, 2, 3, 4] (redundant given the others?)
* `MessagePassingBridge.table.R61` backward_unused_shadows: the backward checker does not use shadow(s) [1, 2] (redundant given the others?)
* `MessagePassingBridge.table.R65` backward_unused_shadows: the backward checker does not use shadow(s) [1, 2, 3] (redundant given the others?)
* `MethodOfStages.R87` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3] (redundant given the others?)
* `MethodOfStages.R88` backward_unused_shadows: the backward checker does not use shadow(s) [1] (redundant given the others?)
* `MethodOfStages.R89a` backward_unused_shadows: the backward checker does not use shadow(s) [1] (redundant given the others?)
* `MethodOfStages.R90a` backward_unused_shadows: the backward checker does not use shadow(s) [1] (redundant given the others?)
* `MethodOfStages.R91a` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `MethodOfStages.R93c` backward_unused_shadows: the backward checker does not use shadow(s) [1] (redundant given the others?)
* `MethodOfStages.erlangTransmissibilityOneLtTwo` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `Obstructions.R18a` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `Obstructions.R19a` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3] (redundant given the others?)
* `Obstructions.R19b` backward_unused_shadows: the backward checker does not use shadow(s) [1, 3, 4] (redundant given the others?)
* `Obstructions.R20a` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `Obstructions.R20b` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3, 4] (redundant given the others?)
* `Obstructions.R21a` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `Obstructions.R21b` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3] (redundant given the others?)
* `Obstructions.R22a` backward_unused_shadows: the backward checker does not use shadow(s) [1, 2] (redundant given the others?)
* `Obstructions.R25b` backward_unused_shadows: the backward checker does not use shadow(s) [3] (redundant given the others?)
* `Obstructions.erlangIsOde` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `Obstructions.header.kirkwoodHierarchyInconsistent` backward_unused_shadows: the backward checker does not use shadow(s) [1, 3] (redundant given the others?)
* `Obstructions.header.networkNotObstruction` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `Obstructions.kirkwoodObstructionWitnessValue-a` backward_unused_shadows: the backward checker does not use shadow(s) [1] (redundant given the others?)
* `Obstructions.table.R18` backward_unused_shadows: the backward checker does not use shadow(s) [3] (redundant given the others?)
* `Obstructions.table.R20` backward_unused_shadows: the backward checker does not use shadow(s) [3] (redundant given the others?)
* `Obstructions.table.R21` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3] (redundant given the others?)
* `PairwiseClosureConditions.header.normalizationOnly` backward_unused_shadows: the backward checker does not use shadow(s) [1] (redundant given the others?)
* `PairwiseClosureConditions.header.safeRegime` backward_unused_shadows: the backward checker does not use shadow(s) [3, 4] (redundant given the others?)
* `PairwiseClosureConditions.keelingFactorNonneg` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `PairwiseClosureConditions.keelingStyleClosureSafe.a` backward_unused_shadows: the backward checker does not use shadow(s) [3, 4, 5] (redundant given the others?)
* `PairwiseClosureConditions.keelingWeightsNonneg` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `PairwiseClosureConditions.tripleMassConserved` backward_unused_shadows: the backward checker does not use shadow(s) [1] (redundant given the others?)
* `SEIREquations.edgeHazard` backward_unused_shadows: the backward checker does not use shadow(s) [1, 3] (redundant given the others?)
* `SEIREquations.iPopWrongNonzeroAtSeed` backward_unused_shadows: the backward checker does not use shadow(s) [1] (redundant given the others?)
* `SEIREquations.seirIGrowthBounded-a` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `SEIREquations.table.SEIR1` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `SurvivalBridge.R42` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3] (redundant given the others?)
* `SurvivalBridge.R44a` backward_unused_shadows: the backward checker does not use shadow(s) [1] (redundant given the others?)
* `SurvivalBridge.R45a` backward_unused_shadows: the backward checker does not use shadow(s) [1] (redundant given the others?)
* `SurvivalBridge.R45b` backward_unused_shadows: the backward checker does not use shadow(s) [1, 3] (redundant given the others?)
* `SurvivalBridge.R46c` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3] (redundant given the others?)
* `SurvivalBridge.R47a` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3] (redundant given the others?)
* `SurvivalBridge.R49a` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3, 4] (redundant given the others?)
* `SurvivalBridge.table.R42` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3] (redundant given the others?)
* `SurvivalBridge.table.R43` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3] (redundant given the others?)
* `SurvivalBridge.table.R44` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3] (redundant given the others?)
* `SurvivalBridge.table.R45` backward_unused_shadows: the backward checker does not use shadow(s) [2, 3, 4] (redundant given the others?)
* `SurvivalBridge.table.R47` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `VolzMeyersEquations.table.VM1` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `VolzMeyersEquations.thetaNonincreasing` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)

## Refuters

Theorems used to refute implementation hypotheses: sound trusted-library theorems `∀ ys, P₁ → … → Pₘ → False` (or `→ ¬ P`, `→ a ≠ b`) and alignment-library `@[sa_refutation]` theorems.

| refuter | origin | status | premise heads | notes |
|---|---|---|---|---|
| `EBCMCategory.Marginalisation.instDecidableEqMotifShape._proof_2` | trusted | valid | Not, Eq |  |
| `EBCMCategory.MarginalisationDynamicalGap.fibre_collapse_obstruction` | trusted | valid | Eq, Ne, EBCMCategory.MarginalisationCharacterization.Equivariant |  |
| `EBCMCategory.MarginalisationDynamicalGap.kirkwood_not_equivariant_via_T4` | trusted | valid | EBCMCategory.MarginalisationCharacterization.Equivariant |  |
| `EBCMCategory.MarginalisationDynamicalGap.no_flow_F3Kℝ` | trusted | valid | EBCMCategory.Marginalisation.IsFlow |  |
| `GF_ne_id._proof_1_1` | trusted | valid | Eq |  |
| `InvariantRegion.missing_seed_factor_overcounts` | trusted | valid | Ne, Eq |  |
| `MarginalisationObstruction.instDecidableEqIdx3._proof_1` | trusted | valid | Not, Eq |  |
| `MarginalisationObstruction.instDecidableEqIdx4._proof_2` | trusted | valid | Not, Eq |  |
| `binomial_kappa_determines_n'._proof_1_1` | trusted | valid | LE.le, Not |  |
| `binomial_recover_n'._proof_1_1` | trusted | valid | LE.le, Eq |  |
| `clustering_breaks_standard` | trusted | valid | standardEbcmValid |  |
| `coarseGrain_mono._proof_1_1` | trusted | valid | Not |  |
| `coarseGrain_not_injective._proof_1_1` | trusted | valid | Eq |  |
| `degreeCorr_breaks_standard` | trusted | valid | standardEbcmValid |  |
| `dynamic_lt_pair._proof_1_2` | trusted | valid | LE.le, Not |  |
| `edgeBased_lt_pair._proof_1_6` | trusted | valid | LE.le, Not |  |
| `edge_refines_node._proof_1_1` | trusted | valid | Not |  |
| `erlang_cv_squared._proof_1_1` | trusted | valid | LT.lt, Eq |  |
| `erlang_mean_preserved._proof_1_1` | trusted | valid | LT.lt, Eq |  |
| `erlang_variance._proof_1_1` | trusted | valid | LT.lt, Eq |  |
| `instDecidableEqAssumption._proof_2` | trusted | valid | Not, Eq |  |
| `instDecidableEqInitCondType._proof_2` | trusted | valid | Not, Eq |  |
| `instDecidableEqModelFamily._proof_2` | trusted | valid | Not, Eq |  |
| `instDecidableEqModelLevel._proof_2` | trusted | valid | Not, Eq |  |
| `instDecidableEqNetworkType._proof_2` | trusted | valid | Not, Eq |  |
| `instDecidableEqPTType._proof_2` | trusted | valid | Not, Eq |  |
| `instDecidableEqSystemType._proof_2` | trusted | valid | Not, Eq |  |
| `instDecidableEqTransitionType._proof_2` | trusted | valid | Not, Eq |  |
| `localised_genuine_obstruction` | trusted | valid | ebcmExists |  |
| `monoidal_dim_assoc._proof_1_1` | trusted | valid | Not |  |
| `monoidal_dim_unit_left._proof_1_1` | trusted | valid | Not |  |
| `monoidal_dim_unit_right._proof_1_1` | trusted | valid | Not |  |
| `not_galoisConnection_coarseGrain_poissonLift` | trusted | valid | GaloisConnection |  |
| `not_galoisConnection_poissonLift_coarseGrain` | trusted | valid | GaloisConnection |  |
| `poissonLift_mono._proof_1_1` | trusted | valid | Not |  |
| `stages_mean_preserved._proof_1_1` | trusted | valid | LT.lt, Eq |  |

## Offending constants

| constant [reason] | checks | examples |
|---|---|---|

## Recorded failures (`sa_fail_*`)

| claim | target | reason | SHADOW? |
|---|---|---|---|
| `CategoricalComposition.R96f` | forward 2 | impl product_subcritical is the identity implication R0_sum ≤ 1 → R0_sum ≤ 1. It says nothing about the next-generation matrix K or its spectral radius, so it does not give S2 (some product with R0_sum ≤ 1 has ρ(K) > 1). The text attributes that example to multiplex_R0_sum_ne_spectral, which is not in this claim's impl list. |  |
| `CategoricalComposition.R96f` | forward 3 | impl product_subcritical is the identity implication R0_sum ≤ 1 → R0_sum ≤ 1 and states no value of R0_sum; S3 (two 3-regular layers with T = 6/25 give R0_sum = 24/25) does not follow from it. |  |
| `CategoricalComposition.R96f` | forward 4 | impl product_subcritical is the identity implication R0_sum ≤ 1 → R0_sum ≤ 1 and mentions no matrix or eigenvalue; S4 (ρ(K) = 6/5 for the 3-regular example) does not follow from it. |  |
| `CategoricalComposition.R97d.1` | forward 1 | impl stratified_dim is the reflexivity d.layer1.dim + d.layer2.dim = d.layer1.dim + d.layer2.dim (proved by rfl) and defines no coproduct dimension, so it carries no information. S1 requires that the coproduct state space Fin dim₁ ⊕ Fin dim₂ has Fintype.card equal to dim₁ + dim₂. That is library content (Fintype.card_sum, Fintype.card_fin) which impl does not state, and no trusted coproduct-dimension definition exists that a bridge could identify. A proof could not use h (vacuous). |  |
| `CategoricalComposition.R98a` | forward 1 | impl stages_n1_recovers_exp is a free-scalar identity, 1 - ((1:ℝ)·γ/(β + (1:ℝ)·γ))^1 = β/(β+γ) for β, γ > 0. It never mentions StagesNatTransData.T_erlang or T_exp. S1 requires d.n = 1 → d.T_erlang = d.T_exp. After rewriting d.n = 1, the unfolding of T_erlang contains the cast ((1:ℕ):ℝ) where impl has the literal (1:ℝ). ((1:ℕ):ℝ) = 1 is Nat.cast_one, a library lemma that is not definitional in ℝ (Real.one is irreducible; rfl fails). So S1 does not follow structurally from h. A faithful impl would state ∀ d, d.n = 1 → d.T_erlang = d.T_exp. |  |
| `CategoricalComposition.R98a` | forward 2 | impl stages_n1_recovers_exp is stated over free reals β, γ with the literal (1:ℝ). S2 requires d.n = 1 → d.T_erlang = d.beta/(d.beta + d.gamma), and after rewriting d.n = 1 the unfolding of T_erlang has the cast ((1:ℕ):ℝ). Bridging the cast needs Nat.cast_one (a library lemma, not definitional in ℝ), so S2 does not follow structurally from h. |  |
| `CategoricalComposition.R98a` | backward | impl is the n = 1 identity over free reals β, γ > 0 with the literal (1:ℝ). S1/S2 give the n = 1 statement only for d.T_erlang, whose unfolding (instantiated at ⟨β, γ, 1, …⟩) has the cast ((1:ℕ):ℝ) in place of (1:ℝ). Converting it needs Nat.cast_one (a library lemma, not definitional in ℝ), so impl does not follow structurally from the shadows. |  |
| `CategoricalComposition.R98b.1` | forward 1 | impl stages_preserve_excess_degree is the field-cancellation disjunction (T₁·e/e = T₁ ∧ T₂·e/e = T₂) ∨ e = 0 over free reals. It mentions no layer, PGF, excess-degree operation or stage count, so it does not state that the excess degree depends only on the PGF. S1 (layers with equal mean and ψ''(1) have equal excessDegree) holds by congruence on the definition of EBCMLayer.excessDegree, so a checker could only prove it without h (vacuous). |  |
| `CategoricalComposition.R98b.1` | backward | impl is a cancellation identity over arbitrary reals; proving it needs a case split on e = 0 and field lemmas (mul_div_cancel_right₀). S1 is a congruence about EBCMLayer.excessDegree and says nothing about cancelling a division, so impl does not follow structurally from S1: the two statements are about different notions. |  |
| `CategoricalComposition.R98c.1` | forward 1 | impl stages_mean_preserved is the closed-form identity (n:ℝ)/((n:ℝ)·γ) = 1/γ for n > 0, γ > 0. S1 requires the expectation of Erlang(n, nγ) itself, ∫ x d(gammaMeasure n (n·γ)) = 1/γ. Linking the closed form n/(nγ) to that integral is the gamma-mean formula (library measure theory), which impl does not state. The Erlang distribution and its expectation are not formalised in the trusted library, so no bridge applies either. |  |
| `CategoricalComposition.R98c.1` | backward | impl is the closed-form arithmetic identity n/(n·γ) = 1/γ. S1 speaks only about the integral ∫ x d(gammaMeasure n (n·γ)). Deriving the closed form from S1 needs ∫ x dΓ(n, nγ) = n/(nγ) (library content, not in the shadow), so impl does not follow structurally. The two statements are about different notions (a ratio of scalars vs an expectation). |  |
| `CategoricalComposition.R98d.1` | backward | No shadow set exists: the blind shadow author skipped the claim ('the only formal rendering of "the equation depends on T and g only" is a congruence, a tautology that no implementation can falsify'; the vocabulary has no sojourn-time distribution and no final size). impl stages_final_size_map is the ring identity 1 - T + T·g = 1 - T·(1 - g) over free reals and is silent about sojourn-time distributions, so the claim cannot pass as registered. Registrar question: reclassify as informal, or state a theorem over a staged model. |  |
| `CategoricalComposition.R99a.3` | forward 1 | S1 is the defining equation of clustering_coefficient (it holds by rfl). impl clustering_zero_is_identity (2·0/(2·0 + ⟨s⟩) = 0 for a free rational ⟨s⟩ > 0) does not mention clustering_coefficient, so a checker could only prove S1 without h (vacuous). Remediation: add the defining equation to impl, or accept it as definitional. |  |
| `CategoricalComposition.R99a.3` | forward 2 | impl is stated for a free rational ⟨s⟩ with the hypothesis 0 < ⟨s⟩. For d : ClusteredPGFData, S2 needs 0 < d.mean_single, which is the data invariant ClusteredPGFData.single_pos; a structural checker may not project it. impl does not state the vanishing for ClusteredPGFData itself (mathematically S2 follows from impl plus single_pos). |  |
| `CategoricalComposition.R99b.1` | forward 1 | impl clustering_zero_R0 is a ℚ ring identity over free scalars, T·e + T·(2·0/(e + 2·0))·(1+T) = T·e. The formula's ⟨s⟩ is replaced by excess_s and ⟨t⟩ is the literal 0. S1 is ∀ l : EBCMLayer, l.R0 = l.T · l.excessDegree over ℝ, which holds by definition (rfl) and cannot be obtained from h (different number type, no EBCMLayer, no R0). Any proof of S1 would ignore h (vacuous). Neither statement connects a clustered R₀ to EBCMLayer.R0. |  |
| `CategoricalComposition.R99b.1` | backward | impl is a ℚ identity for arbitrary T and excess_s. Proving it needs ring normalisation (2·0 = 0, 0/x = 0, T·0·(1+T) = 0, a + 0 = a). S1 is the definitional unfolding of EBCMLayer.R0 over ℝ and gives no ℚ arithmetic, so impl does not follow structurally from S1. |  |
| `CategoricalComposition.R101a` | forward 1 | impl R0_monotone_in_T requires 0 ≤ excessDeg (hypothesis he), which neither the text nor S1 assumes. impl is a free-scalar inequality T₁·e ≤ T₂·e and is not stated for layers. For EBCMLayers, 0 ≤ l.excessDegree = sf/mean holds only through the data invariants sf_nonneg and mean_pos plus div_nonneg (a library lemma), none of which a structural checker may use, so S1 does not follow structurally from h. A faithful impl would be stated over EBCMLayer. |  |
| `CategoricalComposition.R101a` | backward | impl holds for arbitrary reals T₁ ≤ T₂ (including T ≤ 0 or T > 1) and every e ≥ 0. S1 covers only EBCMLayers (0 < T ≤ 1, e = sf/mean), and no layer has T or excessDegree definitionally equal to an arbitrary real. The free-scalar impl is strictly more general than S1, so it does not follow from the shadow. |  |
| `CategoricalComposition.R101b` | backward | impl holds for arbitrary reals T₁ < T₂ (including values outside (0,1]) and every e > 0. S1 covers only EBCMLayers (0 < T ≤ 1, e = sf/mean), and arbitrary reals are not definitionally the T or excessDegree of some layer. The free-scalar impl is strictly more general than S1, so it does not follow from the shadow. |  |
| `CategoricalComposition.R101c` | backward | impl is 0·e = 0 for every real e. S1 (R0atT 0 l = 0) gives it only for e = l.excessDegree = sf/mean ≥ 0 of some layer, and no layer's excessDegree is definitionally an arbitrary real (e.g. a negative e). The free-scalar impl is strictly more general than S1. |  |
| `CategoricalComposition.R101d` | backward | impl is 1·e = e for every real e. S1 (l.T = 1 → l.R0 = l.excessDegree) gives it only for e = sf/mean ≥ 0 of a layer with T = 1, and an arbitrary (e.g. negative) real is not definitionally such an excess degree. The free-scalar impl is strictly more general than S1. |  |
| `CategoricalComposition.R101e` | forward 2 | impl R0_monotone_in_excess is stated for free reals with the hypothesis 0 ≤ T. For layers, S2 needs 0 ≤ l₂.T, which follows only from the data invariant EBCMLayer.T_pos via le_of_lt; a structural checker may use neither. impl does not state the layer-level monotonicity of EBCMLayer.R0 (mathematically S2 follows from impl plus T_pos). |  |
| `CategoricalComposition.R102a.3` | forward 1 | impl neutral_is_terminal_q1 is k₁·(0 + (1-0)·q₁) = k₁·q₁ over free reals: the r = 0 value of the entry k₁·P(1\|1), multiplied by k₁. S1 requires that the r-dependent quantity itself, P(1\|1) = r + (1-r)·q₁, equals q₁ at r = 0 (text: 'the r=0 specialization gives q₁'). Removing the factor k₁ needs cancellation (k₁ ≠ 0, mul_left_cancel₀) or one_mul at k₁ = 1, library content that impl does not state. impl says the specialisation gives k₁·q₁, not q₁. |  |
| `CategoricalComposition.R102a.3` | backward | impl holds for arbitrary reals k₁, q₁. S1 gives 0 + (1-0)·q₁ = q₁ only for q₁ = d.q1 = k₁p₁/⟨k⟩ of a mixing datum, never for an arbitrary real q₁, so the free-scalar impl is strictly more general than S1 and does not follow from it (multiplying by k₁ would be congrArg, but the q₁ gap remains). |  |
| `CategoricalComposition.R102c.2` | backward | impl is four identities over arbitrary reals (k and q free, r the literal 0). S1–S4 give them only for k = d.kᵢ and q = d.qⱼ = kⱼpⱼ/⟨k⟩ of mixing data, and an arbitrary real q is not definitionally some d.qⱼ. The free-scalar impl is strictly more general than the shadows, so it does not follow from them. |  |
| `CategoricalComposition.R102d.2` | forward 1 | impl neutral_mixing_det_zero requires q₁ + q₂ = 1 (hypothesis _hq, unused in its proof), which S1 does not assume. For MixingPullbackData, d.q1 + d.q2 = k₁p₁/⟨k⟩ + k₂p₂/⟨k⟩ = 1 needs field lemmas (div_add_div_same, div_self with meanDeg ≠ 0 from meanDeg_pos), not structural reasoning, so S1 does not follow structurally from h. |  |
| `CategoricalComposition.R102d.2` | backward | impl holds for arbitrary reals k₁, k₂, q₁, q₂ with q₁ + q₂ = 1. S1 gives the determinant identity only for k = d.kᵢ and q = d.qⱼ of mixing data, and arbitrary reals are not definitionally of that form. The free-scalar impl is strictly more general than S1. |  |
| `CategoricalComposition.R102e.1` | forward 1 | impl pullback_R0_at_neutral is the re-association T·A/B = T·(A/B) over free reals, with A = k₁²p₁ + k₂²p₂ and B = k₁p₁ + k₂p₂ > 0. It mentions no degree-correlated model, next-generation matrix, eigenvalue or assortativity r. S1 requires that R0uncorr d τ = τ·⟨k(k−1)⟩/⟨k⟩ is an eigenvalue of ngm d τ at r = 0, which h does not state. impl's quantity also uses ⟨k²⟩/⟨k⟩ rather than ⟨k(k−1)⟩/⟨k⟩, so it is not even the uncorrelated R₀. |  |
| `CategoricalComposition.R102e.1` | forward 2 | impl pullback_R0_at_neutral says nothing about eigenvalues: it is only the re-association T·A/B = T·(A/B). S2 requires every eigenvalue of the degree-correlated next-generation matrix ngm d τ at r = 0 to be at most R0uncorr d τ, and that does not follow from h. |  |
| `CategoricalComposition.R102e.1` | backward | impl is a field identity T·A/B = T·(A/B) over arbitrary reals (proved by field_simp). S1/S2 are eigenvalue statements about ngm for mixing data and give no information about this re-association, so impl does not follow structurally from the shadows. The two are about different notions. |  |
| `CategoricalComposition.r0SumEqTrace` | forward 1 | impl MultiplexProduct.R0_sum_eq_trace states R0_sum = K11 + K22. S1 states R0_sum = Matrix.trace (Kmp p), a Finset sum over Fin 2 that unfolds to K11 + (K22 + 0); x + 0 = x is not definitional in ℝ, and the two agree only by the library lemma Matrix.trace_fin_two (or add_zero). A structural checker may not use it, and no bridge applies because Matrix.trace is not a trusted definition. The mathematical content is the same. |  |
| `CategoricalComposition.r0SumEqTrace` | backward | S1 gives R0_sum = Matrix.trace (Kmp p); impl needs R0_sum = K11 + K22. The trace is a Finset sum over Fin 2 that reduces to K11 + (K22 + 0), and removing + 0 in ℝ needs add_zero / Matrix.trace_fin_two, which a structural checker may not use (no trusted definition to bridge). Same mathematical content, not structurally derivable. |  |
| `CategoricalComposition.multiplexR0SumNeSpectral` | forward 1 | impl multiplex_R0_sum_ne_spectral is existential: ∃ p with K11 + K12 = 6/5, K21 + K22 = 6/5, K11 - K12 = -6/25, K21 - K22 = 6/25 and R0_sum = 24/25. S1 is universal (every product of two 3-regular layers with T = 6/25 has K = [[12/25, 18/25], [18/25, 12/25]]); an existential does not give a universal statement, and the witness's layers are not named in impl's statement. |  |
| `CategoricalComposition.multiplexR0SumNeSpectral` | forward 2 | impl is existential over p; S2 (K(1,1) = (6/5)(1,1)) is universal over all products of two 3-regular layers with T = 6/25, so it does not follow. Even for the witness, turning the row sum K11 + K12 = 6/5 into Matrix.mulVec needs Finset-sum and mul_one lemmas, which are not structural. |  |
| `CategoricalComposition.multiplexR0SumNeSpectral` | forward 3 | impl is existential over p; S3 (K(1,-1) = (-6/25)(1,-1)) is universal over all products of two 3-regular layers with T = 6/25, so it does not follow; converting K11 - K12 = -6/25 into a Matrix.mulVec equation would also need library lemmas. |  |
| `CategoricalComposition.multiplexR0SumNeSpectral` | forward 4 | impl states no eigenvalue or spectral-radius property: it gives row sums and differences of K for one witness p. S4 (6/5 is an eigenvalue of K and bounds every real eigenvalue, for every product of two 3-regular layers with T = 6/25) needs eigenvalue theory and the universal quantifier; impl is weaker. |  |
| `CategoricalComposition.multiplexR0SumNeSpectral` | forward 5 | impl gives R0_sum = 24/25 only for its existential witness p. S5 is universal over every product of two 3-regular layers with T = 6/25; an existential does not give it. |  |
| `CategoricalComposition.multiplexR0SumNeSpectral` | backward | Mathematically S1 and S5 give impl with the witness ⟨threeRegularLayer, threeRegularLayer⟩ (its threeReg hypotheses hold by rfl). But from K = [[12/25, 18/25], [18/25, 12/25]] the conjunct K11 + K12 = 6/5 needs the closed real arithmetic 12/25 + 18/25 = 6/5 (norm_num), and similarly for the other row sums and differences. That is not structural, and no bridge applies because the gap is arithmetic on numerals, not a trusted definition. |  |
| `CategoricalComposition.stagesChangeTransmissibility` | forward 2 | S2 is the defining equation of StagesNatTransData.T_exp (it holds by rfl). impl stages_change_transmissibility (n = 2 → T_exp < T_erlang) does not state it, so a checker could only prove S2 without h (vacuous). Remediation: add the defining equation to impl, or accept it as definitional. |  |
| `CategoricalComposition.stagesChangeTransmissibility` | forward 3 | S3 (for n = 2, T_erlang = 1 - (2γ/(β+2γ))²) is the definition of StagesNatTransData.T_erlang after rewriting n = 2 (it holds by rw and rfl). impl states only the strict inequality T_exp < T_erlang, so a checker could only prove S3 without h (vacuous). |  |
| `CategoricalComposition.stagesChangeTransmissibility` | forward 4 | impl states only the strict inequality T_exp < T_erlang for n = 2. S4 is the closed form of the difference, T_erlang - T_exp = β²γ/((β+γ)(β+2γ)²); it appears only inside impl's proof (the local fact `key`), not in its statement, so impl is weaker than S4. |  |
| `ClosureTheorem.header.verificationStrategy` | forward 2 | impl binomial_closure_ode is stated for n + 2 trials: ((↑n+2)(↑n+1)p²wⁿ)w^(n+2) = ((↑n+1)/(↑n+2))((↑n+2)p w^(n+1))². S2 is for every n ≥ 1 with casts ↑n, ↑n - 1 and exponents n - 2, n - 1. impl does not cover n = 1, and instantiating it at n - 2 for n ≥ 2 needs Nat.cast_add / Nat.cast_sub and Nat.sub_add_cancel, which are library lemmas, not structural. (For n ≥ 2 the identities agree mathematically.) |  |
| `ClosureTheorem.header.verificationStrategy` | forward 3 | impl negbin_general_closure_ode is stated for m + 1 successes with a free p: ((↑m+1)(↑m+2)p²c^(m+1)w^(m+3))(c^(m+1)w^(m+1)) = ((↑m+2)/(↑m+1))((↑m+1)p c^(m+1)w^(m+2))². S3 is the instance p = 1 - c at r = m + 1, but getting it for a variable r ≥ 1 needs a case split on r with Nat.le elimination and ((m+1 : ℕ) : ℚ) = ↑m + 1 (Nat.cast_succ; not definitional in ℚ). That is not structural, though impl implies S3 mathematically. |  |
| `ClosureTheorem.header.verificationStrategy` | backward | impl is more general than the shadows in two conjuncts. (1) negbin_general_closure_ode holds for a free p, while S3 fixes p = 1 - c, so S3 gives only the instances p = 1 - c. (2) nonPT_closure_ratio_varies names the two records ⟨1,1,1⟩ and ⟨5/8,1/2,1⟩, while S4 only asserts that some pair θ₁, θ₂ ∈ (0,1] exists, and the existential does not identify the pair. Also, S2 → binomial_closure_ode at n + 2 needs Nat.cast_add (not structural). |  |
| `ClosureTheorem.table.R52` | forward 1 | impl poisson_closure_ratio is the ratio form closureRatio <E, lam*E, lam^2*E> = 1, i.e. (lam^2 E) E / (lam E)^2 = 1. S1 is the ODE form (lam^2 E) E = 1 * (lam E)^2. Going from the ratio to the ODE needs field reasoning (div_eq_iff with (lam E)^2 /= 0, the content of Result 51), which is not structural and is not a definition bridge. The ODE form is poisson_closure_ode (Result 52), which is not in this claim's impl list. |  |
| `ClosureTheorem.table.R52` | forward 2 | impl is a statement over Q in which psi = psi_val is a free positive rational and psi' = lam*psi, psi'' = lam^2*psi are supplied as expressions (free-scalar abstraction). S2 requires the real Poisson PGF t => exp(lam(t-1)) to satisfy deriv (deriv psi) theta * psi theta = 1 * (deriv psi theta)^2 for theta in [0,1]. impl has no real functions or derivatives. |  |
| `ClosureTheorem.table.R52` | backward | impl's ratio form closureRatio <psi, lam psi, lam^2 psi> = 1 does not follow structurally from S1's ODE form (it needs division by (lam psi)^2 /= 0, field reasoning), and S2 is a statement over R with deriv that cannot give the Q statement. |  |
| `ClosureTheorem.table.R53` | forward 1 | impl binomial_closure_ratio is the ratio form closureRatio <w^(n+2), (n+2) p w^(n+1), (n+2)(n+1) p^2 w^n> = (n+1)/(n+2) under 0 < p and 0 < w. S1 is the ODE form psi'' psi = ((n+1)/(n+2)) psi'^2 for every p in [0,1] and theta in [0,1]. This includes p = 0 and w = 1-p+p*theta = 0 (p = 1, theta = 0), which impl excludes. Going from the ratio to the ODE also needs field reasoning (division by psi'^2), which is not structural. |  |
| `ClosureTheorem.table.R53` | forward 2 | impl is over Q with w a free positive rational standing for 1-p+p*theta, and psi', psi'' supplied as expressions. S2 requires the real Binomial(n+2,p) PGF to satisfy the closure ODE with deriv (deriv psi). impl has no real functions or derivatives. |  |
| `ClosureTheorem.table.R53` | backward | impl is stronger than S1: it covers all p > 0 and w > 0 independently (including p > 1 and w > 1), while S1 covers only p in [0,1] with w = 1-p+p*theta in [1-p, 1]. impl's ratio form also needs division from S1's ODE form, which is not structural. S2 is over R. |  |
| `ClosureTheorem.table.R54` | forward 1 | impl negbin2_closure_ratio is the ratio form closureRatio <c^2 w^2, 2 p c^2 w^3, 6 p^2 c^2 w^4> = 3/2 for free p, c, w > 0. S1 is the ODE form psi'' psi = (3/2) psi'^2 for the closed forms (c/D)^2, 2(1-c)c^2/D^3, 6(1-c)^2 c^2/D^4 with D = 1-(1-c)theta. To identify them one needs p := 1-c, w := 1/D and field algebra ((c/D)^2 = c^2 (1/D)^2, x/D^k = x (1/D)^k). Going from the ratio to the ODE needs division by psi'^2. Neither step is structural. |  |
| `ClosureTheorem.table.R54` | forward 2 | impl is over Q with free p, c, w and psi, psi', psi'' supplied as expressions. S2 requires the real NegBin(2,c) PGF (c/(1-(1-c)t))^2 to satisfy the closure ODE with deriv. impl has no real functions or derivatives. |  |
| `ClosureTheorem.table.R54` | backward | impl is stronger and in a different parametrisation: it covers independent positive p, c, w (not tied by p = 1-c and w = 1/(1-p*theta)), while S1 gives only the closed-form ODE for c in (0,1) and theta in [0,1]. The records also differ syntactically, and the ratio form needs division from the ODE form. S2 is over R. |  |
| `ClosureTheorem.table.R55` | forward 1 | impl negbin3_closure_ratio is the ratio form closureRatio <c^3 w^3, 3 p c^3 w^4, 12 p^2 c^3 w^5> = 4/3 for free p, c, w > 0. S1 is the ODE form psi'' psi = (4/3) psi'^2 for the closed forms (c/D)^3, 3(1-c)c^3/D^4, 12(1-c)^2 c^3/D^5 with D = 1-(1-c)theta. To identify them one needs p := 1-c, w := 1/D and field algebra ((c/D)^3 = c^3 (1/D)^3, x/D^k = x (1/D)^k). Going from the ratio to the ODE needs division by psi'^2. Neither step is structural. |  |
| `ClosureTheorem.table.R55` | forward 2 | impl is over Q with free p, c, w and psi, psi', psi'' supplied as expressions. S2 requires the real NegBin(3,c) PGF (c/(1-(1-c)t))^3 to satisfy the closure ODE with deriv. impl has no real functions or derivatives. |  |
| `ClosureTheorem.table.R55` | backward | impl is stronger and in a different parametrisation: it covers independent positive p, c, w (not tied by p = 1-c and w = 1/(1-p*theta)), while S1 gives only the closed-form ODE for c in (0,1) and theta in [0,1]. The records also differ syntactically, and the ratio form needs division from the ODE form. S2 is over R. |  |
| `ClosureTheorem.table.R56` | forward 1 | impl negbin_general_closure_ode states ((m+1)(m+2)p^2 c^(m+1) w^(m+3))(c^(m+1) w^(m+1)) = ((m+2)/(m+1))((m+1) p c^(m+1) w^(m+2))^2 in free p, c, w. S1 needs the identity for the NegBin(m+1) closed forms psi = (c/D)^(m+1), psi' = (m+1)(1-c)c^(m+1)/D^(m+2), psi'' = (m+1)(m+2)(1-c)^2 c^(m+1)/D^(m+3) with D = 1-(1-c)theta. With p := 1-c, w := 1/D the two statements agree only up to field algebra ((c/D)^k = c^k (1/D)^k, x/D^k = x (1/D)^k), which is not structural. No trusted definition is involved, so no bridge applies. |  |
| `ClosureTheorem.table.R56` | backward | impl is a ring identity for every m and all p, c, w in Q. S1 gives it only for the NegBin closed forms with c in (0,1) and theta in [0,1], in a different parametrisation. So impl is strictly more general than S1. |  |
| `ClosureTheorem.table.R57` | backward | impl asserts that two specific literal records (1,1,1) and (5/8,1/2,1) have different closure ratios. S1 only asserts that some finitely supported distribution has a closure ratio that differs at some theta_1, theta_2. This does not determine the impl's records. |  |
| `ClosureTheorem.table.R59` | forward 1 | impl pt_classification_exhaustive gives the trichotomy only under the hypothesis 0 < κ. For d : PGFData, closureKappa d = ψ''(1)/ψ'(1)² can be 0 (secondFactorial_nonneg allows ψ''(1) = 0, e.g. the 1-regular record), and where it is positive, proving 0 < closureKappa d needs div_pos and the data invariants. So S1 does not follow from h for every record. |  |
| `ClosureTheorem.table.R59` | forward 2 | impl pt_classification_exhaustive needs 0 < κ. PGFEval constrains only ψ > 0 and ψ' > 0, so closureRatio e = ψ''ψ/ψ'² is ≤ 0 whenever ψ'' ≤ 0. For those e, S2 does not follow from h; impl is weaker than S2 (a trichotomy for every rational). |  |
| `ClosureTheorem.table.R59` | backward | impl quantifies over a free rational κ > 0. The shadows give the trichotomy only for closureKappa d = ψ''(1)/ψ'(1)² and closureRatio e = ψ''ψ/ψ'². To hit an arbitrary κ one instantiates, e.g., d = ⟨1, κ⟩ with closureKappa = κ/1², and κ/1² = κ needs div_one/one_pow, which are not definitional for a variable κ in ℚ. Not structurally derivable (mathematically S1 implies impl). |  |
| `ClosureTheorem.R52` | forward 2 | impl is a ring identity over Q in which psi = psi_val is a free rational and psi' = lam*psi, psi'' = lam^2*psi are chosen expressions (free-scalar abstraction). S2 requires the real Poisson PGF t => exp(lam(t-1)) to satisfy deriv (deriv psi) theta * psi theta = 1 * (deriv psi theta)^2 for theta in [0,1]. impl has no real functions or derivatives. |  |
| `ClosureTheorem.R52` | backward | impl is stronger than S1: it is the identity for all lam, psi_val in Q, while S1 gives it only under 0 < lam and 0 < E. The cases lam <= 0 or psi_val <= 0 cannot be derived structurally, and S2 is over R. |  |
| `ClosureTheorem.poissonClosureRatio` | forward 2 | impl is over Q with psi = psi_val a free positive rational and psi', psi'' supplied as lam*psi, lam^2*psi (free-scalar abstraction, 'constant' rendered as for all psi_val > 0). S2 requires the actual ratio deriv (deriv psi) theta * psi theta / (deriv psi theta)^2 of the real Poisson PGF exp(lam(t-1)) to equal 1 for theta in [0,1]. impl has no real functions or derivatives. |  |
| `ClosureTheorem.poissonClosureRatio` | backward | Audit limitation only. S1 is the impl's statement except that it takes 0 < lam*E as a separate hypothesis hpsi'. impl assumes only 0 < lam and 0 < psi_val and builds the record with mul_pos. Supplying hpsi' needs the library lemma mul_pos, which is not structural. There is no semantic gap in S1 => impl. S2 (over R) cannot help. |  |
| `ClosureTheorem.R53` | forward 2 | impl is a ring identity over Q in which w is a free rational standing for 1-p+p*theta, and psi', psi'' are chosen expressions. S2 requires the real Binomial(n+2,p) PGF (1-p+p t)^(n+2) to satisfy the closure ODE with deriv (deriv psi) at every theta in [0,1]. impl has no real functions or derivatives. |  |
| `ClosureTheorem.R53` | backward | impl is stronger than S1: it is the identity for all p, w in Q, while S1 gives it only for p in [0,1] and w = 1-p+p*theta with theta in [0,1]. S2 is over R. |  |
| `ClosureTheorem.binomialClosureRatio` | forward 1 | Audit limitation (no semantic gap in this direction). impl needs the hypotheses 0 < p and 0 < w. S1 supplies 0 <= p <= 1, 0 <= theta <= 1, 0 < psi and 0 < psi'. With w := 1-p+p*theta the records agree definitionally. But 0 < p (from 0 < (n+2) p w^(n+1)) and 0 < 1-p+p*theta (from p <= 1, theta >= 0 and 0 < w^(n+2)) need order reasoning on Q, which is not structural. |  |
| `ClosureTheorem.binomialClosureRatio` | forward 2 | impl is over Q with w a free positive rational and psi, psi', psi'' supplied as expressions ('constant' rendered as for all w > 0). S2 requires the actual ratio of the real Binomial(n+2,p) PGF and its deriv to equal (n+1)/(n+2) at every theta in [0,1] where deriv psi theta /= 0. impl has no real functions or derivatives. |  |
| `ClosureTheorem.binomialClosureRatio` | backward | impl is stronger than S1: it covers all p > 0 and w > 0 independently (including p > 1 and w > 1), while S1 covers only p in [0,1] with w = 1-p+p*theta in [1-p, 1]. S1's extra hypotheses 0 < psi and 0 < psi' would also need order lemmas to discharge. S2 is over R. |  |
| `ClosureTheorem.R54` | forward 1 | impl negbin2_closure_ode is the identity (6 p^2 c^2 w^4)(c^2 w^2) = (3/2)(2 p c^2 w^3)^2 in free p, c, w. S1 needs it for the NegBin(2) closed forms: 6(1-c)^2 c^2/D^4 * (c/D)^2 = (3/2)(2(1-c)c^2/D^3)^2 with D = 1-(1-c)theta. With p := 1-c, w := 1/D the sides agree only up to field algebra ((c/D)^2 = c^2 (1/D)^2, x/D^k = x (1/D)^k), which is not structural. No trusted definition is involved, so no bridge applies. |  |
| `ClosureTheorem.R54` | forward 2 | impl is a ring identity over Q with free p, c, w. S2 requires the real NegBin(2,c) PGF (c/(1-(1-c)t))^2 to satisfy the closure ODE with deriv at every theta in [0,1]. impl has no real functions or derivatives. |  |
| `ClosureTheorem.R54` | backward | impl is stronger than S1 and in a different parametrisation: it is the identity for all p, c, w in Q, while S1 gives only the closed-form identity for c in (0,1) and theta in [0,1]. S2 is over R. |  |
| `ClosureTheorem.negbin2ClosureRatio` | forward 1 | impl gives closureRatio <c^2 w^2, 2 p c^2 w^3, 6 p^2 c^2 w^4> = 3/2 for free positive p, c, w. S1 needs closureRatio of the closed-form record <(c/D)^2, 2(1-c)c^2/D^3, 6(1-c)^2 c^2/D^4> with D = 1-(1-c)theta. No instantiation makes the records definitionally equal: (c/D)^2 = c^2 (1/D)^2 and x/D^k = x (1/D)^k are field algebra. impl's hypotheses 0 < 1-c and 0 < 1/D would also need order reasoning. Neither is structural. |  |
| `ClosureTheorem.negbin2ClosureRatio` | forward 2 | impl is over Q with free p, c, w and psi, psi', psi'' supplied as expressions. S2 requires the actual ratio of the real NegBin(2,c) PGF and its deriv to equal 3/2 at every theta in [0,1]. impl has no real functions or derivatives. |  |
| `ClosureTheorem.negbin2ClosureRatio` | backward | impl ranges over independent positive p, c, w (not tied by p = 1-c and w = 1/(1-p*theta)). This is not covered by S1, whose closed-form records also differ syntactically from impl's. S2 is over R. |  |
| `ClosureTheorem.R55` | forward 1 | impl negbin3_closure_ode is the identity (12 p^2 c^3 w^5)(c^3 w^3) = (4/3)(3 p c^3 w^4)^2 in free p, c, w. S1 needs it for the NegBin(3) closed forms: 12(1-c)^2 c^3/D^5 * (c/D)^3 = (4/3)(3(1-c)c^3/D^4)^2 with D = 1-(1-c)theta. With p := 1-c, w := 1/D the sides agree only up to field algebra ((c/D)^3 = c^3 (1/D)^3, x/D^k = x (1/D)^k), which is not structural. No trusted definition is involved, so no bridge applies. |  |
| `ClosureTheorem.R55` | forward 2 | impl is a ring identity over Q with free p, c, w. S2 requires the real NegBin(3,c) PGF (c/(1-(1-c)t))^3 to satisfy the closure ODE with deriv at every theta in [0,1]. impl has no real functions or derivatives. |  |
| `ClosureTheorem.R55` | backward | impl is stronger than S1 and in a different parametrisation: it is the identity for all p, c, w in Q, while S1 gives only the closed-form identity for c in (0,1) and theta in [0,1]. S2 is over R. |  |
| `ClosureTheorem.negbin3ClosureRatio` | forward 1 | impl gives closureRatio <c^3 w^3, 3 p c^3 w^4, 12 p^2 c^3 w^5> = 4/3 for free positive p, c, w. S1 needs closureRatio of the closed-form record <(c/D)^3, 3(1-c)c^3/D^4, 12(1-c)^2 c^3/D^5> with D = 1-(1-c)theta. No instantiation makes the records definitionally equal: (c/D)^3 = c^3 (1/D)^3 and x/D^k = x (1/D)^k are field algebra. impl's hypotheses 0 < 1-c and 0 < 1/D would also need order reasoning. Neither is structural. |  |
| `ClosureTheorem.negbin3ClosureRatio` | forward 2 | impl is over Q with free p, c, w and psi, psi', psi'' supplied as expressions. S2 requires the actual ratio of the real NegBin(3,c) PGF and its deriv to equal 4/3 at every theta in [0,1]. impl has no real functions or derivatives. |  |
| `ClosureTheorem.negbin3ClosureRatio` | backward | impl ranges over independent positive p, c, w (not tied by p = 1-c and w = 1/(1-p*theta)). This is not covered by S1, whose closed-form records also differ syntactically from impl's. S2 is over R. |  |
| `ClosureTheorem.R56` | forward 1 | impl negbin_general_closure_ode states ((m+1)(m+2)p^2 c^(m+1) w^(m+3))(c^(m+1) w^(m+1)) = ((m+2)/(m+1))((m+1) p c^(m+1) w^(m+2))^2 in free p, c, w. S1 needs the identity for the NegBin(m+1) closed forms psi = (c/D)^(m+1), psi' = (m+1)(1-c)c^(m+1)/D^(m+2), psi'' = (m+1)(m+2)(1-c)^2 c^(m+1)/D^(m+3) with D = 1-(1-c)theta. With p := 1-c, w := 1/D the two statements agree only up to field algebra ((c/D)^k = c^k (1/D)^k, x/D^k = x (1/D)^k), which is not structural. No trusted definition is involved, so no bridge applies. |  |
| `ClosureTheorem.R56` | forward 2 | impl is a ring identity over Q with free p, c, w. S2 requires the real NegBin(m+1,c) PGF (c/(1-(1-c)t))^(m+1) to satisfy the closure ODE with deriv at every theta in [0,1]. impl has no real functions or derivatives. |  |
| `ClosureTheorem.R56` | backward | impl is stronger than S1 and in a different parametrisation: it is the identity for every m and all p, c, w in Q, while S1 gives only the closed-form identity for c in (0,1) and theta in [0,1]. S2 is over R. |  |
| `ClosureTheorem.R57` | forward 2 | impl only asserts closureRatio <1,1,1> /= closureRatio <5/8,1/2,1>. S2 says that no constant kappa satisfies the ODE form 1*(1/2+theta^2/2) = kappa*theta^2 on (0,1]. From a hypothetical kappa one gets closureRatio <1,1,1> = kappa*1^2/1^2 and closureRatio <5/8,1/2,1> = kappa*(1/2)^2/(1/2)^2. Identifying both with kappa needs field cancellation, which is not structural. The non-PT property (in ODE form) is not stated by impl. |  |
| `ClosureTheorem.R57` | forward 3 | impl is about two literal rational records, with no real function or derivative. S3 requires the actual ratio deriv (deriv mixR) theta * mixR theta / (deriv mixR theta)^2 of the real function 1/2 + t^2/2 to take two different values on (0,1]. impl does not relate its records to the derivatives of the mixture. |  |
| `ClosureTheorem.R57` | backward | impl is an inequality between two specific literal records (1,1,1) and (5/8,1/2,1). S1 and S3 are existential (some theta_1, theta_2) and S2 is a negation. None of them determines the impl's records. |  |
| `ClosureTheorem.R59` | forward 1 | impl pt_classification_exhaustive has the hypothesis 0 < kap (unused in its proof, but part of the statement). S1 is the trichotomy for every kappa in Q, and the Result 59 text states no range. So impl gives nothing for kappa <= 0 (the range 'kappa > 0' appears only in the header-table row 59, a separate claim). |  |
| `ClosureTheorem.binomialKappaDeterminesN` | forward 1 | impl binomial_kappa_determines_n' only states (n-1)/n < 1 for n >= 2. It says nothing about closureKappa of the Binomial PGFData <n p, n(n-1) p^2>, so the identification kappa = (n-1)/n (S1) is not in impl. |  |
| `ClosureTheorem.binomialKappaDeterminesN` | forward 2 | impl requires 2 <= n. S2 requires ((n:Q)-1)/n < 1 for every n >= 1, so n = 1 (Binomial(1,p), kappa = 0) is not covered by impl. For n >= 2 there is also an audit limitation: the impl hypothesis 2 <= n cannot be produced structurally from 0 < n (Nat.le constructors are library theorems). |  |
| `ClosureTheorem.binomialKappaDeterminesN` | backward | Audit limitation only. S2 => impl is semantically immediate (n >= 2 implies n >= 1), but S2 needs the hypothesis 0 < n. Obtaining it from impl's 2 <= n needs a Nat order lemma (Nat.le 2 n => Nat.le 1 n), which is not structural. S1 (closureKappa) cannot supply it. |  |
| `ClosureTheorem.binomialRecoverN` | forward 1 | impl requires 2 <= n. S1 requires 1/(1 - ((n:Q)-1)/n) = n for every n >= 1 (a Binomial has n >= 1 trials), so n = 1 is not covered by impl. For n >= 2 there is also an audit limitation: the impl hypothesis 2 <= n cannot be produced structurally from 0 < n (Nat.le constructors are library theorems). |  |
| `ClosureTheorem.binomialRecoverN` | backward | Audit limitation only. S1 => impl is semantically immediate (n >= 2 implies n >= 1), but S1 needs the hypothesis 0 < n. Obtaining it from impl's 2 <= n needs a Nat order lemma (Nat.le 2 n => Nat.le 1 n), which is not structural. |  |
| `ClosureTheorem.negbinKappaDeterminesR` | forward 2 | impl negbin_kappa_determines_r' only proves 0 < 1/(kappa-1) for kappa > 1. S2 requires recovery of the NegBin parameter: kappa = (r+1)/r with r > 0 implies r = 1/(kappa-1). impl mentions neither r nor the relation kappa = (r+1)/r. |  |
| `ClusteringExtension.R71-sec-a` | forward 1 | impl triangle_pair_transmission is only the ring identity 1 - (1-T)(1-T²) = T + T² - T³. It says nothing about the probability that the node is infected through the triangle pair (S1: the sum over the eight transmission outcomes of the direct edge and the two-edge path equals 1 - (1-T)(1-T²)), so impl is weaker than S1. |  |
| `ClusteringExtension.R71-sec-a` | backward | impl states the ring identity for every rational T; S2 states it only for 0 ≤ T ≤ 1 (and S1 is about the outcome sum pTri, which does not give the identity outside [0,1] either). So impl is stronger than the shadows on the domain, and there is no structural route from them to impl at T < 0 or T > 1. |  |
| `ClusteringExtension.R71-sec-b` | forward 1 | impl triangle_per_partner states T(2 - T) = 2T - T². S1 states T(2 - T) = 1 - (1 - T)². The right-hand sides agree only by ring arithmetic (1 - (1-T)² = 2T - T²), which is not definitional in ℚ for a variable T, so S1 does not follow structurally from h. |  |
| `ClusteringExtension.R71-sec-b` | forward 2 | impl is a ring identity about T(2 - T). It says nothing about the probability that at least one of two independent edges transmits (S2: the sum over the four outcomes equals 1 - (1-T)²). |  |
| `ClusteringExtension.R71-sec-b` | forward 3 | impl states only T(2 - T) = 2T - T². It does not say that the triangle-pair probability 1 - (1-T)(1-T²) differs from T(2 - T) at some T ∈ [0,1] (S3); impl is weaker. |  |
| `ClusteringExtension.R71-sec-b` | backward | impl (T(2 - T) = 2T - T² for every rational T) does not follow structurally from the shadows. S1 gives T(2 - T) = 1 - (1-T)², and turning 1 - (1-T)² into 2T - T² needs ring. The registered impl is the ring identity of Result 71b, not the text's negative statement (that the triangle probability is not T(2 - T)). |  |
| `ClusteringExtension.R71a` | backward | impl (triangle_pair_transmission) is stronger than the shadow: it states 1 - (1-T)(1-T^2) = T + T^2 - T^3 for every T : ℚ, while S1 (a pair transmission probability, T a probability as in the docstring 'directly (prob T)') states it only for 0 ≤ T ≤ 1. The impl at T outside [0,1] cannot be obtained from S1 structurally: the hypotheses 0 ≤ T and T ≤ 1 are unavailable, and re-proving the identity needs ring. |  |
| `ClusteringExtension.R71b` | forward 2 | impl triangle_per_partner is only the ring identity T(2 - T) = 2T - T². It says nothing about the per-partner transmissibility in a triangle (S2: the outcome sum pTri T equals T + T² - T³ on [0,1]), so impl is weaker. |  |
| `ClusteringExtension.R71b` | forward 3 | impl states only T(2 - T) = 2T - T². It does not say that T(2 - T) differs from the per-partner transmissibility pTri T at some T ∈ [0,1] (the text's 3/4 against 5/8 at T = 1/2); impl is weaker than S3. |  |
| `ClusteringExtension.R73-sec-b` | forward 2 | impl triangle_per_edge_le_single states only the implication 0 < T → T ≤ 1 → T(1+T)/2 ≤ T. S2 (0 < T → T(1+T)/2 ≤ T → (1+T)/2 ≤ 1) is the forward direction of the text's first equivalence, which impl does not state; deriving it needs division by T > 0 (ordered-field lemmas). |  |
| `ClusteringExtension.R73-sec-b` | forward 3 | S3 (0 < T → (1+T)/2 ≤ 1 → T(1+T)/2 ≤ T) has the hypothesis (1+T)/2 ≤ 1 instead of impl's T ≤ 1. Using impl needs T ≤ 1 from (1+T)/2 ≤ 1, which is ordered-field arithmetic (not structural); the equivalence is not stated by impl. |  |
| `ClusteringExtension.R73-sec-b` | forward 4 | S4 ((1+T)/2 ≤ 1 → T ≤ 1) is a step of the text's chain of equivalences. impl states only the final implication T ≤ 1 → T(1+T)/2 ≤ T, not this equivalence. |  |
| `ClusteringExtension.R73-sec-b` | forward 5 | S5 (T ≤ 1 → (1+T)/2 ≤ 1) is a step of the text's chain of equivalences. impl states only T ≤ 1 → T(1+T)/2 ≤ T; the intermediate inequality (1+T)/2 ≤ 1 is not in impl's statement. |  |
| `ClusteringExtension.R75-sec` | forward 1 | impl poisson_clustering is a rational identity about clustering_coefficient. It says nothing about the real PGF g(x,y) = exp(κs(x-1) + κt(y-1)) or its partial derivative g_x(1,1) = κs (S1). |  |
| `ClusteringExtension.R75-sec` | forward 2 | impl poisson_clustering says nothing about the real PGF g or its partial derivative g_y(1,1) = κt (S2). |  |
| `ClusteringExtension.R75-sec` | forward 3 | S3 holds by unfolding clustering_coefficient on poisNet κs κt (rfl). Using impl instead needs 0 ≤ κt from the shadow's 0 < κt (le_of_lt), which is not structural; a proof without h would be vacuous. |  |
| `ClusteringExtension.R75-sec` | forward 4 | impl gives only the triangle stub fraction. The clustering coefficient 2⟨t⟩/⟨k(k−1)⟩ = 2κt/((κs + 2κt)² + 2κt) of the Poisson PGF (S4, via derivatives of g) is not in impl's statement. |  |
| `ClusteringExtension.R75-sec` | backward | impl holds under 0 ≤ κt (including κt = 0), while the shadows' stub-fraction statement S3 assumes 0 < κt. At κt = 0 impl does not follow, so impl is stronger than the shadow set on its domain. |  |
| `ClusteringExtension.R75` | forward 1 | S1 holds by unfolding clustering_coefficient (it reads only mean_single and mean_triangle, so its value on poisNet κs κt is 2κt/(2κt + κs) by rfl). impl poisson_clustering states the same unfolding for the record ⟨κs, κt, κs⟩ under 0 ≤ κt. A checker that uses h must pass 0 ≤ κt from the shadow's 0 < κt (le_of_lt), which is not structural; without h the proof is vacuous. |  |
| `ClusteringExtension.R75` | forward 2 | impl is the definitional value of the triangle stub fraction clustering_coefficient. It says nothing about the clustering coefficient 2⟨t⟩/⟨k(k−1)⟩ of the bivariate Poisson PGF (S2, computed from derivatives of exp(κs(x-1) + κt(y-1))). The docstring states this value, but impl's statement does not. |  |
| `ClusteringExtension.R75` | backward | impl holds under 0 ≤ κt (it includes the triangle-free case κt = 0), while S1 covers only 0 < κt. At κt = 0 impl does not follow from the shadows, so impl is stronger than the shadow set on its domain. |  |
| `ClusteringExtension.R76-sec` | backward | free-scalar abstraction: impl (degree_conversion_preserves_mean) is (s+2) + 2(t-1) = s + 2t for arbitrary s t : ℚ. It does not mention mean_total_degree or ClusteredPGFData. S1 only speaks about pairs d, d' : ClusteredPGFData, which force s = d.mean_single > 0, t = d.mean_triangle ≥ 0 and t - 1 = d'.mean_triangle ≥ 0. So the impl at, e.g., s = -5 or t = 0 cannot be obtained by instantiating S1: no such data exists, and building data from arbitrary s, t needs positivity proofs. Re-proving the identity needs ring. |  |
| `ClusteringExtension.R76` | backward | free-scalar abstraction: impl (degree_conversion_preserves_mean) is the ring identity (s+2) + 2(t-1) = s + 2t for arbitrary s t : ℚ, not a statement about mean_total_degree or a conversion of ClusteredPGFData. S1 quantifies only over data pairs d, d' (⟨s⟩ > 0, ⟨t⟩ ≥ 1 forced by d' being valid). So the impl for s ≤ 0 or t < 1 cannot be obtained by instantiating S1, and building a ClusteredPGFData from arbitrary s, t needs positivity proofs that are unavailable. |  |
| `CoarseGrain.table.R6` | backward | impl is constructively stronger than S1: coarseGrain_not_injective is the witness form ∃ e₁ e₂ : EpiModel, e₁ ≠ e₂ ∧ coarseGrain e₁ = coarseGrain e₂, while S1 is ¬ (∀ m m', coarseGrain m = coarseGrain m' → m = m'). Getting the witnesses from the negated universal (¬ ∀ → ∃ ¬, then ¬ (A → B) → A ∧ ¬ B) needs classical logic (Classical.byContradiction / Decidable), which is not structural. The only other route is to re-prove the impl from scratch: pick ⟨4, 1⟩, ⟨10, 1⟩ and separate them by a closed kernel computation on ℕ (Nat.beq/Bool.rec), with s1 used only decoratively. That re-proves the impl instead of deriving it from S1, so it is not used. The two forms are classically equivalent and the text's '(lossy)' fits the witness form, so this is a constructive-strength gap, not an overclaim. Remediation: add a trusted theorem ¬ Function.Injective coarseGrain (derived from the witness) as impl. Its forward and backward checks are then structural. |  |
| `CoarseGrain.R6` | backward | impl is constructively stronger than S1: coarseGrain_not_injective is the witness form ∃ e₁ e₂ : EpiModel, e₁ ≠ e₂ ∧ coarseGrain e₁ = coarseGrain e₂, while S1 (the text 'F is not injective', read literally) is ¬ (∀ m m', coarseGrain m = coarseGrain m' → m = m'). Getting the witnesses from the negated universal (¬ ∀ → ∃ ¬, then ¬ (A → B) → A ∧ ¬ B) needs classical logic (Classical.byContradiction / Decidable), which is not structural. The only other route is to re-prove the impl from scratch: pick ⟨4, 1⟩, ⟨10, 1⟩ and separate them by a closed kernel computation on ℕ (Nat.beq/Bool.rec), with s1 used only decoratively. That re-proves the impl instead of deriving it from S1, so it is not used. The two forms are classically equivalent, so this is a constructive-strength gap, not an overclaim. Remediation: add a trusted theorem ¬ Function.Injective coarseGrain (derived from the witness) as impl. Its forward and backward checks are then structural. |  |
| `ConvergenceTheorems.R105c.4` | forward 1 | free-scalar abstraction: impl poisson_R0_edge_formula is ∀ κ β̃ γ̃ : ℝ, 0 < β̃ → 0 < γ̃ → κ·(β̃/(β̃+γ̃)) = κ·β̃/(β̃+γ̃), with two positivity hypotheses (unused in its ring proof). S1 is stated over PoissonEBCMData records d; instantiating the impl at d.kappa d.beta_tilde d.gamma_tilde needs proofs of 0 < d.beta_tilde and 0 < d.gamma_tilde, available only as the structure fields d.beta_tilde_pos / d.gamma_tilde_pos (data invariants, not structural). A faithful impl would drop the unused hypotheses or be stated over PoissonEBCMData. |  |
| `ConvergenceTheorems.R105c.4` | backward | impl is stronger in its quantifier: it holds for every real κ (and any β̃, γ̃ > 0), while S1 covers only κ, β̃, γ̃ that are the fields of a PoissonEBCMData record, so κ > 0. To apply S1 at an arbitrary real κ one must build a record ⟨κ, β̃, γ̃, hκ, hβ, hγ⟩ and needs a proof of 0 < κ, which the impl does not provide (the identity for κ ≤ 0 follows only by real algebra, mul_div_assoc). |  |
| `ConvergenceTheorems.R105d.2` | forward 1 | impl poisson_excess_degree_real asserts only the arithmetic link κ^2/κ = κ (for κ > 0) and never mentions ψ''(1)/ψ'(1) or excessDegree. S1 ((poissonMoments κ hκ).excessDegree = κ²/κ, the link ψ''(1)/ψ'(1) = κ²/κ) holds only by the definitions excessDegree := secondFactorial/mean and poissonMoments (secondFactorial := κ², mean := κ), i.e. by rfl independent of h (the registry impl_note says the identification is carried by the text only). |  |
| `ConvergenceTheorems.R105e.2` | backward | No shadow set exists. The blind shadow author skipped the claim: 'The text describes a Lean statement (and points to another theorem); it asserts no proposition about the model, and the only formula it quotes is a reflexivity instance.' impl S_theta_chain_rule_coeff (κ·S = κ·S) is exactly that reflexivity, so there is nothing for a checker to align. Registrar question: reclassify this sentence as informal (a remark about the Lean statement); its mathematical content is covered by ConvergenceTheorems.sThetaChainRule. |  |
| `ConvergenceTheorems.R107b` | forward 1 | different left-hand side: impl excess_degree_variance_form states m.excessDegree = mean + variance/mean - 1, whose LHS is ψ''(1)/ψ'(1) = secondFactorial/mean; S1 (the text) has LHS (⟨k²⟩ - ⟨k⟩)/⟨k⟩ = (secondMoment - mean)/mean = ((secondFactorial + mean) - mean)/mean. The two LHSs agree only by real arithmetic (add_sub_cancel), i.e. by Result 107a, which is not in this claim's impl list; no admissible bridge exists (excessDegree m = (secondMoment m - mean)/mean would smuggle Result 107a). The registry impl_note records the same mismatch. |  |
| `ConvergenceTheorems.R107b` | backward | S1 gives (secondMoment - mean)/mean = mean + variance/mean - 1; the impl needs excessDegree = secondFactorial/mean on the left. Rewriting (secondFactorial + mean) - mean to secondFactorial needs real arithmetic (add_sub_cancel = Result 107a), not structural reasoning; no admissible bridge (it would restate Result 107a). |  |
| `ConvergenceTheorems.R108b` | forward 2 | impl R0_heterogeneity_amplifies asserts only the inequality R0_homogeneous T m.mean ≤ R0_heterogeneous T m; the equality T·(⟨k⟩ - 1) = R₀(homogeneous) (S2: τ·(m.mean - 1) = R0_homogeneous τ m.mean) is not asserted and holds only by the definition R0_homogeneous T k := T·(k - 1) (rfl, independent of h); an equation cannot be derived structurally from a ≤. |  |
| `ConvergenceTheorems.R110.stability` | forward 1 | impl dfe_stable_iff_R0_le_one is the tautology T·e ≤ 1 ↔ T·e ≤ 1 over free reals (the text itself says 'not formalised here'). It mentions no fixed point of the final-size map, so it does not give S1 (for strictly convex f, if θ = 1 is the only fixed point in [0,1] then f'(1) ≤ 1). |  |
| `ConvergenceTheorems.R110.stability` | forward 2 | impl is the tautology T·e ≤ 1 ↔ T·e ≤ 1. It does not give S2 (for strictly convex f with f'(1) ≤ 1, θ = 1 is the only fixed point in [0,1]), which needs a convexity argument about finalSizeMap. |  |
| `ConvergenceTheorems.R110.stability` | backward | impl (A ↔ A) is provable by Iff.rfl without either shadow, so a backward checker could only be vacuous. The implementation does not state the fixed-point characterisation that the shadows describe. |  |
| `ConvergenceTheorems.R110b.3` | backward | No shadow set exists. The blind shadow author skipped the claim: 'A remark about a Lean statement (a reflexivity instance) and a pointer to another theorem; no proposition to shadow.' impl fixed_point_derivative (T·e = T·e) is that reflexivity. Registrar question: reclassify as informal; the derivative content is ConvergenceTheorems.finalSizeMapHasDerivAt. |  |
| `ConvergenceTheorems.R110c.2` | forward 1 | vacuous impl: dfe_stable_iff_R0_le_one is (T·e ≤ 1 ↔ T·e ≤ 1) by Iff.rfl for free reals T, e ≥ 0; the text's left side \|f'(1)\| ≤ 1 has been replaced by the right side. S1 (\|deriv (θ ↦ finalSizeMap τ (g θ)) 1\| ≤ 1 → τ·excessDegree ≤ 1) needs the derivative f'(1) = τ·secondFactorial/mean (HasDerivAt/deriv lemmas) and le_abs_self; the impl states neither. |  |
| `ConvergenceTheorems.R110c.2` | forward 2 | vacuous impl (P ↔ P by Iff.rfl). S2 (τ·excessDegree ≤ 1 → \|deriv (θ ↦ finalSizeMap τ (g θ)) 1\| ≤ 1) needs the derivative computation, abs_of_nonneg and 0 ≤ excessDegree (data invariants with div_nonneg); the impl states none of it. |  |
| `ConvergenceTheorems.R110c.2` | forward 3 | vacuous impl: (T·e ≤ 1 ↔ T·e ≤ 1) contains no absolute value. S3 (\|τ·excessDegree\| ≤ 1 → τ·excessDegree ≤ 1) is le_abs_self plus le_trans, library lemmas that the impl does not state. |  |
| `ConvergenceTheorems.R110c.2` | forward 4 | vacuous impl: (T·e ≤ 1 ↔ T·e ≤ 1) contains no absolute value. S4 (τ·excessDegree ≤ 1 → \|τ·excessDegree\| ≤ 1) needs abs_of_nonneg with 0 ≤ τ·excessDegree, i.e. mul_nonneg and 0 ≤ excessDegree from the data invariants mean_pos and secondFactorial_nonneg (div_nonneg). The impl's hypothesis 0 ≤ e is an input, never a conclusion, so it supplies none of this. |  |
| `ConvergenceTheorems.R110d` | backward | impl is stronger in form: no_transmission_fixed_point asserts finalSizeMap 0 v = 1 for every real value v, whereas S1/S2 speak only of normalised functions g (g 1 = 1) and of fixed points of θ ↦ finalSizeMap 0 (g θ). S1 yields only finalSizeMap 0 1 = 1. Recovering an arbitrary v from S2 needs a g with g 1 = 1 and g (finalSizeMap 0 v) = v, which requires a classical case split on finalSizeMap 0 v = 1 (by_cases / Decidable, if_pos/if_neg), or the arithmetic 1 - 0 + 0·v = 1; neither is structural. Semantically S1 ∧ S2 imply the impl classically, so this is not an overclaim of the text. |  |
| `ConvergenceTheorems.R112b` | forward 1 | extra hypothesis: impl epidemic_threshold requires 0 < T (_hT, unused in its proof), which the text ('R₀ > 1 iff T > T_c') and S1 do not assume; S1 quantifies over every real τ. From 1 < R0_heterogeneous τ m one gets 0 < τ only via real order lemmas and the data invariants secondFactorial_nonneg / mean_pos (τ ≤ 0 → τ·e ≤ 0), which is not structural. A faithful impl would drop the unused hypothesis. |  |
| `ConvergenceTheorems.R112b` | forward 2 | extra hypothesis: impl epidemic_threshold requires 0 < T, which S2 (T_c m h < τ → 1 < R0_heterogeneous τ m, every real τ) does not assume. 0 < τ follows from T_c < τ only via 0 < T_c = mean/secondFactorial (data invariant mean_pos, div_pos) and lt_trans, which is not structural. |  |
| `ConvergenceTheorems.R112b` | forward 3 | impl epidemic_threshold (an iff between 1 < R₀ and T_c < T) does not assert the identity R₀ = T·excessDeg; S3 (R0_heterogeneous τ m = τ * m.excessDegree) holds only by the definition R0_heterogeneous T m := T·excessDegree m (rfl, independent of h). |  |
| `ConvergenceTheorems.R112b` | forward 4 | impl epidemic_threshold is stated with hypotheses 0 < T and 0 < secondFactorial and conclusion T_c m hsf < T with T_c = mean/secondFactorial. S4 (0 < excessDegree → 1 < R₀ → 1/excessDegree < τ, every real τ) has neither hypothesis: 0 < secondFactorial from 0 < secondFactorial/mean needs mean_pos and div_pos_iff, 0 < τ needs order lemmas, and mean/secondFactorial = 1/(secondFactorial/mean) needs one_div_div; none is structural. |  |
| `ConvergenceTheorems.R112b` | forward 5 | impl epidemic_threshold needs 0 < T and 0 < secondFactorial, and its threshold is mean/secondFactorial; S5 (0 < excessDegree → 1/excessDegree < τ → 1 < R₀, every real τ) supplies only 0 < secondFactorial/mean. Obtaining 0 < secondFactorial (div_pos_iff with mean_pos), 0 < τ (0 < 1/excessDegree, lt_trans) and 1/(sf/mean) = mean/sf (one_div_div) needs data invariants and library lemmas, not structural reasoning. |  |
| `ConvergenceTheorems.R112c` | forward 2 | impl threshold_moment_form states only T_c = ⟨k⟩/(⟨k²⟩ - ⟨k⟩) = mean/(secondMoment - mean); the first form T_c = ⟨k⟩/⟨k(k-1)⟩ (S2: criticalTransmissibility m h = mean/secondFactorial) is not asserted and holds only by the definition criticalTransmissibility m _ := mean/secondFactorial (rfl, independent of h). Deriving it from the impl would need (secondFactorial + mean) - mean = secondFactorial (add_sub_cancel), which is not structural. |  |
| `ConvergenceTheorems.R112d` | backward | audit limitation only (no semantic gap): the impl's statement fixes T_c's positivity argument to the proof pow_pos hk 2 : 0 < κ^2 built inside the statement. S1 takes that proof as a hypothesis h : 0 < (poissonMoments κ hκ).secondFactorial, so applying S1 needs a proof of 0 < κ^2 from 0 < κ, which requires the library lemma pow_pos (or mul_pos) and is not structural. |  |
| `ConvergenceTheorems.r0MassActionEqEdge` | forward 2 | impl gives β/γ = κ·(β̃/(β̃+γ̃)). S2 has R0_heterogeneous (Tedge d) (poissonMoments κ) on the right, which unfolds to Tedge d · (κ²/κ). κ·Tedge = Tedge·(κ²/κ) needs mul_comm and field cancellation (κ ≠ 0), which are not definitional in ℝ, so S2 does not follow structurally from h. Mathematically it holds, since the Poisson excess degree is κ. |  |
| `ConvergenceTheorems.sThetaChainRule` | backward | impl S_theta_chain_rule holds for every real κ; S1 states the chain rule only for κ = d.kappa of a PoissonEBCMData, i.e. κ > 0. For κ ≤ 0 no PoissonEBCMData has that κ, so impl does not follow from S1: impl is stronger on its domain (the text's κ is the Poisson mean degree). |  |
| `DegreeCorrelation.R79-sec` | forward 1 | impl (neutral_mixing_sums_to_one) only states k1*p1/(k1*p1+k2*p2) + k2*p2/(k1*p1+k2*p2) = 1 for four free reals; S1 requires 0 ≤ l*p_l/m for every degree l of an arbitrary degree distribution p : ℕ → ℝ. The impl says nothing about non-negativity and nothing about general (ℕ-indexed, possibly infinite) degree distributions. |  |
| `DegreeCorrelation.R79-sec` | forward 2 | impl (neutral_mixing_sums_to_one) is a two-term identity over free reals; S2 requires HasSum (fun l => l*p_l/m) 1 for an arbitrary degree distribution p : ℕ → ℝ with mean m > 0. The general (HasSum over ℕ) normalisation is not stated by the impl. |  |
| `DegreeCorrelation.R79-sec` | forward 3 | S3 requires 0 ≤ q1 for every TwoDegreeData; impl (neutral_mixing_sums_to_one) states only the sum-to-one identity and contains no inequality, so non-negativity of q1 is not stated. |  |
| `DegreeCorrelation.R79-sec` | forward 4 | S4 requires 0 ≤ q2 for every TwoDegreeData; impl (neutral_mixing_sums_to_one) states only the sum-to-one identity and contains no inequality, so non-negativity of q2 is not stated. |  |
| `DegreeCorrelation.R79-sec` | forward 5 | free-scalar abstraction: impl is ∀ k1 k2 p1 p2 : ℝ, p1 + p2 = 1 → k1*p1 + k2*p2 > 0 → … = 1, not a statement about TwoDegreeData.q1/q2. Instantiating it at d.k1 d.k2 d.p1 d.p2 needs the proofs d.p_sum and 0 < d.k1*d.p1 + d.k2*d.p2 (the latter from d.k1_pos, d.p1_pos, d.k2_pos, d.p2_pos via mul_pos/add_pos): data invariants and library lemmas, which are not structural. (q_sum_one, which states S5 directly, is not in this claim's impl list.) |  |
| `DegreeCorrelation.R79-sec` | backward | impl quantifies over arbitrary reals k1 k2 p1 p2 (only p1 + p2 = 1 and k1*p1 + k2*p2 > 0 assumed; k_i, p_i may be negative or zero). S3-S5 speak only about TwoDegreeData (k_i > 0, p_i > 0, 0 ≤ r ≤ 1), and a TwoDegreeData cannot be built from the impl's hypotheses (0 < k1, 0 < p1, … are unavailable); S1/S2 speak only about ℕ-indexed distributions with HasSum, and turning the two-point case into HasSum facts needs library lemmas (hasSum_fintype, …). So the impl is not derivable from the shadows. |  |
| `DegreeCorrelation.R79b` | forward 1 | free-scalar abstraction: impl is ∀ k1 k2 p1 p2 : ℝ, p1 + p2 = 1 → k1*p1 + k2*p2 > 0 → k1*p1/(k1*p1+k2*p2) + k2*p2/(k1*p1+k2*p2) = 1, not a statement about TwoDegreeData.q1/q2. Using it for S1 (∀ d, d.q1 + d.q2 = 1) needs the hypothesis proofs d.p_sum and 0 < d.k1*d.p1 + d.k2*d.p2 (from the positivity fields via mul_pos/add_pos): data invariants and library lemmas, not structural. |  |
| `DegreeCorrelation.R79b` | forward 2 | free-scalar abstraction: S2 is ∀ d : TwoDegreeData, ∀ m, m = k1*p1 + k2*p2 → k1*p1/m + k2*p2/m = 1. After rw [hm] the goal is the impl's conclusion at d.k1 d.k2 d.p1 d.p2, but the impl's extra hypotheses p1 + p2 = 1 (unused in its proof) and k1*p1 + k2*p2 > 0 can only be discharged from the TwoDegreeData invariants (d.p_sum, d.k1_pos, d.p1_pos, …) with mul_pos/add_pos, which is not structural. |  |
| `DegreeCorrelation.R79b` | backward | impl quantifies over arbitrary reals k1 k2 p1 p2 with only p1 + p2 = 1 and k1*p1 + k2*p2 > 0; S1 and S2 quantify over TwoDegreeData (k_i > 0, p_i > 0, 0 ≤ r ≤ 1). A TwoDegreeData cannot be built from the impl's hypotheses (0 < k1, 0 < k2, 0 < p1, 0 < p2 are unavailable and false in general, e.g. k2 < 0), so the impl is not derivable from the shadows. |  |
| `DegreeCorrelation.R80-sec` | forward 1 | S1 (uncorrelated_R0 Tr ψ = Tr * ((⟨k²⟩ - ⟨k⟩) / ⟨k⟩)) is definitionally true: uncorrelated_R0 Tr ψ unfolds to Tr * excessDegree ψ = Tr * (secondFactorial ψ / mean ψ) = Tr * ((secondMoment - mean) / mean), so it holds by rfl without the impl. The impl states the left-associated form Tr * (secondMoment - mean) / mean = (Tr * (secondMoment - mean)) / mean; deriving S1 from it needs mul_div_assoc (library lemma), and no trusted definition can carry that step as a bridge. The only structural proof ignores the impl (vacuous). Note: the text 'T · ⟨k²-k⟩/⟨k⟩' read left-to-right, (T·⟨k²-k⟩)/⟨k⟩, would coincide with the impl. |  |
| `DegreeCorrelation.R80-sec` | forward 2 | S2 (uncorrelated_R0 Tr ψ = Tr * (secondFactorial ψ / mean ψ)) is definitionally true (uncorrelated_R0 := T * excessDegree, excessDegree := secondFactorial / mean), so it holds by rfl without the impl. The impl states Tr * (secondMoment - mean) / mean = (Tr * (secondMoment - mean)) / mean; deriving S2 from it needs mul_div_assoc (library lemma). The only structural proof ignores the impl (vacuous). Note: the text 'T · ψ''(1)/ψ'(1)' read left-to-right, (T·ψ''(1))/ψ'(1), would coincide with the impl up to unfolding secondFactorial. |  |
| `DegreeCorrelation.R80-sec` | backward | S1 and S2 are both definitional unfoldings of uncorrelated_R0 (Tr * ((⟨k²⟩ - ⟨k⟩)/⟨k⟩)), so they carry no information beyond rfl. The impl is the re-associated form uncorrelated_R0 T d = (T * (secondMoment - mean)) / mean; getting it from S1/S2 needs mul_div_assoc (library lemma), which is not structural. |  |
| `DegreeCorrelation.R83e` | forward 2 | impl (neutral_row_sum_type1) states only r = 0 → C11 + C12 = k1 * (q1 + q2); S2 requires the row sum to equal the degree, C11 + C12 = k1. That needs q1 + q2 = 1 (q_sum_one, not in this claim's impl list) and k1 * 1 = k1 (mul_one); the impl never states that the row sum equals the degree. |  |
| `DegreeCorrelation.R83e` | forward 3 | impl (neutral_row_sum_type1) is about row 1 only (C11 + C12); S3 requires row 2 under r = 0, C21 + C22 = k2, which the impl does not mention (row2_sum_eq_degree, which covers it for every r, is not in this claim's impl list). |  |
| `DegreeCorrelation.R83f` | forward 2 | impl gives q1 + q2 = 1 and r = 0 → C11 + C12 = k1 * (q1 + q2), hence C11 + C12 = k1 * 1 after rw; the last step k1 * 1 = k1 is mul_one (a library lemma; real multiplication does not reduce definitionally), so 'the neutral row sum equals k1' is not stated by the impl and not structurally derivable from it. (row1_sum_eq_degree states C11 + C12 = k1 directly but is not in this claim's impl list.) |  |
| `DegreeCorrelation.R83f` | backward | the impl's second conjunct is r = 0 → C11 + C12 = k1 * (q1 + q2). From S2 (C11 + C12 = k1) and S1 (q1 + q2 = 1) the goal becomes k1 = k1 * 1 after rw [S1], which needs mul_one (library lemma); not structural. |  |
| `DegreeCorrelation.R84-sec` | forward 1 | S1 requires the Poisson second moment, HasSum (fun k => k^2 * e^{-κ} κ^k / k!) (κ^2 + κ). The impl (poisson_excess_degree ∧ poisson_neutral_R0) substitutes ⟨k²⟩ = κ² + κ by hand ((κ^2 + κ - κ)/κ = κ and T * that = T * κ); it never mentions the Poisson pmf or derives its second moment. |  |
| `DegreeCorrelation.R86a` | forward 1 | impl (trace_decomposition) states trC = r * (k1 + k2) + (1 - r) * (k1*q1 + k2*q2); S1 (the text's displayed form) is trC = k1 * r + k2 * r + (1 - r) * (k1*q1 + k2*q2). The statements differ in the first summand: equating r * (k1 + k2) with k1 * r + k2 * r needs distributivity and commutativity (mul_add, mul_comm), which are library lemmas; no trusted definition is involved, so no bridge applies. |  |
| `DegreeCorrelation.R86a` | backward | S1 gives trC = k1 * r + k2 * r + (1 - r) * (k1*q1 + k2*q2); the impl requires trC = r * (k1 + k2) + (1 - r) * (k1*q1 + k2*q2). Converting k1 * r + k2 * r into r * (k1 + k2) needs mul_add / mul_comm (library lemmas); not structural. |  |
| `DegreeCorrelation.R86c` | backward | the impl is stronger than the text: it is neutral_trace (r = 0 → trC = k1*q1 + k2*q2) ∧ weighted_q_sum (k1*q1 + k2*q2 = secondMom/meanDeg for every r). The single shadow S1 (r = 0 → trC = secondMom/meanDeg) does not yield the intermediate form k1*q1 + k2*q2 (neither conjunct follows without weighted_q_sum itself or ring arithmetic on C11 + C22 at r = 0); the text of Result 86c asserts only the trace identity. |  |
| `DegreeCorrelation.R86h-1` | forward 1 | S1 requires trC to be an eigenvalue of C (Module.End.HasEigenvalue (Matrix.toLin' (Cmat d)) trC) at r = 0. The impl's eigenvalue part (neutral_largest_eigenvalue) only says: every real lam with lam^2 - trC*lam + detC = 0 is 0 or trC (the characteristic equation is a hypothesis). It never asserts that trC is a root, and it has no matrix or eigenvalue notion. |  |
| `DegreeCorrelation.R86h-1` | forward 2 | S2 requires every eigenvalue of C to be ≤ trC ('largest'). The impl constrains only real roots lam of the scalar equation lam^2 - trC*lam + detC = 0 (to 0 or trC); linking HasEigenvalue of Matrix.toLin' (Cmat d) to that equation needs Mathlib linear-algebra lemmas, and even then the eigenvalue 0 is ≤ trC only if 0 ≤ trC, which the impl does not state (it would come from positivity of k_i, q_i). |  |
| `DegreeCorrelation.R86h-1` | forward 5 | S5 requires 0 to be an eigenvalue of C at r = 0. neutral_largest_eigenvalue only restricts which lam can solve lam^2 - trC*lam + detC = 0 (to 0 or trC); it does not assert that 0 solves it (that needs detC = 0, i.e. neutral_det_zero, not in the impl list) and has no matrix/eigenvalue notion. |  |
| `DegreeCorrelation.R86h-1` | forward 6 | S6 requires every eigenvalue μ of Matrix.toLin' (Cmat d) to be trC or 0. The impl gives this only for real lam satisfying the scalar characteristic equation lam^2 - trC*lam + detC = 0, supplied as a hypothesis. Deriving that equation from HasEigenvalue (det(C - μI) = 0, the 2x2 characteristic polynomial, trC/detC vs Matrix.trace/det of Cmat d) needs Mathlib lemmas; not structural. |  |
| `DegreeCorrelation.R86h-1` | forward 7 | S7 requires detC = 0 at r = 0. None of the impls (neutral_largest_eigenvalue, neutral_trace, weighted_q_sum) states it: neutral_det_zero is used inside the proof of neutral_largest_eigenvalue but is not part of its statement nor of the impl list, and 'every root of lam^2 - trC*lam + detC = 0 is 0 or trC' does not imply detC = 0 (it holds vacuously when there are no real roots). |  |
| `DegreeCorrelation.R86h-1` | backward | the impl's first conjunct is ∀ d, r = 0 → ∀ lam, lam^2 - trC*lam + detC = 0 → lam = 0 ∨ lam = trC. The shadows speak about Module.End.HasEigenvalue (Matrix.toLin' (Cmat d)) μ; turning the scalar characteristic equation into an eigenvalue of Cmat d (and trC/detC into Matrix.trace/det) needs Mathlib linear-algebra lemmas, so the first conjunct is not derivable structurally. (The other two conjuncts follow from S3, S4.) |  |
| `DegreeCorrelation.R86h-2` | forward 1 | S1 is a general fact about every real 2x2 matrix M with trace τ and det 0 (τ is an eigenvalue). The impl (neutral_largest_eigenvalue) is only about the particular mixing matrix of a TwoDegreeData at r = 0, has no Matrix or eigenvalue notion, and never asserts that τ = trC is a root of lam^2 - trC*lam + detC = 0. |  |
| `DegreeCorrelation.R86h-2` | forward 2 | S2 (0 is an eigenvalue of every real 2x2 matrix with det 0) is not stated: the impl is only about TwoDegreeData's C at r = 0, has no Matrix/eigenvalue notion, and does not assert that 0 is a root of its characteristic equation. |  |
| `DegreeCorrelation.R86h-2` | forward 3 | S3 (every eigenvalue of every real 2x2 matrix M with trace τ and det 0 is τ or 0) is more general than the impl, which only covers the mixing matrix of a TwoDegreeData at r = 0 and only real lam satisfying the scalar equation lam^2 - trC*lam + detC = 0 (given as a hypothesis). An arbitrary M is not of the form Cmat d, and linking HasEigenvalue to the characteristic equation needs Mathlib lemmas. |  |
| `DegreeCorrelation.R86h-2` | backward | the impl is ∀ d, r = 0 → ∀ lam, lam^2 - trC*lam + detC = 0 → lam = 0 ∨ lam = trC. Using S3 at M = Cmat d would need Matrix.trace (Cmat d) = trC and Matrix.det (Cmat d) = 0 (Matrix.trace_fin_two, Matrix.det_fin_two, and neutral_det_zero) and HasEigenvalue from the scalar equation (Mathlib linear algebra); none of this is structural. |  |
| `DegreeCorrelation.neutralDetK` | forward 1 | impl neutral_detK states K11·K22 - K12·K21 = 0 at r = 0. S1 states Matrix.det (Kq d) = 0, where det is the Leibniz sum over permutations of Fin 2. It equals the 2×2 formula only by the library lemma Matrix.det_fin_two, and K12 = (k₁-1)(1-r)q₂ differs from the shadow's entry (k₁-1)((1-r)q₂) by mul_assoc. Neither step is structural, and no bridge applies because Matrix.det is not a trusted definition. The mathematical content agrees. |  |
| `DegreeCorrelation.neutralDetK` | forward 2 | impl gives only the determinant identity K11·K22 - K12·K21 = 0. S2 (Matrix.rank (Kq d) ≤ 1) needs the link between a zero determinant and rank (e.g. Matrix.rank_lt_card_iff_det_eq_zero-type lemmas), which impl does not state. |  |
| `DegreeCorrelation.neutralDetK` | backward | S1 gives Matrix.det (Kq d) = 0, and impl needs K11·K22 - K12·K21 = 0. Going from one to the other needs Matrix.det_fin_two and mul_assoc (library lemmas, not structural), and there is no trusted definition to bridge. |  |
| `DegreeCorrelation.neutralTraceK` | forward 1 | impl neutral_traceK states K11 + K22 = (k₁(k₁-1)p₁ + k₂(k₂-1)p₂)/meanDeg at r = 0. S1 states Matrix.trace (Kq d) = (p₁k₁(k₁-1) + p₂k₂(k₂-1))/(p₁k₁ + p₂k₂). The trace unfolds to K11 + (K22 + 0), and the right-hand sides differ by the order of the factors (k₁·p₁ against p₁·k₁). Both gaps need add_zero / Matrix.trace_fin_two and mul_comm, which are not structural. Same mathematical content. |  |
| `DegreeCorrelation.neutralTraceK` | backward | S1 gives the trace of Kq d as (p₁k₁(k₁-1) + p₂k₂(k₂-1))/(p₁k₁ + p₂k₂). impl needs K11 + K22 = (k₁(k₁-1)p₁ + k₂(k₂-1)p₂)/meanDeg. Moving between them needs Matrix.trace_fin_two (or add_zero) and mul_comm/mul_assoc, which are not structural. |  |
| `DegreeCorrelation.neutralTraceCSubTraceK` | forward 1 | impl neutral_traceC_sub_traceK states trC - (K11 + K22) = 1 at r = 0. S1 states trC - Matrix.trace (Kq d) = 1, where the trace unfolds to K11 + (K22 + 0) (with the shadow's K22 entry equal to impl's). x + 0 = x is not definitional in ℝ, so going from impl to S1 needs add_zero / Matrix.trace_fin_two, which is not structural. Same content. |  |
| `DegreeCorrelation.neutralTraceCSubTraceK` | forward 2 | impl is a trace identity. It says nothing about eigenvalues: S2 (the largest real eigenvalue of C exceeds that of K by one, at r = 0, for k₁, k₂ ≥ 1) needs the rank-one structure of K and C and an eigenvalue argument, none of which impl states. The trace identity alone does not give the largest eigenvalues. |  |
| `DegreeCorrelation.neutralTraceCSubTraceK` | backward | S1 gives trC - Matrix.trace (Kq d) = 1, and impl needs trC - (K11 + K22) = 1. The trace reduces to K11 + (K22 + 0), and removing + 0 needs add_zero (not structural); no trusted definition to bridge. |  |
| `Docs.cf.thm3_2` | forward 1 | impl coarseGrain_not_injective is about the EpiModel records (dimension, R₀): some e₁ ≠ e₂ have coarseGrain e₁ = coarseGrain e₂. S1 is about the map F on EBCM states (θ, φ, R, ψ) ↦ (ψ(θ), 1 − ψ(θ) − R, R), a different map on a different type, which impl does not mention. |  |
| `Docs.cf.thm3_2` | backward | impl is the constructive existential ∃ e₁ e₂, e₁ ≠ e₂ ∧ coarseGrain e₁ = coarseGrain e₂. S2 is ¬ Function.Injective coarseGrain, and ¬∀ ⇒ ∃¬ needs classical logic (not_forall), which structural proofs forbid. S1 is about a different map. Audit limitation (classical logic) for S2. |  |
| `Docs.cf.cor4_2-GF` | forward 2 | S2 (G ∘ F keeps only the R₀: records with equal R₀ have equal images) holds by unfolding poissonLift and coarseGrain (both images are ⟨4, R₀⟩; congrArg on R₀). impl GF_ne_id (∃ e, G(F e) ≠ e) does not state it, so a checker could only prove S2 without h (vacuous). |  |
| `Docs.cf.cor4_2-GF` | backward | impl is the constructive existential ∃ e, G(F e) ≠ e. S1 (G ∘ F ≠ id) gives a witness only by classical logic (not_forall). S2 does not identify a record that G ∘ F moves, so with S2 the witness's disequality is a closed computation that ignores the shadows (vacuous). Audit limitation (classical logic). |  |
| `Docs.cf.thm4_3` | forward 1 | S1 ((a) →: excess = mean ⇒ variance = mean, for every record) would come from poisson_unique_exact_lift at κ := ψ'(1), but that conjunct takes the hypothesis 0 < κ, i.e. 0 < ψ.mean, which only the data invariant PGFData.mean_pos provides (not structural). The route through excess_degree_decomposition needs field arithmetic (σ²/κ = 1 ⇒ σ² = κ). |  |
| `Docs.cf.thm4_3` | forward 2 | S2 ((a) ←: variance = mean ⇒ excess = mean) follows from excess_degree_decomposition (excess = κ − 1 + σ²/κ) only after σ²/κ = κ/κ = 1, which needs div_self with κ ≠ 0 (the data invariant mean_pos) and ring arithmetic. That is not structural. |  |
| `Docs.cf.thm4_3` | forward 4 | S4 ((c) mass-action form for S iff ψ′ = κψ on [0,1]) is about real PGFs and the EBCM S-equation. impl consists of rational identities about two-moment records and does not state it; the doc says (c) is not formalised. |  |
| `Docs.cf.thm4_3` | forward 5 | S5 (ψ′ = κψ on [0,1] with ψ(1) = 1 forces the Poisson PGF) is an ODE uniqueness statement about real functions, which impl does not make. |  |
| `Docs.cf.thm4_3` | forward 6 | S6 (the Poisson PGF e^{κ(x−1)} satisfies ψ′ = κψ) is a real derivative computation that impl does not state. |  |
| `Docs.cf.thm4_3` | forward 7 | S7 ((1 + u²)/2 satisfies (a), via real derivatives) is about the real PGF psiMix, which impl does not mention. |  |
| `Docs.cf.thm4_3` | forward 8 | S8 ((1 + u²)/2 is not a Poisson PGF) is about real functions, which impl does not mention. |  |
| `Docs.cf.thm4_3` | backward | The shadows give impl's first three conjuncts (S3; S1 at the Poisson record; S1 for poisson_unique_exact_lift). The fourth conjunct, excess_degree_decomposition (ψ''(1)/ψ'(1) = κ − 1 + σ²/κ for every record), is a field identity that no shadow states and that is not structural, so impl is stronger than the shadow set. |  |
| `Docs.cf.nonMarkovObstruction` | forward 3 | S3 (a non-Markovian EBCM exists on configuration models) holds by the definition of ebcmExists (.uniform = .uniform, rfl). impl nonmarkov_requires_pde states only systemRequired = .pde, so a checker could only prove S3 without h (vacuous). |  |
| `Docs.cf.validityDomain` | forward 2 | S2 (Markovian + uniform needs an ODE system) is a clause of systemRequired (rfl; the trusted theorem markov_is_ode is not in this claim's impl list). impl (standard_ebcm_valid ∧ clustering_breaks_standard ∧ degreeCorr_breaks_standard) does not mention systemRequired, so a checker could only prove S2 without h (vacuous). |  |
| `Docs.cf.validityDomain` | forward 3 | S3 (general non-Markovian + uniform needs the PDE system) is a clause of systemRequired (rfl; nonmarkov_requires_pde is not in impl). impl does not mention systemRequired, so a checker could only prove S3 without h (vacuous). |  |
| `Docs.cf.validityDomain` | forward 4 | S4 (the non-Markovian EBCM exists on configuration models) holds by the definition of ebcmExists (rfl). impl does not mention ebcmExists, so a checker could only prove S4 without h (vacuous). |  |
| `Docs.cf.thetaNonincreasing` | forward 1 | impl states two sign conditions on rate expressions over ℚ at a single state: -(p.β * φ_I) ≤ 0 for φ_I ≥ 0 (InvariantRegion.theta_dot_nonpos, EBCMParams) and VMState.dθ s p ≤ 0 for P₁, θ ≥ 0 (theta_nonincreasing, Volz–Meyers). S1 is monotonicity of a real function θ on [0, ∞) given HasDerivAt θ (-(β·φI t)) t with φI ∈ [0,1]; getting AntitoneOn from a derivative sign needs the mean value theorem (e.g. antitoneOn_of_deriv_nonpos) and a ℚ → ℝ transfer, which the impl does not state and which is not structural. The impl says nothing about solutions θ(t). |  |
| `Docs.cf.thetaNonincreasing` | backward | S1 is about real functions and their derivatives; the impl conjuncts are ℚ-valued inequalities about EBCMParams (-(β·φ_I) ≤ 0) and VMState (dθ ≤ 0). Obtaining them from S1 would need instantiating S1 at a linear θ, HasDerivAt lemmas and casts ℚ ↔ ℝ (Rat.cast_le): library lemmas, not structural. |  |
| `Docs.cf.thm8_1` | forward 1 | impl (excess_degree_decomposition) is ψ.excessDegree = ψ.mean − 1 + ψ.dispersionIndex, i.e. ψ''(1)/κ = κ − 1 + σ²/κ after unfolding excessDegree and dispersionIndex. S1's right-hand side κ + (σ² − κ)/κ equals this only after (σ² − κ)/κ = σ²/κ − 1, which needs κ ≠ 0 (the data invariant ψ.mean_pos) and sub_div/div_self, plus additive re-association over ℚ: library lemmas and a data invariant, not structural. No trusted definition carries this step, so no bridge applies. |  |
| `Docs.cf.thm8_1` | forward 2 | S2's right-hand side κ + (σ²/κ − 1) differs from the impl's κ − 1 + σ²/κ by additive re-association/commutation over ℚ (add_sub_assoc, add_comm, sub_add_eq_add_sub). This is not definitional (ℚ addition does not reduce on open terms), so it needs library lemmas; no trusted definition can serve as a bridge for it. |  |
| `Docs.cf.thm8_1` | backward | Deriving the impl's form κ − 1 + σ²/κ from S1 (κ + (σ² − κ)/κ) or S2 (κ + (σ²/κ − 1)) needs the same ℚ re-association (and, for S1, division by κ ≠ 0): library lemmas, not structural. |  |
| `Docs.cf.thm8_1-poisson` | forward 1 | impl excess_degree_decomposition gives excess = κ − 1 + σ²/κ. S1 (σ² = κ ⇒ excess = κ) needs, after rewriting σ² = κ, κ − 1 + κ/κ = κ, i.e. div_self with κ ≠ 0 (data invariant mean_pos) and ring arithmetic, which are not structural. |  |
| `Docs.cf.thm8_1-poisson` | forward 2 | S2 (the Poisson record has σ² = κ) is PGFData.poisson_variance_eq_mean, which is not in this claim's impl list. The decomposition identity does not give it. |  |
| `Docs.cf.thm8_1-poisson` | forward 3 | S3 (exact equivalence of S(t) with mass action for Poisson degrees) is a statement about ODE solutions, which impl (a rational identity about records) does not make; the text defers it to Theorem 4.3(c), which is not formalised. |  |
| `Docs.cf.thm8_1-poisson` | forward 4 | S4 ((1 + u²)/2 has σ² = κ, via real derivatives) is about the real PGF psiMix, which impl does not mention. |  |
| `Docs.cf.thm8_1-poisson` | forward 5 | S5 ((1 + u²)/2 violates ψ′ = κψ somewhere on [0,1]) is about real functions, which impl does not mention. |  |
| `Docs.cf.thm8_1-poisson` | backward | impl (excess = κ − 1 + σ²/κ for every record) is a field identity. The shadows state it only in the case σ² = κ (S1), and extending to all records needs field arithmetic, so impl does not follow structurally from the shadow set. |  |
| `Docs.ms.T2` | forward 2 | S2 (M_Q(a, b) = a + b) is the definition of MarginalisationObstruction.M_witness (rfl). impl kirkwood_marginalisation_obstruction states only the existence of a non-commuting state, so a checker could only prove S2 without h (vacuous). |  |
| `Docs.ms.T2` | forward 3 | S3 (the a-component of F4_Kirkwood is a·b) is the definition of F4_Kirkwood (rfl). impl does not state it, so a checker could only prove S3 without h (vacuous). |  |
| `Docs.ms.T2` | forward 4 | S4 (the b-component of F4_Kirkwood is b) is the definition of F4_Kirkwood (rfl). impl does not state it, so a checker could only prove S4 without h (vacuous). |  |
| `Docs.ms.T2` | forward 5 | S5 (F3_Kirkwood c = c²/4) is the definition of F3_Kirkwood (rfl). impl does not state it, so a checker could only prove S5 without h (vacuous). |  |
| `Docs.ms.T3` | forward 3 | impl kirkwood_form_not_equivariant is existential; the T2 surrogate over ℝ (MℝLin, C4ℝ) appears only in its proof. S3 (C4ℝ is Kirkwood-form and no C₃ makes MℝLin intertwine it) is about the named witness and does not follow from the existential. |  |
| `Docs.ms.T3-linearEquivariant` | forward 1 | impl = linear_closure_equivariant ∧ isLinear_admits_equivariant. The first is tautological (its hypothesis is its conclusion unfolded), the second vacuous (∃ F₃, … ∨ True). Neither mentions ker M, so S1 (an equivariant F₃ forces L₄(ker M) ⊆ ker M) does not follow. The text cites linear_admits_equivariant_iff, which is not in impl. |  |
| `Docs.ms.T3-linearEquivariant` | forward 2 | S2 (L₄(ker M) ⊆ ker M gives an equivariant F₃) is the reverse direction of linear_admits_equivariant_iff, which is not in impl; the tautological and vacuous impl conjuncts do not give it. |  |
| `Docs.ms.T3-linearEquivariant` | forward 3 | S3 (some linear L₄ admits no equivariant F₃ for some M) needs a concrete counterexample, which impl does not provide. isLinear_admits_equivariant even asserts '∃ F₃, … ∨ True' for every linear closure. |  |
| `Docs.ms.T3-linearEquivariant` | backward | Both impl conjuncts are provable outright (fun _ _ _ h => h, and ⟨0, Or.inr trivial⟩) without any shadow, so a backward checker could only be vacuous. |  |
| `Docs.ms.T3-kkr` | forward 2 | impl kkr_necessary_not_sufficient is existential over V₄, V₃, M, C₄; the T3b surrogate (MℝLin, C4ℝ) appears only in its proof. S2 (no C₃ makes MℝLin intertwine C4ℝ) is about the named surrogate and does not follow from the existential. |  |
| `Docs.ms.T3-kkr` | backward | With the witnesses from S1 and S2 (U4ℝ, U3ℝ, MℝLin, C4ℝ), impl still needs C4ℝ.IsKirkwoodForm, which no shadow states. It is the trusted lemma C4ℝ_isKirkwoodForm, which a checker may not cite, and a direct proof needs real arithmetic. impl is stronger by that conjunct. |  |
| `Docs.ms.T5-rateTwo` | forward 1 | impl trajectoryGap_rate_two_at_witness assumes global flows φ₄ of F4Kℝ and φ₃ of F3Kℝ. The latter cannot exist (no_flow_F3Kℝ), so impl is vacuous. S1 (for local solutions the gap has rate exactly 2) is witness_localGap_hasDerivAt, which the text cites and which is not in this claim's impl list. |  |
| `Docs.ms.T5-rateTwo` | forward 2 | S2 (local solutions from u₁ and M u₁ exist) is witness_local_solutions_exist, which is not in impl. impl assumes global flows and asserts no existence. |  |
| `Docs.ms.T5-rateTwo` | backward | Deriving impl from S1 needs the global flows turned into LocalSol curves, which requires a positive real radius (0 < 1 in ℝ via zero_lt_one), not structural. impl's hypothesis IsFlow F3Kℝ φ₃ is in any case refuted by no_flow_F3Kℝ (hypothesis_refuted). |  |
| `Docs.ms.T6` | forward 2 | The impl (refinement_failure_exists) is existential; its witnesses (F4Kℝ, F3Kℝ, const 6, u₁) are chosen only inside the proof. S2 ((ClosureFamily.mk F4Kℝ).IsKirkwoodForm) is about the specific map F4Kℝ and cannot be extracted from the existential; the lemma that states it (C4ℝ_isKirkwoodForm) is not in the impl list. |  |
| `Docs.ms.T6` | forward 3 | S3 ((ClosureFamily.mk F3Kℝ).IsKirkwoodForm) is about the specific map F3Kℝ; the impl only asserts Kirkwood form for existentially hidden F3_kirk. The lemma stating it (F3Kℝ_isKirkwoodForm) is not in the impl list. |  |
| `Docs.ms.T6` | forward 4 | S4 (MℝLin (F4Kℝ u₁) = const 6) is about the named witness; the impl's equation MℝLin (F4_kirk u₀) = F3_exact (MℝLin u₀) is about existentially hidden F4_kirk, F3_exact, u₀ and does not identify them with F4Kℝ, const 6, u₁. Computing 1·3 + 3 = 6 over ℝ would also need norm_num. |  |
| `Docs.ms.T6` | forward 5 | S5 (F3Kℝ (MℝLin u₁) ≠ const 6) is about the named witness; the impl's inequality F3_kirk (MℝLin u₀) ≠ F3_exact (MℝLin u₀) is about existentially hidden witnesses, so S5 cannot be extracted. Computing 4²/4 = 4 ≠ 6 over ℝ would also need norm_num. |  |
| `Docs.ms.T6-values` | forward 1 | The impl gives algebraicGap MℝLinCLM F4Kℝ F3Kℝ u₁ = const 2 (only the difference M(F4Kℝ u₁) − F3Kℝ(M u₁)) and the existential refinement_failure_exists (hidden witnesses). The value MℝLin (F4Kℝ u₁) c = 6 is not stated: the difference alone does not determine it, and computing 1·3 + 3 = 6 over ℝ needs norm_num. |  |
| `Docs.ms.T6-values` | forward 2 | F3Kℝ (MℝLin u₁) c = 4 is not stated by the impl: only the difference 2 (algebraicGap_at_witness) and an existential with hidden witnesses (refinement_failure_exists); computing 4²/4 = 4 over ℝ needs norm_num. |  |
| `Docs.ms.T6-values` | forward 3 | F3Kℝ (MℝLin u₁) c ≠ 6 is not stated by the impl: refinement_failure_exists's inequality concerns existentially hidden F3_kirk, F3_exact, u₀, and from the difference = 2 alone one cannot conclude it without the value M(F4Kℝ u₁)(c) = 6 and real arithmetic. |  |
| `Docs.ms.T6-values` | backward | The impl conjunct refinement_failure_exists needs Kirkwood-form proofs for two closures ((ClosureFamily.mk F4_kirk).IsKirkwoodForm and (ClosureFamily.mk F3_kirk).IsKirkwoodForm); no shadow states a Kirkwood-form fact (S1–S4 are values at u₁ only), so the conjunct is not derivable. (The conjunct algebraicGap_at_witness would follow from S4 by funext and case analysis on Idx3.) |  |
| `DynamicLimits.header.interpolation` | forward 2 | S2 (DynamicEBCM.dim m = 5) is the definition of DynamicEBCM.dim (rfl). impl (fast_rewiring_dim ∧ static_limit_dim ∧ full_tower) never mentions DynamicEBCM.dim, so a checker could only prove S2 without h (vacuous). |  |
| `DynamicLimits.header.interpolation` | forward 3 | impl gives only the strict inequality staticLimit.dim < toEpiModel.dim (full_tower) and staticLimit.dim = 4, which leave toEpiModel.dim = 5 undetermined. The equality holds by the definition of toEpiModel (rfl), so a checker could only prove S3 without h (vacuous). |  |
| `DynamicLimits.header.interpolation` | backward | The first two conjuncts of impl are S1 and S4. The third (full_tower: 3 < 4 and 4 < 5 after rewriting with S1, S3, S4) needs closed strict inequalities in ℕ. Nat.lt is the core inductive Nat.le, whose constructors are core-library proofs (and decide is forbidden), so a structural checker cannot prove them. This is an audit limitation on closed ℕ arithmetic, not a semantic difference. |  |
| `DynamicLimits.table.R31` | forward 1 | impl static_limit_dim asserts only the target dimension m.staticLimit.dim = 4; the source dimension in 'dim 5 → 4' (S1: m.dim = 5) is not asserted and holds only by the definition DynamicEBCM.dim _ := 5 (rfl, independent of h). |  |
| `DynamicLimits.table.R31` | forward 2 | impl static_limit_dim asserts only the target dimension m.staticLimit.dim = 4; the source dimension in 'dim 5 → 4' (S2: m.toEpiModel.dim = 5) is not asserted and holds only by the definition toEpiModel.dim := 5 (rfl, independent of h). |  |
| `DynamicLimits.table.R32` | forward 1 | S1 (toEpiModel.dim = 5) holds by the definition of DynamicEBCM.toEpiModel (rfl). impl fast_rewiring_dim states only fastRewiringLimit.dim = 3, so a checker could only prove S1 without h (vacuous). |  |
| `DynamicLimits.table.R32` | forward 2 | S2 (DynamicEBCM.dim m = 5) holds by the definition of DynamicEBCM.dim (rfl). impl states only fastRewiringLimit.dim = 3, so a checker could only prove S2 without h (vacuous). |  |
| `DynamicLimits.table.R33` | forward 3 | impl R0_rewiring_independent (staticLimit.R0 = R0) says nothing about the edge-swapping R₀ at a positive rewiring rate, so S3 (R0 ≠ R₀(η) for η > 0: the stored value is only the static one) does not follow. |  |
| `DynamicLimits.table.R36` | forward 1 | S1 (the Poisson record's stored fast-rewiring value is T·κ) holds by the definition of fastRewiringLimit (rfl). impl states the equality with the static R₀, so a checker could only prove S1 without h (vacuous). |  |
| `DynamicLimits.table.R37` | forward 1 | S1 (the stored fast-rewiring value is T·ψ'(1)) is the definition of fastRewiringLimit (rfl). impl does not state it, so a checker could only prove S1 without h (vacuous). |  |
| `DynamicLimits.table.R37` | forward 3 | S3 (MFSH R₀ > static R₀ for every record) is DynamicEBCM.R0_static_lt_mfsh, which is not in this claim's impl list (fast_rewiring_R0_differs only). |  |
| `DynamicLimits.table.R40` | forward 1 | different notion of '<': impl full_tower states Nat < on the dimensions (m.fastRewiringLimit.dim < m.staticLimit.dim); S1 is the strict order of the EpiModel preorder, m.fastRewiringLimit < m.staticLimit, which unfolds to the Preorder default lt (dim ≤ dim ∧ ¬ reverse ≤, here 3 ≤ 4 ∧ ¬ 4 ≤ 3). The two agree only via Nat order lemmas (Nat.le_of_lt, Nat.not_le_of_lt / lt_iff_le_not_ge), not structurally, and no admissible bridge exists (the head LT.lt / Preorder.toLT is not a trusted definition). Remediation: state the tower with the EpiModel preorder's <. |  |
| `DynamicLimits.table.R40` | forward 2 | different notion of '<': impl full_tower states Nat < on the dimensions (m.staticLimit.dim < m.toEpiModel.dim); S2 is the strict order of the EpiModel preorder, m.staticLimit < m.toEpiModel, i.e. the Preorder default lt (4 ≤ 5 ∧ ¬ 5 ≤ 4). Equivalent only via Nat order lemmas, not structurally; no admissible bridge (LT.lt is not a trusted definition). |  |
| `DynamicLimits.table.R40` | backward | S1, S2 give the EpiModel preorder's strict order (dim ≤ dim ∧ ¬ reverse ≤); full_tower needs Nat < on the dims (Nat.le (d+1) d'), obtainable only via Nat order lemmas (e.g. Nat.lt_of_le_of_ne / lt_iff_le_not_ge), not structurally; no admissible bridge (LT.lt is not a trusted definition). |  |
| `DynamicLimits.R29` | forward 3 | impl static_lt_dynamic asserts only the strict inequality m.staticLimit.dim < m.toEpiModel.dim; the parenthetical value 'static EBCM (dim 4)' (S3: m.staticLimit.dim = 4) is not asserted (it is static_limit_dim, not in R29's impl list) and holds only by the definition edgeModel.dim := 4 (rfl, independent of h). |  |
| `DynamicLimits.R29` | forward 4 | impl static_lt_dynamic asserts only m.staticLimit.dim < m.toEpiModel.dim; the parenthetical value 'dynamic EBCM (dim 5)' (S4: m.dim = 5) is not asserted and holds only by the definition DynamicEBCM.dim _ := 5 (rfl, independent of h). |  |
| `DynamicLimits.R29` | forward 5 | impl static_lt_dynamic asserts only m.staticLimit.dim < m.toEpiModel.dim (a lower bound on m.toEpiModel.dim); the parenthetical value 'dynamic EBCM (dim 5)' (S5: m.toEpiModel.dim = 5) is not asserted and holds only by the definition toEpiModel.dim := 5 (rfl, independent of h). |  |
| `DynamicLimits.R30` | forward 3 | impl dynamic_lt_pair asserts only m.toEpiModel.dim < 12 * N for N ≥ 1; the parenthetical value 'dynamic EBCM (dim 5)' (S3: m.dim = 5) is not asserted and holds only by the definition DynamicEBCM.dim _ := 5 (rfl, independent of h). |  |
| `DynamicLimits.R30` | forward 4 | impl dynamic_lt_pair asserts only the upper bound m.toEpiModel.dim < 12 * N for N ≥ 1; the parenthetical value 'dynamic EBCM (dim 5)' (S4: m.toEpiModel.dim = 5) is not asserted and holds only by the definition toEpiModel.dim := 5 (rfl, independent of h). |  |
| `DynamicLimits.R31a` | forward 1 | impl static_limit_dim asserts only the target m.staticLimit.dim = 4; 'drops from 5' (S1: m.dim = 5) is not asserted (the registry impl_note agrees) and holds only by the definition DynamicEBCM.dim _ := 5 (rfl, independent of h). |  |
| `DynamicLimits.R31a` | forward 2 | impl static_limit_dim asserts only the target m.staticLimit.dim = 4; 'drops from 5' (S2: m.toEpiModel.dim = 5) is not asserted (the registry impl_note agrees) and holds only by the definition toEpiModel.dim := 5 (rfl, independent of h). |  |
| `DynamicLimits.R31a` | forward 4 | S4 ('reducing the dimension by 1': m.staticLimit.dim + 1 = m.dim) relates both endpoints; impl static_limit_dim gives only the lower endpoint m.staticLimit.dim = 4 and never mentions the dynamic dimension, so the drop by 1 is not asserted (the equation is 5 = 5 by rfl, independent of h). |  |
| `DynamicLimits.R31a` | forward 5 | S5 ('reducing the dimension by 1': m.staticLimit.dim + 1 = m.toEpiModel.dim) relates both endpoints; impl static_limit_dim gives only the lower endpoint m.staticLimit.dim = 4 and never mentions m.toEpiModel.dim, so the drop by 1 is not asserted (the equation is 5 = 5 by rfl, independent of h). |  |
| `DynamicLimits.R32a` | forward 2 | impl fast_rewiring_dim asserts only the value m.fastRewiringLimit.dim = 3; S2 ('drops': m.fastRewiringLimit.dim < m.dim, i.e. 3 < 5) is a Nat order fact about the dynamic dimension that the impl does not assert and that cannot be derived structurally from an equation. |  |
| `DynamicLimits.R32a` | forward 3 | impl fast_rewiring_dim asserts only the value m.fastRewiringLimit.dim = 3; S3 ('drops': m.fastRewiringLimit.dim < m.toEpiModel.dim, i.e. 3 < 5) is a Nat order fact about the dynamic dimension that the impl does not assert and that cannot be derived structurally from an equation. |  |
| `DynamicLimits.R33a` | forward 2 | impl R0_rewiring_independent (staticLimit.R0 = R0) says nothing about the edge-swapping R₀ at a positive rewiring rate. S2 (R0 ≠ R₀(η) for every η > 0) is not stated; the edge-swapping R₀ is DynamicEBCM.R0_edgeSwap, which impl does not mention. |  |
| `DynamicLimits.R34` | forward 3 | impl coarseGrain_static_comm asserts only F(m.toEpiModel) = F(m.staticLimit); the value in 'both give dim 3' (S3: (coarseGrain m.toEpiModel).dim = 3) is not asserted and holds only by the definition coarseGrain.dim := 3 (rfl, independent of h). |  |
| `DynamicLimits.R34` | forward 4 | impl coarseGrain_static_comm asserts only F(m.toEpiModel) = F(m.staticLimit); the value in 'both give dim 3' (S4: (coarseGrain m.staticLimit).dim = 3) is not asserted and holds only by the definition coarseGrain.dim := 3 (rfl, independent of h). |  |
| `DynamicLimits.R35a` | forward 2 | impl fast_rewiring_is_coarsegraining asserts only the equality m.fastRewiringLimit.dim = (coarseGrain m.toEpiModel).dim; the value in 'both give dim = 3' (S2: m.fastRewiringLimit.dim = 3) is not asserted (it is fast_rewiring_dim) and holds only by the definition fastRewiringLimit.dim := 3 (rfl, independent of h). |  |
| `DynamicLimits.R35a` | forward 3 | impl fast_rewiring_is_coarsegraining asserts only the equality m.fastRewiringLimit.dim = (coarseGrain m.toEpiModel).dim; the value in 'both give dim = 3' (S3: (coarseGrain m.toEpiModel).dim = 3) is not asserted and holds only by the definition coarseGrain.dim := 3 (rfl, independent of h). |  |
| `DynamicLimits.R35b` | forward 1 | impl fast_rewiring_is_coarsegraining states only fastRewiringLimit.dim = (coarseGrain toEpiModel).dim, the dimension coincidence (3 = 3). It says nothing about R₀; S1 (the MFSH R₀ differs from the static R₀) is R0_static_lt_mfsh, which the text cites and which is not in impl. |  |
| `DynamicLimits.R35b` | forward 2 | impl is the dimension coincidence 3 = 3. S2 (a model with the MFSH R₀ is not the coarse-graining of the dynamic model) needs the R₀ inequality, which impl does not state. |  |
| `DynamicLimits.R35b` | forward 3 | impl is the dimension coincidence 3 = 3. S3 (a model with the MFSH R₀ is not the coarse-graining of the static limit) needs the R₀ inequality, which impl does not state. |  |
| `DynamicLimits.R35b` | backward | impl (fastRewiringLimit.dim = (coarseGrain toEpiModel).dim) holds by rfl, since both are 3, so any backward checker ignores the shadows (vacuous). impl states the first sentence of Result 35 ('has the same dimension as coarse-graining'), not this claim's sentence ('It is not a coarse-graining of the same model'). |  |
| `DynamicLimits.R36a` | forward 1 | S1 (the Poisson record's stored fast-rewiring value is T·κ) holds by the definition of fastRewiringLimit (R0 := T·pgf.mean, and (poisson κ).mean = κ), i.e. by rfl. impl states the equality with the static R₀ instead, so a checker could only prove S1 without h (vacuous). |  |
| `DynamicLimits.R37a` | forward 1 | S1 (the stored fast-rewiring value is T·ψ'(1)) is the definition of fastRewiringLimit (rfl). impl fast_rewiring_R0_differs is an existential inequality and does not state it, so a checker could only prove S1 without h (vacuous). |  |
| `DynamicLimits.R37a` | forward 3 | S3 (the MFSH R₀ exceeds the static R₀ for every record) is DynamicEBCM.R0_static_lt_mfsh, which the text cites and which is not in this claim's impl list. impl states only that some record has T·κ ≠ static R₀. |  |
| `DynamicLimits.R38` | forward 2 | impl dynamic_refines_static asserts only the non-strict m.staticLimit ≤ m.toEpiModel (4 ≤ 5 on dims); 'strictly more state variables' (S2: m.staticLimit.dim < m.toEpiModel.dim) is not asserted (it is Result 29, static_lt_dynamic, not in R38's impl) and does not follow from ≤. |  |
| `DynamicLimits.R38` | forward 3 | impl dynamic_refines_static asserts only the non-strict m.staticLimit ≤ m.toEpiModel (4 ≤ 5 on dims); 'strictly more state variables' (S3: m.staticLimit.dim < m.dim) is not asserted (it is Result 29, static_lt_dynamic, not in R38's impl) and does not follow from ≤. |  |
| `DynamicLimits.R38` | forward 4 | impl dynamic_refines_static asserts only m.staticLimit ≤ m.toEpiModel; the value '5' (S4: m.toEpiModel.dim = 5) is not asserted and holds only by the definition toEpiModel.dim := 5 (rfl, independent of h). |  |
| `DynamicLimits.R38` | forward 5 | impl dynamic_refines_static asserts only m.staticLimit ≤ m.toEpiModel; the value '5' (S5: m.dim = 5) is not asserted and holds only by the definition DynamicEBCM.dim _ := 5 (rfl, independent of h). |  |
| `DynamicLimits.R38` | forward 6 | impl dynamic_refines_static asserts only m.staticLimit ≤ m.toEpiModel; the value '4' (S6: m.staticLimit.dim = 4) is not asserted and holds only by the definition edgeModel.dim := 4 (rfl, independent of h). |  |
| `DynamicLimits.R39` | forward 2 | impl fast_rewiring_coarser_than_static asserts only m.fastRewiringLimit ≤ m.staticLimit; the value 'Mean-field (dim 3)' (S2: m.fastRewiringLimit.dim = 3) is not asserted (it is fast_rewiring_dim) and holds only by the definition fastRewiringLimit.dim := 3 (rfl, independent of h). |  |
| `DynamicLimits.R39` | forward 3 | impl fast_rewiring_coarser_than_static asserts only m.fastRewiringLimit ≤ m.staticLimit; the value 'Static EBCM (dim 4)' (S3: m.staticLimit.dim = 4) is not asserted (it is static_limit_dim) and holds only by the definition edgeModel.dim := 4 (rfl, independent of h). |  |
| `DynamicLimits.R40a` | forward 1 | different notion of '<': impl full_tower states Nat < on the dimensions (m.fastRewiringLimit.dim < m.staticLimit.dim; the registry impl_note: 'stated on dims (not with < of the EpiModel preorder)'); S1 is the strict order of the EpiModel preorder, m.fastRewiringLimit < m.staticLimit, which unfolds to the Preorder default lt (3 ≤ 4 ∧ ¬ 4 ≤ 3 on dims). Equivalent only via Nat order lemmas (Nat.le_of_lt, Nat.not_le_of_lt / lt_iff_le_not_ge), not structurally; no admissible bridge (the head LT.lt / Preorder.toLT is not a trusted definition). Remediation: state the tower with the EpiModel preorder's <. |  |
| `DynamicLimits.R40a` | forward 2 | different notion of '<': impl full_tower states Nat < on the dimensions (m.staticLimit.dim < m.toEpiModel.dim); S2 is the strict order of the EpiModel preorder, m.staticLimit < m.toEpiModel, i.e. the Preorder default lt (4 ≤ 5 ∧ ¬ 5 ≤ 4 on dims). Equivalent only via Nat order lemmas, not structurally; no admissible bridge (LT.lt is not a trusted definition). |  |
| `DynamicLimits.R40a` | backward | S1, S2 give the EpiModel preorder's strict order (dim ≤ dim ∧ ¬ reverse ≤); full_tower needs Nat < on the dims (Nat.le (d+1) d'), obtainable only via Nat order lemmas (e.g. Nat.lt_of_le_of_ne / lt_iff_le_not_ge), not structurally; no admissible bridge (LT.lt is not a trusted definition). |  |
| `DynamicLimits.r0EdgeSwapTendstoMfsh` | forward 1 | impl DynamicEBCM.R0_edgeSwap_tendsto_mfsh is a limit in ℚ (η : ℚ → ∞, with ℚ's order topology). S1 is the limit of the real-valued edge-swapping R₀ as a real η → ∞, towards the cast of the MFSH value. The rational limit does not give the real one structurally: that needs continuity of the cast and density or monotonicity arguments (library lemmas), so impl and S1 are about different functions. |  |
| `DynamicLimits.r0EdgeSwapTendstoMfsh` | backward | S1 is a limit of a function ℝ → ℝ; impl is a limit of a function ℚ → ℚ in ℚ's topology. Restricting the real limit to rational η and pulling it back along the embedding ℚ → ℝ needs Tendsto.comp with the embedding's properties (library lemmas), not structural reasoning. |  |
| `GaloisPair.header.GFLossy` | forward 2 | S2 ((G ∘ F) e has dimension 4 for every record) holds by rfl, since poissonLift sets dim := 4. impl GF_ne_id (∃ e, G(F e) ≠ e) does not state it, so a checker could only prove S2 without h (vacuous). The value 4 appears only in impl's proof (the witness ⟨10, 1⟩), not in its statement. Remediation: add GaloisPair.unit_dim to impl. |  |
| `GaloisPair.table.R14` | forward 2 | S2 (G ∘ F gives every record the same dimension) holds by rfl, since both sides reduce to 4. impl GF_ne_id (∃ e, G(F e) ≠ e) does not state it, so a checker could only prove S2 without h (vacuous). |  |
| `GaloisPair.table.R14` | backward | impl is the closed existential ∃ e, G(F e) ≠ e. S1 (G ∘ F ≠ id) gives a witness only by classical logic (not_forall), which is not structural. S2 says the dimensions of all G(F e) agree but gives no value, so with S2 alone the witness's inequality is a closed kernel computation (4 ≠ 10) that ignores the shadows, and a backward checker would be vacuous. |  |
| `GaloisPair.R14a` | forward 2 | S2 ((G ∘ F) e has dimension 4 for every record) holds by rfl, since poissonLift sets dim := 4. impl GF_ne_id (∃ e, G(F e) ≠ e) does not state it, so a checker could only prove S2 without h (vacuous). Remediation: add GaloisPair.unit_dim to impl. |  |
| `GaloisPair.notGaloisConnectionCoarseGrainPoissonLift` | forward 2 | impl states only ¬ GaloisConnection coarseGrain poissonLift. The witness inequality F⟨10, 1⟩ ≤ ⟨3, 1⟩ (i.e. 3 ≤ 3 in ℕ) appears only in impl's proof. It is a closed fact that a checker could prove only without h (and Nat.le.refl is a core-library constructor, not structural), so S2 does not follow from impl's statement. |  |
| `GaloisPair.notGaloisConnectionCoarseGrainPoissonLift` | forward 3 | impl states only ¬ GaloisConnection coarseGrain poissonLift. S3 (¬ ⟨10, 1⟩ ≤ G⟨3, 1⟩, i.e. ¬ 10 ≤ 4) appears only in impl's proof. The negation of a Galois connection does not identify which pair fails, so S3 does not follow from impl's statement. |  |
| `GaloisPair.notGaloisConnectionPoissonLiftCoarseGrain` | forward 2 | impl states only ¬ GaloisConnection poissonLift coarseGrain. The witness inequality ⟨3, 1⟩ ≤ F⟨3, 1⟩ (i.e. 3 ≤ 3 in ℕ) appears only in impl's proof. It is a closed fact that a checker could prove only without h, so S2 does not follow from impl's statement. |  |
| `GaloisPair.notGaloisConnectionPoissonLiftCoarseGrain` | forward 3 | impl states only ¬ GaloisConnection poissonLift coarseGrain. S3 (¬ G⟨3, 1⟩ ≤ ⟨3, 1⟩, i.e. ¬ 4 ≤ 3) appears only in impl's proof, and the negation of a Galois connection does not identify the failing pair, so S3 does not follow. |  |
| `Hierarchy.header.pairGtEbcmGtMeanField` | forward 3 | S3 (levelDim .pairApproximation N = 12N) is the defining clause of levelDim and holds by rfl. impl (edgeBased_lt_pair ∧ meanField_lt_edgeBased) states only the two strict inequalities, not the dimension values, so a checker could only prove S3 without h (vacuous). |  |
| `Hierarchy.header.pairGtEbcmGtMeanField` | forward 4 | S4 (levelDim .edgeBased N = 4) is the defining clause of levelDim (rfl). impl states only the inequalities, so a checker could only prove S4 without h (vacuous). |  |
| `Hierarchy.header.pairGtEbcmGtMeanField` | forward 5 | S5 (levelDim .meanField N = 3) is the defining clause of levelDim (rfl). impl states only the inequalities, so a checker could only prove S5 without h (vacuous). |  |
| `Hierarchy.table.R27` | forward 1 | impl poisson_unique_exact_lift takes an explicit hypothesis 0 < κ (unused in its proof). Instantiating κ := ψ.mean needs 0 < ψ.mean, which only the data invariant PGFData.mean_pos provides, and a structural checker may not project a proof out of a record. So S1 does not follow structurally from h. Mathematically it follows from impl plus mean_pos; remediation: drop the redundant hypothesis, or state the theorem for records. |  |
| `Hierarchy.table.R28` | forward 1 | S1 ((poisson κ).mean = κ) holds by rfl. impl lift_space_parameterised is existential (∃ ψ, ψ.mean = κ ∧ …) and does not name the Poisson record, so a checker could only prove S1 without h (vacuous). |  |
| `Hierarchy.table.R28` | forward 2 | impl gives, for some record ψ of mean κ, edge R₀ = T·excessDegree ψ. S2 says the Poisson record's edge R₀ equals the node R₀ T·κ, i.e. T·(κ²/κ) = T·κ. impl's existential does not identify ψ as the Poisson record, and κ²/κ = κ needs field cancellation, not structural. The text attributes the iff to edge_lift_R0_eq_iff, which is not in impl. |  |
| `Hierarchy.table.R28` | forward 3 | S3 (edge R₀ = node R₀ at κ ⇒ excess = κ) is the forward direction of edge_lift_R0_eq_iff, which is not in this claim's impl list. impl lift_space_parameterised (∃ ψ with mean κ and edge R₀ = T·excess) does not state it; it needs cancellation of T > 0. |  |
| `Hierarchy.table.R28` | forward 4 | S4 (excess = κ ⇒ edge R₀ = node R₀ at κ) is the reverse direction of edge_lift_R0_eq_iff, which is not in impl. It holds by rewriting with the hypothesis in the definitions (T·excess = T·κ), so a checker could only prove it without h (vacuous). |  |
| `Hierarchy.R25` | forward 2 | impl (ebcm_to_meanfield_exact_iff_poisson) is only ∀ κ hκ, (PGFData.poisson κ hκ).excessDegree = (PGFData.poisson κ hκ).mean, the Poisson ⇒ exact direction (a restatement of EpiCategory Result 1). Despite its name there is no converse and no biconditional. S2 (exact ⇒ Poisson over PGFData: ∀ ψ, ψ.excessDegree = ψ.mean → ψ = PGFData.poisson ψ.mean ψ.mean_pos) quantifies over arbitrary ψ, while impl speaks only of Poisson records. S2 is true within the two-moment record (ψ.secondFactorial / ψ.mean = ψ.mean ⇒ ψ.secondFactorial = ψ.mean²), but impl does not state it. Any proof would need field arithmetic and PGFData extensionality and would ignore h (vacuous). The 'iff' of the text is only half implemented. |  |
| `Hierarchy.R25` | forward 3 | impl states only the Poisson ⇒ exact direction for PGFData.poisson records. S3 (exact ⇒ Poisson over genuine degree distributions p : ℕ → ℝ: excess degree = mean ⇒ p k = e^{-mean} mean^k / k!) is a converse over a different domain that impl never mentions. S3 is also mathematically FALSE under the static reading of 'exact' as excess degree = mean. Counterexample: p0 = 1/3, p1 = 1/2, p3 = 1/6 (mean 1, ψ''(1) = 1, excess degree 1 = mean, not Poisson). So no correct impl can meet it. This is not a shadow misreading: the shadow reads 'exact' as the condition that Result 27 calls 'the exactness condition' and keeps the text's unrestricted 'iff Poisson'. Under a dynamical reading (EBCM trajectories reduce to mean-field SIR), which the vocabulary cannot express, the converse would plausibly hold. |  |
| `Hierarchy.R27` | forward 1 | impl poisson_unique_exact_lift takes an explicit hypothesis 0 < κ (unused in its proof). Instantiating κ := ψ.mean needs 0 < ψ.mean, which only the data invariant PGFData.mean_pos provides, and a structural checker may not project a proof out of a record. So S1 does not follow structurally from h. Mathematically it follows from impl plus mean_pos. |  |
| `Hierarchy.R27` | forward 2 | impl concludes only variance = κ. S2 (the record equals PGFData.poisson ψ.mean) needs ψ''(1) = ψ'(1)² from variance = mean (ring arithmetic) and record extensionality over PGFData, a structure with proof fields, whose eliminator a structural checker may not use. The text cites PGFData.dispersionIndex_eq_one_iff for this step, which is not in impl. |  |
| `Hierarchy.R27` | forward 3 | impl is about two-moment records. It says nothing about the real PGF ψ(u) = (1 + u²)/2 or its derivatives (S3: ψ''(1)/ψ'(1) = 1). |  |
| `Hierarchy.R27` | forward 4 | impl says nothing about the real PGF ψ(u) = (1 + u²)/2 (S4: ψ'(1) = 1). |  |
| `Hierarchy.R27` | forward 5 | impl says nothing about the real PGF ψ(u) = (1 + u²)/2 being non-Poisson (S5: ψ ≠ exp(λ(u − 1)) for every λ). The text's caveat is not formalised in impl. |  |
| `Hierarchy.R28` | forward 1 | S1 ((poisson κ).mean = κ) holds by rfl. impl lift_space_parameterised is existential and does not name the Poisson record, so a checker could only prove S1 without h (vacuous). |  |
| `Hierarchy.R28` | forward 2 | S2 (the Poisson record's edge R₀ is T·ψ''(1)/ψ'(1)) holds by unfolding edgeModel (rfl). impl's existential does not name the Poisson record, so a checker could only prove S2 without h (vacuous). |  |
| `Hierarchy.R28` | forward 3 | impl gives the existence of a record whose edge R₀ is T·excess. It does not give S3 (some p, ψ with edge R₀ ≠ node R₀ at ψ'(1)), which needs a non-Poisson record and the arithmetic T·e ≠ T·κ. |  |
| `Hierarchy.R28` | forward 4 | S4 ((nodeModel p κ).R0 = T·κ) is the definition of nodeModel (rfl). impl does not state it, so a checker could only prove it without h (vacuous). |  |
| `Hierarchy.R28` | forward 5 | S5 (equal R₀ ⇒ ψ''(1)/ψ'(1) = κ) is the forward direction of edge_lift_R0_eq_iff, which is not in this claim's impl list. impl (an existential about the Poisson record) does not state it, and it needs cancellation of T > 0. |  |
| `Hierarchy.R28` | forward 6 | S6 (ψ''(1)/ψ'(1) = κ ⇒ equal R₀) is the reverse direction of edge_lift_R0_eq_iff (not in impl). It holds by rewriting with the hypothesis in the definitions, so a checker could only prove it without h (vacuous). |  |
| `Hierarchy.pairLtFull` | forward 2 | S2 (levelDim .pairApproximation N = 12N) is the defining clause of levelDim (rfl). impl pair_lt_full states only 12N < 3^N for N ≥ 4, so a checker could only prove S2 without h (vacuous). |  |
| `Hierarchy.pairLtFull` | forward 3 | S3 (levelDim .fullStochastic N = 3^N) is the defining clause of levelDim (rfl). impl states only the inequality, so a checker could only prove S3 without h (vacuous). |  |
| `Hierarchy.fullLtPairThree` | forward 2 | S2 (levelDim .fullStochastic 3 = 27) holds by rfl (3³ evaluates to 27). impl full_lt_pair_three states only the inequality, so a checker could only prove S2 without h (vacuous). |  |
| `Hierarchy.fullLtPairThree` | forward 3 | S3 (levelDim .pairApproximation 3 = 36) holds by rfl (12·3 evaluates to 36). impl states only the inequality, so a checker could only prove S3 without h (vacuous). |  |
| `InvariantRegion.header.faceConditions` | forward 1 | impl invariant_region_boundary_conditions has no θ = 0 face conjunct. Its first conjunct is -(β φ_I) ≤ 0 (θ non-increasing), the opposite sign of S1's 0 ≤ -β φ_I. S1 needs φ_I = 0 from φ_I ≤ θ = 0 and 0 ≤ φ_I (order antisymmetry plus the region invariant hφ_I), which impl does not state. |  |
| `InvariantRegion.header.faceConditions` | forward 2 | impl gives -(β·φ_I) ≤ 0. S2 is 0 ≤ -(-β·φ_I). Going from one to the other needs neg_mul (-β·φ_I = -(β·φ_I), not definitional in ℚ because Rat.mul normalises by gcd) and neg_nonneg, which are library lemmas. |  |
| `InvariantRegion.header.faceConditions` | forward 3 | impl's φ_I-face conjunct is the placeholder (0:ℚ) = 0 (its docstring: 'In the Lean statement this conjunct is the placeholder'). It says nothing about the φ_I component correctQ of the vector field at φ_I = 0 (S3). |  |
| `InvariantRegion.header.faceConditions` | forward 5 | impl's fourth conjunct is the I-face drift 0 ≤ β·φ_I·ψ'_θ (dI/dt at I = 0). S5 is the R-face condition 0 ≤ γ(1 − ψ(θ) − R) at R = 0 (dR/dt), a different face and a different component. impl says nothing about dR/dt. |  |
| `InvariantRegion.header.faceConditions` | backward | impl holds at every point of EBCMRegion without the face equations: its first conjunct -(β φ_I) ≤ 0 and its fourth 0 ≤ β φ_I ψ'_θ for an arbitrary ψ'_θ ≥ 0. The shadows state the conditions only on the faces (θ = 1, φ_R = 0, …) and under Hyp (φ_I ≤ θ, S + R ≤ 1), and the I-face drift with a free ψ'_θ appears in none of them. So impl does not follow from the shadow set: it is a statement about a different set of points. |  |
| `InvariantRegion.pgfEvalOne` | forward 2 | impl states only ψ.eval 1 = 1. S2 requires ψ.eval 1 = Σᵢ ψ.coeffs i (the total probability mass). Obtaining it from impl needs 1 = Σᵢ pᵢ, which is the PolyPGF field ψ.sum_one, a data invariant that a structural proof may not extract. ψ.eval 1 unfolds to Σᵢ pᵢ·1^i, which is not definitionally Σᵢ pᵢ (that needs one_pow and mul_one). impl never mentions Σᵢ pᵢ. |  |
| `InvariantRegion.R113` | backward | impl is stronger than the text. pgf_nonneg_on_unit_interval proves 0 ≤ ψ(x) for every x ≥ 0, with no x ≤ 1 hypothesis. S1 (the text, x ∈ [0, 1]) covers only x ≤ 1, so impl's instances with x > 1 cannot be derived from S1. |  |
| `InvariantRegion.R116a` | forward 1 | impl states -(β·φ_I) ≤ 0, i.e. Neg.neg (p.β * φ_I). S1 renders the text's −β φ_I as (-β)·φ_I, i.e. (-p.β) * φI ≤ 0. The two terms are equal only by the ring lemma neg_mul. They are not definitionally equal over ℚ (Rat.mul normalises by gcd, and rfl fails), and there is no trusted definition of dθ/dt that a bridge could identify. The difference is in formulation only, but it cannot be closed structurally. |  |
| `InvariantRegion.R116a` | backward | S1 gives (-β)·φ_I ≤ 0, while impl needs -(β·φ_I) ≤ 0. These are equal only by neg_mul, not definitionally over ℚ, and there is no trusted dθ/dt definition to bridge. The difference is in formulation only. |  |
| `InvariantRegion.R117a` | forward 1 | impl phi_I_dot_zero_at_boundary is stated for the incorrect form (β·0/θ)(ψ'_θ/ψ'_1) − (β+γ)·0 over free rationals, as the text itself says ('The Lean statement uses the incorrect form'). S1 is about the correct field correctQ = β·φ_I·ψ″(θ)/ψ′(1) − (β+γ)·φ_I at φ_I = 0, a different expression (no 1/θ, different grouping), so S1 does not follow from h. The correct form is InvariantRegion.phiIDotCorrectZeroAtBoundary. |  |
| `InvariantRegion.R117a` | backward | impl's left-hand side is the incorrect form (β·0/θ)(ψ'_θ/ψ'_1) − (β+γ)·0 for free θ, ψ'_θ, ψ'_1; S1 is about the correct field correctQ. The two expressions are different, so S1 does not give impl structurally. |  |
| `InvariantRegion.phiIDotFactors.a` | forward 1 | impl phi_I_dot_factors has the extra hypothesis 0 < ψ'_1, i.e. ψ′(1) > 0. S1 quantifies over every PolyPGF, including those with ψ′(1) = 0 (all mass at degree 0), for which impl says nothing. Even when ψ′(1) > 0, a proof of 0 < pgfDeriv ψ 1 needs library lemmas, and a case split on ψ′(1) = 0 needs by_cases. Neither is structural. S1 still holds in the degenerate case under Lean's x/0 = 0, but not from impl. |  |
| `InvariantRegion.phiIDotFactors.a` | backward | impl asserts one explicit factorisation, with factor β·ψ'_θ/(θ·ψ'_1) - (β+γ), for arbitrary rationals ψ'_θ and ψ'_1 > 0 and every φ_I (no φ_I ≥ 0 hypothesis). S1 only asserts that some f exists with dφ_I/dt = φ_I·f(θ), for the PGF-derived ψ′(θ)/ψ′(1) and φ_I ≥ 0. Neither the explicit factor, nor the free-scalar instances, nor the instances with φ_I < 0 can be derived from S1. |  |
| `InvariantRegion.R119a` | backward | free-scalar abstraction. impl R_dot_nonneg is stated for a free rational I (0 ≤ I → 0 ≤ γ·I). S1 speaks only of I = 1 - ψ(θ) - R. Every rational I has that form (take R := 1 - ψ(θ) - I), but only by the ring identity 1 - a - (1 - a - I) = I, which is not definitional over ℚ. So impl's instances are not structurally derivable from S1, although the two statements are logically equivalent. |  |
| `InvariantRegion.R120` | backward | SHADOW?: impl SIR_conservation is the identity S + (1 - S - R) + R = 1 for arbitrary rationals S and R. S1 restricts S to ψ(θ) for a PolyPGF ψ. Every rational S equals ψ(θ) for ψ(x) = x and θ = S, but only up to ring normalisation (ψ.eval θ = 0·θ⁰ + 1·θ¹), not definitionally, so impl is not structurally derivable from S1. The text '**Result 120.** S + I + R = 1 holds as an *algebraic identity* because the EBCM defines I := 1 − S − R' states an identity in S and R that follows from the definition of I alone and never restricts S to ψ(θ). impl's free-S form therefore looks like the intended reading, and S1's specialisation S = ψ(θ) looks narrower than the text. | yes |
| `InvariantRegion.R120b` | forward 1 | impl explicit_seed_initial_conservation is the ring identity (1 - ρ) + ρ + 0 = 1 over ℚ. It mentions no PGF, θ(0) = 1 or ψ(1), and does not state S(0) = (1 - ρ)·ψ(1) = 1 - ρ. S1 needs ψ(1) = 1, which is the separate theorem pgf_eval_one or the PolyPGF data invariant sum_one. Neither is usable structurally, and impl cannot supply it. |  |
| `InvariantRegion.R120b` | forward 2 | impl gives (1 - ρ) + ρ + 0 = 1, with S(0) already replaced by the literal 1 - ρ. S2 requires (1 - ρ)·ψ(1) + ρ + 0 = 1 for every PolyPGF ψ. That needs (1 - ρ)·ψ(1) = 1 - ρ, i.e. ψ(1) = 1 and mul_one. impl omits this PGF step, which the text cites ('Since every PGF satisfies ψ(1)=1'). |  |
| `InvariantRegion.R120b` | forward 3 | impl does not state the observable I(0) = 1 - S(0) - R(0) = ρ. S3 requires 1 - (1 - ρ)·ψ(1) - 0 = ρ, which needs ψ(1) = 1 plus ring algebra (sub_sub_cancel, sub_zero). It cannot be derived from (1 - ρ) + ρ + 0 = 1 by structural steps. |  |
| `InvariantRegion.R120b.guard` | forward 1 | impl missing_seed_factor_overcounts states only 1 + ρ + 0 ≠ 1 for ρ ≠ 0. S1 (ψ(1) + ρ + 0 − 1 = ρ for every PGF ψ) needs ψ.eval 1 = 1 (pgf_eval_one, which uses the data field ψ.sum_one) and ring arithmetic. impl does not mention a PGF and gives no equation. |  |
| `InvariantRegion.missingSeedFactorOvercounts` | forward 1 | impl states only ρ ≠ 0 → 1 + ρ + 0 ≠ 1. It does not state that the total ψ(1) + ρ + 0 equals 1 + ρ (the text's 'the total is `1+ρ`'). An inequality cannot yield that equation, and ψ(1) = 1 is not available structurally. |  |
| `InvariantRegion.missingSeedFactorOvercounts` | forward 2 | impl replaces S(0) = ψ(1) by the literal 1 and gives 1 + ρ + 0 ≠ 1. S2 requires ψ(1) + ρ + 0 ≠ 1 for every PolyPGF ψ. That needs the rewrite ψ(1) = 1, which is the separate theorem pgf_eval_one or the data invariant sum_one, not usable structurally. |  |
| `InvariantRegion.R121` | backward | free-scalar abstraction. impl I_nonneg_iff_SR_le_one holds for arbitrary rationals S and R. S1 and S2 cover only S = ψ(θ). Every rational S is ψ(θ) for ψ(x) = x and θ = S, but only up to ring normalisation (ψ.eval θ = 0·θ⁰ + 1·θ¹), not definitionally, so impl is not structurally derivable from the shadows. |  |
| `InvariantRegion.R122a` | forward 1 | impl I_dot_nonneg_at_zero_boundary is only the sign statement 0 ≤ β·φ_I·ψ'_θ for free rationals φ_I and ψ'_θ. It does not identify the population-level drift. S1 requires IDot = -(ψ′(θ)·(-β·φ_I)) - γ(1 - ψ(θ) - R) = β·φ_I·ψ′(θ) whenever 1 - ψ(θ) - R = 0. impl states no such equation, and the equation itself needs ring algebra. |  |
| `InvariantRegion.R122a` | forward 2 | impl gives 0 ≤ β·φ_I·ψ′(θ) at ψ'_θ := ψ′(θ). S2 requires 0 ≤ IDot on {1 - ψ(θ) - R = 0}. impl has no I = 0 hypothesis and no dI/dt. Transferring the sign needs IDot = β·φ_I·ψ′(θ) at I = 0, which holds only by ring algebra (rewriting the face equation leaves -(ψ′(θ)·(-β·φ_I)) - γ·0, and then neg_mul, mul_comm and sub_zero are needed). That is not structural. |  |
| `InvariantRegion.R122a` | backward | free-scalar abstraction. impl is the bare product inequality 0 ≤ β·φ_I·ψ'_θ for arbitrary rationals φ_I ≥ 0 and ψ'_θ ≥ 0. S1 and S2 concern the drift IDot with ψ′(θ) of a PolyPGF on the face I = 0. Neither the instances at arbitrary ψ'_θ nor the bare-product form (which differs from IDot by ring algebra) can be derived. |  |
| `InvariantRegion.iDotGeneral.a` | forward 1 | impl I_dot_general is the reflexivity β·φ_I·ψ'_θ - γ·I = β·φ_I·ψ'_θ - γ·I, proved by rfl. It asserts nothing about dI/dt and is a tautological implementation. S1 requires the chain-rule drift IDot = -(ψ′(θ)·(-β·φ_I)) - γ(1 - ψ(θ) - R) to equal β·φ_I·ψ′(θ) - γ·(1 - ψ(θ) - R). impl does not state that, and it holds only by ring algebra (neg_mul, neg_neg, mul_comm). A proof of S1 could not use h. |  |
| `InvariantRegion.iDotGeneral.b` | forward 1 | SHADOW?: impl's first part, I_dot_at_zero, is β·φ_I·ψ'_θ - γ·0 = β·φ_I·ψ'_θ for free rationals: the γ I term of the alternative form dI/dt = β φ_I ψ′(θ) − γ I vanishes at I = 0. S1 instead uses the chain-rule drift IDot. After rewriting the face equation 1 - ψ(θ) - R = 0, S1 becomes -(ψ′(θ)·(-β·φ_I)) - γ·0 = β·φ_I·ψ′(θ), which differs from impl's left side -(a·(-b·c)) against b·c·a by ring algebra, so it is not structural. The text 'When I = 0 the γ I term vanishes, leaving the nonneg inward term' continues 'Alternative formulation: dI/dt = β φ_I ψ′(θ) − γ I' (iDotGeneral.a) and refers to that formula's γ I term. S1 also builds in the chain-rule identity of iDotGeneral.a. Read with dI/dt := β φ_I ψ′(θ) − γ I, S1 would follow structurally from impl (rewrite I = 0, then I_dot_at_zero). | yes |
| `InvariantRegion.iDotGeneral.b` | forward 2 | SHADOW?: impl's second part gives 0 ≤ β·φ_I·ψ'_θ under φ_I ≥ 0 and ψ'_θ ≥ 0. S2 requires 0 ≤ IDot, the chain-rule drift, on {1 - ψ(θ) - R = 0}. After rewriting the face equation this is 0 ≤ -(ψ′(θ)·(-β·φ_I)) - γ·0, which needs ring algebra to meet impl. As for S1, the text ('When I = 0 the γ I term vanishes, leaving the nonneg inward term') refers to the alternative form β φ_I ψ′(θ) − γ I. Under that reading S2 would follow structurally: rewrite I = 0, then I_dot_at_zero, then I_dot_nonneg_at_zero_boundary. | yes |
| `InvariantRegion.iDotGeneral.b` | backward | free-scalar abstraction. Both impl parts are stated for arbitrary rationals φ_I and ψ'_θ in bare form: β·φ_I·ψ'_θ - γ·0 = β·φ_I·ψ'_θ, and 0 ≤ φ_I → 0 ≤ ψ'_θ → 0 ≤ β·φ_I·ψ'_θ. S1 and S2 concern only IDot with ψ′(θ) of a PolyPGF. Neither the instances at arbitrary ψ'_θ nor the bare forms can be derived from the shadows. |  |
| `InvariantRegion.iDotAtZero` | forward 1 | impl I_dot_at_zero is β·φ_I·ψ'_θ - γ·0 = β·φ_I·ψ'_θ for free rationals. It is the text's alternative form of dI/dt with I replaced by the literal 0, and it has no I = 0 hypothesis on a state. S1 requires the chain-rule drift IDot = -(ψ′(θ)·(-β·φ_I)) - γ(1 - ψ(θ) - R) to equal β·φ_I·ψ′(θ) on 1 - ψ(θ) - R = 0. After rewriting the face equation, the two left sides differ by ring algebra (-(a·(-b·c)) against b·c·a), which is not structural. If 'the I-derivative' were read as the alternative form β φ_I ψ′(θ) − γ I, S1 would follow structurally. |  |
| `InvariantRegion.iDotAtZero` | forward 2 | impl has no sign statement: I_dot_at_zero is an equation only, and 'nonneg' is not part of it (the registry impl_note says the same). S2 requires 0 ≤ IDot on {I = 0} given φ_I ≥ 0 and ψ′(θ) ≥ 0. |  |
| `InvariantRegion.iDotAtZero` | backward | free-scalar abstraction. impl is stated for arbitrary rationals φ_I and ψ'_θ, in the bare form β·φ_I·ψ'_θ - γ·0 = β·φ_I·ψ'_θ. S1 and S2 concern IDot with ψ′(θ) of a PolyPGF. Neither impl's instances at arbitrary ψ'_θ nor its form can be derived from the shadows. |  |
| `InvariantRegion.R123a` | forward 1 | impl's first conjunct is -(β·φ_I) ≤ 0; S1 is -β·φ_I ≤ 0 on the θ = 1 face. -β·φ_I and -(β·φ_I) are equal only by neg_mul, which is not definitional in ℚ (Rat.mul normalises by gcd), so S1 does not follow structurally from h, though the content is the same. |  |
| `InvariantRegion.R123a` | forward 2 | impl's φ_I-face conjunct is the placeholder (0:ℚ) = 0 (its docstring says the computation is phi_I_dot_zero_at_boundary). It says nothing about the φ_I component correctQ of the vector field at φ_I = 0 (S2). |  |
| `InvariantRegion.R123a` | forward 4 | impl's fourth conjunct is the I-face drift 0 ≤ β·φ_I·ψ'_θ. S4 is the R-face condition 0 ≤ γ(1 − ψ(θ) − R) at R = 0 (dR/dt), a different component; impl says nothing about dR/dt. |  |
| `InvariantRegion.R123a` | forward 5 | impl has no θ = 0 face conjunct. Its first conjunct -(β φ_I) ≤ 0 has the opposite sign of S5's 0 ≤ -β φ_I, and S5 needs φ_I = 0 from φ_I ≤ θ = 0 together with the region invariant 0 ≤ φ_I (order antisymmetry), which impl does not state. |  |
| `InvariantRegion.R123a` | forward 6 | S6 (at some region point with θ = 0 the θ-drift -β φ_I is negative: 'the θ = 0 face also needs φ_I ≤ θ, which EBCMRegion omits') is the text's caveat. impl states only sign conditions that hold at every point and does not exhibit such a point. |  |
| `InvariantRegion.R123a` | backward | impl's conjuncts hold at every point of EBCMRegion: -(β φ_I) ≤ 0 everywhere (S1 only on θ = 1, and with -β·φ_I in place of -(β·φ_I)), and the I-face drift 0 ≤ β φ_I ψ'_θ for an arbitrary ψ'_θ ≥ 0, which no shadow states. So impl does not follow from the shadow set. |  |
| `InvariantRegion.R123b` | forward 1 | impl theta_dot_nonpos needs the hypothesis 0 ≤ φ_I. For S1's region point that is available only as the EBCMRegion field x.hφ_I, a data invariant that structural proofs may not extract. impl also concludes -(β·φ_I) ≤ 0, not S1's (-β)·φ_I ≤ 0, and the two are equal only by neg_mul, not definitionally over ℚ. |  |
| `InvariantRegion.R123b` | forward 2 | impl is a pointwise sign statement about the rational -(β·φ_I). It contains no trajectory, derivative or monotonicity. S2 requires AntitoneOn θ (Set.Ici 0) for a real θ with θ′ = -β·φ_I and φ_I ≥ 0, which is a mean-value-theorem argument that impl does not state. |  |
| `InvariantRegion.R123b` | forward 3 | impl has no trajectory statement. S3 requires that θ(0) = 1 implies θ(t) ≤ 1 for t ≥ 0 along real solutions of θ′ = -β·φ_I (the text's 'θ starts at 1 and can only decrease'). impl does not formalise this (the registry impl_note says the same). |  |
| `InvariantRegion.R123b` | backward | S1 at the region point (θ, φ_I, φ_R, R) = (0, φ_I, 0, 0) gives (-β)·φ_I ≤ 0, but impl requires -(β·φ_I) ≤ 0. The two are equal only by the ring lemma neg_mul, not definitionally over ℚ, and there is no trusted dθ/dt definition to bridge. The difference is in formulation only. |  |
| `InvariantRegion.R123d` | backward | free-scalar abstraction. impl is stated for arbitrary rationals θ, ψ'_θ and ψ'_1, with φ_I replaced by the literal 0. S1 gives the identity only at region points (θ ∈ [0, 1]), with ψ'_θ = ψ′(θ) and ψ'_1 = ψ′(1) of a PolyPGF. impl's instances with ψ'_1 = -1 or θ = 2 cannot be derived. |  |
| `InvariantRegion.R123e` | forward 1 | impl phi_R_dot_nonneg takes 0 ≤ φ_I as an explicit hypothesis and does not mention φ_R or the face. For S1's region point x, 0 ≤ x.φ_I is available only as the EBCMRegion field x.hφ_I, a data invariant that structural proofs may not extract. So 0 ≤ γ·x.φ_I cannot be obtained from impl structurally. |  |
| `InvariantRegion.R123f` | forward 1 | impl I_dot_nonneg_at_zero_boundary is only 0 ≤ β·φ_I·ψ'_θ for free rationals. It does not state dI/dt = β·φ_I·ψ′(θ) on the I face. S1 requires IDot = -(ψ′(θ)·(-β·φ_I)) - γ(1 - ψ(θ) - R) to equal β·φ_I·ψ′(θ) there. impl states no such equation, and the equation needs ring algebra. |  |
| `InvariantRegion.R123f` | forward 2 | impl needs the extra hypotheses 0 ≤ ψ'_θ and 0 ≤ φ_I. S2 supplies no ψ′(θ) ≥ 0 (true on [0,1] from nonneg coefficients, but provable only with library lemmas). 0 ≤ x.φ_I is available only as the data invariant x.hφ_I. On top of that, transferring 0 ≤ β·φ_I·ψ′(θ) to 0 ≤ IDot needs ring algebra. None of this is structural. |  |
| `InvariantRegion.R123f` | forward 3 | impl says nothing about the equivalence I = 0 ↔ S + R = 1: it has no statement involving ψ.eval, R or I. S3 requires 1 - ψ(θ) - R = 0 → ψ(θ) + R = 1 at region points. |  |
| `InvariantRegion.R123f` | forward 4 | impl says nothing about the equivalence I = 0 ↔ S + R = 1: it has no statement involving ψ.eval, R or I. S4 requires ψ(θ) + R = 1 → 1 - ψ(θ) - R = 0 at region points. |  |
| `InvariantRegion.R123f` | backward | free-scalar abstraction. impl holds for arbitrary rationals φ_I ≥ 0 and ψ'_θ ≥ 0, in the bare form 0 ≤ β·φ_I·ψ'_θ. S1–S4 concern IDot on the I face of region points, with ψ′(θ) of a PolyPGF, and the identity I = 0 ↔ S + R = 1. Neither the instances at arbitrary ψ'_θ nor the bare form can be derived from them. |  |
| `InvariantRegion.header.thetaFace.a` | forward 1 | impl theta_lower_boundary_absorbing concludes only -(β·φ_I) = 0. The text's intermediate step φ_I = 0 is not stated. Recovering φ_I = 0 from -(β·φ_I) = 0 needs β ≠ 0 plus mul_eq_zero and neg_eq_zero, which is not structural. impl also requires 0 ≤ φ_I, which for S1's region point is only the data invariant x.hφ_I. |  |
| `InvariantRegion.header.thetaFace.a` | forward 2 | impl needs 0 ≤ φ_I. For S2's region point that is only the EBCMRegion field x.hφ_I, a data invariant that structural proofs may not extract. (Its other hypothesis, φ_I ≤ 0, is obtainable from φ_I ≤ θ and θ = 0 by rewriting.) impl also concludes -(β·φ_I) = 0, not S2's (-β)·φ_I = 0, and the two are equal only by neg_mul, not definitionally over ℚ. |  |
| `InvariantRegion.header.thetaFace.a` | backward | At the region point (0, φ_I, 0, 0), S1 gives φ_I = 0, which turns impl's goal -(β·φ_I) = 0 into -(β·0) = 0. That is not definitional for a variable β: it needs mul_zero and neg_zero. S2 gives (-β)·φ_I = 0, not -(β·φ_I) = 0, and closing that gap needs neg_mul. impl is not structurally derivable from S1 and S2. |  |
| `InvariantRegion.thetaLowerBoundaryAbsorbing` | forward 1 | impl needs 0 ≤ φ_I. For S1's region point that is only the EBCMRegion field x.hφ_I, a data invariant that structural proofs may not extract. impl also concludes -(β·φ_I) = 0 rather than (-β)·φ_I = 0, equal only by neg_mul and not definitionally over ℚ. (impl's hypothesis φ_I ≤ 0, i.e. φ_I ≤ θ with θ := 0 substituted, is obtainable by rewriting.) |  |
| `InvariantRegion.thetaLowerBoundaryAbsorbing` | backward | S1 at the region point (0, φ_I, 0, 0) gives (-β)·φ_I = 0, but impl concludes -(β·φ_I) = 0. The two are equal only by neg_mul, not definitionally over ℚ, and there is no trusted dθ/dt definition to bridge. The difference is in formulation only. |  |
| `InvariantRegion.phiIDotCorrectZeroAtBoundary` | forward 1 | impl states β·0·(ψ''_θ/ψ'_1) − (β+γ)·0 = 0 for free rationals. S1's correctQ p ψ θ 0 unfolds to ((β·0)·ψ″(θ))/ψ′(1) − (β+γ)·0, grouped (a·x)/y where impl has a·(x/y). The two agree only by mul_div_assoc, which is not definitional in ℚ, so S1 does not follow structurally from h. Same content. |  |
| `InvariantRegion.phiIDotCorrectZeroAtBoundary` | backward | impl quantifies over free rationals ψ''_θ, ψ'_1 and groups the term as β·0·(ψ''_θ/ψ'_1); S1 gives the value of ((β·0)·ψ″(θ))/ψ′(1) − (β+γ)·0 only for ψ″, ψ′ of polynomial PGFs. Free rationals are not of that form, and the grouping differs by mul_div_assoc, so impl does not follow structurally from S1. |  |
| `InvariantRegion.phiIDotCorrectFactors` | forward 1 | impl states β·φ_I·(ψ''_θ/ψ'_1) − (β+γ)·φ_I = φ_I·(β·ψ''_θ/ψ'_1 − (β+γ)). S1's left-hand side correctQ unfolds to ((β·φ_I)·ψ″(θ))/ψ′(1) − (β+γ)·φ_I, grouped (a·x)/y where impl has a·(x/y). They agree only by mul_div_assoc (not definitional in ℚ), so S1 does not follow structurally from h. The right-hand sides agree. |  |
| `InvariantRegion.phiIDotCorrectFactors` | forward 2 | impl is a rational factorisation identity. S2 (the real field θ ↦ correctR p ψ θ φ_I is continuous at θ = 0) is an analytic statement that impl does not make. |  |
| `InvariantRegion.phiIDotCorrectFactors` | forward 3 | impl says nothing about the 1/θ form. S3 (that form is not continuous at θ = 0 for some parameters) is not stated. |  |
| `InvariantRegion.phiIDotCorrectFactors` | backward | impl is stated for free rationals ψ''_θ, ψ'_1 with the grouping β·φ_I·(ψ''_θ/ψ'_1). S1 gives the factorisation only for ψ″, ψ′ of polynomial PGFs, and with the grouping ((β·φ_I)·ψ″)/ψ′. Free rationals are not of that form, and the groupings differ by mul_div_assoc (not structural). |  |
| `MarginalisationCharacterization.header.T2witness` | backward | impl is the constructive existential ∃ u : U4, M_witness (F4_Kirkwood u) ≠ F3_Kirkwood (M_witness u). S1 is ¬ ∀ w : U4, M_witness (F4_Kirkwood w) = F3_Kirkwood (M_witness w). The two are classically equivalent, but ¬∀ ⇒ ∃¬ needs Classical (not_forall / by_contra), which structural proofs forbid. The only other route is to re-prove the impl from scratch at the concrete witness (a ℚ disequality 6 ≠ 4 obtained by norm_num), which would not use S1. Audit limitation (classical logic), not a meaning gap. |  |
| `MarginalisationCharacterization.header.T1forces` | forward 2 | S2 (the T2 witness F3Kℝ has no global flow) is the trusted theorem MarginalisationDynamicalGap.no_flow_F3Kℝ. It is not in this claim's impl list; impl rhs_commute_of_traj_commute assumes global flows and says nothing about their existence at the witness. |  |
| `MarginalisationCharacterization.header.T1forces` | forward 3 | S3 (at the witness, local solutions from u₁ and M u₁ do not agree near t = 0) is about the local form rhs_commute_of_local_traj_commute applied at the T2 witness, which is not in this claim's impl list. impl (global flows) does not give it. |  |
| `MarginalisationCharacterization.header.T1forces` | backward | S1 is the contrapositive of impl. Recovering impl (∀ u, M(F₄ u) = F₃(M u) from trajectory commutation) from S1 gives only ¬¬(∀ u, …) and needs double-negation elimination (Classical.byContradiction), which structural proofs forbid. S2 and S3 are about the witness and do not help. Audit limitation (classical logic), not a meaning gap. |  |
| `MarginalisationCharacterization.header.interLevel` | forward 1 | impl kkr_necessary_not_sufficient is existential: some ψ with closureKappa ψ = 1 (the Poisson record appears only in its proof). S1 (every Poisson record has closureKappa = 1) is universal and does not follow from the existential. |  |
| `MarginalisationCharacterization.header.interLevel` | forward 2 | impl is existential over V₄, V₃, M, C₄; the T3b surrogate (MℝLin, C4ℝ) appears only in its proof. S2 (no C₃ makes MℝLin intertwine C4ℝ with C₃) is about the named surrogate and does not follow from impl's statement. |  |
| `MarginalisationCharacterization.header.interLevel` | backward | With the witnesses ψ = poisson 1 (S1), U4ℝ, U3ℝ, MℝLin and C4ℝ (S2), impl still needs C4ℝ.IsKirkwoodForm. That is the trusted lemma C4ℝ_isKirkwoodForm, which a checker may not cite; no shadow states it, and a direct proof needs real arithmetic (1·1 ≠ 0). So impl is stronger than the shadow set by its IsKirkwoodForm conjunct. |  |
| `MarginalisationCharacterization.header.kkrNotSufficient` | backward | impl also asserts that its order-4 closure C₄ is IsKirkwoodForm (non-additive). S2 asserts only the existence of some non-equivariant C₄ and gives no non-additivity, so impl does not follow: impl is stronger than the text ('an order-4 closure that is not equivariant') by that conjunct. |  |
| `MarginalisationCharacterization.table.T3a` | forward 1 | impl linear_closure_equivariant is tautological: its hypothesis h_intertwine is its conclusion Equivariant M L₄ L₃ written out. It says nothing about ker M, so it does not give S1 (an equivariant F₃ forces (ker M).map L₄ ≤ ker M). The row's criterion is linear_admits_equivariant_iff, which is not in this claim's impl list. |  |
| `MarginalisationCharacterization.table.T3a` | forward 2 | impl (tautological intertwining) needs an intertwining linear L₃ as input. It does not give S2 (L₄(ker M) ⊆ ker M produces some equivariant F₃), which needs a construction of F₃ on the range of M (linear_admits_equivariant_iff, not in impl). |  |
| `MarginalisationCharacterization.table.T3a` | backward | impl (∀ M L₄ L₃, (∀ u, M(L₄ u) = L₃(M u)) → Equivariant M L₄ L₃) is its own hypothesis unfolded, provable as fun _ _ _ h => h without any shadow, so a backward checker could only be vacuous. |  |
| `MarginalisationCharacterization.table.T3c.b` | backward | impl also asserts that its order-4 closure is IsKirkwoodForm. S2 gives only some non-equivariant order-4 closure, so impl's non-additivity conjunct does not follow; impl is stronger than the table row ('pairs with a non-equivariant order-4 closure'). |  |
| `MarginalisationCharacterization.isLinearAdmitsEquivariant` | forward 1 | impl isLinear_admits_equivariant concludes ∃ F₃, Equivariant M C₄.C F₃ ∨ True, which holds through the disjunct True (the text: 'Vacuous; kept for compatibility'). It carries no information, so it cannot give S1 (some IsLinear closure admits no equivariant F₃). |  |
| `MarginalisationCharacterization.isLinearAdmitsEquivariant` | forward 2 | S2 (an equivariant F₃ for a linear L₄ forces L₄(ker M) ⊆ ker M) is the forward direction of linear_admits_equivariant_iff, which the text names as the correct criterion and which is not in this claim's impl list. The vacuous impl does not give it. |  |
| `MarginalisationCharacterization.isLinearAdmitsEquivariant` | forward 3 | S3 (L₄(ker M) ⊆ ker M gives an equivariant F₃) is the reverse direction of linear_admits_equivariant_iff (not in impl). The vacuous impl (… ∨ True) does not give it. |  |
| `MarginalisationCharacterization.isLinearAdmitsEquivariant` | backward | impl (∃ F₃, … ∨ True) is provable outright as ⟨0, Or.inr trivial⟩ without any shadow, so a backward checker could only be vacuous. The shadows state the content that the text says impl lacks. |  |
| `MarginalisationCharacterization.c4RealIsKirkwoodForm` | forward 3 | impl states only C4ℝ.IsKirkwoodForm, i.e. ∃ u v, C4ℝ.C (u + v) ≠ C4ℝ.C u + C4ℝ.C v (non-additivity somewhere). It says nothing about which component of C4ℝ.C is bilinear, and non-additivity does not imply an a·b component. S3 (∃ i, ∀ w, C4ℝ.C w i = w a * w b) holds only by unfolding C4ℝ / F4Kℝ (⟨Idx4.a, fun _ => rfl⟩), a proof that does not use h. |  |
| `MarginalisationCharacterization.c4RealIsKirkwoodForm` | forward 4 | impl is the existential ∃ u v, C4ℝ.C (u + v) ≠ C4ℝ.C u + C4ℝ.C v. It does not name the witnesses (1,0), (0,1) (they appear only in the proof) and states no value of C4ℝ.C. S4 (C4ℝ.C (pt 1 0 + pt 0 1) = pt 1 1) is a real-number computation ((1+0)*(0+1) = 1, 0+1 = 1) that follows neither from h nor structurally (no kernel computation on ℝ, no norm_num). |  |
| `MarginalisationCharacterization.c4RealIsKirkwoodForm` | forward 5 | impl is the existential ∃ u v, C4ℝ.C (u + v) ≠ C4ℝ.C u + C4ℝ.C v. It does not name the witnesses and states no value of C4ℝ.C. S5 (C4ℝ.C (pt 1 0) + C4ℝ.C (pt 0 1) = pt 0 1) is a real-number computation (1*0 + 0*1 = 0, 0 + 1 = 1) that follows neither from h nor structurally. |  |
| `MarginalisationCharacterization.c4RealIsKirkwoodForm` | forward 6 | impl is the existential ∃ u v, C4ℝ.C (u + v) ≠ C4ℝ.C u + C4ℝ.C v (C4ℝ.C is definitionally F4Kℝ). It does not name the witnesses and states no value of F4Kℝ. S6 (F4Kℝ (pt 1 0 + pt 0 1) = pt 1 1) is a real-number computation that follows neither from h nor structurally. |  |
| `MarginalisationCharacterization.c4RealIsKirkwoodForm` | forward 7 | impl is the existential ∃ u v, C4ℝ.C (u + v) ≠ C4ℝ.C u + C4ℝ.C v (C4ℝ.C is definitionally F4Kℝ). It does not name the witnesses and states no value of F4Kℝ. S7 (F4Kℝ (pt 1 0) + F4Kℝ (pt 0 1) = pt 0 1) is a real-number computation that follows neither from h nor structurally. |  |
| `MarginalisationCharacterization.kirkwoodFormNotEquivariant` | forward 1 | impl is ∃ V₄ V₃ (ℝ-modules in Type) M C₄, IsKirkwoodForm C₄ ∧ ∀ C₃, ¬ Equivariant M C₄.C C₃.C. It does NOT state Function.Surjective M, which the text requires ('a surjective linear marginalisation M') and S1 contains. The impl's witness MℝLin happens to be surjective, but that is visible only in the proof term, and the ∃ gives an arbitrary M. Proving surjectivity of MℝLin would need real arithmetic (preimage fun _ => y c, 0 with y c + 0 = y c), not a consequence of h. |  |
| `MarginalisationCharacterization.kkrNecessaryNotSufficient.notSufficient` | forward 2 | impl is EXISTENTIAL over the order-4 system: ∃ ψ V₄ V₃ M C₄, closureKappa ψ = 1 ∧ IsKirkwoodForm C₄ ∧ ∀ C₃, ¬ Equivariant M C₄.C C₃.C. It says nothing about the named system (MℝLin, F4Kℝ): that the witness is U4ℝ / U3ℝ / MℝLin / C4ℝ is visible only in the proof term, and eliminating the ∃ gives arbitrary V₄ V₃ M C₄. S2 (¬ ∃ F₃ : U3ℝ → U3ℝ, Equivariant MℝLin F4Kℝ F₃) is about that specific system and would need the real-arithmetic fibre argument at u₁, u₂ (norm_num), which h does not supply. |  |
| `MarginalisationCharacterization.kkrNecessaryNotSufficient.notSufficient` | forward 3 | impl is EXISTENTIAL over the order-4 system: ∃ ψ V₄ V₃ M C₄, closureKappa ψ = 1 ∧ IsKirkwoodForm C₄ ∧ ∀ C₃, ¬ Equivariant M C₄.C C₃.C. It says nothing about the named system (MℝLin, C4ℝ): the witness is visible only in the proof term. S3 (¬ ∃ F₃ : U3ℝ → U3ℝ, Equivariant MℝLin C4ℝ.C F₃) is about that specific system and would need the real-arithmetic fibre argument at u₁, u₂ (norm_num), which h does not supply. |  |
| `MarginalisationCharacterization.kkrNecessaryNotSufficient.notSufficient` | backward | impl additionally asserts C₄.IsKirkwoodForm for its order-4 witness. The shadows give ψ with closureKappa ψ = 1 (S1) and the non-equivariance of the concrete system MℝLin / C4ℝ (S2, S3), so every impl component except IsKirkwoodForm can be assembled from them. The text fragment does not say that the order-4 closure is Kirkwood-form, no shadow states it, and IsKirkwoodForm C4ℝ (the trusted lemma C4ℝ_isKirkwoodForm, proved by norm_num over ℝ) is not derivable structurally. So the impl is strictly stronger than the shadow set. |  |
| `MarginalisationCharacterization.linearAdmitsEquivariantIff` | forward 3 | impl is the iff criterion. S3 (for some linear M, some linear L₄ admits no equivariant F₃: 'linear closures are not equivariant for every linear M') needs a concrete M and L₄ with L₄(ker M) ⊄ ker M. impl exhibits no such pair, and building one needs real arithmetic (e.g. 1 ≠ 0), which is not structural. |  |
| `MarginalisationCharacterization.existsKirkwoodFormEquivariant` | forward 1 | impl exists_kirkwoodForm_equivariant is existential over M, C₄, C₃; the field x ↦ x² appears only in its proof term. S1 (the closure x ↦ x² is IsKirkwoodForm) is about the named field and does not follow from the existential. |  |
| `MarginalisationCharacterization.existsKirkwoodFormEquivariant` | forward 2 | S2 (with M = id, x ↦ x² intertwines itself) holds by rfl (Equivariant id F F unfolds to F u = F u). impl's existential does not name the field, so a checker could only prove S2 without h (vacuous). |  |
| `MarginalisationDynamicalGap.header.overview` | forward 1 | impl trajectoryGap_rate_two_at_witness is about global flows φ₄, φ₃; its hypothesis IsFlow F3Kℝ φ₃ is unsatisfiable (no_flow_F3Kℝ), so it holds vacuously and gives nothing. S1 (algebraicGap MℝLinCLM F4Kℝ F3Kℝ u₁ = 2) is algebraicGap_at_witness, which is not in this claim's impl list. |  |
| `MarginalisationDynamicalGap.header.overview` | forward 2 | S2 is T5 in local form (localGap_hasDerivAt_zero), for general M, F₄, F₃. impl is a statement about global flows at the witness only, and its hypothesis is unsatisfiable, so it does not give S2. |  |
| `MarginalisationDynamicalGap.header.overview` | forward 3 | S3 (for local solutions at the witness the gap has derivative 2) is witness_localGap_hasDerivAt, which the text cites and which is not in impl. impl needs global flows (IsFlow), which local solutions are not; F3Kℝ has no global flow, so impl is vacuous. |  |
| `MarginalisationDynamicalGap.header.overview` | forward 4 | S4 (the gap's norm is at least t for small t > 0) is witness_localGap_ge (not in impl). impl, a vacuous derivative statement for global flows, does not give it. |  |
| `MarginalisationDynamicalGap.header.overview` | backward | To derive impl from S3 one turns the global flows into LocalSol curves (φ₄ u₁, φ₃ (M u₁)), which needs a radius δ with 0 < δ in ℝ (e.g. zero_lt_one). A real inequality is not structural. Otherwise S3's conclusion is impl's up to unfolding trajectoryGap and cst. The implementation's hypothesis is in any case refuted by no_flow_F3Kℝ (hypothesis_refuted). |  |
| `MarginalisationDynamicalGap.header.T6.a` | forward 1 | impl refinement_failure_exists is existential over F4_kirk, F3_kirk, F3_exact and u₀; the named witnesses F4Kℝ, u₁ and the constant 6 appear only in its proof. S1 (MℝLinCLM (F4Kℝ u₁) equals the constant field 6 at u₁) is about the named data, so it does not follow from impl's statement. (It would also need the real arithmetic 1·3 + 3 = 6.) |  |
| `MarginalisationDynamicalGap.header.T6.a` | backward | S1 gives only the agreement at u₁. impl also needs IsKirkwoodForm for the order-4 and order-3 closures (the trusted lemmas C4ℝ_isKirkwoodForm and F3Kℝ_isKirkwoodForm, which a checker may not cite) and the disequality F3Kℝ(M u₁) ≠ 6 (real arithmetic 4 ≠ 6). It is stated with MℝLin rather than MℝLinCLM. impl is stronger than this fragment of the text. |  |
| `MarginalisationDynamicalGap.kirkwoodNotEquivariantViaT4` | forward 2 | impl kirkwood_not_equivariant_via_T4 states only the conclusion ∀ C₃ : ClosureFamily U3ℝ, ¬ Equivariant MℝLin F4Kℝ C₃.C. The fibre-collapse hypothesis at the witness (the points u₁ = (1, 3), u₂ = (4, 0) with MℝLin u₁ = MℝLin u₂ and MℝLin (F4Kℝ u₁) ≠ MℝLin (F4Kℝ u₂)) appears only in its proof, not in its statement. S2 asks for ∃ w₁ w₂ with that property. From impl one gets only ¬¬∃ (if no fibre collapse existed, C₃ v := M (F4Kℝ (section of M at v)) would be equivariant), and removing the double negation needs Classical. Proving S2 directly needs real arithmetic (1 + 3 = 4 + 0, 1·3 + 3 ≠ 4·0 + 0) and would not use h (vacuous). The clause 'the (2,1) ℝ-witness satisfies the fibre-collapse hypothesis' describes how the proof applies T4, but it is also an assertion about the witness that the statement does not carry, so S2 is a fair reading of the text. |  |
| `MarginalisationDynamicalGap.trajectoryGapNormGeHalfEpsT` | forward 1 | impl gives the explicit threshold form ∃ T > 0, ∀ t, 0 < t → t ≤ T → ε·t/2 ≤ ‖trajectoryGap M φ₄ φ₃ u t‖ (same hypotheses: IsFlow for both, 0 < ε, ε ≤ ‖algebraicGap M F₄ F₃ u‖). S1 states the same bound as ∀ᶠ t in 𝓝[>] 0. The two are mathematically equivalent, but turning (0, T] into a set of the filter nhdsWithin 0 (Set.Ioi 0) needs the library lemmas Iio_mem_nhds / mem_nhdsWithin_Ioi_iff_exists_Ioc_subset (nhds on ℝ is an infimum of principal filters and cannot be unfolded structurally). No trusted definition is involved, so no bridge can carry it either. Audit limitation, not a meaning gap. |  |
| `MarginalisationDynamicalGap.trajectoryGapNormGeHalfEpsT` | backward | S1 gives the bound ∀ᶠ t in 𝓝[>] 0. impl asks for an explicit ∃ T > 0, ∀ t, 0 < t → t ≤ T → …. Extracting T from the filter needs mem_nhdsWithin_Ioi_iff_exists_Ioc_subset (or Metric.eventually_nhds_iff) and halving the radius (real arithmetic), which is library content and not structural. The statements are mathematically equivalent. Audit limitation, not a meaning gap. |  |
| `MarginalisationDynamicalGap.f3RealIsKirkwoodForm` | forward 3 | impl F3Kℝ_isKirkwoodForm states only (ClosureFamily.mk F3Kℝ).IsKirkwoodForm, i.e. ∃ u v, F3Kℝ (u + v) ≠ F3Kℝ u + F3Kℝ v. The witness u = v = (c ↦ 1) appears only in its proof. S3 is the witness value F3Kℝ (oneC + oneC) c = 1, i.e. (1 + 1)²/4 = 1 in ℝ. impl does not state it, and proving it needs real arithmetic (norm_num), which is not structural and would not use h (vacuous). |  |
| `MarginalisationDynamicalGap.f3RealIsKirkwoodForm` | forward 4 | impl states only the existential non-additivity (∃ u v, F3Kℝ (u + v) ≠ F3Kℝ u + F3Kℝ v), not the witness values. S4 is F3Kℝ oneC c + F3Kℝ oneC c = 1/2, i.e. 1²/4 + 1²/4 = 1/2 in ℝ. impl does not state it, and proving it needs real arithmetic (norm_num), which is not structural and would not use h (vacuous). |  |
| `MarginalisationDynamicalGap.refinementFailureExists.b` | forward 1 | impl algebraicGap_at_witness is the gap of F4Kℝ against F3Kℝ at u₁ (= 2). S1 is the gap against the fitted constant field F3_exact (= 0), a different order-3 field. impl does not mention F3_exact, and the zero gap needs the real arithmetic 1·3 + 3 = 6. |  |
| `MarginalisationDynamicalGap.refinementFailureExists.b` | forward 2 | S2 (F3Kℝ (M u₁) = 4) is not stated by impl. Deriving it from impl's M(F4Kℝ u₁) − F3Kℝ(M u₁) = 2 needs M(F4Kℝ u₁) = 6 and the arithmetic 6 − x = 2 ⇒ x = 4 in ℝ, which are not structural. |  |
| `MarginalisationDynamicalGap.refinementFailureExists.b` | forward 3 | S3 (‖F3Kℝ(M u₁) − F3_exact(M u₁)‖ = 2) is about the sup norm on Idx3 → ℝ and the field F3_exact, neither of which impl mentions. Computing it needs norm lemmas (pi_norm, Real.norm_eq_abs) and real arithmetic. |  |
| `MarginalisationDynamicalGap.refinementFailureExists.b` | backward | impl (algebraicGap MℝLinCLM F4Kℝ F3Kℝ u₁ = 2) is not given by the shadows: S1 concerns F3_exact, S2 gives F3Kℝ(M u₁) = 4, and combining them with M(F4Kℝ u₁) = 6 needs real subtraction arithmetic (sub_eq_iff_eq_add etc.), which is not structural. |  |
| `MarginalisationDynamicalGap.normGeHalfEpsTOfHasDerivAt` | forward 1 | impl concludes ∃ T > 0, ∀ t, 0 < t → t ≤ T → ε t/2 ≤ ‖f t‖. S1 concludes ∀ᶠ t in 𝓝[>] 0, ε t/2 ≤ ‖f t‖. The two are equivalent, but turning the explicit interval (0, T] into membership in the filter 𝓝[>] 0 needs filter lemmas (mem_nhdsWithin, Ioc_mem_nhdsGT), which are not structural. |  |
| `MarginalisationDynamicalGap.normGeHalfEpsTOfHasDerivAt` | backward | S1 gives an eventually-statement in the filter 𝓝[>] 0; impl needs an explicit T > 0 with the bound on (0, T]. Extracting T from filter membership needs Metric.mem_nhdsWithin_iff-type lemmas (and a positive radius), which are not structural. |  |
| `MarginalisationDynamicalGap.localGapNormGeHalfEpsT` | forward 1 | impl concludes ∃ T > 0, ∀ t, 0 < t → t ≤ T → ε t/2 ≤ ‖M(ψ₄ t) − ψ₃ t‖. S1 concludes the same bound as ∀ᶠ t in 𝓝[>] 0. Converting the explicit interval into filter membership needs filter lemmas (mem_nhdsWithin, Ioc_mem_nhdsGT), which are not structural. The content is the same. |  |
| `MarginalisationDynamicalGap.localGapNormGeHalfEpsT` | backward | S1 gives an eventually-statement in 𝓝[>] 0; impl needs an explicit T > 0. Extracting T from filter membership needs Metric.mem_nhdsWithin_iff-type lemmas, which are not structural. |  |
| `MarginalisationDynamicalGap.algebraicGapWitness` | forward 2 | S2 (MℝLinCLM u₁ = 4) is the real arithmetic 1 + 3 = 4 at u₁. It is used inside impl's proof (the local fact hM), not stated by impl, and it is not structural. |  |
| `MarginalisationDynamicalGap.algebraicGapWitness` | forward 3 | S3 (a rate of 2 forces C₃(4) = 4) follows from impl's 6 − C₃(4) only by the real arithmetic 6 − x = 2 ⇒ x = 4 (sub_eq_iff_eq_add, funext on coordinates), which is not structural. |  |
| `MarginalisationDynamicalGap.algebraicGapWitness` | forward 4 | S4 (F3Kℝ(4) = 4, i.e. 4²/4 = 4 in ℝ) is not stated by impl and is real arithmetic, not structural. |  |
| `MarginalisationDynamicalGap.kirkwoodFormMatchesAtWitness` | forward 2 | impl states algebraicGap MℝLinCLM F4Kℝ C3match u₁ = 0, i.e. M(F4Kℝ u₁) − C3match(M u₁) = 0. S2 is the equation M(F4Kℝ u₁) = C3match(M u₁). Going from the zero difference to the equation needs sub_eq_zero (a library lemma), which is not structural. |  |
| `MarginalisationDynamicalGap.kirkwoodFormMatchesAtWitness` | forward 3 | S3 (some Kirkwood-form order-3 closure matches at u₁) needs the matching equation M(F4Kℝ u₁) = C.C(M u₁). impl gives only the zero algebraic gap, and the step from a zero difference to the equation needs sub_eq_zero, which is not structural. |  |
| `MarginalisationDynamicalGap.kirkwoodFormMatchesAtWitness` | backward | impl's second conjunct is algebraicGap … = 0. From S2's equation it needs x − x = 0 in Idx3 → ℝ (sub_self), which is a library lemma, not structural. The first conjunct is S1. |  |
| `MarginalisationDynamicalGap.witnessLocalSolutionsExist` | forward 1 | impl witness_local_solutions_exist is existential (∃ ψ₄ ψ₃ with IsLocalSolution on radius 1); the curves (exp(3(eᵗ − 1)), 3eᵗ) and 4/(1 − t) appear only in its proof. S1 says the named curve psi4w solves F4Kℝ for every t (a global IsSolution), which neither follows from the existential nor from a local solution on (−1, 1). |  |
| `MarginalisationDynamicalGap.witnessLocalSolutionsExist` | forward 2 | S2 (psi3w 0 = MℝLinCLM u₁, i.e. 4/(1 − 0) = 1 + 3) is about the named curve and is real arithmetic. impl's existential does not name the curve. |  |
| `MarginalisationDynamicalGap.witnessLocalSolutionsExist` | forward 3 | S3 (the named curve 4/(1 − t) solves F3Kℝ on (−1, 1)) is about a curve that impl's existential does not name, so it does not follow from impl's statement. |  |
| `MarginalisationDynamicalGap.witnessLocalSolutionsExist` | backward | With the witnesses psi4w and psi3w, impl needs IsLocalSolution … 1 …, whose first field is 0 < (1 : ℝ) (zero_lt_one, not structural). The order-3 part also needs \|t\| < 1 ⇒ −1 < t ∧ t < 1 (abs_lt), a library lemma, to use S3. Not structurally derivable. |  |
| `MarginalisationDynamicalGap.witnessLocalGapGe` | forward 2 | S2 (the trajectories differ on some (0, T]) follows from impl's t ≤ ‖M(ψ₄ t) − ψ₃ t‖ with t > 0 only through norm_pos_iff / sub_ne_zero and order reasoning (0 < t ≤ ‖x‖ ⇒ x ≠ 0), which are library lemmas, not structural. impl does not state the disequality. |  |
| `MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.b` | forward 2 | impl no_flow_F3Kℝ states only that F3Kℝ has no global flow. S2 (every solution of w′ = w²/4 from w(0) = 4 is 4/(1 − t) before t = 1) is a uniqueness statement for the scalar IVP; it appears in impl's docstring and proof idea but not in its statement. |  |
| `MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.b` | forward 3 | S3 (4/(1 − t) → ∞ as t → 1⁻) is a limit statement that impl does not make; impl's statement is only the non-existence of a global flow. |  |
| `MarginalisationDynamicalGap.noGlobalSolutionSqDivFour` | forward 2 | impl states only that no global solution exists. S2 (t ↦ 4/(1 − t) solves w′ = w²/4 for t < 1) is a derivative computation that impl does not state. |  |
| `MarginalisationDynamicalGap.noGlobalSolutionSqDivFour` | forward 3 | S3 (the solution from w(0) = 4 is 4/(1 − t) before t = 1: uniqueness for the IVP) is not stated by impl, whose conclusion is False under the global-solution hypotheses. |  |
| `MarginalisationDynamicalGap.noGlobalSolutionSqDivFour` | forward 4 | S4 (4/(1 − t) blows up as t → 1⁻) is a limit statement that impl does not make. |  |
| `MarginalisationDynamicalGap.noFlowF3Real` | forward 2 | S2 (F3Kℝ v at c is v(c)²/4) is the definition of F3Kℝ (it holds by rfl). impl no_flow_F3Kℝ does not state it, so a checker could only prove S2 without h (vacuous). |  |
| `MarginalisationFunctor.header.closedNeedNotCommute` | forward 1 | impl kirkwood_marginalisation_obstruction is ∃ u : U4, M_witness (F4_Kirkwood u) ≠ F3_Kirkwood (M_witness u), a statement about the ℚ-valued surrogate U4 = Idx4 → ℚ, U3 = Idx3 → ℚ, where M_witness is a plain function (not a continuous linear map) and F4_Kirkwood/F3_Kirkwood are not ClosedSystem fields over real normed spaces. S1 is ¬ ∀ (V₄ V₃ : Type) real normed spaces, M : V₄ →L[ℝ] V₃, C₄ C₃ : ClosedSystem, ⇑M ∘ C₄.F = C₃.F ∘ ⇑M. The ℚ surrogate is not an instance of that universal (U4, U3 carry no real normed-space structure), so the impl supplies no counterexample to it; refuting the universal needs a separate real-valued counterexample (e.g. M = 0, C₃.F constant 1) and library facts such as (0 : ℝ) ≠ 1, which the impl does not provide. |  |
| `MarginalisationFunctor.header.closedNeedNotCommute` | forward 2 | impl kirkwood_marginalisation_obstruction is an algebraic (right-hand-side) non-commutation ∃ u : U4, M_witness (F4_Kirkwood u) ≠ F3_Kirkwood (M_witness u) on the ℚ-valued surrogate; it has no flows at all. S2 is the trajectory-level non-commutation ¬ ∀ (V₄ V₃ : Type) real normed spaces, M : V₄ →L[ℝ] V₃, closed systems with flows φ₄ φ₃ (IsFlow), ∀ w t, M (φ₄ w t) = φ₃ (M w) t. The ℚ surrogate is not an instance (no real normed structure, no IsFlow), and the impl states nothing about trajectories, so S2 does not follow from it. |  |
| `MarginalisationFunctor.header.closedNeedNotCommute` | backward | impl is the constructive existential ∃ u : U4, M_witness (F4_Kirkwood u) ≠ F3_Kirkwood (M_witness u). The only shadow about the Kirkwood surrogate is S3 : ¬ (M_witness ∘ F4_Kirkwood = F3_Kirkwood ∘ M_witness); S1 and S2 concern real normed spaces and say nothing about U4/U3. S3 ⇒ impl is classically valid (funext plus ¬∀ ⇒ ∃¬), but ¬∀ ⇒ ∃¬ needs Classical (not_forall / by_contra), which structural proofs forbid. The only other route is to re-prove the impl from scratch with the concrete witness u = (1, 3), which would not use the shadows. Same situation as Obstructions.header.kirkwoodHierarchyInconsistent. |  |
| `MarginalisationFunctor.RM1` | forward 3 | impl pushforward_isSolution states only that the pushforward is a solution. It does not exhibit a system without uniqueness in which another solution of F₃ through M w exists (S3, the text's 'It is the solution only if solutions of F₃ are unique'). A witness needs a non-Lipschitz field and real analysis that impl does not provide. |  |
| `MarginalisationFunctor.RM4b` | forward 3 | impl rhs_commute_of_traj_commute is the general implication trajectory ⇒ infinitesimal commutation for continuous linear M between real normed spaces with flows. It says nothing about the Theorem T2 Kirkwood witness. S3 is ¬ (M_witness ∘ F4_Kirkwood = F3_Kirkwood ∘ M_witness) on the ℚ-valued surrogate U4/U3, which is not an instance of the impl's setting (no real normed structure, M_witness not continuous linear, no flows). The algebraic failure lives in MarginalisationObstruction.kirkwood_marginalisation_obstruction, which the registry lists only as supporting, not as impl, so S3 does not follow from the impl. |  |
| `MarginalisationFunctor.RM4b` | backward | impl rhs_commute_of_traj_commute is the direct implication (∀ u t, M (φ₄ u t) = φ₃ (M u) t) ⇒ ∀ u, M (F₄ u) = F₃ (M u). S1 and S2 state only its contrapositive, ¬ (⇑M ∘ F₄ = F₃ ∘ ⇑M) ⇒ ¬ ∀ w t, …, and S3 concerns only the ℚ surrogate. From trajectory commutation, S1 yields ¬¬ (⇑M ∘ F₄ = F₃ ∘ ⇑M). Recovering the equation itself needs double-negation elimination (Classical.byContradiction), which structural proofs forbid. The claim text states only the contrapositive, so this is a classical-vs-constructive gap: the impl is intuitionistically stronger than the text. |  |
| `MarginalisationFunctor.rhsCommuteOfLocalTrajCommute` | backward | impl allows three radii: local solutions on \|t\| < δ₄ and \|t\| < δ₃ and agreement on \|t\| < δ. S1 uses one δ for all three. To apply S1 one must shrink to δ' = min(δ, δ₄, δ₃) and transport the hypotheses (lt_min, lt_of_lt_of_le), which are order lemmas, not structural. Mathematically S1 implies impl. |  |
| `MessagePassingBridge.table.R62` | forward 1 | impl (chain_rule_bridge) is the rational identity psi_prime * (-beta * SI_over_N / psi_prime) = -beta * SI_over_N under psi_prime ≠ 0 and beta ≠ 0: three free numbers in ℚ, with no function ψ, no trajectory H₁(t), no [SI](t) and no derivative. S1 requires the analytic statement over ℝ that S(t) = ψ(H(t)) has HasDerivAt value -β·[SI](t) when H satisfies Eq. 18 (dH/dt = -β·[SI]/ψ'(H)). That is the chain rule HasDerivAt.comp plus the algebra, and the impl supplies only the algebra, over ℚ and with the extra hypothesis β ≠ 0. There is no structural derivation. |  |
| `MessagePassingBridge.table.R62` | backward | impl is a ℚ-valued algebraic identity for arbitrary psi_prime, SI_over_N, beta. S1 speaks only about real functions and HasDerivAt. Recovering the rational identity from S1 would need explicit differentiable witnesses (e.g. linear ψ, H), uniqueness of derivatives (HasDerivAt.unique) and injectivity of the cast ℚ → ℝ, all library content. The impl is about a different notion (free-scalar algebra, not derivatives). |  |
| `MessagePassingBridge.table.R63` | forward 1 | impl (markov_transmissibility) is the definitional identity ∀ p : SIRParams, p.transmissibility = p.β / (p.β + p.γ) (rfl). It never mentions ModelFamily or requiredAssumptions. S1 (markovTransmission ∈ ebcmODE.requiredAssumptions) is a fact about the assumption table that impl does not state. Any proof would ignore h (vacuous), and List.Mem constructors are library content. |  |
| `MessagePassingBridge.table.R63` | forward 2 | impl is only p.transmissibility = p.β / (p.β + p.γ) (rfl) and says nothing about assumptions. S2 (markovRecovery ∈ ebcmODE.requiredAssumptions) is not stated by impl. Any proof would ignore h (vacuous). |  |
| `MessagePassingBridge.table.R63` | forward 3 | impl is only p.transmissibility = p.β / (p.β + p.γ) (rfl). S3 (markovTransmission ∉ ebcmPDE.requiredAssumptions) is a non-membership fact about the assumption table that impl does not mention. A proof would need case analysis on List.Mem (library) and would ignore h. |  |
| `MessagePassingBridge.table.R63` | forward 4 | impl is only p.transmissibility = p.β / (p.β + p.γ) (rfl). S4 (markovRecovery ∉ ebcmPDE.requiredAssumptions) is not stated by impl. A proof would ignore h. |  |
| `MessagePassingBridge.table.R63` | forward 5 | impl is only p.transmissibility = p.β / (p.β + p.γ) (rfl). S5 (every ebcmPDE assumption is an ebcmODE assumption, i.e. the ODE is a specialisation of the PDE) is an inclusion of assumption lists that impl does not state. A proof would ignore h. |  |
| `MessagePassingBridge.table.R65` | forward 1 | S1 (massAction.effectiveDim = 2) is a clause of the lookup table ModelFamily.effectiveDim and holds by rfl. impl dim_tower_monotone states only the three inequalities, so a checker could only prove S1 without h (vacuous). |  |
| `MessagePassingBridge.table.R65` | forward 2 | S2 (pairwise.effectiveDim = 4) is a clause of the lookup table (rfl). impl states only the inequalities, so a checker could only prove S2 without h (vacuous). |  |
| `MessagePassingBridge.table.R65` | forward 3 | S3 (ebcmODE.effectiveDim = 5) is a clause of the lookup table (rfl). impl states only the inequalities, so a checker could only prove S3 without h (vacuous). |  |
| `MessagePassingBridge.table.R66` | forward 1 | impl (bridge_requires_edge_formulation) is the list-length inequality messagePassing.requiredAssumptions.length < pairwise.requiredAssumptions.length (1 < 4). It says nothing about [SI], the message H₁, ψ or derivatives. S1 requires that [SI], through Eq. 18, makes S = ψ(H₁) satisfy dS/dt = -β·[SI] (HasDerivAt over ℝ). That is a different notion and not implied. |  |
| `MessagePassingBridge.table.R66` | backward | impl is a closed count inequality between MP's and pairwise's assumption lists (1 < 4). S1 is an analytic statement about real functions and HasDerivAt and says nothing about requiredAssumptions. impl does not follow from S1, and a proof of the closed Nat.lt would need Nat.le constructors (library) independently of S1. |  |
| `MessagePassingBridge.table.R67` | forward 1 | impl (pairwise_needs_more_than_ebcm) is the count inequality ebcmODE.requiredAssumptions.length < pairwise.requiredAssumptions.length (3 < 4). It does not say which assumption is extra. S1 (poissonType ∈ pairwise.requiredAssumptions, 'Pairwise requires PT') is not implied by a count. |  |
| `MessagePassingBridge.table.R67` | forward 2 | impl compares only the list lengths of ebcmODE and pairwise and never mentions messagePassing. S2 (poissonType ∉ messagePassing.requiredAssumptions, 'MP ... do not') is not stated by impl. |  |
| `MessagePassingBridge.table.R67` | forward 3 | impl compares only the list lengths of ebcmODE and pairwise and never mentions ebcmPDE. S3 (poissonType ∉ ebcmPDE.requiredAssumptions) is not stated by impl. |  |
| `MessagePassingBridge.table.R67` | forward 4 | impl is a count inequality (3 < 4). S4 (poissonType ∉ ebcmODE.requiredAssumptions) is a non-membership fact that a count cannot imply: a shorter list may still contain poissonType. |  |
| `MessagePassingBridge.table.R67` | backward | impl is len ebcmODE < len pairwise (a count). The shadows are membership and non-membership facts about poissonType. poissonType ∈ pairwise ∧ poissonType ∉ ebcmODE does not imply len ebcmODE < len pairwise (e.g. [configModel, markovTransmission] vs [poissonType]). impl is a different notion and not derivable from S1…S4. |  |
| `MessagePassingBridge.table.R68` | forward 1 | impl full_equivalence_poisson is the reflexivity massAction.requiredAssumptions.length = massAction.requiredAssumptions.length (proved by rfl). It says nothing about the mass-action and EBCM trajectories, so it does not give S1 (after β = κβ̃, γ = β̃ + γ̃, the mass-action S(t) matches the network S(t)). |  |
| `MessagePassingBridge.table.R68` | forward 2 | impl is a reflexivity about list lengths. S2 (the mass-action I(t) is not the network prevalence) is a statement about solutions of two ODE systems, which impl does not mention. |  |
| `MessagePassingBridge.table.R68` | backward | impl (x = x) is provable by rfl without the shadows, so a backward checker could only be vacuous. impl carries none of the row's content (the row itself says the equivalence chain is informal). |  |
| `MessagePassingBridge.R64` | forward 2 | impl hierarchy_monotone_assumptions compares list lengths only. S2 (poissonType ∈ pairwise.requiredAssumptions) is a closed fact about the list contents that impl does not state. A checker could prove it only without h, and List.Mem constructors are core-library proofs, not structural. |  |
| `MessagePassingBridge.R64` | forward 3 | S3 (poissonType ∉ massAction.requiredAssumptions) is a closed fact about list contents. impl, a length comparison, does not state it. |  |
| `MessagePassingBridge.R64` | forward 4 | S4 (poissonDegree ∈ massAction.requiredAssumptions) is a closed fact about list contents. impl, a length comparison, does not state it. |  |
| `MessagePassingBridge.R64` | forward 5 | S5 (the pairwise list is not contained in the mass-action list: 'The lists are not nested') is not stated by impl, which compares lengths only; the text itself says so ('a comparison of list lengths only'). |  |
| `MessagePassingBridge.R60` | forward 2 | impl (hazard_density_identity) states only f_mp = f_ebcm. S2 (f_mp = (ζ·ξ_τ)·ξ_q, the text's first link f(a) = τ(a)·ξ_q(a) = ζ(a)·ξ_τ(a)·ξ_q(a)) is not a consequence of that equation. It holds only by unfolding the definition EpiProcess.f_mp := ζ * ξ_τ * ξ_q, so any proof ignores h (vacuous). The substantive step τ(a) = ζ(a)·ξ_τ(a) has no counterpart in impl (τ is not a field of EpiProcess); it is built into the definition. |  |
| `MessagePassingBridge.R62d` | forward 1 | impl (chain_rule_bridge) has the extra hypothesis hbeta : beta ≠ 0. S1 (∀ β dψ dΘ SI : ℚ, dψ ≠ 0 → dΘ = -β·SI/dψ → dψ·dΘ = -β·SI) has none, and the text 'dS/dt = ψ'(Θ)·dΘ/dt = -β·[SI]' needs none. After rewriting dΘ, h closes S1 only when β ≠ 0. The case β = 0 is not covered by impl, and a case split on β = 0 (Classical/Decidable) is not structural. |  |
| `MessagePassingBridge.R62d` | forward 2 | impl is a ℚ-algebraic identity for three free numbers psi_prime, SI_over_N, beta, with no function ψ or Θ and no derivative. S2 is the analytic chain rule over ℝ (HasDerivAt ψ dψ (Θ t) → HasDerivAt Θ dΘ t → HasDerivAt (ψ ∘ Θ) (dψ·dΘ) t), i.e. Mathlib's HasDerivAt.comp. impl does not contain it: the text's 'via the chain rule' step is absent from the implementation, which assumes dS/dt = ψ'·dΘ/dt by writing it into the expression. |  |
| `MessagePassingBridge.R63d` | forward 2 | impl (markov_transmissibility) is the definitional identity p.transmissibility = p.β / (p.β + p.γ) (rfl). 'Markovian' is connected to no distribution or integral. S2 (∫₀^∞ β·e^{-βa}·e^{-γa} da = transmissibility, cast to ℝ) is the substantive content of 'is the Markovian transmissibility'. It needs an improper-integral computation (integral_exp_neg_Ioi etc., library content) that impl does not provide. |  |
| `MessagePassingBridge.markovEbcmDim` | forward 1 | impl (markov_ebcm_dim) is the closed numeral tautology (3 : ℕ) + 2 = 5 (rfl). No model or variable occurs in it. S1 (ModelFamily.ebcmODE.effectiveDim = 3 + 2) is about the Markovian EBCM and holds only by the definition of effectiveDim (ebcmODE ↦ 5), which impl does not mention. h.symm would typecheck only by kernel evaluation of effectiveDim, so impl would contribute nothing but the kernel-decidable fact 3 + 2 = 5 (audit limitation 1). This is a tautological impl, so it is not used. |  |
| `MessagePassingBridge.pdeToOdeReduction` | forward 1 | impl (pde_to_ode_reduction) is the tautology ∀ n : ℕ, 3 ≤ n → n ≤ n (le_refl) and has no content. It mentions neither ModelFamily nor effectiveDim. S1 (ebcmODE.effectiveDim < ebcmPDE.effectiveDim, the Markovian specialisation strictly reduces the dimension) is not implied. Any proof would ignore h (vacuous). |  |
| `MessagePassingBridge.pdeToOdeReduction` | backward | impl ∀ n : ℕ, 3 ≤ n → n ≤ n is reflexivity of ≤ on a variable n. Its only proof is Nat.le.refl / le_refl (library constructor/lemma, not in the structural whitelist). It is unrelated to S1 (a strict inequality between two fixed effectiveDim values), which cannot supply n ≤ n for an arbitrary n. impl is a different, contentless statement. |  |
| `MessagePassingBridge.R65` | forward 1 | impl (dim_tower_monotone) is massAction ≤ pairwise ∧ pairwise ≤ ebcmODE ∧ ebcmODE ≤ ebcmPDE (effectiveDim) and omits the MP level of the tower. S1 (ebcmPDE.effectiveDim ≤ messagePassing.effectiveDim) is not stated. |  |
| `MessagePassingBridge.R65` | forward 3 | impl compares massAction with pairwise and pairwise with ebcmODE. It has no direct comparison of massAction with ebcmODE. S3 (massAction.effectiveDim ≤ ebcmODE.effectiveDim) follows only by transitivity (Nat.le_trans), a library lemma. impl's chain goes through a pairwise level that the text's tower does not contain. |  |
| `MessagePassingBridge.R65` | backward | impl's first two conjuncts, massAction ≤ pairwise (2 ≤ 4) and pairwise ≤ ebcmODE (4 ≤ 5), involve the pairwise level. The tower of S1…S3 (MP ≥ EBCM(PDE) ≥ ODE ≥ SIR) omits it. Neither conjunct is, up to definitional unfolding, any of S1…S3, so impl states a different chain from the shadows. |  |
| `MessagePassingBridge.R66a` | forward 1 | impl (bridge_requires_edge_formulation) is the list-length inequality messagePassing.requiredAssumptions.length < pairwise.requiredAssumptions.length (1 < 4). It says nothing about [SI] or a bridge. S1 requires that [SI], defined from the message H₁ through Eq. 18, makes S = ψ(H₁) satisfy dS/dt = -β·[SI] (HasDerivAt over ℝ). That is a different notion and not implied. |  |
| `MessagePassingBridge.R66a` | backward | impl is a closed count inequality between MP's and pairwise's assumption lists (1 < 4). S1 is an analytic statement about real functions and derivatives and says nothing about requiredAssumptions. impl does not follow from S1, and a proof of the closed Nat.lt would need Nat.le constructors (library) independently of S1. |  |
| `MessagePassingBridge.R67` | forward 1 | impl (pairwise_needs_more_than_ebcm) is the count inequality len ebcmODE.requiredAssumptions < len pairwise.requiredAssumptions (3 < 4). It does not say which assumption is extra. S1 (poissonType ∈ pairwise.requiredAssumptions, 'Pairwise requires PT') is not implied by a count. |  |
| `MessagePassingBridge.R67` | forward 2 | impl mentions only ebcmODE and pairwise. S2 (poissonType ∉ messagePassing.requiredAssumptions, 'MP ... do not') is about MP, which impl does not mention. |  |
| `MessagePassingBridge.R67` | forward 3 | impl mentions only ebcmODE and pairwise. S3 (poissonType ∉ ebcmPDE.requiredAssumptions) is about the EBCM PDE, which impl does not mention. |  |
| `MessagePassingBridge.R67` | forward 4 | impl is a count inequality (3 < 4). S4 (poissonType ∉ ebcmODE.requiredAssumptions) is a non-membership fact that a count cannot imply: a shorter list may still contain poissonType. |  |
| `MessagePassingBridge.R68a` | forward 1 | impl full_equivalence_poisson is the reflexivity massAction.requiredAssumptions.length = massAction.requiredAssumptions.length. It says nothing about the mass-action or EBCM trajectories, so it does not give S1 (mass action with β = κβ̃, γ = β̃ + γ̃ matches S(t), with I corresponding to φ_I). |  |
| `MessagePassingBridge.R68a` | forward 2 | impl is a reflexivity about list lengths. S2 (the mass-action I(t) is not the network prevalence) is about solutions of the two ODE systems, which impl does not mention. |  |
| `MessagePassingBridge.R68a` | backward | impl (x = x) is provable by rfl without any shadow, so a backward checker could only be vacuous. impl states none of Result 68's content. |  |
| `MethodOfStages.R87` | forward 1 | free-scalar abstraction with an extra hypothesis: impl erlang_one_is_exponential is ∀ γ : ℝ, 0 < γ → ↑(1:ℕ)·γ = γ, with the hypothesis 0 < γ (_hg, unused in its ring proof). S1 is stated over ErlangParams p with p.n = 1; after rewriting p.n = 1, instantiating the impl at p.gamma needs a proof of 0 < p.gamma, available only as the structure field p.gamma_pos (a data invariant, not structural). A faithful impl would drop the unused hypothesis or be stated over ErlangParams. |  |
| `MethodOfStages.R87` | forward 2 | different notion: impl is the real-arithmetic identity ↑(1:ℕ)·γ = γ and mentions no density. S2 requires the Gamma(1, γ) density gammaPDFReal 1 γ x to equal the Exponential(γ) density γe^{-γx} (x ≥ 0, else 0) pointwise; this needs unfolding gammaPDFReal (γ^1/Γ(1)·x^0·e^{-γx}), Real.Gamma_one and rpow lemmas, none of which the impl states. The heading 'Erlang(1,γ) is Exponential(γ)' is not formalised by the impl. |  |
| `MethodOfStages.R87` | forward 3 | different notion: impl is the real-arithmetic identity ↑(1:ℕ)·γ = γ and mentions no measure. S3 requires gammaMeasure 1 γ = volume.withDensity (ofReal ∘ Exponential(γ) density), an equality of distributions on ℝ; the impl states nothing about gammaMeasure, so 'Erlang(1,γ) is Exponential(γ)' as distributions is not proved. |  |
| `MethodOfStages.R88` | forward 1 | different notion: impl erlang_mean_preserved is the arithmetic identity n/(nγ) = 1/γ for free reals (n > 0, γ > 0) and mentions no distribution. S1 requires the mean of the Erlang(n, nγ) law, ∫ x d(gammaMeasure n (nγ)), to equal n/(nγ); the impl never computes an expectation, so 'E[Erlang(n,nγ)] = n/(nγ)' is not stated. |  |
| `MethodOfStages.R88` | forward 2 | free-scalar abstraction: impl is ∀ n γ, 0 < n → 0 < γ → n/(nγ) = 1/γ. S2 is stated over ErlangParams p; instantiating the impl at p.n, p.gamma needs proofs of 0 < p.n and 0 < p.gamma, available only as the structure fields p.n_pos / p.gamma_pos (data invariants, not structural). A faithful impl would be stated over ErlangParams. |  |
| `MethodOfStages.R89a` | forward 1 | different notion: impl erlang_variance is the arithmetic identity n/(nγ)² = 1/(nγ²) for free reals (n > 0, γ > 0) and mentions no distribution. S1 requires the variance of the Erlang(n, nγ) law, ProbabilityTheory.variance id (gammaMeasure n (nγ)), to equal n/(nγ)²; the impl never computes a variance, so 'Var[Erlang(n,nγ)] = n/(nγ)²' is not stated. |  |
| `MethodOfStages.R89a` | forward 2 | free-scalar abstraction: impl is ∀ n γ, 0 < n → 0 < γ → n/(nγ)² = 1/(nγ²). S2 is stated over ErlangParams p; instantiating the impl at p.n, p.gamma needs proofs of 0 < p.n and 0 < p.gamma, available only as the structure fields p.n_pos / p.gamma_pos (data invariants, not structural). A faithful impl would be stated over ErlangParams. |  |
| `MethodOfStages.R90a` | forward 1 | different notion: impl erlang_cv_squared is the arithmetic identity (1/(nγ²))/(1/γ)² = 1/n for free reals (n > 0, γ > 0) and mentions no distribution. S1 requires Var/Mean² of the Erlang(n, nγ) law (variance and mean of gammaMeasure n (nγ)) to equal (1/(nγ²))/(1/γ)²; the impl computes neither the variance nor the mean, so 'CV² = Var/Mean² = (1/(nγ²))/(1/γ)²' is not stated. |  |
| `MethodOfStages.R90a` | forward 2 | free-scalar abstraction: impl is ∀ n γ, 0 < n → 0 < γ → (1/(nγ²))/(1/γ)² = 1/n. S2 is stated over ErlangParams p; instantiating the impl at p.n, p.gamma needs proofs of 0 < p.n and 0 < p.gamma, available only as the structure fields p.n_pos / p.gamma_pos (data invariants, not structural). A faithful impl would be stated over ErlangParams. |  |
| `MethodOfStages.R91a` | forward 2 | different notion: impl erlang_variance_limit is the limit of the explicit real expression 1/(nγ²) → 0 and mentions no distribution. S2 requires the variance of the Erlang(n, nγ) law, ProbabilityTheory.variance id (gammaMeasure n (nγ)), to tend to 0; linking it to 1/(nγ²) needs the Gamma variance formula, which no impl states (erlang_variance is also only the arithmetic n/(nγ)² = 1/(nγ²)). So 'Variance vanishes' for the distribution is not proved. |  |
| `MethodOfStages.R92` | forward 1 | tautological impl: ode_dimension is ∀ l : List ℕ, l.sum + 2 = (l.map id).sum + 2, which holds because List.map id = id and mentions no model, state space or dimension. S1 requires the dimension of the staged ODE state space (Module.finrank ℝ of the functions on one coordinate per sub-stage plus θ and R) to be Σᵢ nᵢ + 2; that needs Module.finrank_fintype_fun_eq_card and a cardinality count of Σ i, Fin nᵢ ⊕ (Unit ⊕ Unit), none of which the impl states. The count Σᵢ nᵢ + 2 is never tied to any system. |  |
| `MethodOfStages.R93c` | forward 1 | different notion: impl transmissibility_n_one is the arithmetic identity 1 − γ/(β+γ) = β/(β+γ) for β, γ > 0 and defines no transmissibility. S1 requires T₁, the transmission probability ∫ (1 − e^{−βτ}) dErlang(1, γ)(τ), to equal 1 − γ/(β+γ); that needs the exponential integral ∫ e^{−βτ} γe^{−γτ} dτ = γ/(β+γ), which the impl does not state. 'T₁ = 1 − γ/(β+γ)' is not proved. |  |
| `MethodOfStages.R94b` | forward 1 | free-scalar abstraction: impl transmissibility_ratio is ∀ n β γ, 0 < n → 0 < β → 0 < γ → nγ/(β+nγ) = 1/(1+β/(nγ)). S1 is stated over ErlangParams p and β > 0; instantiating the impl at p.n, β, p.gamma needs proofs of 0 < p.n and 0 < p.gamma, available only as the structure fields p.n_pos / p.gamma_pos (data invariants, not structural). A faithful impl would be stated over ErlangParams. |  |
| `MethodOfStages.erlangTransmissibilityOneLtTwo` | forward 2 | impl erlangTransmissibility_one_lt_two states only T₁ < T₂. S2 is the closed form of the difference, T₂ − T₁ = β²γ/((β+γ)(β+2γ)²); it appears only in impl's docstring (as the reason), not in its statement, so impl is weaker than S2. |  |
| `Obstructions.header.networkNotObstruction` | forward 2 | impl (clustering_ebcm_exists ∧ degreeCorr_ebcm_exists ∧ multiplex_ebcm_exists) states only existence, via ebcmExists, which is definitionally 'uniform seeding'. It says nothing about the dimension cost (S2: every non-standard class needs more variables than the standard EBCM in extensionDim). That is a closed ℕ comparison of table entries, which impl does not state and which is not structurally provable (Nat.le constructors are core-library proofs). |  |
| `Obstructions.table.R18` | forward 3 | S3 (the triangle EBCM is an ODE system: extensionDim .clusteredTriangles .markovian ≠ 0) is a closed fact about the table (13 ≠ 0). impl (clustering_breaks_standard ∧ clustering_ebcm_exists) does not state it, so a checker could only prove S3 without h (vacuous). |  |
| `Obstructions.table.R19` | forward 2 | impl (nonmarkov_requires_pde ∧ nonmarkov_ebcm_exists) never mentions standardEbcmValid. ¬ standardEbcmValid .configurationModel .generalNonMarkov .uniform holds only by the definition of standardEbcmValid (generalNonMarkov ≠ markovian), independently of the impl. systemRequired and standardEbcmValid are separate lookup tables with no definitional link, so 'the standard ODE EBCM fails' is not stated. |  |
| `Obstructions.table.R19` | forward 3 | impl never mentions standardEbcmValid. ∀ n i, ¬ standardEbcmValid n .generalNonMarkov i holds only by the definition of standardEbcmValid (generalNonMarkov ≠ markovian), independently of the impl, and is not stated. |  |
| `Obstructions.table.R19` | backward | SHADOW?: the impl's second conjunct is ∀ net, ebcmExists net .generalNonMarkov .uniform (every network), but the shadow set requires existence only on the configuration model (S5). The row text 'Non-Markovian: ODE fails, PDE EBCM works (exact)' does not fix the network. The blind author's own reading of the same passage for R19b ('Non-Markovian + uniform: an EBCM exists', network left free) requires every network. The ∀-conjunct cannot be derived from S5 except by re-using the configuration-model proof at other networks, which works only because ebcmExists ignores its network argument. | yes |
| `Obstructions.table.R21` | forward 2 | impl degreeCorr_ebcm_exists says only ebcmExists .degreeCorrelated .markovian .uniform. It says nothing about extensionDim, so '(ODE)' as a finite positive dimension (0 < extensionDim .degreeCorrelated .markovian) is not stated. |  |
| `Obstructions.table.R21` | forward 3 | impl says nothing about systemRequired. systemRequired .markovian .uniform = .ode is the supporting theorem markov_is_ode, which is not in the impl list. |  |
| `Obstructions.table.R22` | forward 1 | S1 (extensionDim .clusteredTriangles .markovian = 13) is a clause of the table extensionDim (rfl). impl (clustering_dimension_cost ∧ standard_most_compact) states only inequalities, so a checker could only prove S1 without h (vacuous). |  |
| `Obstructions.table.R22` | forward 2 | S2 (extensionDim .configurationModel .markovian = 4) is a clause of the table (rfl). impl states only inequalities, so a checker could only prove S2 without h (vacuous). |  |
| `Obstructions.table.R22` | backward | impl's second conjunct standard_most_compact (∀ net, extensionDim .configurationModel .markovian ≤ extensionDim net .markovian: the standard EBCM has the fewest variables of all classes) is not in the row and not in any shadow. The shadows give only the two counts and the comparison clustered > 3·standard − 1, so impl is stronger than the row. |  |
| `Obstructions.R18c` | forward 1 | impl clustering_dimension_cost only compares extensionDim values. 'handles it' (ebcmExists .clusteredTriangles .markovian .uniform) is not stated, because clustering_ebcm_exists is not in the impl list. |  |
| `Obstructions.R18c` | forward 2 | impl states extensionDim .clusteredTriangles .markovian > 3·extensionDim .configurationModel .markovian − 1 (truncated ℕ subtraction). That is a different inequality from S2, extensionDim .configurationModel .markovian < extensionDim .clusteredTriangles .markovian. S2 follows only by ℕ arithmetic (d ≤ 3d − 1, then transitivity: Nat.lt_of_le_of_lt / Nat.le constructors), which structural proofs cannot use, and no bridge on a trusted definition can carry an order lemma. Logically the impl is stronger here, so this failure is an audit limitation for this shadow. |  |
| `Obstructions.R18c` | backward | impl's ~3× bound (extensionDim .clusteredTriangles .markovian > 3·extensionDim .configurationModel .markovian − 1) is stronger than 'more variables'. S1 ∧ S2 hold with dimensions 4 < 5, which violate 5 > 11. The impl states Result 22's ~3× cost, not this sentence's 'more variables'. |  |
| `Obstructions.R21b` | forward 2 | impl degreeCorr_ebcm_exists states only ebcmExists .degreeCorrelated .markovian .uniform. 'Still an ODE system', read as 0 < extensionDim .degreeCorrelated .markovian, is not stated (the impl says nothing about extensionDim). |  |
| `Obstructions.R21b` | forward 3 | impl says nothing about systemRequired. 'Still an ODE system', read as systemRequired .markovian .uniform = .ode, is the supporting theorem markov_is_ode, which is not in the impl list (registry: 'multi-type', 'mixing matrix' and 'ODE' are not formalised for this network type). |  |
| `Obstructions.R19a` | forward 2 | impl nonmarkov_requires_pde states only systemRequired .generalNonMarkov .uniform = .pde. The 'from ODE' baseline, systemRequired .markovian .uniform = .ode, is markov_is_ode, which is not in the impl list (registry: 'Change from ODE' is not stated). |  |
| `Obstructions.R19a` | forward 3 | impl says nothing about extensionDim. 'infinite-dimensional state space', read as the PDE sentinel extensionDim n .generalNonMarkov = 0 on every network, is not stated (registry: 'infinite-dimensional' is not stated). |  |
| `Obstructions.R19b` | forward 3 | impl nonmarkov_ebcm_exists states only ebcmExists net .generalNonMarkov .uniform. 'as a PDE system' (systemRequired .generalNonMarkov .uniform = .pde) is the supporting theorem nonmarkov_requires_pde, which is not in the impl list. |  |
| `Obstructions.R19b` | forward 4 | impl says nothing about systemRequired. 'Changes the type of system' (systemRequired .generalNonMarkov .uniform ≠ systemRequired .markovian .uniform) is not stated. |  |
| `Obstructions.erlangIsOde` | forward 2 | impl erlang_is_ode states only systemRequired .erlangStaged .uniform = .ode. It says nothing about extensionDim, so 0 < extensionDim n .erlangStaged on every network (a hard-coded table fact) is not stated. |  |
| `Obstructions.R20a` | forward 2 | S2 (every network and transition type has an EBCM variant under uniform seeding) holds by the definition of ebcmExists (it is .uniform = .uniform, rfl). impl localised_genuine_obstruction states only the localised case, so a checker could only prove S2 without h (vacuous). |  |
| `Obstructions.R22a` | forward 1 | S1 (the table gives 13 variables for the triangle-clustered EBCM) is a clause of extensionDim (rfl). impl clustering_dimension_cost states only the inequality, so a checker could only prove S1 without h (vacuous). |  |
| `Obstructions.R22a` | forward 2 | S2 (the table gives 4 variables for the standard EBCM) is a clause of extensionDim (rfl). impl states only the inequality, so a checker could only prove S2 without h (vacuous). |  |
| `Obstructions.standardMostCompact` | forward 1 | impl standard_most_compact states only extensionDim .configurationModel .markovian ≤ extensionDim net .markovian. It does not state that the standard EBCM is an ODE variant (0 < extensionDim .configurationModel .markovian). |  |
| `Obstructions.standardMostCompact` | forward 2 | impl compares only Markovian variants (∀ net, … ≤ extensionDim net .markovian). S2 quantifies over every ODE variant (n, t), including the erlangStaged ones, which the impl does not cover. They are larger in the table (6/15/12/22 ≥ 4), but this is not stated (registry: Erlang-staged ODE variants are not quantified over). |  |
| `Obstructions.standardMostCompact` | forward 3 | impl states only ≤, not strictly fewer, and only over Markovian variants. S3 (the unique minimum: every other ODE variant, including erlangStaged, is strictly larger) is not stated. |  |
| `Obstructions.standardMostCompact` | backward | impl is unconditional over Markovian networks (extensionDim .configurationModel .markovian ≤ extensionDim net .markovian for every net), whereas the shadows compare only ODE variants (hypothesis 0 < extensionDim n t). Deriving the impl from S2 needs 0 < extensionDim net .markovian for every net, which the shadow set does not state (S1 covers only the configuration model). For example, a table with extensionDim .degreeCorrelated .markovian = 0 satisfies S1–S3 but not the impl. |  |
| `Obstructions.R24a` | forward 2 | impl (erlang_costs_more ∧ erlang_is_ode) does not state the presupposition 'the PDE' (systemRequired .generalNonMarkov .uniform = .pde). That is nonmarkov_requires_pde, which is not in the impl list (registry: no PDE → ODE approximation is formalised). |  |
| `Obstructions.R24a` | forward 3 | impl erlang_costs_more states only ≤ (extensionDim net .markovian ≤ extensionDim net .erlangStaged). 'at the cost of extra variables' requires strict < on every network. |  |
| `Obstructions.R24a` | backward | Not structurally derivable, although logically implied. S3 gives extensionDim n .markovian < extensionDim n .erlangStaged, and the impl's first conjunct needs ≤. The step < ⇒ ≤ on ℕ is Nat.le_of_lt (or Nat.le.step), which the structural rule forbids, and no bridge on a trusted definition can carry an order lemma. S1 gives the second conjunct. The impl is weaker than the shadows here, so this backward failure is an audit limitation, not an over-strong impl. |  |
| `Obstructions.R24c` | forward 1 | impl erlang_costs_more states ≤ (extensionDim net .markovian ≤ extensionDim net .erlangStaged), but the text 'always needs more variables' requires strict <. The registry notes the same. |  |
| `Obstructions.R24c` | backward | Not structurally derivable, although logically implied. S1 (<) implies the impl (≤) only through Nat.le_of_lt (or Nat.le.step), which the structural rule forbids, and no bridge on a trusted definition can carry an order lemma. The impl is weaker than the shadow, so this backward failure is an audit limitation, not an over-strong impl. |  |
| `Obstructions.R23b` | forward 3 | impl system_classification is only about systemRequired. 'always works' (∀ n, ebcmExists n .markovian .uniform) is not stated, because ebcmExists does not occur in the impl (registry: '(always works)' is not formalised). |  |
| `Obstructions.R23b` | forward 4 | impl system_classification is only about systemRequired. 'always works' (∀ n, ebcmExists n .erlangStaged .uniform) is not stated, because ebcmExists does not occur in the impl. |  |
| `Obstructions.R23b` | backward | impl system_classification also states the other two rows of the table for every trans: uniform ∧ generalNonMarkov → pde, and localised → impossible. The R23b shadow set (the Markovian/Erlang row only) does not imply them. The single impl covers the whole Result 23 table, so it is stronger than this row. |  |
| `Obstructions.R23c` | forward 2 | impl system_classification is only about systemRequired. 'always works' (∀ n, ebcmExists n .generalNonMarkov .uniform) is not stated, because ebcmExists does not occur in the impl. |  |
| `Obstructions.R23c` | forward 3 | impl says nothing about extensionDim. 'infinite-dim' (the PDE sentinel extensionDim n .generalNonMarkov = 0) is not stated (registry: 'infinite-dim' is not formalised). |  |
| `Obstructions.R23c` | backward | impl system_classification also states the rows uniform ∧ (markovian ∨ erlangStaged) → ode and localised → impossible, which the R23c shadow set does not imply. The single impl covers the whole Result 23 table, so it is stronger than this row. |  |
| `Obstructions.header.kirkwoodHierarchyInconsistent` | forward 1 | S1 (the surrogate marginalisation is M(a, b) = a + b) is the definition of M_witness (rfl). impl kirkwood_marginalisation_obstruction states only the existence of a non-commuting state, so a checker could only prove S1 without h (vacuous). |  |
| `Obstructions.header.kirkwoodHierarchyInconsistent` | forward 3 | impl is existential (∃ u, M(F₄ u) ≠ F₃(M u)); the witness state (1, 3) appears only in its proof. S3 (the diagram does not commute at the named state (1, 3)) does not follow from the existential. |  |
| `Obstructions.R25b` | forward 1 | impl kirkwood_obstruction_witness_value states only the difference M_witness (F4_Kirkwood u) c − F3_Kirkwood (M_witness u) c = 2 at the witness. The individual value M (F₄ u)(c) = 6 is not stated, since a difference does not determine its terms. The registry notes the same. |  |
| `Obstructions.R25b` | forward 2 | impl kirkwood_obstruction_witness_value states only the difference LHS − RHS = 2 at the witness. The individual value F₃ (M u)(c) = 4 is not stated, since a difference does not determine its terms. The registry notes the same. |  |
| `PairwiseClosureConditions.header.nonnegNeedsPointwise` | forward 2 | impl is the conjunction of triple_term_nonneg (0 ≤ base → (∀ b, 0 ≤ p b) → 0 ≤ tripleTerm base p a) and negative_weight_gives_negative_triple (∀ base p a, 0 < base → p a < 0 → tripleTerm base p a < 0). Both are universal implications; neither exhibits a weight family nor mentions normalization together with a negative weight. S2 is the existence statement ∃ α (Fintype), base ≥ 0, p with ∑ a, p a = 1 and some tripleTerm base p a < 0, i.e. that normalization (with B ≥ 0) does not suffice for nonnegativity. Its content, that a normalized family can have a strictly negative entry (e.g. Bool, p = (2, -1), base = 1), is not stated by impl. A checker would have to supply that witness and verify ∑ p = 1, 0 ≤ 1, 0 < 1 and p false < 0 by closed kernel computation on ℚ; tripleTerm 1 p false = -1 < 0 then holds by the same computation, so S2 is provable from scratch and any use of h would be inessential (README Known limitations 1). The registry impl_note already says necessity is proved 'only in the pointwise sense'. Recorded rather than forced. |  |
| `PairwiseClosureConditions.header.nonnegNeedsPointwise` | backward | impl is stronger than, and partly different from, the shadows. (1) Its first conjunct triple_term_nonneg gives 0 ≤ tripleTerm base p a for every pointwise nonnegative p WITHOUT normalization, whereas S1 gives it only for normalized p (∑ a, p a = 1); an unnormalized p is not definitionally normalized, and rescaling is not structural. (2) Its second conjunct negative_weight_gives_negative_triple is a universal statement (every negative weight with positive base gives a negative triple), whereas S2 is a single existential counterexample and S1 is about nonnegativity; no universal implication about arbitrary negative weights follows from them. |  |
| `PairwiseClosureConditions.header.conservationNotPositivity` | forward 1 | impl negative_weight_gives_negative_triple is the pointwise implication ∀ base p a, 0 < base → p a < 0 → tripleTerm base p a < 0. It says nothing about conservation: no weight family with ∑ a, tripleTerm base p a = base (or ∑ p = 1) and a negative entry is exhibited. S1 is the non-implication 'conservation alone does not imply positivity' as a counterexample: ∃ α (Fintype), base ≥ 0, p with ∑ a, tripleTerm base p a = base and some tripleTerm base p a < 0. That existence is not stated by impl; a checker would have to supply the witness (e.g. Bool, p = (2, -1), base = 1) and verify the conservation equation and the sign facts by closed kernel computation on ℚ, which also proves the negative triple directly, so S1 is provable from scratch and h would be inessential (README Known limitations 1). The registry impl_note says the non-implication is 'only implicit'. |  |
| `PairwiseClosureConditions.header.conservationNotPositivity` | forward 2 | impl negative_weight_gives_negative_triple is the pointwise implication ∀ base p a, 0 < base → p a < 0 → tripleTerm base p a < 0 and never mentions normalization. S2 requires ∃ α (Fintype), base ≥ 0, p with ∑ a, p a = 1 and some tripleTerm base p a < 0 (normalized weights that are not positive). impl exhibits no such family; its content would have to come entirely from a checker-supplied witness (e.g. Bool, p = (2, -1), base = 1) checked by closed kernel computation, which proves the whole of S2 without h (README Known limitations 1). The registry notes anticipate this failure ('no existence statement'). |  |
| `PairwiseClosureConditions.header.conservationNotPositivity` | backward | impl is a universal statement (every negative weight with a strictly positive base gives a strictly negative triple, for every finite α, base and p). S1 and S2 are single existential counterexamples; they do not imply anything about arbitrary negative weights, so impl does not follow from the shadows. impl and the text are about different notions: a pointwise sign mechanism versus the non-implication 'conservation ⇏ positivity'. |  |
| `PairwiseClosureConditions.negativeWeightGivesNegativeTriple.b` | forward 1 | impl negative_weight_gives_negative_triple is the pointwise implication ∀ base p a, 0 < base → p a < 0 → tripleTerm base p a < 0 and does not mention mass conservation. S1 requires the counterexample ∃ α (Fintype), base ≥ 0, p with ∑ a, tripleTerm base p a = base and some tripleTerm base p a < 0 ('mass conservation alone cannot certify positivity'). impl exhibits no weight family whose triple mass is conserved; the witness and its conservation equation would have to be supplied by the checker and checked by closed kernel computation on ℚ (e.g. Bool, p = (2, -1), base = 1), which also yields the negative triple without h, so S1 is provable from scratch and h would be inessential (README Known limitations 1). The registry impl_note: 'no statement combines ∑ p = 1 with a negative weight'. |  |
| `PairwiseClosureConditions.negativeWeightGivesNegativeTriple.b` | forward 2 | impl negative_weight_gives_negative_triple (∀ base p a, 0 < base → p a < 0 → tripleTerm base p a < 0) never combines normalization with a negative weight. S2 requires ∃ α (Fintype), base ≥ 0, p with ∑ a, p a = 1 and some tripleTerm base p a < 0. That existence is not in impl; a proof would rest on a checker-supplied witness verified by closed kernel computation, which proves S2 without h (README Known limitations 1). |  |
| `PairwiseClosureConditions.negativeWeightGivesNegativeTriple.b` | backward | impl is universal (every negative weight with strictly positive base gives a strictly negative triple). S1 and S2 are single existential counterexamples and imply nothing about arbitrary negative weights, so impl does not follow from them. The statements are about different notions: a pointwise sign mechanism versus the non-implication 'conservation ⇏ positivity'. |  |
| `PairwiseClosureConditions.barnardWeightsNormalized.a` | backward | impl barnardWeights_normalized is stronger than the text: it gives ∑ a, barnardWeights φ p_uc p_c a = 1 for EVERY φ ∈ ℚ (an affine combination (1 - φ)·p_uc + φ·p_c of two normalized families), with no hypothesis 0 ≤ φ ≤ 1. S1, the text's 'convex mixture', gives the normalization only for φ ∈ [0,1] (DataTypes: 'convex' means 0 ≤ φ ∧ φ ≤ 1). For φ outside [0,1] (e.g. φ = 2) S1 says nothing, so impl does not follow from S1. The registry impl_note records the same: 'for ANY φ (affine combination), i.e. stronger than convex'. |  |
| `PairwiseClosureConditions.keelingFactorNonneg` | forward 2 | SHADOW?: impl keelingFactor_nonneg assumes 0 ≤ φ ≤ 1 (hφ0, hφ1); S2 drops the φ range and quantifies over every φ ∈ ℚ. S2 is false, so no implementation could prove it: keelingFactor φ corr = (1 - φ) + φ·corr, and φ = 2, corr = 0 give keelingFactor 2 0 = -1 < 0 with 0 ≤ corr. The text 'If the Keeling correlation correction stays nonnegative, then the Keeling weight factor is nonnegative' concerns 'the Keeling weight factor', i.e. Keeling's clustered closure, whose φ is the clustering coefficient (DataTypes: 'Keeling-style multiplicative clustering factor'; 'The mixing parameter φ is the clustering weight'), with domain [0,1]. The literal all-φ reading makes the text false; φ ∈ [0,1] is its implicit domain, which is exactly S1 (proved). | yes |
| `PairwiseClosureConditions.keelingWeightsNonneg` | forward 2 | SHADOW?: impl keelingWeights_nonneg assumes 0 ≤ φ ≤ 1 (hφ0, hφ1); S2 quantifies over every φ ∈ ℚ. S2 is false: keelingWeights φ p corr a = p a · ((1 - φ) + φ·corr a), and on α = Unit with p ≡ 1, corr ≡ 0 (both nonnegative) and φ = 2 the weight is 1·(-1) = -1 < 0. The text 'If the baseline weights and the correlation correction are both nonnegative, then the Keeling-reweighted weights are nonnegative' is about Keeling's clustered closure, whose φ is the clustering coefficient with domain [0,1] (DataTypes: 'The mixing parameter φ is the clustering weight'); the all-φ reading makes the text false. The implicit-domain reading is S1 (proved). | yes |
| `PairwiseClosureConditions.keelingStyleClosureSafe.a` | forward 3 | SHADOW?: impl keeling_style_closure_safe assumes 0 ≤ φ ≤ 1 (hφ0, hφ1) and so gives conservation of the Keeling closure only for φ ∈ [0,1]; S3 requires it for every φ ∈ ℚ, and no hypothesis of S3 supplies 0 ≤ φ or φ ≤ 1, so S3 does not follow from h. S3 itself is true (conservation needs only the supplied normalization ∑ a, keelingWeights φ p corr a = 1), so if the all-φ reading were intended the remedy would be a trusted conservation theorem without hφ0/hφ1. But the text 'Keeling-style closures are safe only after an additional normalization theorem is supplied' is about Keeling's clustered closure, whose φ is the clustering coefficient with domain [0,1] (DataTypes: 'Keeling-style multiplicative clustering factor'; 'The mixing parameter φ is the clustering weight'), and under the all-φ reading the text's 'safe' is false (see S4). The in-domain reading is S1 (proved). | yes |
| `PairwiseClosureConditions.keelingStyleClosureSafe.a` | forward 4 | SHADOW?: impl assumes 0 ≤ φ ≤ 1 (hφ0, hφ1); S4 (nonnegativity of the Keeling triple terms for every φ ∈ ℚ, given normalization, base ≥ 0, p ≥ 0, corr ≥ 0) is false: on α = Bool with φ = 2, corr = (0, 2), p ≡ 1/2 and base = 1 the Keeling factors are (1 - 2) + 2·0 = -1 and (1 - 2) + 2·2 = 3, the weights (-1/2, 3/2) sum to 1, and tripleTerm 1 w true = -1/2 < 0. The text is about Keeling's clustered closure, whose φ is the clustering coefficient in [0,1] (DataTypes: 'The mixing parameter φ is the clustering weight'); the all-φ reading makes 'Keeling-style closures are safe' false. The in-domain reading is S2 (proved). | yes |
| `PairwiseClosureConditions.keelingStyleClosureSafe.a` | forward 5 | impl proves only sufficiency: under 0 ≤ base, 0 ≤ φ ≤ 1, p ≥ 0, corr ≥ 0 AND the supplied normalization ∑ a, keelingWeights φ p corr a = 1, the Keeling closure is safe (conservation ∧ pointwise nonnegativity). S5 is the necessity half of 'safe ONLY after an additional normalization theorem is supplied': ∃ α (Fintype), base, φ ∈ [0,1], p ≥ 0, corr ≥ 0 such that the closure is NOT safe. Every conclusion obtainable from h is a safety fact, never its negation, and h can only be applied to families that are already normalized; the failure of safety needs a witness violating normalization (e.g. Unit, φ = 1, p ≡ 1, corr ≡ 2, base = 1, total mass 2 ≠ 1), whose refutation 2 ≠ 1 is a closed computation independent of h. So any proof of S5 would be vacuous. The registry impl_note: 'The only after (necessity: without it conservation can fail) is not proved'. |  |
| `PairwiseClosureConditions.keelingStyleClosureSafe.b` | forward 2 | SHADOW?: impl's first conjunct keelingWeights_nonneg assumes 0 ≤ φ ≤ 1 (hφ0, hφ1); S2 requires nonnegative Keeling triple terms for every φ ∈ ℚ. S2 is false: on α = Unit with base = 1, p ≡ 1, corr ≡ 0 (all nonnegative) and φ = 2, tripleTerm 1 (keelingWeights 2 p corr) () = 1·(1·((1 - 2) + 2·0)) = -1 < 0. The text 'Positivity follows from nonnegative baseline weights and nonnegative correlation corrections' is about Keeling's clustered closure, whose φ is the clustering coefficient in [0,1] (DataTypes: 'The mixing parameter φ is the clustering weight'); the all-φ reading makes it false. The in-domain reading is S1 (proved). | yes |
| `PairwiseClosureConditions.keelingStyleClosureSafe.b` | backward | impl is the conjunction of two general lemmas, each stronger than or different from the composite shadow S1 (nonnegativity of tripleTerm base (keelingWeights φ p corr) a for base ≥ 0, φ ∈ [0,1], p ≥ 0, corr ≥ 0). (1) keelingWeights_nonneg concludes 0 ≤ keelingWeights φ p corr a itself, with no base term; from S1 one only gets 0 ≤ tripleTerm base w a = base·w a, and recovering 0 ≤ w a (e.g. at base = 1) needs 1·x = x on ℚ (one_mul, not definitional for a variable x) and 0 ≤ 1. (2) triple_term_nonneg is about an ARBITRARY nonnegative weight family p, not only Keeling-reweighted ones; an arbitrary p is not definitionally keelingWeights φ p' corr for any φ, p', corr (p a·((1 - 0) + 0·c) = p a needs ring laws). So impl does not follow structurally from S1 (and S2, which is false). |  |
| `SEIREquations.table.SEIR1` | forward 1 | impl I_pop_zero_at_seed states I_pop = 0 only at the literal states <theta=1, phi_E=eps, phi_I=0, pop_E=eps, pop_I=0, pop_R=0> (one state per eps). S1 requires I_pop s = s.pop_I for every state s, and in particular for states with pop_I /= 0. The impl says nothing about those states. S1 holds only by the definition of SEIRState.I_pop, which would mean re-proving it without h. |  |
| `SEIREquations.table.SEIR1` | forward 2 | impl I_pop_zero_at_seed is a statement about the literal seed states only (in which pop_E and phi_E vary together through eps, and pop_I = 0). S2 requires I_pop to be invariant under replacing pop_E by any x in every state s. The impl does not state this. It holds only because the definition of I_pop does not read pop_E, and using that means re-proving S2 without h. |  |
| `SEIREquations.table.SEIR2` | backward | impl is stronger than S1. impl edge_hazard_independent_of_E says that s1.phi_I = s2.phi_I implies s1.edgeHazard p = s2.edgeHazard p, for states s1, s2 that may differ in every field other than phi_I (theta, phi_E, pop_E, pop_I, pop_R). S1 only gives invariance under changing phi_E. From S1 one gets edgeHazard s1 p = edgeHazard {s1 with phi_E := s2.phi_E} p, but that state still differs from s2 in theta and the population fields. Closing the gap needs the definition edgeHazard = beta * phi_I, i.e. re-proving the impl without S1. |  |
| `SEIREquations.table.SEIR3` | forward 1 | impl seir_population_conservation gives dE p inc + dI p + dR p = inc. S1 requires ((dS inc + dE p inc) + dI p) + dR p = 0 with dS inc = -inc. Going from one to the other needs reassociation of + and the cancellation -inc + inc = 0 on Q (ring arithmetic), which is not structural, and no bridge on a trusted definition can carry it (audit limitation). The impl also has no susceptible fraction S and no normalisation S + E + I + R = 1. It is only the rate identity for the non-susceptible classes, with 'excluding seed' having no counterpart. |  |
| `SEIREquations.table.SEIR3` | backward | impl dE + dI + dR = inc follows from S1 (-inc + dE + dI + dR = 0) only by ring arithmetic on Q (reassociation and adding inc to both sides), which is not structural (audit limitation). The two statements are equivalent algebraically. |  |
| `SEIREquations.table.SEIR4` | forward 1 | impl seir_theta_nonincreasing states only 0 <= phi_I -> dtheta <= 0. S1 ('not E-edges') requires dtheta to be invariant under replacing phi_E by any x. The impl says nothing about phi_E. The invariance holds only because the definition dtheta = -(beta * phi_I) does not read phi_E, and using that means re-proving S1 without h. |  |
| `SEIREquations.table.SEIR4` | forward 2 | impl gives an upper bound dtheta <= 0 when phi_I >= 0. S2 ('only from I-edges') requires the lower bound 0 <= dtheta when phi_I = 0. With phi_I = 0 the impl yields only dtheta <= 0, the opposite inequality. 0 <= dtheta follows only from the definition, via -(beta * 0) = 0 (mul_zero, neg_zero), which is not stated by the impl and not structural. |  |
| `SEIREquations.table.SEIR4` | backward | SHADOW?: the text 'θ only decreases from I-edges (not E-edges)' asserts that the effect of I-edges on θ is a decrease. The shadow set drops that direction. S1 (dtheta independent of phi_E) and S2 (phi_I = 0 -> 0 <= dtheta) are both satisfied by dtheta = +beta * phi_I, in which θ increases through I-edges, and that violates the impl (0 <= phi_I -> dtheta <= 0) at phi_I > 0. So the impl states the decrease direction (it matches the verb 'decreases'), which no shadow requires, and it cannot be derived from S1 and S2. | yes |
| `SEIREquations.edgeHazard` | forward 3 | impl edge_hazard_independent_of_E states only that two states with equal phi_I have equal edgeHazard p. It does not determine the value of the hazard. S3 requires the formula edgeHazard s p = beta * phi_I (0 * phi_E + beta * phi_I, 'E has zero transmission rate'). The formula is the definition of SEIRState.edgeHazard, but no impl conjunct states it. Any function of phi_I (e.g. beta^2 * phi_I, or 0) satisfies the impl, so a proof would have to re-prove S3 from the definition without h. |  |
| `SEIREquations.dTheta` | forward 1 | impl seir_theta_nonincreasing states only the sign 0 <= phi_I -> dtheta <= 0. S1 requires the formula dtheta = (-beta) * phi_I. The impl does not determine the value (any non-positive rate, e.g. dtheta = -beta^2 * phi_I or 0, satisfies it). The formula is the definition of SEIRState.dtheta (literally -(beta * phi_I), which equals (-beta) * phi_I only by neg_mul), and no impl conjunct states it. A bridge stating it would be the claim itself, and its checker would not use h. |  |
| `SEIREquations.dTheta` | forward 2 | impl states only 0 <= phi_I -> dtheta <= 0. S2 ('θ does not decrease from E-edges') requires dtheta to be invariant under replacing phi_E by any x. The impl says nothing about phi_E. The invariance holds only because the definition of dtheta does not read phi_E, and using that means re-proving S2 without h. |  |
| `SEIREquations.dTheta` | backward | impl 0 <= phi_I -> dtheta <= 0 follows from S1 (dtheta = (-beta) * phi_I) only by ordered-field arithmetic ((-beta) * phi_I <= 0 from beta > 0 and phi_I >= 0: neg_mul, mul_nonneg, neg_nonpos) and the data invariant p.beta_pos. Neither is structural (audit limitation). The impl is also a different statement from the text: the text gives the formula, and the impl gives only its sign. |  |
| `SEIREquations.iPopZeroAtSeed-a` | forward 1 | impl I_pop_zero_at_seed states I_pop = 0 only at the literal states <1, eps, 0, eps, 0, 0> (a single-instance check proved by rfl). S1 requires I_pop s = s.pop_I for every state s, including states with pop_I /= 0 and pop_E /= 0. The impl says nothing about those states. The universal statement holds only by the definition of SEIRState.I_pop, which would mean re-proving it without h. |  |
| `SEIREquations.iPopZeroAtSeed-b` | forward 1 | impl I_pop_zero_at_seed fixes the edge variables of the seed state at theta = 1, phi_E = eps, phi_I = 0. S1 requires I_pop <theta, phiE, phiI, eps, 0, 0> = 0 for arbitrary theta, phiE, phiI. Both statements reduce definitionally to 0 = 0. A checker 'fun eps _ _ _ _ => h eps' would type-check, but it would use h only to supply rfl at a different instance (a vacuity dodge, README limitation 1). The impl's statement does not cover the other edge values. |  |
| `SEIREquations.iPopZeroAtSeed-b` | forward 2 | impl does not state 'not ε' (I_pop /= eps), and it fixes theta = 1, phi_E = eps, phi_I = 0 where S2 quantifies over all edge variables. I_pop /= eps under 0 < eps follows only by rewriting the definitional I_pop = 0 into 0 < eps (the order fact 0 < 0 -> False). That needs no h, so any use of h would be a dodge. |  |
| `SEIREquations.iPopZeroAtSeed-b` | backward | impl is stronger in eps. I_pop_zero_at_seed holds for every eps in Q with no positivity hypothesis, while S1 and S2 assume 0 < eps (the seed is positive) and so give nothing at eps <= 0. The only route would apply s1 at some positive eps' (itself needing a proof of 0 < eps', not structural) and rely on both statements reducing definitionally to 0 = 0. That re-uses a definitional triviality at a different instance and is not a derivation from the shadows. |  |
| `SEIREquations.iPopWrongNonzeroAtSeed` | forward 1 | impl I_pop_wrong_nonzero_at_seed states only I_pop_wrong /= 0 at the seed state <1, eps, 0, eps, 0, 0> under 0 < eps. S1 requires the value I_pop_wrong = eps ('gives ε'). The impl does not state the value (any nonzero value satisfies it). It follows only from the definition pop_E + pop_I = eps + 0 and eps + 0 = eps (add_zero, not definitional on Q), which is re-proving S1 without h. |  |
| `SEIREquations.edgeHazardIndependentOfE` | backward | impl is stronger than the text. edge_hazard_independent_of_E says that s1.phi_I = s2.phi_I implies equal edgeHazard, so the hazard is independent of every field other than phi_I (theta, phi_E, pop_E, pop_I, pop_R). S1 ('independent of φ_E') gives invariance under changing phi_E only. Two states with equal phi_I but different theta or population fields are not related by S1. Closing the gap needs the definition edgeHazard = beta * phi_I, i.e. re-proving the impl without S1. |  |
| `SEIREquations.seirIGrowthBounded-a` | forward 2 | S2 (dI/dt = σ·pop_E − γ·pop_I) is the definition of SEIRState.dI (rfl). impl seir_I_growth_bounded states only the bound, so a checker could only prove S2 without h (vacuous). |  |
| `SurvivalBridge.header.kappaInvariant-b` | forward 1 | S1 needs the real-function identity kappaAt (binomialPGF n q) θ = deriv (deriv ψ) θ * ψ θ / (deriv ψ θ)^2 = (n-1)/n for ψ(u) = (1-q+qu)^n, every n ≥ 1, 0 < q ≤ 1 and θ ∈ (0,1]. The impl conjunct binomial_closure_ratio is a ℚ statement about the record PGFEval.mk (w^(n+2)) ((n+2)p w^(n+1)) ((n+2)(n+1)p^2 w^n). There w > 0 is a free scalar, and the derivative values are supplied as expressions, not computed from a PGF with deriv. It covers only n+2 ≥ 2 trials, so n = 1 (κ = 0) is missing, and the passage from Mathlib deriv on ℝ to these ℚ expressions is calculus, not structure. |  |
| `SurvivalBridge.header.kappaInvariant-b` | forward 2 | S2 needs kappaAt (poissonPGF ℓ) θ = 1 on (0,1] for the real function ψ(u) = exp(ℓ(u-1)) with Mathlib deriv. The impl conjunct poisson_closure_ratio states closureRatio (PGFEval.mk ψ (λψ) (λ²ψ)) = 1 over ℚ with a free ψ > 0 and the derivatives ψ' = λψ, ψ'' = λ²ψ supplied, not derived. It never mentions exp, deriv or ℝ. |  |
| `SurvivalBridge.header.kappaInvariant-b` | forward 3 | S3 needs kappaAt (negBinPGF r q) θ = (r+1)/r on (0,1] for real r > 0 and ψ(u) = ((1-q)/(1-qu))^r. The impl conjunct negbin_general_closure_ode is the polynomial identity (m+1)(m+2)p²c^(m+1)w^(m+3)·c^(m+1)w^(m+1) = ((m+2)/(m+1))((m+1)p c^(m+1)w^(m+2))² over ℚ in free p, c, w. It covers only integer r = m+1 and has the ODE form ψ''ψ = κψ'², not a ratio. It has no deriv and no PGF function, and non-integer r is not covered. |  |
| `SurvivalBridge.header.kappaInvariant-b` | forward 4 | S4 needs PGFData.closureKappa ψ = (n-1)/n for every PGFData with Binomial(n,q) moments (mean nq, secondFactorial n(n-1)q²), n ≥ 1. No impl conjunct mentions closureKappa or PGFData. binomial_closure_ratio is about PGFEval.closureRatio of an explicit record in a free w, for n+2 ≥ 2 only. Matching it (at w = 1, n = n'+2) with n(n-1)q²/(nq)² is field algebra (1^k = 1, casts, cancellation), not structure, and n = 1 is not covered. |  |
| `SurvivalBridge.header.kappaInvariant-b` | forward 5 | S5 needs PGFData.closureKappa (PGFData.poisson ℓ h) = 1, i.e. ℓ²/ℓ² = 1 in ℚ. The impl conjunct poisson_closure_ratio is about PGFEval.closureRatio: (λ²ψ)ψ/(λψ)² = 1 for a free ψ > 0. Even at ψ := 1, the terms (ℓ²·1)·1/(ℓ·1)² and ℓ²/ℓ² are not definitionally equal for a variable ℓ (Rat.mul normalises through gcd), so the step needs ring normalisation. No trusted definition is misread, so no bridge applies. |  |
| `SurvivalBridge.header.kappaInvariant-b` | forward 6 | S6 needs PGFData.closureKappa ψ = (r+1)/r for every PGFData with NB(r,q) moments (mean rq/(1-q), secondFactorial r(r+1)q²/(1-q)²) and every rational r > 0. The impl conjunct negbin_general_closure_ode is an ODE-form polynomial identity in free p, c, w for integer r = m+1 only. It mentions neither closureKappa nor moments, so non-integer r and the ratio form are not covered. |  |
| `SurvivalBridge.header.kappaInvariant-b` | backward | sa_impl% is the conjunction of three ℚ statements about explicit PGFEval records and polynomial identities in free scalars: binomial_closure_ratio (every w > 0, p > 0), poisson_closure_ratio (every psi_val > 0) and negbin_general_closure_ode (every p, c, w). S1-S3 are about real PGF functions through Mathlib deriv, and S4-S6 are about PGFData.closureKappa of moment data. None mentions PGFEval.closureRatio at a free point w or these polynomials, so the impl conjuncts cannot be obtained from the shadows by structure. That would need deriv evaluation, ℝ→ℚ transfer and field algebra. |  |
| `SurvivalBridge.table.R42` | forward 2 | impl poisson_kappa_eq_one is about the two-moment record: closureKappa (poisson λ) = 1, i.e. κ(1) = 1. S2 (the real Poisson PGF e^{λ(u−1)} has κ(u) = ψ''ψ/ψ'² = 1 at every u) is a statement about derivatives of the real PGF that impl does not make. |  |
| `SurvivalBridge.table.R42` | forward 3 | S3 (κ ≡ 1 on an interval forces Poisson weights: the converse, KKR Theorem 1) is not stated by impl, which says only that the Poisson record has κ(1) = 1. |  |
| `SurvivalBridge.table.R43` | forward 2 | impl binomial_kappa_lt_one is the existential ∃ ψ, closureKappa ψ < 1 (its witness, the Binomial(3, 1/2) record, appears only in its proof). S2 (the real binomial PGF has κ(u) ≡ (n−1)/n on (0,1]) is a statement about derivatives of real PGFs that impl does not make. |  |
| `SurvivalBridge.table.R43` | forward 3 | S3 (the binomial record of any n ≥ 1, p > 0 has closureKappa (n−1)/n) is universal over n and p. impl is a single existential with an unnamed witness, so it does not give S3. |  |
| `SurvivalBridge.table.R44` | forward 2 | impl negbin_kappa_gt_one is the existential ∃ ψ, closureKappa ψ > 1 (witness NegBin(2, 1/2), only in its proof). S2 (the real negative-binomial PGF has κ(u) ≡ (r+1)/r on [0,1]) is about derivatives of real PGFs, which impl does not mention. |  |
| `SurvivalBridge.table.R44` | forward 3 | S3 (the negative-binomial record of any r > 0, c ∈ (0,1) has closureKappa (r+1)/r) is universal over r and c. impl is a single existential with an unnamed witness, so it does not give S3. |  |
| `SurvivalBridge.table.R45` | forward 2 | S2 is the right inverse volzToDSA (dsaToVolz d c h) c = d (DSA → Volz → DSA). The impl volz_dsa_roundtrip states only the left inverse dsaToVolz (volzToDSA v ψ') ψ' h = v. The right inverse needs (x/c)·c = x in the x_SI and x_SS components (field algebra, div_mul_cancel), and the impl does not provide it. |  |
| `SurvivalBridge.table.R45` | forward 4 | S4 (volzToDSA · c is surjective for c ≠ 0) needs, for each DSA state d, a Volz state v with volzToDSA v c = d, i.e. a right inverse ((x/c)·c = x). The impl gives only the left inverse, which yields injectivity (S3) but not surjectivity. |  |
| `SurvivalBridge.table.R47` | forward 2 | impl poisson_closure_is_one states only closureKappa (poisson μ) = 1. S2 (the Poisson DSA survival equation has the rescaled mass-action form) is a statement about the DSA ODE (KKR Eq. 33), which impl does not mention; the Result 47 docstring says so ('The Lean theorem proves only that the Poisson record has closureKappa = 1'). |  |
| `SurvivalBridge.table.R48` | forward 1 | The impl states closureKappa ψ = secondFactorial/mean^2, which is definitional (proved by rfl). S1 needs closureKappa ψ = excessDegree ψ / mean = (secondFactorial/mean)/mean, the 'excess/degree ratio'. The step a/m^2 = (a/m)/m is field algebra (div_div, sq) and is not definitional in ℚ for a variable m (Rat.mul and Rat.inv normalise through gcd). The impl does not state the excess/degree form. A bridge closureKappa ψ = excessDegree ψ / ψ.mean would be the claim itself and would leave h unused. |  |
| `SurvivalBridge.table.R48` | forward 2 | S2 needs closureKappa ψ = secondFactorial/mean/mean. The impl gives secondFactorial/mean^2. The gap a/m^2 = a/m/m is ring and field normalisation in ℚ, not definitional for a variable m, and the impl does not state the iterated-quotient (excess ÷ degree) form. |  |
| `SurvivalBridge.table.R49` | forward 1 | S1 is universal over non-PT degree distributions p with positive mean: κ(θ) = ψ''ψ/ψ'² of the real series PGF takes two different values on (0,1). The impl nonPT_closure_varies is ∃ ψ : PGFData, closureKappa ψ ≠ 1 ∧ dispersionIndex ψ ≠ 1, one moment record with no θ, no PGF function, no PT predicate and no universal quantifier. Its proof witness ⟨10, 200⟩ even has geometric (NB(1), PT) moments, since secondFactorial = 2·mean². |  |
| `SurvivalBridge.table.R49` | forward 2 | S2 says that for every non-PT distribution no constant κ gives ψ''ψ/ψ'² = κ on (0,1), i.e. the closure is inexact. It is universal and function-level. The impl only asserts that some PGFData has closureKappa ≠ 1 and dispersionIndex ≠ 1. It has no closure exactness notion, no θ-dependence and no PT notion. |  |
| `SurvivalBridge.table.R50` | forward 2 | S2 is the right inverse volzToDSA (dsaToVolz d c h) c = d for c > 0. The impl volz_dsa_equiv_general proves only the left inverse dsaToVolz (volzToDSA v ψ.mean) ψ.mean h = v. The right inverse needs (x/c)·c = x (field algebra), which the impl does not state. |  |
| `SurvivalBridge.table.R50` | forward 3 | S3 needs Volz θ(t) = DSA x_θ(t), for t ≥ 0, for every pair of solutions of the Volz (paper eqs. 6-7) and DSA (eqs. 8-9) ODEs and every finite-variance degree distribution. The impl volz_dsa_equiv_general is only the static state-space identity dsaToVolz (volzToDSA v ψ.mean) ψ.mean h = v, for one VolzState record with the scale ψ'(1) = ψ.mean. It has no ODE, trajectory or time, and no equivalence of dynamics. |  |
| `SurvivalBridge.table.R50` | forward 4 | S4 needs the Volz x_S(t) = ψ(θ(t)) to equal the DSA x_S(t) for all solutions of the two ODE systems. The impl is a static left-inverse identity on VolzState records and mentions no ODE, solution or trajectory. |  |
| `SurvivalBridge.table.R50` | forward 5 | S5 needs the Volz and DSA infected fractions x_I(t) to agree for all solutions of the two ODE systems. The impl is a static left-inverse identity on VolzState records and mentions no ODE, solution or trajectory. |  |
| `SurvivalBridge.table.R50` | backward | The impl quantifies over every ψ : PGFData with the hypothesis ψ.mean ≠ 0 and uses the scale ψ.mean. S1 and S2 give the round trip only for scales with 0 < c, and 0 < ψ.mean does not follow from ψ.mean ≠ 0 in ℚ. The only other route is the data invariant ψ.mean_pos, a proof extracted from data, which structural proofs may not use. S3-S5 are ODE statements and do not help. The impl follows from S1 only modulo the PGFData invariant, so this is an audit limitation, not a stronger claim: mathematically S1 implies the impl. |  |
| `SurvivalBridge.volzState-b` | forward 2 | S2 (DSA → Volz → DSA is the identity) is dsa_volz_roundtrip, which is not in this claim's impl list. impl volz_dsa_roundtrip is the other composite (Volz → DSA → Volz) and does not give it. |  |
| `SurvivalBridge.volzState-b` | backward | impl holds for every nonzero scalar factor ψ' (including negative factors, and states with θ = 0). The shadows state the round trips only for factors of the form θ·d with θ·d > 0, so impl does not follow for an arbitrary ψ' ≠ 0: impl is stronger than the text's 'invertible whenever θ·ψ'(θ) > 0'. |  |
| `SurvivalBridge.R42` | forward 2 | SHADOW?: S2 ((PGFData.poisson κ hκ).secondFactorial = κ²) restates the definition of the operation under test: PGFData.poisson sets secondFactorial := κ ^ 2 (DataTypes: 'Key property: ψ''(1) = κ²'). It holds by rfl, so no wrong implementation theorem can falsify it, and any forward proof ignores h (vacuous). The impl states only closureKappa (PGFData.poisson κ hκ) = 1. The text 'This is because ψ''(1) = κ² [...]' justifies κ = 1 from the Poisson PGF. A falsifiable reading is the function-level fact deriv (deriv (poissonPGF κ)) 1 = κ² for ψ(u) = e^{κ(u-1)}, which the impl does not state either: in the library ψ''(1) = κ² is built in, not derived. | yes |
| `SurvivalBridge.R42` | forward 3 | SHADOW?: S3 ((PGFData.poisson κ hκ).mean = κ) restates the definition of PGFData.poisson ('The Poisson PGF with mean κ': mean := κ). It holds by rfl, cannot be falsified by an implementation theorem, and any forward proof ignores h (vacuous). The impl states only closureKappa (PGFData.poisson κ hκ) = 1. The clause 'ψ'(1) = κ' of the text is part of a justification, and a falsifiable reading, deriv (poissonPGF κ) 1 = κ, is function-level and not stated by the impl. | yes |
| `SurvivalBridge.R43a` | forward 1 | S1 needs closureKappa ψ = (n-1)/n for every PGFData with Binomial(n,q) moments (mean nq, secondFactorial n(n-1)q²), n ≥ 1, 0 < q ≤ 1. The impl binomial_kappa_lt_one is the bare existential ∃ ψ, closureKappa ψ < 1. It has no Binomial family, no n or q and no value (n-1)/n, and an existential cannot give the universal family statement. |  |
| `SurvivalBridge.R43a` | forward 2 | S2 needs closureKappa ψ < 1 for every PGFData with Binomial(n,q) moments. The impl only asserts one unnamed ψ with closureKappa ψ < 1 (existential), and nothing ties it to Binomial moments. |  |
| `SurvivalBridge.R44a` | forward 1 | S1 needs closureKappa ψ = (r+1)/r for every PGFData with NB(r,q) moments (mean rq/(1-q), secondFactorial r(r+1)q²/(1-q)²), r > 0, 0 < q < 1. The impl negbin_kappa_gt_one is the bare existential ∃ ψ, closureKappa ψ > 1. It has no negative-binomial family, no r or q and no value (r+1)/r, and an existential cannot give the universal family statement. |  |
| `SurvivalBridge.R44a` | forward 2 | S2 needs 1 < closureKappa ψ for every PGFData with NB(r,q) moments. The impl only asserts one unnamed ψ with closureKappa ψ > 1 (existential), and nothing ties it to NB moments. |  |
| `SurvivalBridge.R45b` | forward 1 | S1 (volzToDSA · c is a bijection) needs surjectivity, i.e. the other round trip DSA → Volz → DSA (dsa_volz_roundtrip). The text names that theorem ('Together with dsa_volz_roundtrip'), but it is not in this claim's impl list. impl volz_dsa_roundtrip gives only a left inverse, hence only injectivity. |  |
| `SurvivalBridge.R45b` | forward 3 | S3 (Function.RightInverse, i.e. DSA → Volz → DSA is the identity) is dsa_volz_roundtrip, which is not in impl. volz_dsa_roundtrip is the other composite. |  |
| `SurvivalBridge.R46c` | forward 2 | S2 ((nodeModel p μ).R0 = T·μ) is the definition of nodeModel (rfl). impl survival_map_R0_poisson states only the equality of the two R₀ values for the Poisson record, so a checker could only prove S2 without h (vacuous). |  |
| `SurvivalBridge.R46c` | forward 3 | S3 ((edgeModel p ψ).R0 = T·ψ''(1)/ψ'(1) for every record) is the definition of edgeModel (rfl). impl is about the Poisson record only, so a checker could only prove S3 without h (vacuous). |  |
| `SurvivalBridge.R47a` | forward 2 | impl poisson_closure_is_one states only closureKappa (poisson μ) = 1 (the text: 'The Lean theorem proves only that the Poisson record has closureKappa = 1'). S2 (the Poisson DSA survival equation −dS/dt = β̃(S − S²) + γ̃ S log S + ρ̃ S with the stated rescaled rates) is not stated. |  |
| `SurvivalBridge.R47a` | forward 3 | S3 (the mass-action SIR survival equation has the same form) is about the mass-action ODE, which impl does not mention. |  |
| `SurvivalBridge.R47b` | forward 1 | S1 is the real-function identity kappaAt (poissonPGF ℓ) u = ψ''(u)ψ(u)/ψ'(u)² = 1 for every u ∈ ℝ and ℓ > 0, where ψ(u) = exp(ℓ(u-1)) and the derivatives are Mathlib deriv. The impl poisson_closure_is_one is the ℚ moment identity closureKappa (PGFData.poisson κ hκ) = 1 at u = 1 only, and there ψ''(1) = κ² is built into the definition of PGFData.poisson. There is no function, no derivative and nothing 'identically' in u. |  |
| `SurvivalBridge.R47b` | backward | The impl (∀ κ > 0 in ℚ, closureKappa (PGFData.poisson κ hκ) = 1, i.e. κ²/κ² = 1) cannot be obtained from S1 by structure. S1 is about Real.exp and deriv on ℝ and never mentions PGFData or closureKappa. Linking them needs deriv evaluation at u = 1, the moment definitions and a ℚ→ℝ cast argument. |  |
| `SurvivalBridge.R49a` | forward 2 | impl nonPT_closure_varies is an existential about two-moment records. S2 (the non-PT law (1 + u²)/2 has the same record as Poisson(1): ψ'(1) = 1 and ψ''(1) = 1, as real derivatives) is about the real PGF psiMix, which impl does not mention. |  |
| `SurvivalBridge.R49a` | forward 3 | S3 (κ(θ) = (1 + θ²)/(2θ²) for ψ = (1 + u²)/2) is a computation with real derivatives of psiMix that impl does not make. |  |
| `SurvivalBridge.R49a` | forward 4 | S4 (κ(θ) of (1 + u²)/2 takes two different values on (0,1]) is not stated by impl, which concerns only records (κ(1) ≠ 1 and dispersion ≠ 1 for some record). |  |
| `SurvivalBridge.R50a` | forward 2 | S2 is the right inverse volzToDSA (dsaToVolz d c h) c = d for c > 0. The impl volz_dsa_equiv_general proves only the left inverse dsaToVolz (volzToDSA v ψ.mean) ψ.mean h = v. The right inverse needs (x/c)·c = x (field algebra), which the impl does not state. |  |
| `SurvivalBridge.R50a` | forward 3 | S3 needs Volz θ(t) = DSA x_θ(t) for all solutions of the Volz (paper eqs. 6-7) and DSA (eqs. 8-9) ODEs, for every finite-variance degree distribution. The impl is a static state-space identity for VolzState records with the scale ψ.mean = ψ'(1), not ψ'(θ). It has no ODE, trajectory or time, and the variance plays no role. |  |
| `SurvivalBridge.R50a` | forward 4 | S4 needs the Volz x_S(t) = ψ(θ(t)) to equal the DSA x_S(t) along solutions of the two ODE systems. The impl is a static left-inverse identity on VolzState records and mentions no ODE or trajectory. |  |
| `SurvivalBridge.R50a` | forward 5 | S5 needs the Volz and DSA infected fractions x_I(t) to agree along solutions of the two ODE systems. The impl is a static left-inverse identity on VolzState records and mentions no ODE or trajectory. |  |
| `SurvivalBridge.R50a` | backward | The impl quantifies over every ψ : PGFData with the hypothesis ψ.mean ≠ 0 and uses the scale ψ.mean. S1 and S2 give the round trip only for scales with 0 < c, and 0 < ψ.mean does not follow from ψ.mean ≠ 0 in ℚ. The only other route is the data invariant ψ.mean_pos, a proof extracted from data, which structural proofs may not use. S3-S5 are ODE statements. The impl follows from S1 only modulo the PGFData invariant, so this is an audit limitation, not a stronger claim. |  |
| `SurvivalBridge.R50b` | forward 1 | S1 ((volzToDSA v (θ·d)).x_SI = p_I·(θ·d)) is the definition of volzToDSA (rfl). impl volz_dsa_roundtrip states only the round trip, so a checker could only prove S1 without h (vacuous). |  |
| `SurvivalBridge.R50b` | forward 3 | S3 (DSA → Volz → DSA is the identity when x_θ·d > 0) is an instance of dsa_volz_roundtrip, which is not in this claim's impl list. volz_dsa_roundtrip is the other composite. |  |
| `SurvivalBridge.R50b` | backward | impl holds for every nonzero factor ψ'. S2 gives the round trip only for factors θ·d with θ·d > 0, so impl does not follow for negative factors or states with θ = 0. impl is stronger than 'invertible whenever θ·ψ'(θ) > 0'. |  |
| `SurvivalBridge.R50e` | forward 1 | SHADOW?: S1 states the round trip DSA → Volz → DSA (volzToDSA (dsaToVolz x ψ'(1)) ψ'(1) = x). The text says 'formalised here only as the round trip of Result 45 with the scalar factor ψ'(1)', and Result 45 is, by its docstring, 'The round-trip Volz → DSA → Volz is the identity' (volz_dsa_roundtrip, the registered impl). The shadow uses the other composite, dsa_volz_roundtrip, which impl does not give. The Volz → DSA → Volz reading at factor ψ'(1) would be an instance of impl. | yes |
| `SurvivalBridge.R50e` | backward | S1 is the DSA → Volz → DSA round trip at the factor ψ'(1) of a record. impl is the Volz → DSA → Volz round trip for every nonzero factor. The composites differ, and S1 covers only positive factors that are record means, so impl does not follow from S1. |  |
| `VolzMeyersEquations.table.VM1` | forward 2 | impl theta_nonincreasing is the sign of the ℚ-valued rate expression s.dθ p (= -(β·P₁·θ)) at a single state with P₁ ≥ 0 and θ ≥ 0. S2 requires monotonicity in time: a real function θ : ℝ → ℝ is Antitone along every trajectory of θ' = -β·P₁(t)·θ(t) with P₁(t) ≥ 0, θ(t) ≥ 0. The impl has no trajectory, no time derivative and no real-valued solution. The step from a non-positive derivative to Antitone needs the mean value theorem (antitone_of_deriv_nonpos) and the order transfer from ℚ to ℝ; the impl states neither and neither is structural. |  |
| `VolzMeyersEquations.thetaNonincreasing` | forward 2 | impl theta_nonincreasing is the sign condition s.dθ p ≤ 0 on the ℚ-valued rate expression at one state with P₁ ≥ 0, θ ≥ 0. S2 (the headline 'θ is non-increasing' read literally) requires θ : ℝ → ℝ to be Antitone along every real trajectory of θ' = -β·P₁(t)·θ(t) with P₁(t) ≥ 0 and θ(t) ≥ 0 at all times. The impl has no trajectory or time derivative. Deriving S2 needs the mean value theorem (antitone_of_deriv_nonpos) and the ℚ → ℝ order transfer, which the impl does not state and which are not structural. |  |
| `VolzMeyersEquations.table.VM4` | forward 1 | impl S_nonincreasing states only p.κ * s.dθ p ≤ 0 over ℚ, under 0 ≤ P₁, 0 ≤ θ and the extra hypothesis 0 < p.κ. S does not appear. S1 requires psi1 q θ * (dθ : ℝ) ≤ 0, i.e. dS/dt = ψ'(θ)·dθ/dt ≤ 0, for every degree distribution q and every parameter set (no κ > 0 hypothesis), at states with 0 ≤ θ ≤ 1. The factor ψ'(θ) is a real tsum, not the free scalar κ. Deriving S1 needs 0 ≤ ψ'(θ) (tsum_nonneg from the degree distribution), dθ ≤ 0 from κ·dθ ≤ 0 and κ > 0 (division, and unavailable when κ ≤ 0), the cast Rat.cast_nonpos and mul_nonpos_of_nonneg_of_nonpos. None of these is stated by the impl or structural. |  |
| `VolzMeyersEquations.table.VM4` | forward 2 | impl is a sign statement about the ℚ-valued product κ·dθ at one state. S2 requires S(t) = ψ(θ(t)) to be Antitone along every real trajectory of θ' = -β·P₁·θ with P₁ ≥ 0 and θ ∈ [0,1], for every PGF ψ. The impl has no ψ, no S and no trajectory. The proof needs PGF monotonicity on [0,1] (termwise tsum comparison), the mean value theorem and the ℚ → ℝ transfer, none of which the impl states. |  |
| `VolzMeyersEquations.table.VM4` | backward | impl is about the free scalar κ (free-scalar abstraction): p.κ * s.dθ p ≤ 0 over ℚ at every state with P₁ ≥ 0, θ ≥ 0 and κ > 0, including states with θ > 1. S1 constrains ψ'(θ)·dθ in ℝ for a PGF ψ and only at 0 ≤ θ ≤ 1, and S2 concerns trajectories. S1 gives nothing at θ > 1. At θ ≤ 1, turning psi1 q θ * dθ ≤ 0 into κ·dθ ≤ 0 needs a concrete PGF with ψ' ≡ 1 (evaluating a tsum), Rat.cast_le to return to ℚ, and mul_nonpos with κ > 0. That is not structural, and the impl's κ is not ψ'(θ). |  |
| `VolzMeyersEquations.sNonincreasing-a` | forward 1 | impl S_nonincreasing is a pointwise sign statement p.κ * s.dθ p ≤ 0 over ℚ. S1 requires t ↦ exp(κ(θ(t) - 1)) to be Antitone along every real trajectory of θ' = -β·P₁·θ with P₁ ≥ 0 and θ ≥ 0. The impl mentions neither S = exp(κ(θ-1)) nor a trajectory. The proof needs the mean value theorem, monotonicity of Real.exp and the ℚ → ℝ transfer, none of which the impl states. |  |
| `VolzMeyersEquations.sNonincreasing-a` | forward 2 | impl states p.κ * s.dθ p ≤ 0 over ℚ. S2 requires deriv (fun x => Real.exp (κ(x-1))) θ * (dθ : ℝ) ≤ 0 over ℝ, i.e. dS/dt ≤ 0 for S = exp(κ(θ-1)). The impl mentions neither exp nor S. Closing the gap needs the derivative computation deriv = κ·exp(κ(θ-1)) (HasDerivAt.exp, a library theorem), Real.exp_pos, the casts Rat.cast_mul and Rat.cast_nonpos, and mul_nonpos after reassociation. The two agree only up to the positive factor exp(κ(θ-1)), which the impl omits. None of this is structural. |  |
| `VolzMeyersEquations.sNonincreasing-a` | backward | impl p.κ * s.dθ p ≤ 0 (over ℚ) follows from S2 only through analysis and order steps that are not structural: computing deriv (fun x => exp(κ(x-1))) θ = κ·exp(κ(θ-1)), cancelling exp(κ(θ-1)) > 0, and reflecting the real inequality back to ℚ (Rat.cast_le). S1 is about real trajectories and gives no pointwise statement about the ℚ rate. |  |
| `VolzMeyersEquations.sNonincreasing-b` | forward 1 | impl S_nonincreasing is the rational sign statement κ·dθ ≤ 0 at a state. S1 is the real chain rule dS/dt = κ·S·dθ/dt for S = exp(κ(θ − 1)) along a curve θ. The text says 'nothing is proved about S along solutions', and impl indeed has no derivative, curve or exponential. |  |
| `VolzMeyersEquations.sNonincreasing-b` | forward 2 | impl gives κ·dθ ≤ 0; S2 is κ·S·dθ ≤ 0 for S ≥ 0. The text notes that impl omits the factor S. Inserting it needs mul_nonpos_of_nonneg_of_nonpos-type ordered-ring lemmas (and reassociation), which are not structural. |  |
| `VolzMeyersEquations.sNonincreasing-b` | backward | impl (κ·dθ ≤ 0) would follow from S2 at S = 1 only after κ·1·dθ = κ·dθ (mul_one, not definitional in ℚ for variable κ and dθ). S1 is about real curves and does not help, so impl is not structurally derivable from the shadows. |  |
| `VolzMeyersEquations.table.VM5` | forward 1 | Formulation only (audit limitation). impl static_theta_eq states s.dθ (staticParams β γ κ hβ hγ) = -(β * s.P₁ * s.θ). S1 requires the same left-hand side to equal -β * s.P₁ * s.θ, i.e. ((-β) * P₁) * θ. The right-hand sides are equal over ℚ only via the ring lemma neg_mul (applied twice). They are not definitionally equal (rfl fails; Rat.mul normalises by gcd). The only trusted definition in the statement is VMState.dθ. A bridge dθ s p = -p.β * s.P₁ * s.θ would be the claim itself and would make the checker independent of h, so no bridge is used. The impl also names no static EBCM, so 'reduces to static EBCM' is carried only by the shadow's reading of −β P₁ θ as the static θ-equation. |  |
| `VolzMeyersEquations.table.VM5` | backward | Formulation only (audit limitation). From S1 (dθ at staticParams = (-β)·P₁·θ), the impl's right-hand side -(β·P₁·θ) follows only via neg_mul, which is not definitional over ℚ. The impl is itself the definitional unfolding of dθ at ρ = 0 (provable by rfl). A proof by rfl would ignore S1 and re-prove the impl from the definition rather than derive it from the shadow, so it was not used. |  |
| `VolzMeyersEquations.staticThetaEq-a` | forward 1 | impl static_theta_eq evaluates dθ at one swap rate only, staticParams with ρ = 0: s.dθ (staticParams β γ κ hβ hγ) = -(β·P₁·θ). S1 requires dθ to agree at two arbitrary swap rates ρ₁ and ρ₂ (independence of ρ). The impl does not state that. The equality holds only because the definition of VMState.dθ does not read p.ρ. A checker could unfold dθ at ρ₁ and ρ₂ to -(β·P₁·θ) and cite h. But h would then supply only a definitional fact (the impl is provable by rfl), and the ρ-independence would come from unfolding the definition, which is re-proving S1 without h (vacuity dodge, README limitation 1). |  |
| `VolzMeyersEquations.staticThetaEq-a` | forward 2 | S2 requires s.dθ p = s.dθ (staticParams p.β p.γ p.κ p.β_pos p.γ_pos) for every parameter set p. That is, dθ at an arbitrary swap rate equals its value at ρ = 0. impl gives only the value at ρ = 0. The value at arbitrary p, and so the equality, comes only from unfolding VMState.dθ, not from h. The term (h s p.β p.γ p.κ p.β_pos p.γ_pos).symm does type-check against S2, because s.dθ p unfolds to -(p.β·P₁·θ). But the ρ-independence content would come from that unfolding, and h (itself an rfl-provable unfolding) would supply only a definitional triviality (vacuity dodge, README limitation 1). So it was not used. |  |
| `VolzMeyersEquations.staticThetaEq-a` | backward | impl states the value -(β·P₁·θ) of dθ at ρ = 0. S1 and S2 state only that dθ does not depend on ρ. They do not determine its value: every ρ-free rate satisfies both (e.g. dθ := 0, or +β·P₁·θ), which would violate the impl. In the text the formula 'dθ/dt = −β P₁ θ' names the equation whose ρ-independence is asserted, and the shadows accordingly do not require it. The impl holds by rfl from the definition of VMState.dθ. That would re-prove the impl without the shadows and is not a derivation from S1 and S2. |  |
| `VolzMeyersEquations.fastMixingP1Equilibrium-a` | forward 1 | impl fast_mixing_P1_equilibrium states only s.P₁ = s.M₁ → p.ρ * (s.M₁ - s.P₁) = 0 (the swap term vanishes at P₁ = M₁, at a fixed ρ). No ρ → ∞ limit and no convergence P₁ → M₁ is stated. S1 requires, for every ε > 0, some R such that for all ρ > R every root x ∈ [0,1] of the Ṗ₁ right-hand side rateP1 lies within ε of M₁. That needs a quantitative estimate of the non-swap terms and an Archimedean choice of R. The impl states none of this, and none of it is structural. |  |
| `VolzMeyersEquations.fastMixingP1Equilibrium-a` | backward | impl states ρ(M₁ - P₁) = 0 whenever P₁ = M₁, for every ρ including ρ = 0. S1 is an asymptotic statement about the roots of rateP1 in ℝ for large ρ, and gives no information about the ℚ expression ρ(M₁ - P₁). The impl follows from its hypothesis only via sub_self and mul_zero over ℚ, i.e. by re-proving it without S1. |  |
| `VolzMeyersEquations.fastMixingP1Equilibrium-d` | forward 1 | impl fast_mixing_P1_equilibrium is only the algebraic fact ρ(M₁ − P₁) = 0 when P₁ = M₁; the text says 'no limit ρ → ∞ is formalised'. S1 (solutions of P′ = ρ(M₁ − P) relax to M₁ as (P(0) − M₁)e^{−ρt}) is a statement about ODE solutions that impl does not make. |  |
| `VolzMeyersEquations.fastMixingP1Equilibrium-d` | forward 2 | impl is the algebraic vanishing of the P₁ swap term. S2 (solutions of P′ = ρ(c − P), the P_S swap, relax to c at rate ρ) is about ODE solutions and about the P_S term, neither of which impl mentions. |  |
| `VolzMeyersEquations.fastMixingP1Equilibrium-d` | backward | impl (ρ(M₁ − P₁) = 0 when P₁ = M₁, over ℚ) is an algebraic identity at a state. The shadows describe real ODE solutions and do not give it. Proving it needs sub_self and mul_zero, which are not structural in any case. |  |
| `VolzMeyersEquations.table.VM8` | forward 1 | impl mass_action_incidence states only incidence = I·S for the one parameter record β = γ = κ = 1, ρ = 0 and the state (S, I, 1 − I, I, I, 0). S1 (dθ = −β·I·θ whenever P₁ = I, for all parameters) is about dθ, which impl does not mention. Also dθ is −(β·P₁·θ), which equals −β·I·θ only by neg_mul (not definitional in ℚ). |  |
| `VolzMeyersEquations.table.VM8` | forward 2 | S2 (dI = β·I·θ − γ·I whenever κ = 1 and P₁ = I, for all β, γ, ρ) is universal over parameters. impl covers only β = γ = κ = 1, ρ = 0 and states incidence = I·S rather than dI. Even at those parameters, β·I·θ·1 = β·I·θ needs mul_one (not definitional in ℚ). |  |
| `VolzMeyersEquations.table.VM8` | forward 3 | S3 (dR = γ·I) is the definition of VMState.dR (rfl). impl does not state it, so a checker could only prove S3 without h (vacuous). |  |
| `VolzMeyersEquations.table.VM8` | backward | impl (incidence = I·S at the specific record) does not follow structurally from the shadows. S2 at that record gives incidence − 1·I = 1·I·S − 1·I, and cancelling needs sub_left_inj / one_mul in ℚ, which are not structural. |  |
| `VolzMeyersEquations.massActionIncidence-a` | forward 1 | impl mass_action_incidence states only incidence = I·S for the single record β = γ = κ = 1, ρ = 0. S1 (dθ = −β·I·θ whenever P₁ = I) is about dθ, which impl does not mention; dθ is −(β·P₁·θ), equal to −β·I·θ only by neg_mul. |  |
| `VolzMeyersEquations.massActionIncidence-a` | forward 2 | S2 (dI = β·I·θ − γ·I for κ = 1 and P₁ = I, all β, γ) is universal over parameters. impl covers only β = γ = κ = 1, ρ = 0 and states incidence rather than dI; β·I·θ·1 = β·I·θ needs mul_one. |  |
| `VolzMeyersEquations.massActionIncidence-a` | forward 3 | S3 (dR = γ·I) is the definition of VMState.dR (rfl). impl does not state it, so a checker could only prove S3 without h (vacuous). |  |
| `VolzMeyersEquations.massActionIncidence-a` | forward 4 | S4 (for ψ(x) = x, the M₁ equation −γM₁ + βP₁θ equals dI when M₁ = I) relates the M₁ and I equations of the model. impl states only the incidence value at one record, and matching β·P₁·θ with β·P₁·θ·κ at κ = 1 needs mul_one. |  |
| `VolzMeyersEquations.massActionIncidence-a` | backward | impl (incidence = I·S at the specific record) is not structurally derivable from the shadows. S2 at that record gives dI = 1·I·S − 1·I, and extracting incidence = I·S needs cancellation (sub_left_inj) and one_mul in ℚ. |  |
| `VolzMeyersEquations.massActionIncidence-b` | forward 1 | impl fixes β = 1, together with γ = 1, κ = 1 and ρ = 0, and a single state shape ⟨S, I, 1-I, I, I, 0⟩ (P_S = 1-I, M₁ = I, R = 0). S1 requires incidence = β·I·θ for every β and every state and parameter set with P₁ = I and κ = 1. The impl gives nothing for β ≠ 1 or for other P_S, M₁, R, γ, ρ. The general identity holds only from the definition incidence = β·P₁·θ·κ with the rewrite P₁ = I and mul_one (not definitional over ℚ), so it would be re-proved without h. |  |
| `VolzMeyersEquations.massActionIncidence-b` | backward | Formulation only (audit limitation). S1 at the impl's state ⟨S, I, 1-I, I, I, 0⟩ and parameters ⟨1, 1, 0, 1, …⟩ (κ = 1 and P₁ = I hold by rfl) gives incidence = 1·I·S. The impl states incidence = I·S. The step 1·I·S = I·S is one_mul over ℚ. It is not definitional (rfl fails, because Rat.mul normalises by gcd) and not structural, and no trusted definition could carry it in a bridge. |  |

Check statuses: `pass` (exact statement, structural, not vacuous), `fail` (wrong statement or recorded failure), `vacuous`, `audit_violation` (offenders listed), `sorry`, `missing`. Passes whose shadows were written after seeing the implementation are weak passes.
