-- Categorical Foundations of Edge-Based Compartmental Models
-- Core categorical infrastructure
import EBCMCategory.EpiCategory
import EBCMCategory.CoarseGrain
-- Galois connection and adjunction
import EBCMCategory.GaloisPair
-- Obstructions to edge-based modelling
import EBCMCategory.Obstructions
-- Model hierarchy
import EBCMCategory.Hierarchy
-- Dynamic network limits
import EBCMCategory.DynamicLimits
-- EBCM ↔ DSA survival analysis bridge
import EBCMCategory.SurvivalBridge
-- Exact pairwise closure characterization
import EBCMCategory.ClosureTheorem
-- Message passing ↔ EBCM ↔ Pairwise hierarchy
import EBCMCategory.MessagePassingBridge
-- Clustering extension for bivariate PGF framework
import EBCMCategory.ClusteringExtension
-- Method of stages for non-exponential sojourn times
import EBCMCategory.MethodOfStages
-- Degree correlation and assortative mixing
import EBCMCategory.DegreeCorrelation
-- Convergence and exactness theorems
import EBCMCategory.ConvergenceTheorems
-- Conditional positivity / conservation for normalized pairwise closures
import EBCMCategory.PairwiseClosureConditions
-- Positivity and invariant-region guarantees for the EBCM ODE system
import EBCMCategory.InvariantRegion
-- Categorical composition: products, coproducts, natural transformations
import EBCMCategory.CategoricalComposition
-- Subgraph-marginalisation functor and the equivariance theorem (T1)
import EBCMCategory.MarginalisationFunctor
-- Structural characterization of marginalisation equivariance (T3)
import EBCMCategory.MarginalisationCharacterization
-- Dynamical gap and refinement failure (T4–T6)
import EBCMCategory.MarginalisationDynamicalGap
