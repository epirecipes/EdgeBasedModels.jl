import EBCMCategory.CoarseGrain
import Mathlib.Tactic

/-!
# Hierarchy — The tower of epidemic model approximations

Epidemic models are compared here by the state-space dimension of an
N-node SIR network model (`levelDim`):

    Full stochastic (3^N)  >  Pair approximation (12N)  >  EBCM (4)  >  Mean-field SIR (3)

The first inequality holds only for N ≥ 4 (`pair_lt_full`); for N = 3,
3³ = 27 < 36 = 12·3 (`full_lt_pair_three`). The comparison is by
dimension only: no coarse-graining map between the levels is formalised.

## Key results

| Result | Statement                                           |
|--------|-----------------------------------------------------|
| 23     | Mean-field < EBCM                                    |
| 24     | EBCM < Pair approximation (for N ≥ 1)               |
| 25     | EBCM → Mean-field is exact for Poisson networks      |
| 26     | Every node model has a canonical Poisson lift         |
| 27     | Excess = mean forces variance = mean (records only)   |
| 28     | A Poisson-record lift exists; R₀ kept iff excess = κ  |

## References

* Kiss, Miller, Simon (2017). Mathematics of Epidemics on Networks.
-/

/-! ## Model levels -/

/-- Levels in the modelling hierarchy. -/
inductive ModelLevel where
  | fullStochastic
  | pairApproximation
  | edgeBased
  | meanField
  deriving DecidableEq, Repr

/-- State-space dimension at each level for an N-node SIR network model. -/
def levelDim (level : ModelLevel) (N : ℕ) : ℕ :=
  match level with
  | .fullStochastic    => 3 ^ N
  | .pairApproximation => 12 * N
  | .edgeBased         => 4
  | .meanField         => 3

/-! ## Strict hierarchy -/

/-- **Result 23.** Mean-field has fewer variables than EBCM. -/
theorem meanField_lt_edgeBased (N : ℕ) :
    levelDim .meanField N < levelDim .edgeBased N := by
  simp [levelDim]

/-- **Result 24.** EBCM has fewer variables than pair approximation for N ≥ 1. -/
theorem edgeBased_lt_pair (N : ℕ) (hN : 1 ≤ N) :
    levelDim .edgeBased N < levelDim .pairApproximation N := by
  simp [levelDim]
  omega

/-! ## Exactness conditions -/

/-- **Result 25.** The EBCM → Mean-field step is exact iff Poisson.
    The Lean theorem proves only the algebraic consequence for the Poisson
    record, ψ''(1)/ψ'(1) = ψ'(1). The dynamical statement (the EBCM has
    mass-action form iff ψ' = κψ, i.e. iff ψ is Poisson; Rempała 2023) is
    not formalised. -/
theorem ebcm_to_meanfield_exact_iff_poisson (κ : ℚ) (hκ : 0 < κ) :
    (PGFData.poisson κ hκ).excessDegree = (PGFData.poisson κ hκ).mean := by
  exact PGFData.poisson_excess_eq_mean κ hκ

/-! ## The inverse problem: Node → Edge -/

/-- **Result 26.** Every node model lifts to an edge model via Poisson,
    preserving R₀. -/
theorem node_lifts_to_edge (p : SIRParams) (κ : ℚ) (hκ : 0 < κ) :
    (nodeModel p κ).R0 = (edgeModel p (PGFData.poisson κ hκ)).R0 :=
  poisson_R0_agree p κ hκ

/-- **Result 27.** For a two-moment record with mean κ, excess degree = mean
    forces variance = mean, so the record is the Poisson record `poisson κ`
    (`PGFData.dispersionIndex_eq_one_iff`).
    This does not make Poisson the unique degree distribution with excess
    degree = mean: ψ(u) = (1 + u²)/2 has ψ''(1)/ψ'(1) = 1 = ψ'(1) and is not
    Poisson. -/
theorem poisson_unique_exact_lift (κ : ℚ) (_hκ : 0 < κ) (ψ : PGFData)
    (h_mean : ψ.mean = κ)
    (h_excess : ψ.excessDegree = κ) :
    ψ.variance = κ := by
  have h_decomp := excess_degree_decomposition ψ
  rw [h_excess, h_mean] at h_decomp
  -- From κ = κ - 1 + σ²/κ we get σ²/κ = 1, so σ² = κ
  have h_disp : ψ.dispersionIndex = 1 := by linarith
  -- dispersionIndex = variance / mean = 1, so variance = mean = κ
  have hm : ψ.mean ≠ 0 := ne_of_gt ψ.mean_pos
  simp only [PGFData.dispersionIndex] at h_disp
  have := div_eq_one_iff_eq hm |>.mp h_disp
  linarith [h_mean]

/-- **Result 28.** Some PGF record with mean κ (the Poisson record) gives an
    edge model with R₀ = T·ψ''(1)/ψ'(1).
    Matching the mean does not preserve R₀: the edge model of a record ψ has
    the node model's R₀ T·κ iff ψ''(1)/ψ'(1) = κ (`edge_lift_R0_eq_iff`). -/
theorem lift_space_parameterised (p : SIRParams) (κ : ℚ) (hκ : 0 < κ) :
    ∃ (ψ : PGFData), ψ.mean = κ ∧
      (edgeModel p ψ).R0 = p.transmissibility * ψ.excessDegree :=
  ⟨PGFData.poisson κ hκ, rfl, rfl⟩

/-- The edge model of a record ψ has the R₀ of the node model with mean degree
    κ iff ψ''(1)/ψ'(1) = κ. -/
theorem edge_lift_R0_eq_iff (p : SIRParams) (κ : ℚ) (ψ : PGFData) :
    (edgeModel p ψ).R0 = (nodeModel p κ).R0 ↔ ψ.excessDegree = κ := by
  simp only [edgeModel, nodeModel]
  exact mul_right_inj' (ne_of_gt p.transmissibility_pos)

/-! ## Dimension comparisons -/

/-- The pair approximation has fewer variables than the full stochastic
    model for N ≥ 4: 12N < 3^N. -/
theorem pair_lt_full (N : ℕ) (hN : 4 ≤ N) :
    levelDim .pairApproximation N < levelDim .fullStochastic N := by
  simp only [levelDim]
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    nlinarith [ih, hn]

/-- For N = 3 the full stochastic model has fewer variables than the pair
    approximation: 3³ = 27 < 36 = 12·3. -/
theorem full_lt_pair_three :
    levelDim .fullStochastic 3 < levelDim .pairApproximation 3 := by
  simp only [levelDim]
  norm_num
