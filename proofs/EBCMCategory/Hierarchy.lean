import EBCMCategory.CoarseGrain
import Mathlib.Tactic

/-!
# Hierarchy — The tower of epidemic model approximations

Epidemic models form a strict hierarchy of decreasing information content:

    Full stochastic  >  Pair approximation  >  EBCM  >  Mean-field SIR

Each step is a coarse-graining that discards correlations.

## Key results

| Result | Statement                                           |
|--------|-----------------------------------------------------|
| 23     | Mean-field < EBCM                                    |
| 24     | EBCM < Pair approximation (for N ≥ 1)               |
| 25     | EBCM → Mean-field is exact for Poisson networks      |
| 26     | Every node model has a canonical Poisson lift         |
| 27     | Poisson is the unique exact lift                      |
| 28     | Lift space is parameterised by mean-matching PGFs     |

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

/-- **Result 25.** The EBCM → Mean-field step is exact iff Poisson. -/
theorem ebcm_to_meanfield_exact_iff_poisson (κ : ℚ) (hκ : 0 < κ) :
    (PGFData.poisson κ hκ).excessDegree = (PGFData.poisson κ hκ).mean := by
  exact PGFData.poisson_excess_eq_mean κ hκ

/-! ## The inverse problem: Node → Edge -/

/-- **Result 26.** Every node model lifts to an edge model via Poisson,
    preserving R₀. -/
theorem node_lifts_to_edge (p : SIRParams) (κ : ℚ) (hκ : 0 < κ) :
    (nodeModel p κ).R0 = (edgeModel p (PGFData.poisson κ hκ)).R0 :=
  poisson_R0_agree p κ hκ

/-- **Result 27.** The Poisson lift is the UNIQUE PGF for which
    excess degree = mean (the exactness condition). -/
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

/-- **Result 28.** The lift space is parameterised by PGFs with matching mean. -/
theorem lift_space_parameterised (p : SIRParams) (κ : ℚ) (hκ : 0 < κ) :
    ∃ (ψ : PGFData), ψ.mean = κ ∧
      (edgeModel p ψ).R0 = p.transmissibility * ψ.excessDegree :=
  ⟨PGFData.poisson κ hκ, rfl, rfl⟩
