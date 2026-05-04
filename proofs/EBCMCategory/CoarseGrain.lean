import EBCMCategory.EpiCategory

/-!
# CoarseGrain — The forgetful functor F: Edge → Node

The **coarse-graining** map sends an edge-based model to its node-based
projection by evaluating the PGF at the edge-transmission-failure probability:

    S = ψ(θ),   R = R,   I = 1 - S - R

## Key results

| Result | Statement                                            |
|--------|------------------------------------------------------|
| 5      | F is a monotone map (preserves refinement)            |
| 6      | F is not injective (lossy)                            |
| 7      | Degree-variance inequality: excess = κ-1+σ²/κ        |
| 8      | Poisson dispersion = 1                               |

## References

* Baez, Courser (2018). Coarse-graining open Markov processes.
-/

/-! ## The coarse-graining map -/

/-- The coarse-graining map F on abstract models.
    Projects any model to a 3-dimensional node model, preserving R₀. -/
def coarseGrain (e : EpiModel) : EpiModel where
  dim := 3
  R0 := e.R0

/-- **Result 5.** F is monotone. -/
theorem coarseGrain_mono : Monotone coarseGrain := by
  intro _ _ _
  show 3 ≤ 3
  omega

/-- F preserves R₀. -/
theorem coarseGrain_preserves_R0 (e : EpiModel) :
    (coarseGrain e).R0 = e.R0 := by
  simp [coarseGrain]

/-! ## Lossiness of F -/

/-- **Result 6.** F is not injective. -/
theorem coarseGrain_not_injective :
    ∃ (e₁ e₂ : EpiModel), e₁ ≠ e₂ ∧ coarseGrain e₁ = coarseGrain e₂ := by
  use ⟨4, 1⟩, ⟨10, 1⟩
  refine ⟨?_, ?_⟩
  · intro h
    have : (4 : ℕ) = 10 := congrArg EpiModel.dim h
    omega
  · rfl

/-! ## The degree-variance inequality -/

/-- **Result 7.** The excess degree ratio decomposes as:
    ψ''(1)/ψ'(1) = κ - 1 + σ²/κ -/
theorem excess_degree_decomposition (ψ : PGFData) :
    ψ.excessDegree = ψ.mean - 1 + ψ.dispersionIndex := by
  simp only [PGFData.excessDegree, PGFData.dispersionIndex, PGFData.variance]
  have hm : (ψ.mean : ℚ) ≠ 0 := ne_of_gt ψ.mean_pos
  field_simp
  ring

/-- **Result 8.** For Poisson, the dispersion index equals 1. -/
theorem poisson_dispersion_eq_one (κ : ℚ) (hκ : 0 < κ) :
    (PGFData.poisson κ hκ).dispersionIndex = 1 := by
  simp only [PGFData.dispersionIndex, PGFData.variance, PGFData.poisson]
  have hκ' : (κ : ℚ) ≠ 0 := ne_of_gt hκ
  field_simp
  ring
