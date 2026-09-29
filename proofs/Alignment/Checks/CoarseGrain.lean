import Alignment.Registry
import Alignment.Shadows.CoarseGrain

/-!
# Checkers: group `CoarseGrain`

Checker author (SA-PASS role 3, non-blind). For every claim of `EBCMCategory/CoarseGrain.lean`
with `status: implemented` this file holds the `sa_claim` registration (verbatim registry text,
registry `impl` list in registry order), the forward checkers `sa_impl% → Sᵢ`, the backward checker
`S₁ → … → Sₙ → sa_impl%`, and `sa_fail_*` records where a check cannot be proved structurally
because the implementation says something different from the shadow.

No bridges are declared. The trusted definitions are used exactly as the shadows use them:
`coarseGrain e := ⟨3, e.R0⟩`, the `Preorder EpiModel` instance (`m₁ ≤ m₂ := m₁.dim ≤ m₂.dim`),
`PGFData.excessDegree ψ := ψ.secondFactorial / ψ.mean`,
`PGFData.dispersionIndex ψ := ψ.variance / ψ.mean` and `PGFData.poisson κ hκ` (mean κ). Every
passing check therefore needs only the hypotheses, `Exists.elim`/`And` projections and definitional
unfolding (`Monotone`, `excessDegree`, `dispersionIndex`).

Summary of recorded failures: the two "not injective" claims (`table.R6`, `R6`). The impl
`coarseGrain_not_injective` is the constructive witness form `∃ e₁ e₂, e₁ ≠ e₂ ∧ F e₁ = F e₂`, and
the shadow is `¬ ∀ m m', F m = F m' → m = m'`. The forward checks pass. The backward checks are
recorded as `sa_fail_backward`, because `¬ ∀ → ∃ ¬` needs classical logic. The two forms are
classically equivalent, so this is not an overclaim of the text. The backward check could be made
to pass by re-proving the impl from scratch (a closed kernel computation separating `4` and `10`,
README "Known limitations" 1), with `s1` used only decoratively. That was deliberately not done.
-/

/-! ## Header table rows -/

namespace Alignment.Shadows.CoarseGrain.table_R5

sa_claim "CoarseGrain.table.R5" group "CoarseGrain" required
  text "| 5 | F is a monotone map (preserves refinement) |"
  impl coarseGrain_mono

/-- `Monotone coarseGrain` unfolds to `∀ ⦃a b⦄, a ≤ b → coarseGrain a ≤ coarseGrain b`. -/
@[sa_forward "CoarseGrain.table.R5" 1]
theorem fwd1 (h : sa_impl% "CoarseGrain.table.R5") : S1 := by
  intro m m' hle
  exact h hle

@[sa_backward "CoarseGrain.table.R5"]
theorem bwd (s1 : S1) : sa_impl% "CoarseGrain.table.R5" := by
  intro a b hab
  exact s1 a b hab

end Alignment.Shadows.CoarseGrain.table_R5

namespace Alignment.Shadows.CoarseGrain.table_R6

sa_claim "CoarseGrain.table.R6" group "CoarseGrain" required
  text "| 6 | F is not injective (lossy) |"
  impl coarseGrain_not_injective

/-- A collision `e₁ ≠ e₂`, `F e₁ = F e₂` refutes injectivity at `(e₁, e₂)`. -/
@[sa_forward "CoarseGrain.table.R6" 1]
theorem fwd1 (h : sa_impl% "CoarseGrain.table.R6") : S1 :=
  fun hinj => Exists.elim h fun e₁ he => Exists.elim he fun e₂ hp => hp.1 (hinj e₁ e₂ hp.2)

sa_fail_backward "CoarseGrain.table.R6" "impl is constructively stronger than S1: coarseGrain_not_injective is the witness form ∃ e₁ e₂ : EpiModel, e₁ ≠ e₂ ∧ coarseGrain e₁ = coarseGrain e₂, while S1 is ¬ (∀ m m', coarseGrain m = coarseGrain m' → m = m'). Getting the witnesses from the negated universal (¬ ∀ → ∃ ¬, then ¬ (A → B) → A ∧ ¬ B) needs classical logic (Classical.byContradiction / Decidable), which is not structural. The only other route is to re-prove the impl from scratch: pick ⟨4, 1⟩, ⟨10, 1⟩ and separate them by a closed kernel computation on ℕ (Nat.beq/Bool.rec), with s1 used only decoratively. That re-proves the impl instead of deriving it from S1, so it is not used. The two forms are classically equivalent and the text's '(lossy)' fits the witness form, so this is a constructive-strength gap, not an overclaim. Remediation: add a trusted theorem ¬ Function.Injective coarseGrain (derived from the witness) as impl. Its forward and backward checks are then structural."

end Alignment.Shadows.CoarseGrain.table_R6

namespace Alignment.Shadows.CoarseGrain.table_R7

sa_claim "CoarseGrain.table.R7" group "CoarseGrain" required
  text "| 7 | Degree-variance inequality: excess = κ-1+σ²/κ |"
  impl excess_degree_decomposition

/-- `ψ.dispersionIndex` unfolds definitionally to `ψ.variance / ψ.mean`. -/
@[sa_forward "CoarseGrain.table.R7" 1]
theorem fwd1 (h : sa_impl% "CoarseGrain.table.R7") : S1 :=
  fun ψ => h ψ

/-- In addition, `ψ.excessDegree` unfolds definitionally to `ψ.secondFactorial / ψ.mean`. -/
@[sa_forward "CoarseGrain.table.R7" 2]
theorem fwd2 (h : sa_impl% "CoarseGrain.table.R7") : S2 :=
  fun ψ => h ψ

@[sa_backward "CoarseGrain.table.R7"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "CoarseGrain.table.R7" :=
  fun ψ => s1 ψ

end Alignment.Shadows.CoarseGrain.table_R7

namespace Alignment.Shadows.CoarseGrain.table_R8

sa_claim "CoarseGrain.table.R8" group "CoarseGrain" required
  text "| 8 | Poisson dispersion = 1 |"
  impl poisson_dispersion_eq_one

@[sa_forward "CoarseGrain.table.R8" 1]
theorem fwd1 (h : sa_impl% "CoarseGrain.table.R8") : S1 :=
  fun κ hκ => h κ hκ

/-- `(PGFData.poisson κ hκ).dispersionIndex` unfolds definitionally to `variance / mean`. -/
@[sa_forward "CoarseGrain.table.R8" 2]
theorem fwd2 (h : sa_impl% "CoarseGrain.table.R8") : S2 :=
  fun κ hκ => h κ hκ

@[sa_backward "CoarseGrain.table.R8"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "CoarseGrain.table.R8" :=
  fun κ hκ => s1 κ hκ

end Alignment.Shadows.CoarseGrain.table_R8

/-! ## Theorem docstrings -/

namespace Alignment.Shadows.CoarseGrain.R5

sa_claim "CoarseGrain.R5" group "CoarseGrain" required
  text "**Result 5.** F is monotone."
  impl coarseGrain_mono

@[sa_forward "CoarseGrain.R5" 1]
theorem fwd1 (h : sa_impl% "CoarseGrain.R5") : S1 := by
  intro m m' hle
  exact h hle

@[sa_backward "CoarseGrain.R5"]
theorem bwd (s1 : S1) : sa_impl% "CoarseGrain.R5" := by
  intro a b hab
  exact s1 a b hab

end Alignment.Shadows.CoarseGrain.R5

namespace Alignment.Shadows.CoarseGrain.coarseGrainPreservesR0

sa_claim "CoarseGrain.coarseGrainPreservesR0" group "CoarseGrain" required
  text "F preserves R₀."
  impl coarseGrain_preserves_R0

@[sa_forward "CoarseGrain.coarseGrainPreservesR0" 1]
theorem fwd1 (h : sa_impl% "CoarseGrain.coarseGrainPreservesR0") : S1 :=
  fun m => h m

@[sa_backward "CoarseGrain.coarseGrainPreservesR0"]
theorem bwd (s1 : S1) : sa_impl% "CoarseGrain.coarseGrainPreservesR0" :=
  fun e => s1 e

end Alignment.Shadows.CoarseGrain.coarseGrainPreservesR0

namespace Alignment.Shadows.CoarseGrain.R6

sa_claim "CoarseGrain.R6" group "CoarseGrain" required
  text "**Result 6.** F is not injective."
  impl coarseGrain_not_injective

/-- A collision `e₁ ≠ e₂`, `F e₁ = F e₂` refutes injectivity at `(e₁, e₂)`. -/
@[sa_forward "CoarseGrain.R6" 1]
theorem fwd1 (h : sa_impl% "CoarseGrain.R6") : S1 :=
  fun hinj => Exists.elim h fun e₁ he => Exists.elim he fun e₂ hp => hp.1 (hinj e₁ e₂ hp.2)

sa_fail_backward "CoarseGrain.R6" "impl is constructively stronger than S1: coarseGrain_not_injective is the witness form ∃ e₁ e₂ : EpiModel, e₁ ≠ e₂ ∧ coarseGrain e₁ = coarseGrain e₂, while S1 (the text 'F is not injective', read literally) is ¬ (∀ m m', coarseGrain m = coarseGrain m' → m = m'). Getting the witnesses from the negated universal (¬ ∀ → ∃ ¬, then ¬ (A → B) → A ∧ ¬ B) needs classical logic (Classical.byContradiction / Decidable), which is not structural. The only other route is to re-prove the impl from scratch: pick ⟨4, 1⟩, ⟨10, 1⟩ and separate them by a closed kernel computation on ℕ (Nat.beq/Bool.rec), with s1 used only decoratively. That re-proves the impl instead of deriving it from S1, so it is not used. The two forms are classically equivalent, so this is a constructive-strength gap, not an overclaim. Remediation: add a trusted theorem ¬ Function.Injective coarseGrain (derived from the witness) as impl. Its forward and backward checks are then structural."

end Alignment.Shadows.CoarseGrain.R6

namespace Alignment.Shadows.CoarseGrain.R7

sa_claim "CoarseGrain.R7" group "CoarseGrain" required
  text "**Result 7.** The excess degree ratio decomposes as: ψ''(1)/ψ'(1) = κ - 1 + σ²/κ"
  impl excess_degree_decomposition

/-- `ψ.excessDegree` unfolds to `ψ.secondFactorial / ψ.mean` and `ψ.dispersionIndex` to
`ψ.variance / ψ.mean`, both definitionally. -/
@[sa_forward "CoarseGrain.R7" 1]
theorem fwd1 (h : sa_impl% "CoarseGrain.R7") : S1 :=
  fun ψ => h ψ

/-- `ψ.dispersionIndex` unfolds definitionally to `ψ.variance / ψ.mean`. -/
@[sa_forward "CoarseGrain.R7" 2]
theorem fwd2 (h : sa_impl% "CoarseGrain.R7") : S2 :=
  fun ψ => h ψ

@[sa_backward "CoarseGrain.R7"]
theorem bwd (_s1 : S1) (s2 : S2) : sa_impl% "CoarseGrain.R7" :=
  fun ψ => s2 ψ

end Alignment.Shadows.CoarseGrain.R7

namespace Alignment.Shadows.CoarseGrain.R8

sa_claim "CoarseGrain.R8" group "CoarseGrain" required
  text "**Result 8.** For Poisson, the dispersion index equals 1."
  impl poisson_dispersion_eq_one

@[sa_forward "CoarseGrain.R8" 1]
theorem fwd1 (h : sa_impl% "CoarseGrain.R8") : S1 :=
  fun κ hκ => h κ hκ

/-- `(PGFData.poisson κ hκ).dispersionIndex` unfolds definitionally to `variance / mean`. -/
@[sa_forward "CoarseGrain.R8" 2]
theorem fwd2 (h : sa_impl% "CoarseGrain.R8") : S2 :=
  fun κ hκ => h κ hκ

@[sa_backward "CoarseGrain.R8"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "CoarseGrain.R8" :=
  fun κ hκ => s1 κ hκ

end Alignment.Shadows.CoarseGrain.R8
