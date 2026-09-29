import Alignment.Registry
import Alignment.Shadows.DynamicLimits
import Mathlib.Tactic.NormNum   -- only for the positivity fields inside the R37 witness *data*

/-!
# Checkers: group `DynamicLimits`

Registrations, checkers and failure records for the claims of `EBCMCategory/DynamicLimits.lean`
(shadows: `Alignment/Shadows/DynamicLimits.lean`, written blind).

No bridges are needed: every identification of a trusted definition with the text's notion that
the shadows use is definitional (`m.dim ≡ m.toEpiModel.dim ≡ 5`, `m.staticLimit ≡ edgeModel
m.disease m.pgf`, `m.toEpiModel.R0 ≡ m.R0`, `levelDim .pairApproximation N ≡ 12 * N`,
`PGFData.excessDegree ψ ≡ ψ.secondFactorial / ψ.mean`, `(PGFData.poisson κ hκ).mean ≡ κ`).

Policy for the recorded failures. Many shadows require a dimension *value* that the text writes
in parentheses ("(dim 5)", "(dim 4)", "both give dim 3", "5 > 4"). Every such value holds by the
*definition* (`DynamicEBCM.dim _ := 5`, `toEpiModel.dim := 5`, `edgeModel.dim := 4`,
`fastRewiringLimit.dim := 3`, `coarseGrain.dim := 3`), i.e. by `rfl` without the hypothesis. When
the claim's implementation theorem does not itself assert that value, a checker could only be
vacuous or thread `h` through spuriously (README, known limitation 1), so the check is recorded
as `sa_fail_forward` ("impl does not assert …") instead. Nat order facts (`<`, `≤` on dims) are
never derivable structurally from equations, and the `EpiModel` preorder's `<` (Preorder
default `a ≤ b ∧ ¬ b ≤ a`) is not structurally interchangeable with Nat `<` on dims.
-/

namespace Alignment.Checks.DynamicLimits

/-- R37 backward witness: a degree record with mean 1 and second factorial moment 0 (so it is
not `PGFData.poisson κ _` for any κ, which would need secondFactorial = κ² = 1). The positivity
fields are proofs inside data (skipped by the structural audit; irrelevant by proof
irrelevance). -/
def witnessPGF : PGFData := ⟨1, 0, by norm_num, le_refl 0⟩

/-- R37 backward witness: β = γ = 1. -/
def witnessSIR : SIRParams := ⟨1, 1, by norm_num, by norm_num⟩

/-- R37 backward witness: the dynamic EBCM on `witnessPGF`. -/
def witness : DynamicEBCM := ⟨witnessSIR, witnessPGF⟩

/-- A data-level separator of the rationals 0 and 1 (kernel computation on `Rat.num`): it is
`True` at 0 and `False` at 1. -/
def sepZeroOne (q : ℚ) : Prop :=
  Nat.casesOn (motive := fun _ => Prop) q.num.natAbs True (fun _ => False)

/-- The witness is non-Poisson in the shadows' sense: `m.pgf ≠ PGFData.poisson κ hκ` for every
κ > 0. Structural: projections `mean`/`secondFactorial` of the equation, transport of κ to 1,
and the separator (0 = 1² is refuted by kernel computation). -/
theorem witness_nonPoisson : ∀ (κ : ℚ) (hκ : 0 < κ), witness.pgf ≠ PGFData.poisson κ hκ := by
  intro κ hκ heq
  have h1 : (1 : ℚ) = κ := congrArg PGFData.mean heq
  have h2 : (0 : ℚ) = κ ^ 2 := congrArg PGFData.secondFactorial heq
  have h3 : (0 : ℚ) = (1 : ℚ) ^ 2 := @Eq.ndrec ℚ κ (fun x => (0 : ℚ) = x ^ 2) h2 1 h1.symm
  exact Eq.mp (congrArg sepZeroOne h3) True.intro

end Alignment.Checks.DynamicLimits

/-! ## header.interpolation (`sa_impl%` = `fast_rewiring_dim ∧ static_limit_dim ∧ full_tower`) -/
namespace Alignment.Shadows.DynamicLimits.header_interpolation

sa_claim "DynamicLimits.header.interpolation" group "DynamicLimits" required
  text "The dynamic model thus interpolates between two extremes: MFSH (dim 3 as recorded) ← fast rewiring — Dynamic (dim 5) — static → EBCM (dim 4)"
  impl fast_rewiring_dim static_limit_dim full_tower

@[sa_forward "DynamicLimits.header.interpolation" 1]
theorem fwd1 (h : sa_impl% "DynamicLimits.header.interpolation") : S1 := fun m => h.1 m

sa_fail_forward "DynamicLimits.header.interpolation" 2 "S2 (DynamicEBCM.dim m = 5) is the definition of DynamicEBCM.dim (rfl). impl (fast_rewiring_dim ∧ static_limit_dim ∧ full_tower) never mentions DynamicEBCM.dim, so a checker could only prove S2 without h (vacuous)."

sa_fail_forward "DynamicLimits.header.interpolation" 3 "impl gives only the strict inequality staticLimit.dim < toEpiModel.dim (full_tower) and staticLimit.dim = 4, which leave toEpiModel.dim = 5 undetermined. The equality holds by the definition of toEpiModel (rfl), so a checker could only prove S3 without h (vacuous)."

@[sa_forward "DynamicLimits.header.interpolation" 4]
theorem fwd4 (h : sa_impl% "DynamicLimits.header.interpolation") : S4 := fun m => h.2.1 m

sa_fail_backward "DynamicLimits.header.interpolation" "The first two conjuncts of impl are S1 and S4. The third (full_tower: 3 < 4 and 4 < 5 after rewriting with S1, S3, S4) needs closed strict inequalities in ℕ. Nat.lt is the core inductive Nat.le, whose constructors are core-library proofs (and decide is forbidden), so a structural checker cannot prove them. This is an audit limitation on closed ℕ arithmetic, not a semantic difference."

end Alignment.Shadows.DynamicLimits.header_interpolation

/-! ## Header table rows -/

namespace Alignment.Shadows.DynamicLimits.table_R29

sa_claim "DynamicLimits.table.R29" group "DynamicLimits" required
  text "| 29 | Static EBCM dim < Dynamic EBCM dim |"
  impl static_lt_dynamic

/-- `m.dim` and `m.toEpiModel.dim` are both definitionally 5 (two definitions of the dynamic
dimension), so the impl statement is `S1` up to unfolding. -/
@[sa_forward "DynamicLimits.table.R29" 1]
theorem fwd1 (h : sa_impl% "DynamicLimits.table.R29") : S1 :=
  fun m => h m

@[sa_forward "DynamicLimits.table.R29" 2]
theorem fwd2 (h : sa_impl% "DynamicLimits.table.R29") : S2 :=
  fun m => h m

@[sa_backward "DynamicLimits.table.R29"]
theorem bwd (_s1 : S1) (s2 : S2) : sa_impl% "DynamicLimits.table.R29" :=
  fun m => s2 m

end Alignment.Shadows.DynamicLimits.table_R29

namespace Alignment.Shadows.DynamicLimits.table_R30

sa_claim "DynamicLimits.table.R30" group "DynamicLimits" required
  text "| 30 | Dynamic EBCM dim < Pair approximation dim (N ≥ 1) |"
  impl dynamic_lt_pair

/-- `levelDim ModelLevel.pairApproximation N` reduces to `12 * N` and `m.dim` to 5. -/
@[sa_forward "DynamicLimits.table.R30" 1]
theorem fwd1 (h : sa_impl% "DynamicLimits.table.R30") : S1 :=
  fun m N hN => h m N hN

@[sa_forward "DynamicLimits.table.R30" 2]
theorem fwd2 (h : sa_impl% "DynamicLimits.table.R30") : S2 :=
  fun m N hN => h m N hN

@[sa_forward "DynamicLimits.table.R30" 3]
theorem fwd3 (h : sa_impl% "DynamicLimits.table.R30") : S3 :=
  fun m N hN => h m N hN

@[sa_forward "DynamicLimits.table.R30" 4]
theorem fwd4 (h : sa_impl% "DynamicLimits.table.R30") : S4 :=
  fun m N hN => h m N hN

@[sa_backward "DynamicLimits.table.R30"]
theorem bwd (_s1 : S1) (_s2 : S2) (_s3 : S3) (s4 : S4) : sa_impl% "DynamicLimits.table.R30" :=
  fun m N hN => s4 m N hN

end Alignment.Shadows.DynamicLimits.table_R30

namespace Alignment.Shadows.DynamicLimits.table_R31

sa_claim "DynamicLimits.table.R31" group "DynamicLimits" required
  text "| 31 | Static limit: dynamic → static (dim 5 → 4) |"
  impl static_limit_dim

sa_fail_forward "DynamicLimits.table.R31" 1 "impl static_limit_dim asserts only the target dimension m.staticLimit.dim = 4; the source dimension in 'dim 5 → 4' (S1: m.dim = 5) is not asserted and holds only by the definition DynamicEBCM.dim _ := 5 (rfl, independent of h)."

sa_fail_forward "DynamicLimits.table.R31" 2 "impl static_limit_dim asserts only the target dimension m.staticLimit.dim = 4; the source dimension in 'dim 5 → 4' (S2: m.toEpiModel.dim = 5) is not asserted and holds only by the definition toEpiModel.dim := 5 (rfl, independent of h)."

@[sa_forward "DynamicLimits.table.R31" 3]
theorem fwd3 (h : sa_impl% "DynamicLimits.table.R31") : S3 :=
  fun m => h m

@[sa_backward "DynamicLimits.table.R31"]
theorem bwd (_s1 : S1) (_s2 : S2) (s3 : S3) : sa_impl% "DynamicLimits.table.R31" :=
  fun m => s3 m

end Alignment.Shadows.DynamicLimits.table_R31

/-! ## table.R32 -/
namespace Alignment.Shadows.DynamicLimits.table_R32

sa_claim "DynamicLimits.table.R32" group "DynamicLimits" required
  text "| 32 | Fast-rewiring limit record: dim 5 → 3 |"
  impl fast_rewiring_dim

sa_fail_forward "DynamicLimits.table.R32" 1 "S1 (toEpiModel.dim = 5) holds by the definition of DynamicEBCM.toEpiModel (rfl). impl fast_rewiring_dim states only fastRewiringLimit.dim = 3, so a checker could only prove S1 without h (vacuous)."

sa_fail_forward "DynamicLimits.table.R32" 2 "S2 (DynamicEBCM.dim m = 5) holds by the definition of DynamicEBCM.dim (rfl). impl states only fastRewiringLimit.dim = 3, so a checker could only prove S2 without h (vacuous)."

@[sa_forward "DynamicLimits.table.R32" 3]
theorem fwd3 (h : sa_impl% "DynamicLimits.table.R32") : S3 := fun m => h m

@[sa_backward "DynamicLimits.table.R32"]
theorem bwd (_s1 : S1) (_s2 : S2) (s3 : S3) : sa_impl% "DynamicLimits.table.R32" := fun m => s3 m

end Alignment.Shadows.DynamicLimits.table_R32

/-! ## table.R33 -/
namespace Alignment.Shadows.DynamicLimits.table_R33

sa_claim "DynamicLimits.table.R33" group "DynamicLimits" required
  text "| 33 | `DynamicEBCM.R0` stores the static-limit R₀ only |"
  impl R0_rewiring_independent

@[sa_forward "DynamicLimits.table.R33" 1]
theorem fwd1 (h : sa_impl% "DynamicLimits.table.R33") : S1 := fun m => (h m).symm

@[sa_forward "DynamicLimits.table.R33" 2]
theorem fwd2 (h : sa_impl% "DynamicLimits.table.R33") : S2 := fun m => (h m).symm

sa_fail_forward "DynamicLimits.table.R33" 3 "impl R0_rewiring_independent (staticLimit.R0 = R0) says nothing about the edge-swapping R₀ at a positive rewiring rate, so S3 (R0 ≠ R₀(η) for η > 0: the stored value is only the static one) does not follow."

@[sa_backward "DynamicLimits.table.R33"]
theorem bwd (_s1 : S1) (s2 : S2) (_s3 : S3) : sa_impl% "DynamicLimits.table.R33" :=
  fun m => (s2 m).symm

end Alignment.Shadows.DynamicLimits.table_R33

namespace Alignment.Shadows.DynamicLimits.table_R34

sa_claim "DynamicLimits.table.R34" group "DynamicLimits" required
  text "| 34 | Coarse-graining commutes with static limit |"
  impl coarseGrain_static_comm

@[sa_forward "DynamicLimits.table.R34" 1]
theorem fwd1 (h : sa_impl% "DynamicLimits.table.R34") : S1 :=
  fun m => congrArg EpiModel.dim (h m)

@[sa_forward "DynamicLimits.table.R34" 2]
theorem fwd2 (h : sa_impl% "DynamicLimits.table.R34") : S2 :=
  fun m => congrArg EpiModel.R0 (h m)

/-- Structure eta: `e ≡ ⟨e.dim, e.R0⟩`, so the two field equations give the model equation. -/
@[sa_backward "DynamicLimits.table.R34"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "DynamicLimits.table.R34" :=
  fun m =>
    have e : EpiModel.mk (coarseGrain m.toEpiModel).dim (coarseGrain m.toEpiModel).R0 =
        EpiModel.mk (coarseGrain m.staticLimit).dim (coarseGrain m.staticLimit).R0 :=
      congr (congrArg EpiModel.mk (s1 m)) (s2 m)
    e

end Alignment.Shadows.DynamicLimits.table_R34

/-! ## table.R35 (every coarse-graining has dimension 3 by definition, so `h m` has the
shadow's type; weak evidence) -/
namespace Alignment.Shadows.DynamicLimits.table_R35

sa_claim "DynamicLimits.table.R35" group "DynamicLimits" required
  text "| 35 | Fast-rewiring record has the dimension of a coarse-graining |"
  impl fast_rewiring_is_coarsegraining

@[sa_forward "DynamicLimits.table.R35" 1]
theorem fwd1 (h : sa_impl% "DynamicLimits.table.R35") : S1 := fun m _e => h m

@[sa_backward "DynamicLimits.table.R35"]
theorem bwd (s1 : S1) : sa_impl% "DynamicLimits.table.R35" := fun m => s1 m m.toEpiModel

end Alignment.Shadows.DynamicLimits.table_R35

/-! ## table.R36 -/
namespace Alignment.Shadows.DynamicLimits.table_R36

sa_claim "DynamicLimits.table.R36" group "DynamicLimits" required
  text "| 36 | For Poisson, the stored T·κ equals the static R₀ |"
  impl fast_rewiring_R0_poisson

sa_fail_forward "DynamicLimits.table.R36" 1 "S1 (the Poisson record's stored fast-rewiring value is T·κ) holds by the definition of fastRewiringLimit (rfl). impl states the equality with the static R₀, so a checker could only prove S1 without h (vacuous)."

@[sa_forward "DynamicLimits.table.R36" 2]
theorem fwd2 (h : sa_impl% "DynamicLimits.table.R36") : S2 := fun p κ hκ => h p κ hκ

@[sa_backward "DynamicLimits.table.R36"]
theorem bwd (_s1 : S1) (s2 : S2) : sa_impl% "DynamicLimits.table.R36" := fun p κ hκ => s2 p κ hκ

end Alignment.Shadows.DynamicLimits.table_R36

/-! ## table.R37 -/
namespace Alignment.Shadows.DynamicLimits.table_R37

sa_claim "DynamicLimits.table.R37" group "DynamicLimits" required
  text "| 37 | Some record has T·κ ≠ static R₀; MFSH R₀ > static R₀ |"
  impl fast_rewiring_R0_differs

sa_fail_forward "DynamicLimits.table.R37" 1 "S1 (the stored fast-rewiring value is T·ψ'(1)) is the definition of fastRewiringLimit (rfl). impl does not state it, so a checker could only prove S1 without h (vacuous)."

@[sa_forward "DynamicLimits.table.R37" 2]
theorem fwd2 (h : sa_impl% "DynamicLimits.table.R37") : S2 := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m, hm⟩

sa_fail_forward "DynamicLimits.table.R37" 3 "S3 (MFSH R₀ > static R₀ for every record) is DynamicEBCM.R0_static_lt_mfsh, which is not in this claim's impl list (fast_rewiring_R0_differs only)."

@[sa_backward "DynamicLimits.table.R37"]
theorem bwd (_s1 : S1) (s2 : S2) (_s3 : S3) : sa_impl% "DynamicLimits.table.R37" := by
  obtain ⟨m, hm⟩ := s2
  exact ⟨m, hm⟩

end Alignment.Shadows.DynamicLimits.table_R37

namespace Alignment.Shadows.DynamicLimits.table_R38

sa_claim "DynamicLimits.table.R38" group "DynamicLimits" required
  text "| 38 | Dynamic refines static |"
  impl dynamic_refines_static

@[sa_forward "DynamicLimits.table.R38" 1]
theorem fwd1 (h : sa_impl% "DynamicLimits.table.R38") : S1 :=
  fun m => h m

@[sa_backward "DynamicLimits.table.R38"]
theorem bwd (s1 : S1) : sa_impl% "DynamicLimits.table.R38" :=
  fun m => s1 m

end Alignment.Shadows.DynamicLimits.table_R38

namespace Alignment.Shadows.DynamicLimits.table_R39

sa_claim "DynamicLimits.table.R39" group "DynamicLimits" required
  text "| 39 | Fast-rewiring is coarser than static |"
  impl fast_rewiring_coarser_than_static

@[sa_forward "DynamicLimits.table.R39" 1]
theorem fwd1 (h : sa_impl% "DynamicLimits.table.R39") : S1 :=
  fun m => h m

@[sa_backward "DynamicLimits.table.R39"]
theorem bwd (s1 : S1) : sa_impl% "DynamicLimits.table.R39" :=
  fun m => s1 m

end Alignment.Shadows.DynamicLimits.table_R39

namespace Alignment.Shadows.DynamicLimits.table_R40

sa_claim "DynamicLimits.table.R40" group "DynamicLimits" required
  text "| 40 | Full tower: mean-field < static < dynamic |"
  impl full_tower

sa_fail_forward "DynamicLimits.table.R40" 1 "different notion of '<': impl full_tower states Nat < on the dimensions (m.fastRewiringLimit.dim < m.staticLimit.dim); S1 is the strict order of the EpiModel preorder, m.fastRewiringLimit < m.staticLimit, which unfolds to the Preorder default lt (dim ≤ dim ∧ ¬ reverse ≤, here 3 ≤ 4 ∧ ¬ 4 ≤ 3). The two agree only via Nat order lemmas (Nat.le_of_lt, Nat.not_le_of_lt / lt_iff_le_not_ge), not structurally, and no admissible bridge exists (the head LT.lt / Preorder.toLT is not a trusted definition). Remediation: state the tower with the EpiModel preorder's <."

sa_fail_forward "DynamicLimits.table.R40" 2 "different notion of '<': impl full_tower states Nat < on the dimensions (m.staticLimit.dim < m.toEpiModel.dim); S2 is the strict order of the EpiModel preorder, m.staticLimit < m.toEpiModel, i.e. the Preorder default lt (4 ≤ 5 ∧ ¬ 5 ≤ 4). Equivalent only via Nat order lemmas, not structurally; no admissible bridge (LT.lt is not a trusted definition)."

sa_fail_backward "DynamicLimits.table.R40" "S1, S2 give the EpiModel preorder's strict order (dim ≤ dim ∧ ¬ reverse ≤); full_tower needs Nat < on the dims (Nat.le (d+1) d'), obtainable only via Nat order lemmas (e.g. Nat.lt_of_le_of_ne / lt_iff_le_not_ge), not structurally; no admissible bridge (LT.lt is not a trusted definition)."

end Alignment.Shadows.DynamicLimits.table_R40

/-! ## Results (docstrings) -/

namespace Alignment.Shadows.DynamicLimits.R29

sa_claim "DynamicLimits.R29" group "DynamicLimits" required
  text "**Result 29.** The static EBCM (dim 4) has fewer variables than the dynamic EBCM (dim 5)."
  impl static_lt_dynamic

/-- `m.dim ≡ m.toEpiModel.dim ≡ 5`. -/
@[sa_forward "DynamicLimits.R29" 1]
theorem fwd1 (h : sa_impl% "DynamicLimits.R29") : S1 :=
  fun m => h m

@[sa_forward "DynamicLimits.R29" 2]
theorem fwd2 (h : sa_impl% "DynamicLimits.R29") : S2 :=
  fun m => h m

sa_fail_forward "DynamicLimits.R29" 3 "impl static_lt_dynamic asserts only the strict inequality m.staticLimit.dim < m.toEpiModel.dim; the parenthetical value 'static EBCM (dim 4)' (S3: m.staticLimit.dim = 4) is not asserted (it is static_limit_dim, not in R29's impl list) and holds only by the definition edgeModel.dim := 4 (rfl, independent of h)."

sa_fail_forward "DynamicLimits.R29" 4 "impl static_lt_dynamic asserts only m.staticLimit.dim < m.toEpiModel.dim; the parenthetical value 'dynamic EBCM (dim 5)' (S4: m.dim = 5) is not asserted and holds only by the definition DynamicEBCM.dim _ := 5 (rfl, independent of h)."

sa_fail_forward "DynamicLimits.R29" 5 "impl static_lt_dynamic asserts only m.staticLimit.dim < m.toEpiModel.dim (a lower bound on m.toEpiModel.dim); the parenthetical value 'dynamic EBCM (dim 5)' (S5: m.toEpiModel.dim = 5) is not asserted and holds only by the definition toEpiModel.dim := 5 (rfl, independent of h)."

@[sa_backward "DynamicLimits.R29"]
theorem bwd (_s1 : S1) (s2 : S2) (_s3 : S3) (_s4 : S4) (_s5 : S5) : sa_impl% "DynamicLimits.R29" :=
  fun m => s2 m

end Alignment.Shadows.DynamicLimits.R29

namespace Alignment.Shadows.DynamicLimits.R30

sa_claim "DynamicLimits.R30" group "DynamicLimits" required
  text "**Result 30.** The dynamic EBCM (dim 5) has fewer variables than pair approximation (dim 12N) for N ≥ 1."
  impl dynamic_lt_pair

@[sa_forward "DynamicLimits.R30" 1]
theorem fwd1 (h : sa_impl% "DynamicLimits.R30") : S1 :=
  fun m N hN => h m N hN

@[sa_forward "DynamicLimits.R30" 2]
theorem fwd2 (h : sa_impl% "DynamicLimits.R30") : S2 :=
  fun m N hN => h m N hN

sa_fail_forward "DynamicLimits.R30" 3 "impl dynamic_lt_pair asserts only m.toEpiModel.dim < 12 * N for N ≥ 1; the parenthetical value 'dynamic EBCM (dim 5)' (S3: m.dim = 5) is not asserted and holds only by the definition DynamicEBCM.dim _ := 5 (rfl, independent of h)."

sa_fail_forward "DynamicLimits.R30" 4 "impl dynamic_lt_pair asserts only the upper bound m.toEpiModel.dim < 12 * N for N ≥ 1; the parenthetical value 'dynamic EBCM (dim 5)' (S4: m.toEpiModel.dim = 5) is not asserted and holds only by the definition toEpiModel.dim := 5 (rfl, independent of h)."

@[sa_backward "DynamicLimits.R30"]
theorem bwd (_s1 : S1) (s2 : S2) (_s3 : S3) (_s4 : S4) : sa_impl% "DynamicLimits.R30" :=
  fun m N hN => s2 m N hN

end Alignment.Shadows.DynamicLimits.R30

namespace Alignment.Shadows.DynamicLimits.R31a

sa_claim "DynamicLimits.R31a" group "DynamicLimits" required
  text "reducing the dimension by 1 [...] **Result 31.** Static limit: the dimension drops from 5 to 4."
  impl static_limit_dim

sa_fail_forward "DynamicLimits.R31a" 1 "impl static_limit_dim asserts only the target m.staticLimit.dim = 4; 'drops from 5' (S1: m.dim = 5) is not asserted (the registry impl_note agrees) and holds only by the definition DynamicEBCM.dim _ := 5 (rfl, independent of h)."

sa_fail_forward "DynamicLimits.R31a" 2 "impl static_limit_dim asserts only the target m.staticLimit.dim = 4; 'drops from 5' (S2: m.toEpiModel.dim = 5) is not asserted (the registry impl_note agrees) and holds only by the definition toEpiModel.dim := 5 (rfl, independent of h)."

@[sa_forward "DynamicLimits.R31a" 3]
theorem fwd3 (h : sa_impl% "DynamicLimits.R31a") : S3 :=
  fun m => h m

sa_fail_forward "DynamicLimits.R31a" 4 "S4 ('reducing the dimension by 1': m.staticLimit.dim + 1 = m.dim) relates both endpoints; impl static_limit_dim gives only the lower endpoint m.staticLimit.dim = 4 and never mentions the dynamic dimension, so the drop by 1 is not asserted (the equation is 5 = 5 by rfl, independent of h)."

sa_fail_forward "DynamicLimits.R31a" 5 "S5 ('reducing the dimension by 1': m.staticLimit.dim + 1 = m.toEpiModel.dim) relates both endpoints; impl static_limit_dim gives only the lower endpoint m.staticLimit.dim = 4 and never mentions m.toEpiModel.dim, so the drop by 1 is not asserted (the equation is 5 = 5 by rfl, independent of h)."

@[sa_backward "DynamicLimits.R31a"]
theorem bwd (_s1 : S1) (_s2 : S2) (s3 : S3) (_s4 : S4) (_s5 : S5) :
    sa_impl% "DynamicLimits.R31a" :=
  fun m => s3 m

end Alignment.Shadows.DynamicLimits.R31a

namespace Alignment.Shadows.DynamicLimits.R32a

sa_claim "DynamicLimits.R32a" group "DynamicLimits" required
  text "**Result 32.** Fast-rewiring limit: the dimension drops to 3."
  impl fast_rewiring_dim

@[sa_forward "DynamicLimits.R32a" 1]
theorem fwd1 (h : sa_impl% "DynamicLimits.R32a") : S1 :=
  fun m => h m

sa_fail_forward "DynamicLimits.R32a" 2 "impl fast_rewiring_dim asserts only the value m.fastRewiringLimit.dim = 3; S2 ('drops': m.fastRewiringLimit.dim < m.dim, i.e. 3 < 5) is a Nat order fact about the dynamic dimension that the impl does not assert and that cannot be derived structurally from an equation."

sa_fail_forward "DynamicLimits.R32a" 3 "impl fast_rewiring_dim asserts only the value m.fastRewiringLimit.dim = 3; S3 ('drops': m.fastRewiringLimit.dim < m.toEpiModel.dim, i.e. 3 < 5) is a Nat order fact about the dynamic dimension that the impl does not assert and that cannot be derived structurally from an equation."

@[sa_backward "DynamicLimits.R32a"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) : sa_impl% "DynamicLimits.R32a" :=
  fun m => s1 m

end Alignment.Shadows.DynamicLimits.R32a

/-! ## R33a

`m.staticLimit.R0` unfolds to `T·(ψ''(1)/ψ'(1))`, which is `staticR0 m.disease m.pgf`, so the
implementation `staticLimit.R0 = R0` read right to left is S1. -/
namespace Alignment.Shadows.DynamicLimits.R33a

sa_claim "DynamicLimits.R33a" group "DynamicLimits" required
  text "`DynamicEBCM` records no rewiring rate, so this is not the R₀ of the dynamic model. [...] **Result 33.** `DynamicEBCM` stores only the static-limit R₀: `DynamicEBCM.R0` is T·ψ''(1)/ψ'(1)."
  impl R0_rewiring_independent

@[sa_forward "DynamicLimits.R33a" 1]
theorem fwd1 (h : sa_impl% "DynamicLimits.R33a") : S1 := fun m => (h m).symm

sa_fail_forward "DynamicLimits.R33a" 2 "impl R0_rewiring_independent (staticLimit.R0 = R0) says nothing about the edge-swapping R₀ at a positive rewiring rate. S2 (R0 ≠ R₀(η) for every η > 0) is not stated; the edge-swapping R₀ is DynamicEBCM.R0_edgeSwap, which impl does not mention."

@[sa_backward "DynamicLimits.R33a"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "DynamicLimits.R33a" := fun m => (s1 m).symm

end Alignment.Shadows.DynamicLimits.R33a

namespace Alignment.Shadows.DynamicLimits.R33b

sa_claim "DynamicLimits.R33b" group "DynamicLimits" required
  text "The static limit preserves R₀ exactly,"
  impl R0_rewiring_independent

@[sa_forward "DynamicLimits.R33b" 1]
theorem fwd1 (h : sa_impl% "DynamicLimits.R33b") : S1 :=
  fun m => h m

/-- `m.toEpiModel.R0` unfolds to `m.R0`. -/
@[sa_forward "DynamicLimits.R33b" 2]
theorem fwd2 (h : sa_impl% "DynamicLimits.R33b") : S2 :=
  fun m => h m

@[sa_backward "DynamicLimits.R33b"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "DynamicLimits.R33b" :=
  fun m => s1 m

end Alignment.Shadows.DynamicLimits.R33b

namespace Alignment.Shadows.DynamicLimits.R34

sa_claim "DynamicLimits.R34" group "DynamicLimits" required
  text "**Result 34.** Coarse-graining commutes with the static limit. F(dynamic) = F(staticLimit(dynamic)), because both give dim 3 with the same R₀."
  impl coarseGrain_static_comm

@[sa_forward "DynamicLimits.R34" 1]
theorem fwd1 (h : sa_impl% "DynamicLimits.R34") : S1 :=
  fun m => congrArg EpiModel.dim (h m)

@[sa_forward "DynamicLimits.R34" 2]
theorem fwd2 (h : sa_impl% "DynamicLimits.R34") : S2 :=
  fun m => congrArg EpiModel.R0 (h m)

sa_fail_forward "DynamicLimits.R34" 3 "impl coarseGrain_static_comm asserts only F(m.toEpiModel) = F(m.staticLimit); the value in 'both give dim 3' (S3: (coarseGrain m.toEpiModel).dim = 3) is not asserted and holds only by the definition coarseGrain.dim := 3 (rfl, independent of h)."

sa_fail_forward "DynamicLimits.R34" 4 "impl coarseGrain_static_comm asserts only F(m.toEpiModel) = F(m.staticLimit); the value in 'both give dim 3' (S4: (coarseGrain m.staticLimit).dim = 3) is not asserted and holds only by the definition coarseGrain.dim := 3 (rfl, independent of h)."

/-- Structure eta: `e ≡ ⟨e.dim, e.R0⟩`. -/
@[sa_backward "DynamicLimits.R34"]
theorem bwd (s1 : S1) (s2 : S2) (_s3 : S3) (_s4 : S4) : sa_impl% "DynamicLimits.R34" :=
  fun m =>
    have e : EpiModel.mk (coarseGrain m.toEpiModel).dim (coarseGrain m.toEpiModel).R0 =
        EpiModel.mk (coarseGrain m.staticLimit).dim (coarseGrain m.staticLimit).R0 :=
      congr (congrArg EpiModel.mk (s1 m)) (s2 m)
    e

end Alignment.Shadows.DynamicLimits.R34

namespace Alignment.Shadows.DynamicLimits.R35a

sa_claim "DynamicLimits.R35a" group "DynamicLimits" required
  text "**Result 35.** The fast-rewiring limit has the same dimension as coarse-graining (both give dim = 3)."
  impl fast_rewiring_is_coarsegraining

@[sa_forward "DynamicLimits.R35a" 1]
theorem fwd1 (h : sa_impl% "DynamicLimits.R35a") : S1 :=
  fun m => h m

sa_fail_forward "DynamicLimits.R35a" 2 "impl fast_rewiring_is_coarsegraining asserts only the equality m.fastRewiringLimit.dim = (coarseGrain m.toEpiModel).dim; the value in 'both give dim = 3' (S2: m.fastRewiringLimit.dim = 3) is not asserted (it is fast_rewiring_dim) and holds only by the definition fastRewiringLimit.dim := 3 (rfl, independent of h)."

sa_fail_forward "DynamicLimits.R35a" 3 "impl fast_rewiring_is_coarsegraining asserts only the equality m.fastRewiringLimit.dim = (coarseGrain m.toEpiModel).dim; the value in 'both give dim = 3' (S3: (coarseGrain m.toEpiModel).dim = 3) is not asserted and holds only by the definition coarseGrain.dim := 3 (rfl, independent of h)."

@[sa_backward "DynamicLimits.R35a"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) : sa_impl% "DynamicLimits.R35a" :=
  fun m => s1 m

end Alignment.Shadows.DynamicLimits.R35a

/-! ## R35b -/
namespace Alignment.Shadows.DynamicLimits.R35b

sa_claim "DynamicLimits.R35b" group "DynamicLimits" required
  text "It is not a coarse-graining of the same model: the MFSH R₀ differs from the static R₀ (`R0_static_lt_mfsh`)."
  impl fast_rewiring_is_coarsegraining

sa_fail_forward "DynamicLimits.R35b" 1 "impl fast_rewiring_is_coarsegraining states only fastRewiringLimit.dim = (coarseGrain toEpiModel).dim, the dimension coincidence (3 = 3). It says nothing about R₀; S1 (the MFSH R₀ differs from the static R₀) is R0_static_lt_mfsh, which the text cites and which is not in impl."

sa_fail_forward "DynamicLimits.R35b" 2 "impl is the dimension coincidence 3 = 3. S2 (a model with the MFSH R₀ is not the coarse-graining of the dynamic model) needs the R₀ inequality, which impl does not state."

sa_fail_forward "DynamicLimits.R35b" 3 "impl is the dimension coincidence 3 = 3. S3 (a model with the MFSH R₀ is not the coarse-graining of the static limit) needs the R₀ inequality, which impl does not state."

sa_fail_backward "DynamicLimits.R35b" "impl (fastRewiringLimit.dim = (coarseGrain toEpiModel).dim) holds by rfl, since both are 3, so any backward checker ignores the shadows (vacuous). impl states the first sentence of Result 35 ('has the same dimension as coarse-graining'), not this claim's sentence ('It is not a coarse-graining of the same model')."

end Alignment.Shadows.DynamicLimits.R35b

/-! ## R36a (`staticLimit.R0` of the Poisson record unfolds to `DynamicEBCM.R0`) -/
namespace Alignment.Shadows.DynamicLimits.R36a

sa_claim "DynamicLimits.R36a" group "DynamicLimits" required
  text "**Result 36.** For Poisson networks, the value T·κ stored by `fastRewiringLimit` equals the static EBCM R₀."
  impl fast_rewiring_R0_poisson

sa_fail_forward "DynamicLimits.R36a" 1 "S1 (the Poisson record's stored fast-rewiring value is T·κ) holds by the definition of fastRewiringLimit (R0 := T·pgf.mean, and (poisson κ).mean = κ), i.e. by rfl. impl states the equality with the static R₀ instead, so a checker could only prove S1 without h (vacuous)."

@[sa_forward "DynamicLimits.R36a" 2]
theorem fwd2 (h : sa_impl% "DynamicLimits.R36a") : S2 := fun p κ hκ => h p κ hκ

@[sa_backward "DynamicLimits.R36a"]
theorem bwd (_s1 : S1) (s2 : S2) : sa_impl% "DynamicLimits.R36a" := fun p κ hκ => s2 p κ hκ

end Alignment.Shadows.DynamicLimits.R36a

namespace Alignment.Shadows.DynamicLimits.R36b

sa_claim "DynamicLimits.R36b" group "DynamicLimits" required
  text "This is because the Poisson excess degree equals the mean degree: ψ''(1)/ψ'(1) = κ."
  impl PGFData.poisson_excess_eq_mean

@[sa_forward "DynamicLimits.R36b" 1]
theorem fwd1 (h : sa_impl% "DynamicLimits.R36b") : S1 :=
  fun κ hκ => h κ hκ

/-- `(PGFData.poisson κ hκ).mean` reduces to `κ`. -/
@[sa_forward "DynamicLimits.R36b" 2]
theorem fwd2 (h : sa_impl% "DynamicLimits.R36b") : S2 :=
  fun κ hκ => h κ hκ

/-- `PGFData.excessDegree ψ` unfolds to `ψ.secondFactorial / ψ.mean`. -/
@[sa_forward "DynamicLimits.R36b" 3]
theorem fwd3 (h : sa_impl% "DynamicLimits.R36b") : S3 :=
  fun κ hκ => h κ hκ

@[sa_backward "DynamicLimits.R36b"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) : sa_impl% "DynamicLimits.R36b" :=
  fun κ hκ => s1 κ hκ

end Alignment.Shadows.DynamicLimits.R36b

/-! ## R37a -/
namespace Alignment.Shadows.DynamicLimits.R37a

sa_claim "DynamicLimits.R37a" group "DynamicLimits" required
  text "**Result 37.** Some degree record has a stored fast-rewiring value T·κ different from the static EBCM R₀. The genuine fast-rewiring (MFSH) R₀ exceeds the static R₀ for every degree law (`R0_static_lt_mfsh`)."
  impl fast_rewiring_R0_differs

sa_fail_forward "DynamicLimits.R37a" 1 "S1 (the stored fast-rewiring value is T·ψ'(1)) is the definition of fastRewiringLimit (rfl). impl fast_rewiring_R0_differs is an existential inequality and does not state it, so a checker could only prove S1 without h (vacuous)."

@[sa_forward "DynamicLimits.R37a" 2]
theorem fwd2 (h : sa_impl% "DynamicLimits.R37a") : S2 := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m, hm⟩

sa_fail_forward "DynamicLimits.R37a" 3 "S3 (the MFSH R₀ exceeds the static R₀ for every record) is DynamicEBCM.R0_static_lt_mfsh, which the text cites and which is not in this claim's impl list. impl states only that some record has T·κ ≠ static R₀."

@[sa_backward "DynamicLimits.R37a"]
theorem bwd (_s1 : S1) (s2 : S2) (_s3 : S3) : sa_impl% "DynamicLimits.R37a" := by
  obtain ⟨m, hm⟩ := s2
  exact ⟨m, hm⟩

end Alignment.Shadows.DynamicLimits.R37a

namespace Alignment.Shadows.DynamicLimits.R38

sa_claim "DynamicLimits.R38" group "DynamicLimits" required
  text "**Result 38.** The dynamic model refines the static model (it has strictly more state variables: 5 > 4)."
  impl dynamic_refines_static

@[sa_forward "DynamicLimits.R38" 1]
theorem fwd1 (h : sa_impl% "DynamicLimits.R38") : S1 :=
  fun m => h m

sa_fail_forward "DynamicLimits.R38" 2 "impl dynamic_refines_static asserts only the non-strict m.staticLimit ≤ m.toEpiModel (4 ≤ 5 on dims); 'strictly more state variables' (S2: m.staticLimit.dim < m.toEpiModel.dim) is not asserted (it is Result 29, static_lt_dynamic, not in R38's impl) and does not follow from ≤."

sa_fail_forward "DynamicLimits.R38" 3 "impl dynamic_refines_static asserts only the non-strict m.staticLimit ≤ m.toEpiModel (4 ≤ 5 on dims); 'strictly more state variables' (S3: m.staticLimit.dim < m.dim) is not asserted (it is Result 29, static_lt_dynamic, not in R38's impl) and does not follow from ≤."

sa_fail_forward "DynamicLimits.R38" 4 "impl dynamic_refines_static asserts only m.staticLimit ≤ m.toEpiModel; the value '5' (S4: m.toEpiModel.dim = 5) is not asserted and holds only by the definition toEpiModel.dim := 5 (rfl, independent of h)."

sa_fail_forward "DynamicLimits.R38" 5 "impl dynamic_refines_static asserts only m.staticLimit ≤ m.toEpiModel; the value '5' (S5: m.dim = 5) is not asserted and holds only by the definition DynamicEBCM.dim _ := 5 (rfl, independent of h)."

sa_fail_forward "DynamicLimits.R38" 6 "impl dynamic_refines_static asserts only m.staticLimit ≤ m.toEpiModel; the value '4' (S6: m.staticLimit.dim = 4) is not asserted and holds only by the definition edgeModel.dim := 4 (rfl, independent of h)."

@[sa_backward "DynamicLimits.R38"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) (_s4 : S4) (_s5 : S5) (_s6 : S6) :
    sa_impl% "DynamicLimits.R38" :=
  fun m => s1 m

end Alignment.Shadows.DynamicLimits.R38

namespace Alignment.Shadows.DynamicLimits.R39

sa_claim "DynamicLimits.R39" group "DynamicLimits" required
  text "**Result 39.** The fast-rewiring limit is coarser than the static limit. Mean-field (dim 3) ≤ Static EBCM (dim 4)."
  impl fast_rewiring_coarser_than_static

@[sa_forward "DynamicLimits.R39" 1]
theorem fwd1 (h : sa_impl% "DynamicLimits.R39") : S1 :=
  fun m => h m

sa_fail_forward "DynamicLimits.R39" 2 "impl fast_rewiring_coarser_than_static asserts only m.fastRewiringLimit ≤ m.staticLimit; the value 'Mean-field (dim 3)' (S2: m.fastRewiringLimit.dim = 3) is not asserted (it is fast_rewiring_dim) and holds only by the definition fastRewiringLimit.dim := 3 (rfl, independent of h)."

sa_fail_forward "DynamicLimits.R39" 3 "impl fast_rewiring_coarser_than_static asserts only m.fastRewiringLimit ≤ m.staticLimit; the value 'Static EBCM (dim 4)' (S3: m.staticLimit.dim = 4) is not asserted (it is static_limit_dim) and holds only by the definition edgeModel.dim := 4 (rfl, independent of h)."

@[sa_backward "DynamicLimits.R39"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) : sa_impl% "DynamicLimits.R39" :=
  fun m => s1 m

end Alignment.Shadows.DynamicLimits.R39

namespace Alignment.Shadows.DynamicLimits.R40a

sa_claim "DynamicLimits.R40a" group "DynamicLimits" required
  text "**Result 40.** The full tower: mean-field < static EBCM < dynamic EBCM."
  impl full_tower

sa_fail_forward "DynamicLimits.R40a" 1 "different notion of '<': impl full_tower states Nat < on the dimensions (m.fastRewiringLimit.dim < m.staticLimit.dim; the registry impl_note: 'stated on dims (not with < of the EpiModel preorder)'); S1 is the strict order of the EpiModel preorder, m.fastRewiringLimit < m.staticLimit, which unfolds to the Preorder default lt (3 ≤ 4 ∧ ¬ 4 ≤ 3 on dims). Equivalent only via Nat order lemmas (Nat.le_of_lt, Nat.not_le_of_lt / lt_iff_le_not_ge), not structurally; no admissible bridge (the head LT.lt / Preorder.toLT is not a trusted definition). Remediation: state the tower with the EpiModel preorder's <."

sa_fail_forward "DynamicLimits.R40a" 2 "different notion of '<': impl full_tower states Nat < on the dimensions (m.staticLimit.dim < m.toEpiModel.dim); S2 is the strict order of the EpiModel preorder, m.staticLimit < m.toEpiModel, i.e. the Preorder default lt (4 ≤ 5 ∧ ¬ 5 ≤ 4 on dims). Equivalent only via Nat order lemmas, not structurally; no admissible bridge (LT.lt is not a trusted definition)."

sa_fail_backward "DynamicLimits.R40a" "S1, S2 give the EpiModel preorder's strict order (dim ≤ dim ∧ ¬ reverse ≤); full_tower needs Nat < on the dims (Nat.le (d+1) d'), obtainable only via Nat order lemmas (e.g. Nat.lt_of_le_of_ne / lt_iff_le_not_ge), not structurally; no admissible bridge (LT.lt is not a trusted definition)."

end Alignment.Shadows.DynamicLimits.R40a

/-! ## r0EdgeSwapZero (`edgeSwapR0 p ψ` and `staticR0 p ψ` unfold to `R0_edgeSwap` and `R0` of
`⟨p, ψ⟩`) -/
namespace Alignment.Shadows.DynamicLimits.r0EdgeSwapZero

sa_claim "DynamicLimits.r0EdgeSwapZero" group "DynamicLimits" required
  text "At rewiring rate η = 0 the edge-swapping R₀ is the static-limit R₀ T·ψ''(1)/ψ'(1)."
  impl DynamicEBCM.R0_edgeSwap_zero

@[sa_forward "DynamicLimits.r0EdgeSwapZero" 1]
theorem fwd1 (h : sa_impl% "DynamicLimits.r0EdgeSwapZero") : S1 := fun p ψ => h ⟨p, ψ⟩

@[sa_forward "DynamicLimits.r0EdgeSwapZero" 2]
theorem fwd2 (h : sa_impl% "DynamicLimits.r0EdgeSwapZero") : S2 := fun p ψ => h ⟨p, ψ⟩

@[sa_backward "DynamicLimits.r0EdgeSwapZero"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "DynamicLimits.r0EdgeSwapZero" :=
  fun m => s1 m.disease m.pgf

end Alignment.Shadows.DynamicLimits.r0EdgeSwapZero

/-! ## r0EdgeSwapTendstoMfsh -/
namespace Alignment.Shadows.DynamicLimits.r0EdgeSwapTendstoMfsh

sa_claim "DynamicLimits.r0EdgeSwapTendstoMfsh" group "DynamicLimits" required
  text "As the rewiring rate η → ∞, the edge-swapping R₀ tends to the MFSH R₀ (β/γ)(ψ''(1)/ψ'(1) + 1)."
  impl DynamicEBCM.R0_edgeSwap_tendsto_mfsh

sa_fail_forward "DynamicLimits.r0EdgeSwapTendstoMfsh" 1 "impl DynamicEBCM.R0_edgeSwap_tendsto_mfsh is a limit in ℚ (η : ℚ → ∞, with ℚ's order topology). S1 is the limit of the real-valued edge-swapping R₀ as a real η → ∞, towards the cast of the MFSH value. The rational limit does not give the real one structurally: that needs continuity of the cast and density or monotonicity arguments (library lemmas), so impl and S1 are about different functions."

sa_fail_backward "DynamicLimits.r0EdgeSwapTendstoMfsh" "S1 is a limit of a function ℝ → ℝ; impl is a limit of a function ℚ → ℚ in ℚ's topology. Restricting the real limit to rational η and pulling it back along the embedding ℚ → ℝ needs Tendsto.comp with the embedding's properties (library lemmas), not structural reasoning."

end Alignment.Shadows.DynamicLimits.r0EdgeSwapTendstoMfsh

/-! ## r0StaticLtMfsh -/
namespace Alignment.Shadows.DynamicLimits.r0StaticLtMfsh

sa_claim "DynamicLimits.r0StaticLtMfsh" group "DynamicLimits" required
  text "The MFSH (fast-rewiring) R₀ exceeds the static-limit R₀ for every degree record: (β/γ)(ψ''(1)/ψ'(1) + 1) > β/(β+γ) · ψ''(1)/ψ'(1)."
  impl DynamicEBCM.R0_static_lt_mfsh

@[sa_forward "DynamicLimits.r0StaticLtMfsh" 1]
theorem fwd1 (h : sa_impl% "DynamicLimits.r0StaticLtMfsh") : S1 := fun p ψ => h ⟨p, ψ⟩

@[sa_backward "DynamicLimits.r0StaticLtMfsh"]
theorem bwd (s1 : S1) : sa_impl% "DynamicLimits.r0StaticLtMfsh" := fun m => s1 m.disease m.pgf

end Alignment.Shadows.DynamicLimits.r0StaticLtMfsh

/-! ## r0MfshPoisson -/
namespace Alignment.Shadows.DynamicLimits.r0MfshPoisson

sa_claim "DynamicLimits.r0MfshPoisson" group "DynamicLimits" required
  text "For Poisson degrees the MFSH (fast-rewiring) R₀ is (β/γ)(κ + 1)."
  impl DynamicEBCM.R0_mfsh_poisson

@[sa_forward "DynamicLimits.r0MfshPoisson" 1]
theorem fwd1 (h : sa_impl% "DynamicLimits.r0MfshPoisson") : S1 := fun p κ hκ => h p κ hκ

@[sa_backward "DynamicLimits.r0MfshPoisson"]
theorem bwd (s1 : S1) : sa_impl% "DynamicLimits.r0MfshPoisson" := fun p κ hκ => s1 p κ hκ

end Alignment.Shadows.DynamicLimits.r0MfshPoisson

/-! ## `DynamicLimits.R32b` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.DynamicLimits.R32b

sa_claim "DynamicLimits.R32b" group "DynamicLimits"
  text "When the network randomises infinitely fast, partnerships become fleeting and the model approaches MFSH (θ and R, with S = ψ(θ) and I = 1 − S − R), in which degree heterogeneity survives through ψ."
  impl

end Alignment.Shadows.DynamicLimits.R32b

/-! ## `DynamicLimits.R33c` (registry status `informal`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.DynamicLimits.R33c

sa_claim "DynamicLimits.R33c" group "DynamicLimits"
  text "In the edge-swapping EBCM, R₀ depends on η (Miller, Slim & Volz 2012, §3.2.1; `R0_edgeSwap`). [...] In the edge-swapping EBCM, R₀ depends on the rewiring rate η (Miller, Slim & Volz 2012, §3.2.1; see `R0_edgeSwap`)."
  impl

end Alignment.Shadows.DynamicLimits.R33c

/-! ## `DynamicLimits.R37b` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.DynamicLimits.R37b

sa_claim "DynamicLimits.R37b" group "DynamicLimits"
  text "Witness: a network with mean κ=3, second factorial=15 (excess=5). T=1/2, so EBCM R₀ = 5/2 and T·κ = 3/2; with β = γ = 1 the MFSH R₀ is 5 + 1 = 6."
  impl

end Alignment.Shadows.DynamicLimits.R37b

/-! ## `DynamicLimits.R40b` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.DynamicLimits.R40b

sa_claim "DynamicLimits.R40b" group "DynamicLimits"
  text "Combined with Hierarchy.lean, this gives, for N ≥ 4: Mean-field (3) < Static EBCM (4) < Dynamic EBCM (5) < Pair (12N) < Full (3^N); the last inequality fails for N ≤ 3."
  impl

end Alignment.Shadows.DynamicLimits.R40b

/-! ## `DynamicLimits.fastRewiringR0MeanDegree` (registry status `informal`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.DynamicLimits.fastRewiringR0MeanDegree

sa_claim "DynamicLimits.fastRewiringR0MeanDegree" group "DynamicLimits"
  text "Its R₀ is (β/γ)⟨K²⟩/⟨K⟩ = (β/γ)(ψ''(1)/ψ'(1) + 1) (`R0_mfsh`), which keeps degree heterogeneity. The R₀ stored here, T·ψ'(1) = βκ/(β+γ), is not that limit; it is kept for compatibility (Results 36, 37)."
  impl

end Alignment.Shadows.DynamicLimits.fastRewiringR0MeanDegree

/-! ## `DynamicLimits.header.fastRewiringCollapse` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.DynamicLimits.header_fastRewiringCollapse

sa_claim "DynamicLimits.header.fastRewiringCollapse" group "DynamicLimits"
  text "**Fast-rewiring limit (η → ∞)**: The network reshuffles so quickly that partnerships are fleeting. The system approaches the mean-field social-heterogeneity (MFSH) model of Miller, Slim & Volz (2012): nodes keep their degrees, so degree heterogeneity survives, and R₀ tends to (β/γ)⟨K²⟩/⟨K⟩."
  impl

end Alignment.Shadows.DynamicLimits.header_fastRewiringCollapse
