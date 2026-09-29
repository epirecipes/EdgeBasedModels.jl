import Alignment.Registry
import Alignment.Shadows.GaloisPair

/-!
# Checkers: group `GaloisPair`

Checker author (SA-PASS role 3, non-blind). For every claim of `EBCMCategory/GaloisPair.lean`
with `status: implemented` this file holds the `sa_claim` registration (verbatim registry text,
registry `impl` list in registry order), the forward checkers `sa_impl% → Sᵢ`, the backward checker
`S₁ → … → Sₙ → sa_impl%`, and `sa_fail_*` records where a check cannot be proved because the
implementation says something different from the shadow.

No bridges are declared. The trusted definitions `coarseGrain := ⟨3, e.R0⟩`,
`poissonLift := ⟨4, n.R0⟩`, `nodeModel`, `edgeModel` and the `Preorder EpiModel` instance
(`m₁ ≤ m₂ := m₁.dim ≤ m₂.dim`) are used exactly as the shadows use them, so every passing check
needs only definitional unfolding (`Function.comp`, `Monotone`).

Conventions of the proofs below (README "Writing structural proofs"): hypotheses, projections of
the conjunction `h`, `funext` (pointwise implementation → function equation of the shadow),
`congrFun` (function equation of the shadow → pointwise implementation), `Exists.elim`, and
definitional unfolding. The backward checkers of the three `G ∘ F ≠ id` claims also use a closed
kernel computation (`Nat.beq`, `Bool.rec` on plain data; README "Known limitations" 1) to
discriminate the dimensions 4 and 10, see the comment at `header_GFLossy.bwd`.

Summary of recorded failures: the three `G ∘ F ≠ id` claims (`header.GFLossy`, `table.R14`,
`R14a`) have a shadow S2 ("G ∘ F does not fix every `edgeModel p ψ`") that is refutable by `rfl`
in the trusted library, so its forward check is recorded as `sa_fail_forward … 2 "SHADOW?: …"`.
-/

/-! ## Header prose -/

namespace Alignment.Shadows.GaloisPair.header_idempotency

sa_claim "GaloisPair.header.idempotency" group "GaloisPair" required
  text "F ∘ G ∘ F = F and G ∘ F ∘ G = G (idempotency)"
  impl F_G_F_eq_F G_F_G_eq_G

/-- The impl is pointwise (`∀ e, F (G (F e)) = F e`); `funext` gives the function equation. -/
@[sa_forward "GaloisPair.header.idempotency" 1]
theorem fwd1 (h : sa_impl% "GaloisPair.header.idempotency") : S1 :=
  funext fun e => h.1 e

@[sa_forward "GaloisPair.header.idempotency" 2]
theorem fwd2 (h : sa_impl% "GaloisPair.header.idempotency") : S2 :=
  funext fun n => h.2 n

@[sa_backward "GaloisPair.header.idempotency"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "GaloisPair.header.idempotency" :=
  ⟨fun e => congrFun s1 e, fun n => congrFun s2 n⟩

end Alignment.Shadows.GaloisPair.header_idempotency

namespace Alignment.Shadows.GaloisPair.header_FGPreservesR0

sa_claim "GaloisPair.header.FGPreservesR0" group "GaloisPair" required
  text "F ∘ G preserves R₀ exactly"
  impl FG_preserves_R0

/-- `(coarseGrain ∘ poissonLift) M` unfolds to `coarseGrain (poissonLift M)`. -/
@[sa_forward "GaloisPair.header.FGPreservesR0" 1]
theorem fwd1 (h : sa_impl% "GaloisPair.header.FGPreservesR0") : S1 :=
  fun M => h M

@[sa_backward "GaloisPair.header.FGPreservesR0"]
theorem bwd (s1 : S1) : sa_impl% "GaloisPair.header.FGPreservesR0" :=
  fun n => s1 n

end Alignment.Shadows.GaloisPair.header_FGPreservesR0

/-! ## header.GFLossy

S2 (`(G (F e)).dim = 4`) holds by `rfl` (`poissonLift` sets the dimension to 4) and is not
stated by `GF_ne_id`. The backward checker derives the implementation's witness from S2: the
record ⟨10, 1⟩ is moved to dimension 4, and `4 = 10` is refuted by `Nat.noConfusion`. Because
S2 is definitional, this backward pass is weak evidence. -/
namespace Alignment.Shadows.GaloisPair.header_GFLossy

sa_claim "GaloisPair.header.GFLossy" group "GaloisPair" required
  text "G ∘ F ≠ id (G ∘ F sets every dimension to 4)"
  impl GF_ne_id

@[sa_forward "GaloisPair.header.GFLossy" 1]
theorem fwd1 (h : sa_impl% "GaloisPair.header.GFLossy") : S1 := by
  obtain ⟨e, he⟩ := h
  exact fun heq => he (congrFun heq e)

sa_fail_forward "GaloisPair.header.GFLossy" 2 "S2 ((G ∘ F) e has dimension 4 for every record) holds by rfl, since poissonLift sets dim := 4. impl GF_ne_id (∃ e, G(F e) ≠ e) does not state it, so a checker could only prove S2 without h (vacuous). The value 4 appears only in impl's proof (the witness ⟨10, 1⟩), not in its statement. Remediation: add GaloisPair.unit_dim to impl."

@[sa_backward "GaloisPair.header.GFLossy"]
theorem bwd (_s1 : S1) (s2 : S2) : sa_impl% "GaloisPair.header.GFLossy" :=
  ⟨⟨10, 1⟩, fun he =>
    Nat.noConfusion ((s2 ⟨10, 1⟩).symm.trans (congrArg EpiModel.dim he)) fun h3 =>
      Nat.noConfusion h3 fun h2 => Nat.noConfusion h2 fun h1 =>
        Nat.noConfusion h1 fun h0 => Nat.noConfusion h0⟩

end Alignment.Shadows.GaloisPair.header_GFLossy

/-! ## Header table rows -/

namespace Alignment.Shadows.GaloisPair.table_R9

sa_claim "GaloisPair.table.R9" group "GaloisPair" required
  text "| 9 | G is monotone |"
  impl poissonLift_mono

/-- `Monotone poissonLift` unfolds to `∀ ⦃a b⦄, a ≤ b → poissonLift a ≤ poissonLift b`. -/
@[sa_forward "GaloisPair.table.R9" 1]
theorem fwd1 (h : sa_impl% "GaloisPair.table.R9") : S1 := by
  intro M M' hle
  exact h hle

@[sa_backward "GaloisPair.table.R9"]
theorem bwd (s1 : S1) : sa_impl% "GaloisPair.table.R9" := by
  intro a b hab
  exact s1 a b hab

end Alignment.Shadows.GaloisPair.table_R9

namespace Alignment.Shadows.GaloisPair.table_R10

sa_claim "GaloisPair.table.R10" group "GaloisPair" required
  text "| 10 | Counit: F(G(N)).dim = 3 |"
  impl counit_dim

@[sa_forward "GaloisPair.table.R10" 1]
theorem fwd1 (h : sa_impl% "GaloisPair.table.R10") : S1 :=
  fun N => h N

/-- The impl is universal over `EpiModel`; instantiate at the node model `nodeModel p r`. -/
@[sa_forward "GaloisPair.table.R10" 2]
theorem fwd2 (h : sa_impl% "GaloisPair.table.R10") : S2 :=
  fun p r => h (nodeModel p r)

@[sa_backward "GaloisPair.table.R10"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "GaloisPair.table.R10" :=
  fun n => s1 n

end Alignment.Shadows.GaloisPair.table_R10

namespace Alignment.Shadows.GaloisPair.table_R11

sa_claim "GaloisPair.table.R11" group "GaloisPair" required
  text "| 11 | G(F(E)).dim = 4 for all E |"
  impl unit_dim

@[sa_forward "GaloisPair.table.R11" 1]
theorem fwd1 (h : sa_impl% "GaloisPair.table.R11") : S1 :=
  fun E => h E

/-- The impl is universal over `EpiModel`; instantiate at the edge model `edgeModel p ψ`. -/
@[sa_forward "GaloisPair.table.R11" 2]
theorem fwd2 (h : sa_impl% "GaloisPair.table.R11") : S2 :=
  fun p ψ => h (edgeModel p ψ)

@[sa_backward "GaloisPair.table.R11"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "GaloisPair.table.R11" :=
  fun e => s1 e

end Alignment.Shadows.GaloisPair.table_R11

namespace Alignment.Shadows.GaloisPair.table_R12

sa_claim "GaloisPair.table.R12" group "GaloisPair" required
  text "| 12 | Idempotency: F ∘ G ∘ F = F |"
  impl F_G_F_eq_F

@[sa_forward "GaloisPair.table.R12" 1]
theorem fwd1 (h : sa_impl% "GaloisPair.table.R12") : S1 :=
  funext fun e => h e

@[sa_backward "GaloisPair.table.R12"]
theorem bwd (s1 : S1) : sa_impl% "GaloisPair.table.R12" :=
  fun e => congrFun s1 e

end Alignment.Shadows.GaloisPair.table_R12

namespace Alignment.Shadows.GaloisPair.table_R13

sa_claim "GaloisPair.table.R13" group "GaloisPair" required
  text "| 13 | Idempotency: G ∘ F ∘ G = G |"
  impl G_F_G_eq_G

@[sa_forward "GaloisPair.table.R13" 1]
theorem fwd1 (h : sa_impl% "GaloisPair.table.R13") : S1 :=
  funext fun n => h n

@[sa_backward "GaloisPair.table.R13"]
theorem bwd (s1 : S1) : sa_impl% "GaloisPair.table.R13" :=
  fun n => congrFun s1 n

end Alignment.Shadows.GaloisPair.table_R13

/-! ## table.R14 -/
namespace Alignment.Shadows.GaloisPair.table_R14

sa_claim "GaloisPair.table.R14" group "GaloisPair" required
  text "| 14 | G ∘ F ≠ id (G ∘ F forgets the dimension) |"
  impl GF_ne_id

@[sa_forward "GaloisPair.table.R14" 1]
theorem fwd1 (h : sa_impl% "GaloisPair.table.R14") : S1 := by
  obtain ⟨e, he⟩ := h
  exact fun heq => he (congrFun heq e)

sa_fail_forward "GaloisPair.table.R14" 2 "S2 (G ∘ F gives every record the same dimension) holds by rfl, since both sides reduce to 4. impl GF_ne_id (∃ e, G(F e) ≠ e) does not state it, so a checker could only prove S2 without h (vacuous)."

sa_fail_backward "GaloisPair.table.R14" "impl is the closed existential ∃ e, G(F e) ≠ e. S1 (G ∘ F ≠ id) gives a witness only by classical logic (not_forall), which is not structural. S2 says the dimensions of all G(F e) agree but gives no value, so with S2 alone the witness's inequality is a closed kernel computation (4 ≠ 10) that ignores the shadows, and a backward checker would be vacuous."

end Alignment.Shadows.GaloisPair.table_R14

namespace Alignment.Shadows.GaloisPair.table_R15

sa_claim "GaloisPair.table.R15" group "GaloisPair" required
  text "| 15 | Round-trip preserves R₀ |"
  impl FG_preserves_R0

@[sa_forward "GaloisPair.table.R15" 1]
theorem fwd1 (h : sa_impl% "GaloisPair.table.R15") : S1 :=
  fun M => h M

@[sa_backward "GaloisPair.table.R15"]
theorem bwd (s1 : S1) : sa_impl% "GaloisPair.table.R15" :=
  fun n => s1 n

end Alignment.Shadows.GaloisPair.table_R15

/-! ## Numbered results (theorem docstrings) -/

namespace Alignment.Shadows.GaloisPair.R9

sa_claim "GaloisPair.R9" group "GaloisPair" required
  text "**Result 9.** G is (trivially) monotone."
  impl poissonLift_mono

@[sa_forward "GaloisPair.R9" 1]
theorem fwd1 (h : sa_impl% "GaloisPair.R9") : S1 := by
  intro M M' hle
  exact h hle

@[sa_backward "GaloisPair.R9"]
theorem bwd (s1 : S1) : sa_impl% "GaloisPair.R9" := by
  intro a b hab
  exact s1 a b hab

end Alignment.Shadows.GaloisPair.R9

namespace Alignment.Shadows.GaloisPair.R10

sa_claim "GaloisPair.R10" group "GaloisPair" required
  text "**Result 10.** Counit: F(G(N)).dim = 3."
  impl counit_dim

@[sa_forward "GaloisPair.R10" 1]
theorem fwd1 (h : sa_impl% "GaloisPair.R10") : S1 :=
  fun N => h N

@[sa_forward "GaloisPair.R10" 2]
theorem fwd2 (h : sa_impl% "GaloisPair.R10") : S2 :=
  fun p r => h (nodeModel p r)

@[sa_backward "GaloisPair.R10"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "GaloisPair.R10" :=
  fun n => s1 n

end Alignment.Shadows.GaloisPair.R10

namespace Alignment.Shadows.GaloisPair.R11

sa_claim "GaloisPair.R11" group "GaloisPair" required
  text "**Result 11.** G(F(E)).dim = 4 for all E."
  impl unit_dim

@[sa_forward "GaloisPair.R11" 1]
theorem fwd1 (h : sa_impl% "GaloisPair.R11") : S1 :=
  fun E => h E

@[sa_forward "GaloisPair.R11" 2]
theorem fwd2 (h : sa_impl% "GaloisPair.R11") : S2 :=
  fun p ψ => h (edgeModel p ψ)

@[sa_backward "GaloisPair.R11"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "GaloisPair.R11" :=
  fun e => s1 e

end Alignment.Shadows.GaloisPair.R11

namespace Alignment.Shadows.GaloisPair.R12

sa_claim "GaloisPair.R12" group "GaloisPair" required
  text "**Result 12.** F ∘ G ∘ F = F (left idempotency)."
  impl F_G_F_eq_F

@[sa_forward "GaloisPair.R12" 1]
theorem fwd1 (h : sa_impl% "GaloisPair.R12") : S1 :=
  funext fun e => h e

@[sa_backward "GaloisPair.R12"]
theorem bwd (s1 : S1) : sa_impl% "GaloisPair.R12" :=
  fun e => congrFun s1 e

end Alignment.Shadows.GaloisPair.R12

namespace Alignment.Shadows.GaloisPair.R13

sa_claim "GaloisPair.R13" group "GaloisPair" required
  text "**Result 13.** G ∘ F ∘ G = G (right idempotency)."
  impl G_F_G_eq_G

@[sa_forward "GaloisPair.R13" 1]
theorem fwd1 (h : sa_impl% "GaloisPair.R13") : S1 :=
  funext fun n => h n

@[sa_backward "GaloisPair.R13"]
theorem bwd (s1 : S1) : sa_impl% "GaloisPair.R13" :=
  fun n => congrFun s1 n

end Alignment.Shadows.GaloisPair.R13

/-! ## R14a (as for `header.GFLossy`; the backward pass is weak evidence because S2 is
definitional) -/
namespace Alignment.Shadows.GaloisPair.R14a

sa_claim "GaloisPair.R14a" group "GaloisPair" required
  text "**Result 14.** G ∘ F ≠ id: G ∘ F sets the dimension of every record to 4."
  impl GF_ne_id

@[sa_forward "GaloisPair.R14a" 1]
theorem fwd1 (h : sa_impl% "GaloisPair.R14a") : S1 := by
  obtain ⟨e, he⟩ := h
  exact fun heq => he (congrFun heq e)

sa_fail_forward "GaloisPair.R14a" 2 "S2 ((G ∘ F) e has dimension 4 for every record) holds by rfl, since poissonLift sets dim := 4. impl GF_ne_id (∃ e, G(F e) ≠ e) does not state it, so a checker could only prove S2 without h (vacuous). Remediation: add GaloisPair.unit_dim to impl."

@[sa_backward "GaloisPair.R14a"]
theorem bwd (_s1 : S1) (s2 : S2) : sa_impl% "GaloisPair.R14a" :=
  ⟨⟨10, 1⟩, fun he =>
    Nat.noConfusion ((s2 ⟨10, 1⟩).symm.trans (congrArg EpiModel.dim he)) fun h3 =>
      Nat.noConfusion h3 fun h2 => Nat.noConfusion h2 fun h1 =>
        Nat.noConfusion h1 fun h0 => Nat.noConfusion h0⟩

end Alignment.Shadows.GaloisPair.R14a

namespace Alignment.Shadows.GaloisPair.coarseGrainR0

sa_claim "GaloisPair.coarseGrainR0" group "GaloisPair" required
  text "F preserves R₀."
  impl coarseGrain_R0

@[sa_forward "GaloisPair.coarseGrainR0" 1]
theorem fwd1 (h : sa_impl% "GaloisPair.coarseGrainR0") : S1 :=
  fun M => h M

@[sa_backward "GaloisPair.coarseGrainR0"]
theorem bwd (s1 : S1) : sa_impl% "GaloisPair.coarseGrainR0" :=
  fun e => s1 e

end Alignment.Shadows.GaloisPair.coarseGrainR0

namespace Alignment.Shadows.GaloisPair.poissonLiftR0

sa_claim "GaloisPair.poissonLiftR0" group "GaloisPair" required
  text "G preserves R₀."
  impl poissonLift_R0

@[sa_forward "GaloisPair.poissonLiftR0" 1]
theorem fwd1 (h : sa_impl% "GaloisPair.poissonLiftR0") : S1 :=
  fun M => h M

@[sa_backward "GaloisPair.poissonLiftR0"]
theorem bwd (s1 : S1) : sa_impl% "GaloisPair.poissonLiftR0" :=
  fun n => s1 n

end Alignment.Shadows.GaloisPair.poissonLiftR0

namespace Alignment.Shadows.GaloisPair.R15

sa_claim "GaloisPair.R15" group "GaloisPair" required
  text "**Result 15.** The round-trip F ∘ G preserves R₀ exactly."
  impl FG_preserves_R0

@[sa_forward "GaloisPair.R15" 1]
theorem fwd1 (h : sa_impl% "GaloisPair.R15") : S1 :=
  fun M => h M

@[sa_backward "GaloisPair.R15"]
theorem bwd (s1 : S1) : sa_impl% "GaloisPair.R15" :=
  fun n => s1 n

end Alignment.Shadows.GaloisPair.R15

/-! ## fgEqSelfOfDimThree -/
namespace Alignment.Shadows.GaloisPair.fgEqSelfOfDimThree

sa_claim "GaloisPair.fgEqSelfOfDimThree" group "GaloisPair" required
  text "F ∘ G is the identity on records of dimension 3."
  impl FG_eq_self_of_dim_three

@[sa_forward "GaloisPair.fgEqSelfOfDimThree" 1]
theorem fwd1 (h : sa_impl% "GaloisPair.fgEqSelfOfDimThree") : S1 := fun e he => h e he

@[sa_backward "GaloisPair.fgEqSelfOfDimThree"]
theorem bwd (s1 : S1) : sa_impl% "GaloisPair.fgEqSelfOfDimThree" := fun e he => s1 e he

end Alignment.Shadows.GaloisPair.fgEqSelfOfDimThree

/-! ## notGaloisConnectionCoarseGrainPoissonLift -/
namespace Alignment.Shadows.GaloisPair.notGaloisConnectionCoarseGrainPoissonLift

sa_claim "GaloisPair.notGaloisConnectionCoarseGrainPoissonLift" group "GaloisPair" required
  text "F and G are not a Galois connection for the dimension preorder on `EpiModel`: for E = ⟨10, 1⟩ and N = ⟨3, 1⟩, F(E) ≤ N holds but E ≤ G(N) fails."
  impl not_galoisConnection_coarseGrain_poissonLift

@[sa_forward "GaloisPair.notGaloisConnectionCoarseGrainPoissonLift" 1]
theorem fwd1 (h : sa_impl% "GaloisPair.notGaloisConnectionCoarseGrainPoissonLift") : S1 := h

sa_fail_forward "GaloisPair.notGaloisConnectionCoarseGrainPoissonLift" 2 "impl states only ¬ GaloisConnection coarseGrain poissonLift. The witness inequality F⟨10, 1⟩ ≤ ⟨3, 1⟩ (i.e. 3 ≤ 3 in ℕ) appears only in impl's proof. It is a closed fact that a checker could prove only without h (and Nat.le.refl is a core-library constructor, not structural), so S2 does not follow from impl's statement."

sa_fail_forward "GaloisPair.notGaloisConnectionCoarseGrainPoissonLift" 3 "impl states only ¬ GaloisConnection coarseGrain poissonLift. S3 (¬ ⟨10, 1⟩ ≤ G⟨3, 1⟩, i.e. ¬ 10 ≤ 4) appears only in impl's proof. The negation of a Galois connection does not identify which pair fails, so S3 does not follow from impl's statement."

@[sa_backward "GaloisPair.notGaloisConnectionCoarseGrainPoissonLift"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) :
    sa_impl% "GaloisPair.notGaloisConnectionCoarseGrainPoissonLift" := s1

end Alignment.Shadows.GaloisPair.notGaloisConnectionCoarseGrainPoissonLift

/-! ## notGaloisConnectionPoissonLiftCoarseGrain -/
namespace Alignment.Shadows.GaloisPair.notGaloisConnectionPoissonLiftCoarseGrain

sa_claim "GaloisPair.notGaloisConnectionPoissonLiftCoarseGrain" group "GaloisPair" required
  text "G and F are not a Galois connection in the other order either: for E = N = ⟨3, 1⟩, E ≤ F(N) holds but G(E) ≤ N fails."
  impl not_galoisConnection_poissonLift_coarseGrain

@[sa_forward "GaloisPair.notGaloisConnectionPoissonLiftCoarseGrain" 1]
theorem fwd1 (h : sa_impl% "GaloisPair.notGaloisConnectionPoissonLiftCoarseGrain") : S1 := h

sa_fail_forward "GaloisPair.notGaloisConnectionPoissonLiftCoarseGrain" 2 "impl states only ¬ GaloisConnection poissonLift coarseGrain. The witness inequality ⟨3, 1⟩ ≤ F⟨3, 1⟩ (i.e. 3 ≤ 3 in ℕ) appears only in impl's proof. It is a closed fact that a checker could prove only without h, so S2 does not follow from impl's statement."

sa_fail_forward "GaloisPair.notGaloisConnectionPoissonLiftCoarseGrain" 3 "impl states only ¬ GaloisConnection poissonLift coarseGrain. S3 (¬ G⟨3, 1⟩ ≤ ⟨3, 1⟩, i.e. ¬ 4 ≤ 3) appears only in impl's proof, and the negation of a Galois connection does not identify the failing pair, so S3 does not follow."

@[sa_backward "GaloisPair.notGaloisConnectionPoissonLiftCoarseGrain"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) :
    sa_impl% "GaloisPair.notGaloisConnectionPoissonLiftCoarseGrain" := s1

end Alignment.Shadows.GaloisPair.notGaloisConnectionPoissonLiftCoarseGrain

/-! ## `GaloisPair.R14b` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.GaloisPair.R14b

sa_claim "GaloisPair.R14b" group "GaloisPair"
  text "Witness: a record of dimension 10 maps to dimension 3 via F and back to dimension 4 via G."
  impl

end Alignment.Shadows.GaloisPair.R14b

/-! ## `GaloisPair.header.galoisConnection` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.GaloisPair.header_galoisConnection

sa_claim "GaloisPair.header.galoisConnection" group "GaloisPair"
  text "F and G are not a Galois connection for the dimension preorder: for E = ⟨10, r⟩ and N = ⟨3, r⟩, F(E) ≤ N holds but E ≤ G(N) fails (`not_galoisConnection_coarseGrain_poissonLift`)."
  impl

end Alignment.Shadows.GaloisPair.header_galoisConnection
