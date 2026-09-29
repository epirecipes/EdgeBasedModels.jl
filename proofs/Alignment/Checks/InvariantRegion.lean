import Alignment.Registry
import Alignment.Shadows.InvariantRegion

/-!
# Checkers: group `InvariantRegion`

Checker author (SA-PASS role 3, non-blind). For every claim of `EBCMCategory/InvariantRegion.lean`
with `status: implemented` this file holds the `sa_claim` registration (verbatim registry text,
registry `impl` list in registry order), the forward checkers `sa_impl% → Sᵢ`, the backward checker
`S₁ → … → Sₙ → sa_impl%`, and `sa_fail_*` records where a check cannot be proved because the
implementation says something different from the shadow.

No bridges are declared. The only trusted definition in the module is `PolyPGF.eval`, which the
shadows use exactly as the implementation does. The EBCM vector field, ψ′, S, I and dI/dt have
no trusted definitions: the implementation writes them as inline expressions over free rationals,
and the shadows write them as alignment helpers (`pgfDeriv`, `phiIDot`, `RDot`, `IDot`). A bridge
needs a trusted definition at the head of its left-hand side, so none of the purely algebraic
differences below (e.g. `-(β * φ_I)` against `-β * φ_I`, not definitionally equal over ℚ because
`Rat.mul` normalises by gcd) can be bridged. They are recorded as failures.

Conventions of the proofs below (README "Writing structural proofs"): `intro`, `exact`,
projections of conjunctions and iffs, `subst`/`rw` with a face equation, and definitional
unfolding of the shadow helpers. Three alignment helpers build data (their proof fields are
arguments of data terms and are skipped by the audit; README "What the audit checks"):

* `chkUnitPGF : PolyPGF 1`, the PGF of the point mass at degree 0 (ψ(x) = 1), used as an
  inhabitant of the implementation's unused `_ψ` argument and, in one backward check, because
  `chkUnitPGF.eval 1` reduces to `1` by closed kernel computation (README "Known limitations" 1);
* `chkPt φ hφ : EBCMRegion`, the region point (θ, φ_I, φ_R, R) = (0, φ, 0, 0);
* the forward checker of `iNonnegFromRegion` S1 builds the region point `x` with its `R`
  replaced by a given `R ≥ 0`.

The implementation's `0 ≤ ψ'_θ` hypothesis of `invariant_region_boundary_conditions` is
discharged at `ψ'_θ := 0` by `rfl` (`(0:ℚ) ≤ 0` unfolds to `Rat.blt 0 0 = false`, a closed kernel
computation).

Recurring failure causes (see each record):

* formulation only: `-(β * φ_I)` in the implementation against `-β * φ_I` in the shadows; `≤`
  against the shadows' `= ∨ <`; the chain-rule drift `IDot` against the bare products of the
  implementation. These are equal over ℚ only by ring or order lemmas;
* data invariants: `0 ≤ φ_I` at a region point is only the `EBCMRegion` field `x.hφ_I`, and
  `Σᵢ pᵢ = 1` is only the field `ψ.sum_one`. A structural proof may not extract either;
* free-scalar abstraction: the implementation quantifies over free rationals (ψ'_θ, ψ'_1, S, I)
  where the shadows use ψ′(θ), ψ(θ) or 1 − ψ(θ) − R, so backward checks fail;
* missing content: no θ = 0 or R = 0 face conjunct, a literal `(0:ℚ) = 0` for the φ_I face, no
  trajectory statements, no PGF in the seed identities, a reflexivity for `iDotGeneral.a`.
-/

open InvariantRegion

namespace Alignment.Shadows.InvariantRegion

/-- The PGF of the point mass at degree 0: `coeffs = fun _ => 1` on `Fin 1`, so ψ(x) = 1·x⁰.
The proof fields are closed kernel computations (arguments of a data term). -/
def chkUnitPGF : PolyPGF 1 := ⟨fun _ => 1, fun _ => rfl, by with_unfolding_all rfl⟩

/-- The region point (θ, φ_I, φ_R, R) = (0, φ, 0, 0). The bounds are closed kernel computations
and `hφ`; all are arguments of a data term. -/
def chkPt (φ : ℚ) (hφ : 0 ≤ φ) : EBCMRegion := ⟨0, φ, 0, 0, rfl, rfl, hφ, rfl, rfl⟩

end Alignment.Shadows.InvariantRegion

/-! ## header.faceConditions

Only the φ_R face (S4) is a projection of the implementation (third conjunct, instantiated at the
shadow's ψ and at `ψ'_θ := 0` with `(0:ℚ) ≤ 0` by `rfl`). -/
namespace Alignment.Shadows.InvariantRegion.header_faceConditions

sa_claim "InvariantRegion.header.faceConditions" group "InvariantRegion" required
  text "**Sign/monotone conditions**: at each face of the region the component of the vector field normal to the face is ≥ 0 (it vanishes or points inward), given the constraints φ_I ≤ θ and S + R ≤ 1, which `EBCMRegion` omits."
  impl InvariantRegion.invariant_region_boundary_conditions

sa_fail_forward "InvariantRegion.header.faceConditions" 1 "impl invariant_region_boundary_conditions has no θ = 0 face conjunct. Its first conjunct is -(β φ_I) ≤ 0 (θ non-increasing), the opposite sign of S1's 0 ≤ -β φ_I. S1 needs φ_I = 0 from φ_I ≤ θ = 0 and 0 ≤ φ_I (order antisymmetry plus the region invariant hφ_I), which impl does not state."

sa_fail_forward "InvariantRegion.header.faceConditions" 2 "impl gives -(β·φ_I) ≤ 0. S2 is 0 ≤ -(-β·φ_I). Going from one to the other needs neg_mul (-β·φ_I = -(β·φ_I), not definitional in ℚ because Rat.mul normalises by gcd) and neg_nonneg, which are library lemmas."

sa_fail_forward "InvariantRegion.header.faceConditions" 3 "impl's φ_I-face conjunct is the placeholder (0:ℚ) = 0 (its docstring: 'In the Lean statement this conjunct is the placeholder'). It says nothing about the φ_I component correctQ of the vector field at φ_I = 0 (S3)."

@[sa_forward "InvariantRegion.header.faceConditions" 4]
theorem fwd4 (h : sa_impl% "InvariantRegion.header.faceConditions") : S4 :=
  fun x p _n ψ _ _ => (@h p _ ψ x 0 rfl).2.2.1

sa_fail_forward "InvariantRegion.header.faceConditions" 5 "impl's fourth conjunct is the I-face drift 0 ≤ β·φ_I·ψ'_θ (dI/dt at I = 0). S5 is the R-face condition 0 ≤ γ(1 − ψ(θ) − R) at R = 0 (dR/dt), a different face and a different component. impl says nothing about dR/dt."

sa_fail_backward "InvariantRegion.header.faceConditions" "impl holds at every point of EBCMRegion without the face equations: its first conjunct -(β φ_I) ≤ 0 and its fourth 0 ≤ β φ_I ψ'_θ for an arbitrary ψ'_θ ≥ 0. The shadows state the conditions only on the faces (θ = 1, φ_R = 0, …) and under Hyp (φ_I ≤ θ, S + R ≤ 1), and the I-face drift with a free ψ'_θ appears in none of them. So impl does not follow from the shadow set: it is a statement about a different set of points."

end Alignment.Shadows.InvariantRegion.header_faceConditions

/-! ## `InvariantRegion.pgfEvalOne` -/

namespace Alignment.Shadows.InvariantRegion.pgfEvalOne

sa_claim "InvariantRegion.pgfEvalOne" group "InvariantRegion" required
  text "ψ(1) = 1: the PGF evaluated at 1 gives total probability mass."
  impl InvariantRegion.pgf_eval_one

@[sa_forward "InvariantRegion.pgfEvalOne" 1]
theorem fwd1 (h : sa_impl% "InvariantRegion.pgfEvalOne") : S1 := by
  intro n ψ
  exact h ψ

sa_fail_forward "InvariantRegion.pgfEvalOne" 2 "impl states only ψ.eval 1 = 1. S2 requires ψ.eval 1 = Σᵢ ψ.coeffs i (the total probability mass). Obtaining it from impl needs 1 = Σᵢ pᵢ, which is the PolyPGF field ψ.sum_one, a data invariant that a structural proof may not extract. ψ.eval 1 unfolds to Σᵢ pᵢ·1^i, which is not definitionally Σᵢ pᵢ (that needs one_pow and mul_one). impl never mentions Σᵢ pᵢ."

@[sa_backward "InvariantRegion.pgfEvalOne"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "InvariantRegion.pgfEvalOne" := by
  intro n ψ
  exact s1 n ψ

end Alignment.Shadows.InvariantRegion.pgfEvalOne

/-! ## `InvariantRegion.R113` -/

namespace Alignment.Shadows.InvariantRegion.R113

sa_claim "InvariantRegion.R113" group "InvariantRegion" required
  text "**Result 113.** ψ(x) ≥ 0 for all x ∈ [0, 1]."
  impl InvariantRegion.pgf_nonneg_on_unit_interval

/-- The implementation needs only `0 ≤ x`; the text's upper bound `x ≤ 1` is dropped. -/
@[sa_forward "InvariantRegion.R113" 1]
theorem fwd1 (h : sa_impl% "InvariantRegion.R113") : S1 := by
  intro n ψ x h0 _
  exact h ψ x h0

sa_fail_backward "InvariantRegion.R113" "impl is stronger than the text. pgf_nonneg_on_unit_interval proves 0 ≤ ψ(x) for every x ≥ 0, with no x ≤ 1 hypothesis. S1 (the text, x ∈ [0, 1]) covers only x ≤ 1, so impl's instances with x > 1 cannot be derived from S1."

end Alignment.Shadows.InvariantRegion.R113

/-! ## `InvariantRegion.R114` -/

namespace Alignment.Shadows.InvariantRegion.R114

sa_claim "InvariantRegion.R114" group "InvariantRegion" required
  text "**Result 114.** ψ(x) ≤ 1 for all x ∈ [0, 1]."
  impl InvariantRegion.pgf_le_one_on_unit_interval

@[sa_forward "InvariantRegion.R114" 1]
theorem fwd1 (h : sa_impl% "InvariantRegion.R114") : S1 := by
  intro n ψ x h0 h1
  exact h ψ x h0 h1

@[sa_backward "InvariantRegion.R114"]
theorem bwd (s1 : S1) : sa_impl% "InvariantRegion.R114" := by
  intro n ψ x h0 h1
  exact s1 n ψ x h0 h1

end Alignment.Shadows.InvariantRegion.R114

/-! ## `InvariantRegion.R115` -/

namespace Alignment.Shadows.InvariantRegion.R115

sa_claim "InvariantRegion.R115" group "InvariantRegion" required
  text "**Result 115.** S = ψ(θ) ∈ [0, 1] whenever θ ∈ [0, 1]."
  impl InvariantRegion.S_in_unit_interval

@[sa_forward "InvariantRegion.R115" 1]
theorem fwd1 (h : sa_impl% "InvariantRegion.R115") : S1 := by
  intro n ψ θ h0 h1
  exact (h ψ θ h0 h1).1

@[sa_forward "InvariantRegion.R115" 2]
theorem fwd2 (h : sa_impl% "InvariantRegion.R115") : S2 := by
  intro n ψ θ h0 h1
  exact (h ψ θ h0 h1).2

@[sa_backward "InvariantRegion.R115"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "InvariantRegion.R115" := by
  intro n ψ θ h0 h1
  exact ⟨s1 n ψ θ h0 h1, s2 n ψ θ h0 h1⟩

end Alignment.Shadows.InvariantRegion.R115

/-! ## `InvariantRegion.R116a` -/

namespace Alignment.Shadows.InvariantRegion.R116a

sa_claim "InvariantRegion.R116a" group "InvariantRegion" required
  text "**Result 116.** dθ/dt = −β φ_I ≤ 0 when φ_I ≥ 0."
  impl InvariantRegion.theta_dot_nonpos

sa_fail_forward "InvariantRegion.R116a" 1 "impl states -(β·φ_I) ≤ 0, i.e. Neg.neg (p.β * φ_I). S1 renders the text's −β φ_I as (-β)·φ_I, i.e. (-p.β) * φI ≤ 0. The two terms are equal only by the ring lemma neg_mul. They are not definitionally equal over ℚ (Rat.mul normalises by gcd, and rfl fails), and there is no trusted definition of dθ/dt that a bridge could identify. The difference is in formulation only, but it cannot be closed structurally."
sa_fail_backward "InvariantRegion.R116a" "S1 gives (-β)·φ_I ≤ 0, while impl needs -(β·φ_I) ≤ 0. These are equal only by neg_mul, not definitionally over ℚ, and there is no trusted dθ/dt definition to bridge. The difference is in formulation only."

end Alignment.Shadows.InvariantRegion.R116a

/-! ## R117a -/
namespace Alignment.Shadows.InvariantRegion.R117a

sa_claim "InvariantRegion.R117a" group "InvariantRegion" required
  text "**Result 117.** When φ_I = 0, the full φ_I component of the EBCM vector field vanishes: dφ_I/dt = β φ_I ψ″(θ)/ψ′(1) − (β + γ) φ_I = 0. The Lean statement uses the incorrect form (β φ_I / θ)(ψ′(θ)/ψ′(1)) − (β + γ) φ_I; the correct form is `phi_I_dot_correct_zero_at_boundary`."
  impl InvariantRegion.phi_I_dot_zero_at_boundary

sa_fail_forward "InvariantRegion.R117a" 1 "impl phi_I_dot_zero_at_boundary is stated for the incorrect form (β·0/θ)(ψ'_θ/ψ'_1) − (β+γ)·0 over free rationals, as the text itself says ('The Lean statement uses the incorrect form'). S1 is about the correct field correctQ = β·φ_I·ψ″(θ)/ψ′(1) − (β+γ)·φ_I at φ_I = 0, a different expression (no 1/θ, different grouping), so S1 does not follow from h. The correct form is InvariantRegion.phiIDotCorrectZeroAtBoundary."

sa_fail_backward "InvariantRegion.R117a" "impl's left-hand side is the incorrect form (β·0/θ)(ψ'_θ/ψ'_1) − (β+γ)·0 for free θ, ψ'_θ, ψ'_1; S1 is about the correct field correctQ. The two expressions are different, so S1 does not give impl structurally."

end Alignment.Shadows.InvariantRegion.R117a

/-! ## `InvariantRegion.phiIDotFactors.a` -/

namespace Alignment.Shadows.InvariantRegion.phiIDotFactors_a

sa_claim "InvariantRegion.phiIDotFactors.a" group "InvariantRegion" required
  text "More general: when φ_I ≥ 0, the φ_I-derivative factors as φ_I × (something), [...] Concretely, for θ > 0 the derivative has the form φ_I * f(θ) for some f;"
  impl InvariantRegion.phi_I_dot_factors

sa_fail_forward "InvariantRegion.phiIDotFactors.a" 1 "impl phi_I_dot_factors has the extra hypothesis 0 < ψ'_1, i.e. ψ′(1) > 0. S1 quantifies over every PolyPGF, including those with ψ′(1) = 0 (all mass at degree 0), for which impl says nothing. Even when ψ′(1) > 0, a proof of 0 < pgfDeriv ψ 1 needs library lemmas, and a case split on ψ′(1) = 0 needs by_cases. Neither is structural. S1 still holds in the degenerate case under Lean's x/0 = 0, but not from impl."
sa_fail_backward "InvariantRegion.phiIDotFactors.a" "impl asserts one explicit factorisation, with factor β·ψ'_θ/(θ·ψ'_1) - (β+γ), for arbitrary rationals ψ'_θ and ψ'_1 > 0 and every φ_I (no φ_I ≥ 0 hypothesis). S1 only asserts that some f exists with dφ_I/dt = φ_I·f(θ), for the PGF-derived ψ′(θ)/ψ′(1) and φ_I ≥ 0. Neither the explicit factor, nor the free-scalar instances, nor the instances with φ_I < 0 can be derived from S1."

end Alignment.Shadows.InvariantRegion.phiIDotFactors_a

/-! ## `InvariantRegion.R118a` -/

namespace Alignment.Shadows.InvariantRegion.R118a

sa_claim "InvariantRegion.R118a" group "InvariantRegion" required
  text "**Result 118.** dφ_R/dt = γ φ_I ≥ 0 when φ_I ≥ 0."
  impl InvariantRegion.phi_R_dot_nonneg

@[sa_forward "InvariantRegion.R118a" 1]
theorem fwd1 (h : sa_impl% "InvariantRegion.R118a") : S1 := by
  intro p φI hφ
  exact h p hφ

@[sa_backward "InvariantRegion.R118a"]
theorem bwd (s1 : S1) : sa_impl% "InvariantRegion.R118a" := by
  intro p φI hφ
  exact s1 p φI hφ

end Alignment.Shadows.InvariantRegion.R118a

/-! ## `InvariantRegion.R119a` -/

namespace Alignment.Shadows.InvariantRegion.R119a

sa_claim "InvariantRegion.R119a" group "InvariantRegion" required
  text "**Result 119.** dR/dt = γ I ≥ 0 when I ≥ 0."
  impl InvariantRegion.R_dot_nonneg

/-- `RDot p ψ θ R` unfolds to `p.γ * (1 - ψ.eval θ - R)`: the implementation at
`I := 1 - ψ(θ) - R`. -/
@[sa_forward "InvariantRegion.R119a" 1]
theorem fwd1 (h : sa_impl% "InvariantRegion.R119a") : S1 := by
  intro p n ψ θ R hI
  exact h p (I := 1 - ψ.eval θ - R) hI

sa_fail_backward "InvariantRegion.R119a" "free-scalar abstraction. impl R_dot_nonneg is stated for a free rational I (0 ≤ I → 0 ≤ γ·I). S1 speaks only of I = 1 - ψ(θ) - R. Every rational I has that form (take R := 1 - ψ(θ) - I), but only by the ring identity 1 - a - (1 - a - I) = I, which is not definitional over ℚ. So impl's instances are not structurally derivable from S1, although the two statements are logically equivalent."

end Alignment.Shadows.InvariantRegion.R119a

/-! ## `InvariantRegion.R120` -/

namespace Alignment.Shadows.InvariantRegion.R120

sa_claim "InvariantRegion.R120" group "InvariantRegion" required
  text "**Result 120.** S + I + R = 1 holds as an *algebraic identity* because the EBCM defines I := 1 − S − R. No ODE solution theory is required."
  impl InvariantRegion.SIR_conservation

/-- The implementation at `S := ψ(θ)`; its `let I := 1 - S - R` ζ-reduces to the shadow body. -/
@[sa_forward "InvariantRegion.R120" 1]
theorem fwd1 (h : sa_impl% "InvariantRegion.R120") : S1 := by
  intro n ψ θ R
  exact h (ψ.eval θ) R

sa_fail_backward "InvariantRegion.R120" "SHADOW?: impl SIR_conservation is the identity S + (1 - S - R) + R = 1 for arbitrary rationals S and R. S1 restricts S to ψ(θ) for a PolyPGF ψ. Every rational S equals ψ(θ) for ψ(x) = x and θ = S, but only up to ring normalisation (ψ.eval θ = 0·θ⁰ + 1·θ¹), not definitionally, so impl is not structurally derivable from S1. The text '**Result 120.** S + I + R = 1 holds as an *algebraic identity* because the EBCM defines I := 1 − S − R' states an identity in S and R that follows from the definition of I alone and never restricts S to ψ(θ). impl's free-S form therefore looks like the intended reading, and S1's specialisation S = ψ(θ) looks narrower than the text."

end Alignment.Shadows.InvariantRegion.R120

/-! ## `InvariantRegion.R120b` -/

namespace Alignment.Shadows.InvariantRegion.R120b

sa_claim "InvariantRegion.R120b" group "InvariantRegion" required
  text "**Result 120b.** Under the explicit seed convention used by the Julia builders, θ(0)=1 and the susceptible observable is `(1-ρ)ψ(θ)`. Since every PGF satisfies ψ(1)=1, the initial observable values are S(0)=1−ρ, I(0)=ρ, R(0)=0 and therefore conserve total population."
  impl InvariantRegion.explicit_seed_initial_conservation

sa_fail_forward "InvariantRegion.R120b" 1 "impl explicit_seed_initial_conservation is the ring identity (1 - ρ) + ρ + 0 = 1 over ℚ. It mentions no PGF, θ(0) = 1 or ψ(1), and does not state S(0) = (1 - ρ)·ψ(1) = 1 - ρ. S1 needs ψ(1) = 1, which is the separate theorem pgf_eval_one or the PolyPGF data invariant sum_one. Neither is usable structurally, and impl cannot supply it."
sa_fail_forward "InvariantRegion.R120b" 2 "impl gives (1 - ρ) + ρ + 0 = 1, with S(0) already replaced by the literal 1 - ρ. S2 requires (1 - ρ)·ψ(1) + ρ + 0 = 1 for every PolyPGF ψ. That needs (1 - ρ)·ψ(1) = 1 - ρ, i.e. ψ(1) = 1 and mul_one. impl omits this PGF step, which the text cites ('Since every PGF satisfies ψ(1)=1')."
sa_fail_forward "InvariantRegion.R120b" 3 "impl does not state the observable I(0) = 1 - S(0) - R(0) = ρ. S3 requires 1 - (1 - ρ)·ψ(1) - 0 = ρ, which needs ψ(1) = 1 plus ring algebra (sub_sub_cancel, sub_zero). It cannot be derived from (1 - ρ) + ρ + 0 = 1 by structural steps."

/-- `S1` rewrites `(1 - ρ)·ψ(1)` to `1 - ρ` inside `S2` (any PGF; `chkUnitPGF` is used). -/
@[sa_backward "InvariantRegion.R120b"]
theorem bwd (s1 : S1) (s2 : S2) (_s3 : S3) : sa_impl% "InvariantRegion.R120b" := by
  intro ρ
  exact (congrArg (fun a => a + ρ + 0) (s1 1 chkUnitPGF ρ)).symm.trans (s2 1 chkUnitPGF ρ)

end Alignment.Shadows.InvariantRegion.R120b

/-! ## R120b.guard

The backward checker instantiates S1 at the point-mass PGF `chkUnitPGF` (whose `eval 1` is `1` by
closed kernel computation), rewrites with the assumed `1 + ρ + 0 = 1`, and obtains `0 = ρ`, which
contradicts `ρ ≠ 0`. -/
namespace Alignment.Shadows.InvariantRegion.R120b_guard

sa_claim "InvariantRegion.R120b.guard" group "InvariantRegion" required
  text "This identity records the arithmetic behind a regression in which the expanded-form EBCM used `S = ψ(θ)` while still seeding `I(0)=ρ`, which overcounted population by exactly ρ at t=0. It is not linked to the Julia builders and cannot detect that regression."
  impl InvariantRegion.missing_seed_factor_overcounts

sa_fail_forward "InvariantRegion.R120b.guard" 1 "impl missing_seed_factor_overcounts states only 1 + ρ + 0 ≠ 1 for ρ ≠ 0. S1 (ψ(1) + ρ + 0 − 1 = ρ for every PGF ψ) needs ψ.eval 1 = 1 (pgf_eval_one, which uses the data field ψ.sum_one) and ring arithmetic. impl does not mention a PGF and gives no equation."

@[sa_backward "InvariantRegion.R120b.guard"]
theorem bwd (s1 : S1) : sa_impl% "InvariantRegion.R120b.guard" := by
  intro ρ hρ h1
  have e : chkUnitPGF.eval 1 + ρ + 0 - 1 = ρ := s1 1 chkUnitPGF ρ
  have e1 : chkUnitPGF.eval 1 = 1 := by with_unfolding_all exact rfl
  rw [e1, h1] at e
  have e0 : (1 : ℚ) - 1 = 0 := by with_unfolding_all exact rfl
  rw [e0] at e
  exact hρ e.symm

end Alignment.Shadows.InvariantRegion.R120b_guard

/-! ## `InvariantRegion.missingSeedFactorOvercounts` -/

namespace Alignment.Shadows.InvariantRegion.missingSeedFactorOvercounts

sa_claim "InvariantRegion.missingSeedFactorOvercounts" group "InvariantRegion" required
  text "If the seed factor is omitted from `S(0)` while `I(0)=ρ`, the total is `1+ρ`; for any nonzero seed this is not a conserved population."
  impl InvariantRegion.missing_seed_factor_overcounts

sa_fail_forward "InvariantRegion.missingSeedFactorOvercounts" 1 "impl states only ρ ≠ 0 → 1 + ρ + 0 ≠ 1. It does not state that the total ψ(1) + ρ + 0 equals 1 + ρ (the text's 'the total is `1+ρ`'). An inequality cannot yield that equation, and ψ(1) = 1 is not available structurally."
sa_fail_forward "InvariantRegion.missingSeedFactorOvercounts" 2 "impl replaces S(0) = ψ(1) by the literal 1 and gives 1 + ρ + 0 ≠ 1. S2 requires ψ(1) + ρ + 0 ≠ 1 for every PolyPGF ψ. That needs the rewrite ψ(1) = 1, which is the separate theorem pgf_eval_one or the data invariant sum_one, not usable structurally."

/-- `S2` at the point-mass PGF `chkUnitPGF`, whose `eval 1` reduces to `1` by closed kernel
computation, is the implementation's statement. -/
@[sa_backward "InvariantRegion.missingSeedFactorOvercounts"]
theorem bwd (_s1 : S1) (s2 : S2) : sa_impl% "InvariantRegion.missingSeedFactorOvercounts" := by
  intro ρ hρ
  with_unfolding_all exact s2 1 chkUnitPGF ρ hρ

end Alignment.Shadows.InvariantRegion.missingSeedFactorOvercounts

/-! ## `InvariantRegion.R121` -/

namespace Alignment.Shadows.InvariantRegion.R121

sa_claim "InvariantRegion.R121" group "InvariantRegion" required
  text "**Result 121.** I ≥ 0 is equivalent to S + R ≤ 1."
  impl InvariantRegion.I_nonneg_iff_SR_le_one

@[sa_forward "InvariantRegion.R121" 1]
theorem fwd1 (h : sa_impl% "InvariantRegion.R121") : S1 := by
  intro n ψ θ R hI
  exact (h (ψ.eval θ) R).mp hI

@[sa_forward "InvariantRegion.R121" 2]
theorem fwd2 (h : sa_impl% "InvariantRegion.R121") : S2 := by
  intro n ψ θ R hSR
  exact (h (ψ.eval θ) R).mpr hSR

sa_fail_backward "InvariantRegion.R121" "free-scalar abstraction. impl I_nonneg_iff_SR_le_one holds for arbitrary rationals S and R. S1 and S2 cover only S = ψ(θ). Every rational S is ψ(θ) for ψ(x) = x and θ = S, but only up to ring normalisation (ψ.eval θ = 0·θ⁰ + 1·θ¹), not definitionally, so impl is not structurally derivable from the shadows."

end Alignment.Shadows.InvariantRegion.R121

/-! ## `InvariantRegion.R122a` -/

namespace Alignment.Shadows.InvariantRegion.R122a

sa_claim "InvariantRegion.R122a" group "InvariantRegion" required
  text "**Result 122.** At the boundary face {I = 0}, the population-level drift is dI/dt = β φ_I ψ′(θ) ≥ 0 whenever φ_I ≥ 0 and ψ′(θ) ≥ 0."
  impl InvariantRegion.I_dot_nonneg_at_zero_boundary

sa_fail_forward "InvariantRegion.R122a" 1 "impl I_dot_nonneg_at_zero_boundary is only the sign statement 0 ≤ β·φ_I·ψ'_θ for free rationals φ_I and ψ'_θ. It does not identify the population-level drift. S1 requires IDot = -(ψ′(θ)·(-β·φ_I)) - γ(1 - ψ(θ) - R) = β·φ_I·ψ′(θ) whenever 1 - ψ(θ) - R = 0. impl states no such equation, and the equation itself needs ring algebra."
sa_fail_forward "InvariantRegion.R122a" 2 "impl gives 0 ≤ β·φ_I·ψ′(θ) at ψ'_θ := ψ′(θ). S2 requires 0 ≤ IDot on {1 - ψ(θ) - R = 0}. impl has no I = 0 hypothesis and no dI/dt. Transferring the sign needs IDot = β·φ_I·ψ′(θ) at I = 0, which holds only by ring algebra (rewriting the face equation leaves -(ψ′(θ)·(-β·φ_I)) - γ·0, and then neg_mul, mul_comm and sub_zero are needed). That is not structural."
sa_fail_backward "InvariantRegion.R122a" "free-scalar abstraction. impl is the bare product inequality 0 ≤ β·φ_I·ψ'_θ for arbitrary rationals φ_I ≥ 0 and ψ'_θ ≥ 0. S1 and S2 concern the drift IDot with ψ′(θ) of a PolyPGF on the face I = 0. Neither the instances at arbitrary ψ'_θ nor the bare-product form (which differs from IDot by ring algebra) can be derived."

end Alignment.Shadows.InvariantRegion.R122a

/-! ## `InvariantRegion.iDotGeneral.a` -/

namespace Alignment.Shadows.InvariantRegion.iDotGeneral_a

sa_claim "InvariantRegion.iDotGeneral.a" group "InvariantRegion" required
  text "Alternative formulation: dI/dt = β φ_I ψ′(θ) − γ I."
  impl InvariantRegion.I_dot_general

sa_fail_forward "InvariantRegion.iDotGeneral.a" 1 "impl I_dot_general is the reflexivity β·φ_I·ψ'_θ - γ·I = β·φ_I·ψ'_θ - γ·I, proved by rfl. It asserts nothing about dI/dt and is a tautological implementation. S1 requires the chain-rule drift IDot = -(ψ′(θ)·(-β·φ_I)) - γ(1 - ψ(θ) - R) to equal β·φ_I·ψ′(θ) - γ·(1 - ψ(θ) - R). impl does not state that, and it holds only by ring algebra (neg_mul, neg_neg, mul_comm). A proof of S1 could not use h."

/-- The implementation is a reflexivity, so it follows from anything (it is never stronger than
the text). -/
@[sa_backward "InvariantRegion.iDotGeneral.a"]
theorem bwd (_s1 : S1) : sa_impl% "InvariantRegion.iDotGeneral.a" := by
  intro p φI ψ'θ I
  exact rfl

end Alignment.Shadows.InvariantRegion.iDotGeneral_a

/-! ## `InvariantRegion.iDotGeneral.b` -/

namespace Alignment.Shadows.InvariantRegion.iDotGeneral_b

sa_claim "InvariantRegion.iDotGeneral.b" group "InvariantRegion" required
  text "When I = 0 the γ I term vanishes, leaving the nonneg inward term."
  impl InvariantRegion.I_dot_at_zero InvariantRegion.I_dot_nonneg_at_zero_boundary

sa_fail_forward "InvariantRegion.iDotGeneral.b" 1 "SHADOW?: impl's first part, I_dot_at_zero, is β·φ_I·ψ'_θ - γ·0 = β·φ_I·ψ'_θ for free rationals: the γ I term of the alternative form dI/dt = β φ_I ψ′(θ) − γ I vanishes at I = 0. S1 instead uses the chain-rule drift IDot. After rewriting the face equation 1 - ψ(θ) - R = 0, S1 becomes -(ψ′(θ)·(-β·φ_I)) - γ·0 = β·φ_I·ψ′(θ), which differs from impl's left side -(a·(-b·c)) against b·c·a by ring algebra, so it is not structural. The text 'When I = 0 the γ I term vanishes, leaving the nonneg inward term' continues 'Alternative formulation: dI/dt = β φ_I ψ′(θ) − γ I' (iDotGeneral.a) and refers to that formula's γ I term. S1 also builds in the chain-rule identity of iDotGeneral.a. Read with dI/dt := β φ_I ψ′(θ) − γ I, S1 would follow structurally from impl (rewrite I = 0, then I_dot_at_zero)."
sa_fail_forward "InvariantRegion.iDotGeneral.b" 2 "SHADOW?: impl's second part gives 0 ≤ β·φ_I·ψ'_θ under φ_I ≥ 0 and ψ'_θ ≥ 0. S2 requires 0 ≤ IDot, the chain-rule drift, on {1 - ψ(θ) - R = 0}. After rewriting the face equation this is 0 ≤ -(ψ′(θ)·(-β·φ_I)) - γ·0, which needs ring algebra to meet impl. As for S1, the text ('When I = 0 the γ I term vanishes, leaving the nonneg inward term') refers to the alternative form β φ_I ψ′(θ) − γ I. Under that reading S2 would follow structurally: rewrite I = 0, then I_dot_at_zero, then I_dot_nonneg_at_zero_boundary."
sa_fail_backward "InvariantRegion.iDotGeneral.b" "free-scalar abstraction. Both impl parts are stated for arbitrary rationals φ_I and ψ'_θ in bare form: β·φ_I·ψ'_θ - γ·0 = β·φ_I·ψ'_θ, and 0 ≤ φ_I → 0 ≤ ψ'_θ → 0 ≤ β·φ_I·ψ'_θ. S1 and S2 concern only IDot with ψ′(θ) of a PolyPGF. Neither the instances at arbitrary ψ'_θ nor the bare forms can be derived from the shadows."

end Alignment.Shadows.InvariantRegion.iDotGeneral_b

/-! ## `InvariantRegion.iDotAtZero` -/

namespace Alignment.Shadows.InvariantRegion.iDotAtZero

sa_claim "InvariantRegion.iDotAtZero" group "InvariantRegion" required
  text "When I = 0, the I-derivative reduces to the nonneg inward term."
  impl InvariantRegion.I_dot_at_zero

sa_fail_forward "InvariantRegion.iDotAtZero" 1 "impl I_dot_at_zero is β·φ_I·ψ'_θ - γ·0 = β·φ_I·ψ'_θ for free rationals. It is the text's alternative form of dI/dt with I replaced by the literal 0, and it has no I = 0 hypothesis on a state. S1 requires the chain-rule drift IDot = -(ψ′(θ)·(-β·φ_I)) - γ(1 - ψ(θ) - R) to equal β·φ_I·ψ′(θ) on 1 - ψ(θ) - R = 0. After rewriting the face equation, the two left sides differ by ring algebra (-(a·(-b·c)) against b·c·a), which is not structural. If 'the I-derivative' were read as the alternative form β φ_I ψ′(θ) − γ I, S1 would follow structurally."
sa_fail_forward "InvariantRegion.iDotAtZero" 2 "impl has no sign statement: I_dot_at_zero is an equation only, and 'nonneg' is not part of it (the registry impl_note says the same). S2 requires 0 ≤ IDot on {I = 0} given φ_I ≥ 0 and ψ′(θ) ≥ 0."
sa_fail_backward "InvariantRegion.iDotAtZero" "free-scalar abstraction. impl is stated for arbitrary rationals φ_I and ψ'_θ, in the bare form β·φ_I·ψ'_θ - γ·0 = β·φ_I·ψ'_θ. S1 and S2 concern IDot with ψ′(θ) of a PolyPGF. Neither impl's instances at arbitrary ψ'_θ nor its form can be derived from the shadows."

end Alignment.Shadows.InvariantRegion.iDotAtZero

/-! ## `InvariantRegion.sFromRegion` -/

namespace Alignment.Shadows.InvariantRegion.sFromRegion

sa_claim "InvariantRegion.sFromRegion" group "InvariantRegion" required
  text "For a point in the invariant region, S = ψ(θ) is automatically in [0, 1]."
  impl InvariantRegion.S_from_region

@[sa_forward "InvariantRegion.sFromRegion" 1]
theorem fwd1 (h : sa_impl% "InvariantRegion.sFromRegion") : S1 := by
  intro n ψ x
  exact (h ψ x).1

@[sa_forward "InvariantRegion.sFromRegion" 2]
theorem fwd2 (h : sa_impl% "InvariantRegion.sFromRegion") : S2 := by
  intro n ψ x
  exact (h ψ x).2

@[sa_backward "InvariantRegion.sFromRegion"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "InvariantRegion.sFromRegion" := by
  intro n ψ s
  exact ⟨s1 n ψ s, s2 n ψ s⟩

end Alignment.Shadows.InvariantRegion.sFromRegion

/-! ## `InvariantRegion.iNonnegFromRegion` -/

namespace Alignment.Shadows.InvariantRegion.iNonnegFromRegion

sa_claim "InvariantRegion.iNonnegFromRegion" group "InvariantRegion" required
  text "Given S from region and R ≥ 0 with S + R ≤ 1, the infected fraction I ≥ 0."
  impl InvariantRegion.I_nonneg_from_region

/-- The given `R ≥ 0` makes `x` with its `R` replaced a region point; the implementation at that
point is `S1` (the new point's `θ` and `R` are `x.θ` and `R` definitionally). -/
@[sa_forward "InvariantRegion.iNonnegFromRegion" 1]
theorem fwd1 (h : sa_impl% "InvariantRegion.iNonnegFromRegion") : S1 := by
  intro n ψ x R hR hSR
  exact h ψ ⟨x.θ, x.φ_I, x.φ_R, R, x.hθ_lo, x.hθ_hi, x.hφ_I, x.hφ_R, hR⟩ hSR

@[sa_forward "InvariantRegion.iNonnegFromRegion" 2]
theorem fwd2 (h : sa_impl% "InvariantRegion.iNonnegFromRegion") : S2 := by
  intro n ψ x hSR
  exact h ψ x hSR

@[sa_backward "InvariantRegion.iNonnegFromRegion"]
theorem bwd (_s1 : S1) (s2 : S2) : sa_impl% "InvariantRegion.iNonnegFromRegion" := by
  intro n ψ s hSR
  exact s2 n ψ s hSR

end Alignment.Shadows.InvariantRegion.iNonnegFromRegion

/-! ## R123a -/
namespace Alignment.Shadows.InvariantRegion.R123a

sa_claim "InvariantRegion.R123a" group "InvariantRegion" required
  text "**Result 123 (Invariant Region Boundary Conditions).** Four sign conditions at the boundary faces of the EBCM region hold at every point of `EBCMRegion`. They are the conditions Nagumo's theorem would need, except that the θ = 0 face also needs φ_I ≤ θ, which `EBCMRegion` omits:"
  impl InvariantRegion.invariant_region_boundary_conditions

sa_fail_forward "InvariantRegion.R123a" 1 "impl's first conjunct is -(β·φ_I) ≤ 0; S1 is -β·φ_I ≤ 0 on the θ = 1 face. -β·φ_I and -(β·φ_I) are equal only by neg_mul, which is not definitional in ℚ (Rat.mul normalises by gcd), so S1 does not follow structurally from h, though the content is the same."

sa_fail_forward "InvariantRegion.R123a" 2 "impl's φ_I-face conjunct is the placeholder (0:ℚ) = 0 (its docstring says the computation is phi_I_dot_zero_at_boundary). It says nothing about the φ_I component correctQ of the vector field at φ_I = 0 (S2)."

@[sa_forward "InvariantRegion.R123a" 3]
theorem fwd3 (h : sa_impl% "InvariantRegion.R123a") : S3 :=
  fun x p _ => (@h p 1 chkUnitPGF x 0 rfl).2.2.1

sa_fail_forward "InvariantRegion.R123a" 4 "impl's fourth conjunct is the I-face drift 0 ≤ β·φ_I·ψ'_θ. S4 is the R-face condition 0 ≤ γ(1 − ψ(θ) − R) at R = 0 (dR/dt), a different component; impl says nothing about dR/dt."

sa_fail_forward "InvariantRegion.R123a" 5 "impl has no θ = 0 face conjunct. Its first conjunct -(β φ_I) ≤ 0 has the opposite sign of S5's 0 ≤ -β φ_I, and S5 needs φ_I = 0 from φ_I ≤ θ = 0 together with the region invariant 0 ≤ φ_I (order antisymmetry), which impl does not state."

sa_fail_forward "InvariantRegion.R123a" 6 "S6 (at some region point with θ = 0 the θ-drift -β φ_I is negative: 'the θ = 0 face also needs φ_I ≤ θ, which EBCMRegion omits') is the text's caveat. impl states only sign conditions that hold at every point and does not exhibit such a point."

sa_fail_backward "InvariantRegion.R123a" "impl's conjuncts hold at every point of EBCMRegion: -(β φ_I) ≤ 0 everywhere (S1 only on θ = 1, and with -β·φ_I in place of -(β·φ_I)), and the I-face drift 0 ≤ β φ_I ψ'_θ for an arbitrary ψ'_θ ≥ 0, which no shadow states. So impl does not follow from the shadow set."

end Alignment.Shadows.InvariantRegion.R123a

/-! ## `InvariantRegion.R123b` -/

namespace Alignment.Shadows.InvariantRegion.R123b

sa_claim "InvariantRegion.R123b" group "InvariantRegion" required
  text "1. **θ face** (θ = 0 and θ = 1): θ is non-increasing since dθ/dt ≤ 0. This handles the upper face θ ≤ 1 automatically (θ starts at 1 and can only decrease)."
  impl InvariantRegion.theta_dot_nonpos

sa_fail_forward "InvariantRegion.R123b" 1 "impl theta_dot_nonpos needs the hypothesis 0 ≤ φ_I. For S1's region point that is available only as the EBCMRegion field x.hφ_I, a data invariant that structural proofs may not extract. impl also concludes -(β·φ_I) ≤ 0, not S1's (-β)·φ_I ≤ 0, and the two are equal only by neg_mul, not definitionally over ℚ."
sa_fail_forward "InvariantRegion.R123b" 2 "impl is a pointwise sign statement about the rational -(β·φ_I). It contains no trajectory, derivative or monotonicity. S2 requires AntitoneOn θ (Set.Ici 0) for a real θ with θ′ = -β·φ_I and φ_I ≥ 0, which is a mean-value-theorem argument that impl does not state."
sa_fail_forward "InvariantRegion.R123b" 3 "impl has no trajectory statement. S3 requires that θ(0) = 1 implies θ(t) ≤ 1 for t ≥ 0 along real solutions of θ′ = -β·φ_I (the text's 'θ starts at 1 and can only decrease'). impl does not formalise this (the registry impl_note says the same)."
sa_fail_backward "InvariantRegion.R123b" "S1 at the region point (θ, φ_I, φ_R, R) = (0, φ_I, 0, 0) gives (-β)·φ_I ≤ 0, but impl requires -(β·φ_I) ≤ 0. The two are equal only by the ring lemma neg_mul, not definitionally over ℚ, and there is no trusted dθ/dt definition to bridge. The difference is in formulation only."

end Alignment.Shadows.InvariantRegion.R123b

/-! ## `InvariantRegion.R123d` -/

namespace Alignment.Shadows.InvariantRegion.R123d

sa_claim "InvariantRegion.R123d" group "InvariantRegion" required
  text "2. **φ_I face** (φ_I = 0): dφ_I/dt = 0 there — the face is absorbing."
  impl InvariantRegion.phi_I_dot_zero_at_boundary

/-- After rewriting `x.φ_I = 0`, `phiIDot p ψ x.θ 0` unfolds to the implementation's expression
with `ψ'_θ := ψ′(x.θ)` and `ψ'_1 := ψ′(1)`. -/
@[sa_forward "InvariantRegion.R123d" 1]
theorem fwd1 (h : sa_impl% "InvariantRegion.R123d") : S1 := by
  intro p n ψ x hx
  rw [hx]
  exact h p x.θ (pgfDeriv ψ x.θ) (pgfDeriv ψ 1)

sa_fail_backward "InvariantRegion.R123d" "free-scalar abstraction. impl is stated for arbitrary rationals θ, ψ'_θ and ψ'_1, with φ_I replaced by the literal 0. S1 gives the identity only at region points (θ ∈ [0, 1]), with ψ'_θ = ψ′(θ) and ψ'_1 = ψ′(1) of a PolyPGF. impl's instances with ψ'_1 = -1 or θ = 2 cannot be derived."

end Alignment.Shadows.InvariantRegion.R123d

/-! ## `InvariantRegion.R123e` -/

namespace Alignment.Shadows.InvariantRegion.R123e

sa_claim "InvariantRegion.R123e" group "InvariantRegion" required
  text "3. **φ_R face** (φ_R = 0): dφ_R/dt = γ φ_I ≥ 0 — inward pointing."
  impl InvariantRegion.phi_R_dot_nonneg

sa_fail_forward "InvariantRegion.R123e" 1 "impl phi_R_dot_nonneg takes 0 ≤ φ_I as an explicit hypothesis and does not mention φ_R or the face. For S1's region point x, 0 ≤ x.φ_I is available only as the EBCMRegion field x.hφ_I, a data invariant that structural proofs may not extract. So 0 ≤ γ·x.φ_I cannot be obtained from impl structurally."

/-- `S1` at the region point `(0, φ, 0, 0)`, which lies on the face `φ_R = 0` by `rfl`. -/
@[sa_backward "InvariantRegion.R123e"]
theorem bwd (s1 : S1) : sa_impl% "InvariantRegion.R123e" := by
  intro p φ hφ
  exact s1 p (chkPt φ hφ) rfl

end Alignment.Shadows.InvariantRegion.R123e

/-! ## `InvariantRegion.R123f` -/

namespace Alignment.Shadows.InvariantRegion.R123f

sa_claim "InvariantRegion.R123f" group "InvariantRegion" required
  text "4. **I face** (I = 0, equivalently S + R = 1): dI/dt = β φ_I ψ′(θ) ≥ 0 — the Nagumo tangency condition holds."
  impl InvariantRegion.I_dot_nonneg_at_zero_boundary

sa_fail_forward "InvariantRegion.R123f" 1 "impl I_dot_nonneg_at_zero_boundary is only 0 ≤ β·φ_I·ψ'_θ for free rationals. It does not state dI/dt = β·φ_I·ψ′(θ) on the I face. S1 requires IDot = -(ψ′(θ)·(-β·φ_I)) - γ(1 - ψ(θ) - R) to equal β·φ_I·ψ′(θ) there. impl states no such equation, and the equation needs ring algebra."
sa_fail_forward "InvariantRegion.R123f" 2 "impl needs the extra hypotheses 0 ≤ ψ'_θ and 0 ≤ φ_I. S2 supplies no ψ′(θ) ≥ 0 (true on [0,1] from nonneg coefficients, but provable only with library lemmas). 0 ≤ x.φ_I is available only as the data invariant x.hφ_I. On top of that, transferring 0 ≤ β·φ_I·ψ′(θ) to 0 ≤ IDot needs ring algebra. None of this is structural."
sa_fail_forward "InvariantRegion.R123f" 3 "impl says nothing about the equivalence I = 0 ↔ S + R = 1: it has no statement involving ψ.eval, R or I. S3 requires 1 - ψ(θ) - R = 0 → ψ(θ) + R = 1 at region points."
sa_fail_forward "InvariantRegion.R123f" 4 "impl says nothing about the equivalence I = 0 ↔ S + R = 1: it has no statement involving ψ.eval, R or I. S4 requires ψ(θ) + R = 1 → 1 - ψ(θ) - R = 0 at region points."
sa_fail_backward "InvariantRegion.R123f" "free-scalar abstraction. impl holds for arbitrary rationals φ_I ≥ 0 and ψ'_θ ≥ 0, in the bare form 0 ≤ β·φ_I·ψ'_θ. S1–S4 concern IDot on the I face of region points, with ψ′(θ) of a PolyPGF, and the identity I = 0 ↔ S + R = 1. Neither the instances at arbitrary ψ'_θ nor the bare form can be derived from them."

end Alignment.Shadows.InvariantRegion.R123f

/-! ## `InvariantRegion.header.thetaFace.a` -/

namespace Alignment.Shadows.InvariantRegion.header_thetaFace_a

sa_claim "InvariantRegion.header.thetaFace.a" group "InvariantRegion" required
  text "The θ ≥ 0 face requires the *edge conservation* constraint φ_I ≤ θ: when θ = 0, we have φ_I ≤ θ = 0, so φ_I = 0, and therefore dθ/dt = 0 (the wall is absorbing)."
  impl InvariantRegion.theta_lower_boundary_absorbing

sa_fail_forward "InvariantRegion.header.thetaFace.a" 1 "impl theta_lower_boundary_absorbing concludes only -(β·φ_I) = 0. The text's intermediate step φ_I = 0 is not stated. Recovering φ_I = 0 from -(β·φ_I) = 0 needs β ≠ 0 plus mul_eq_zero and neg_eq_zero, which is not structural. impl also requires 0 ≤ φ_I, which for S1's region point is only the data invariant x.hφ_I."
sa_fail_forward "InvariantRegion.header.thetaFace.a" 2 "impl needs 0 ≤ φ_I. For S2's region point that is only the EBCMRegion field x.hφ_I, a data invariant that structural proofs may not extract. (Its other hypothesis, φ_I ≤ 0, is obtainable from φ_I ≤ θ and θ = 0 by rewriting.) impl also concludes -(β·φ_I) = 0, not S2's (-β)·φ_I = 0, and the two are equal only by neg_mul, not definitionally over ℚ."
sa_fail_backward "InvariantRegion.header.thetaFace.a" "At the region point (0, φ_I, 0, 0), S1 gives φ_I = 0, which turns impl's goal -(β·φ_I) = 0 into -(β·0) = 0. That is not definitional for a variable β: it needs mul_zero and neg_zero. S2 gives (-β)·φ_I = 0, not -(β·φ_I) = 0, and closing that gap needs neg_mul. impl is not structurally derivable from S1 and S2."

end Alignment.Shadows.InvariantRegion.header_thetaFace_a

/-! ## `InvariantRegion.thetaLowerBoundaryAbsorbing` -/

namespace Alignment.Shadows.InvariantRegion.thetaLowerBoundaryAbsorbing

sa_claim "InvariantRegion.thetaLowerBoundaryAbsorbing" group "InvariantRegion" required
  text "Assuming the edge conservation identity φ_I ≤ θ (a physical constraint of the EBCM), the lower boundary θ = 0 is absorbing: dθ/dt = 0."
  impl InvariantRegion.theta_lower_boundary_absorbing

sa_fail_forward "InvariantRegion.thetaLowerBoundaryAbsorbing" 1 "impl needs 0 ≤ φ_I. For S1's region point that is only the EBCMRegion field x.hφ_I, a data invariant that structural proofs may not extract. impl also concludes -(β·φ_I) = 0 rather than (-β)·φ_I = 0, equal only by neg_mul and not definitionally over ℚ. (impl's hypothesis φ_I ≤ 0, i.e. φ_I ≤ θ with θ := 0 substituted, is obtainable by rewriting.)"
sa_fail_backward "InvariantRegion.thetaLowerBoundaryAbsorbing" "S1 at the region point (0, φ_I, 0, 0) gives (-β)·φ_I = 0, but impl concludes -(β·φ_I) = 0. The two are equal only by neg_mul, not definitionally over ℚ, and there is no trusted dθ/dt definition to bridge. The difference is in formulation only."

end Alignment.Shadows.InvariantRegion.thetaLowerBoundaryAbsorbing

/-! ## phiIDotCorrectZeroAtBoundary -/
namespace Alignment.Shadows.InvariantRegion.phiIDotCorrectZeroAtBoundary

sa_claim "InvariantRegion.phiIDotCorrectZeroAtBoundary" group "InvariantRegion" required
  text "The correct φ_I field β φ_I ψ″(θ)/ψ′(1) − (β + γ) φ_I vanishes at φ_I = 0."
  impl InvariantRegion.phi_I_dot_correct_zero_at_boundary

sa_fail_forward "InvariantRegion.phiIDotCorrectZeroAtBoundary" 1 "impl states β·0·(ψ''_θ/ψ'_1) − (β+γ)·0 = 0 for free rationals. S1's correctQ p ψ θ 0 unfolds to ((β·0)·ψ″(θ))/ψ′(1) − (β+γ)·0, grouped (a·x)/y where impl has a·(x/y). The two agree only by mul_div_assoc, which is not definitional in ℚ, so S1 does not follow structurally from h. Same content."

sa_fail_backward "InvariantRegion.phiIDotCorrectZeroAtBoundary" "impl quantifies over free rationals ψ''_θ, ψ'_1 and groups the term as β·0·(ψ''_θ/ψ'_1); S1 gives the value of ((β·0)·ψ″(θ))/ψ′(1) − (β+γ)·0 only for ψ″, ψ′ of polynomial PGFs. Free rationals are not of that form, and the grouping differs by mul_div_assoc, so impl does not follow structurally from S1."

end Alignment.Shadows.InvariantRegion.phiIDotCorrectZeroAtBoundary

/-! ## phiIDotCorrectFactors -/
namespace Alignment.Shadows.InvariantRegion.phiIDotCorrectFactors

sa_claim "InvariantRegion.phiIDotCorrectFactors" group "InvariantRegion" required
  text "The correct φ_I field factors as φ_I · (β ψ″(θ)/ψ′(1) − (β + γ)), with no condition on θ: unlike the form with 1/θ, it is regular at θ = 0."
  impl InvariantRegion.phi_I_dot_correct_factors

sa_fail_forward "InvariantRegion.phiIDotCorrectFactors" 1 "impl states β·φ_I·(ψ''_θ/ψ'_1) − (β+γ)·φ_I = φ_I·(β·ψ''_θ/ψ'_1 − (β+γ)). S1's left-hand side correctQ unfolds to ((β·φ_I)·ψ″(θ))/ψ′(1) − (β+γ)·φ_I, grouped (a·x)/y where impl has a·(x/y). They agree only by mul_div_assoc (not definitional in ℚ), so S1 does not follow structurally from h. The right-hand sides agree."

sa_fail_forward "InvariantRegion.phiIDotCorrectFactors" 2 "impl is a rational factorisation identity. S2 (the real field θ ↦ correctR p ψ θ φ_I is continuous at θ = 0) is an analytic statement that impl does not make."

sa_fail_forward "InvariantRegion.phiIDotCorrectFactors" 3 "impl says nothing about the 1/θ form. S3 (that form is not continuous at θ = 0 for some parameters) is not stated."

sa_fail_backward "InvariantRegion.phiIDotCorrectFactors" "impl is stated for free rationals ψ''_θ, ψ'_1 with the grouping β·φ_I·(ψ''_θ/ψ'_1). S1 gives the factorisation only for ψ″, ψ′ of polynomial PGFs, and with the grouping ((β·φ_I)·ψ″)/ψ′. Free rationals are not of that form, and the groupings differ by mul_div_assoc (not structural)."

end Alignment.Shadows.InvariantRegion.phiIDotCorrectFactors

/-! ## phiILeTheta -/
namespace Alignment.Shadows.InvariantRegion.phiILeTheta

sa_claim "InvariantRegion.phiILeTheta" group "InvariantRegion" required
  text "Edge conservation: θ = φ_S + φ_I + φ_R with φ_S, φ_R ≥ 0 gives φ_I ≤ θ."
  impl InvariantRegion.phi_I_le_theta

@[sa_forward "InvariantRegion.phiILeTheta" 1]
theorem fwd1 (h : sa_impl% "InvariantRegion.phiILeTheta") : S1 :=
  fun _θ _φS _φI _φR he hS hR => h he hS hR

@[sa_backward "InvariantRegion.phiILeTheta"]
theorem bwd (s1 : S1) : sa_impl% "InvariantRegion.phiILeTheta" := by
  intro θ φS φI φR he hS hR
  exact s1 θ φS φI φR he hS hR

end Alignment.Shadows.InvariantRegion.phiILeTheta

/-! ## `InvariantRegion.R123c` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.InvariantRegion.R123c

sa_claim "InvariantRegion.R123c" group "InvariantRegion"
  text "The lower face θ = 0 requires the additional physical constraint φ_I ≤ θ (edge conservation), which holds in the full model; it is not a hypothesis of this theorem (see `theta_lower_boundary_absorbing` and `phi_I_le_theta`)."
  impl

end Alignment.Shadows.InvariantRegion.R123c

/-! ## `InvariantRegion.header.invariance.I` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.InvariantRegion.header_invariance_I

sa_claim "InvariantRegion.header.invariance.I" group "InvariantRegion"
  text "The state variables of the single-type static SIR edge-based compartmental model (EBCM) remain in a physically meaningful region for all t ≥ 0 (for the correct field below; this is not proved here — the file records only pointwise sign conditions on the right-hand side): [...] * I = 1 − S − R ≥ 0 — infected fraction"
  impl

end Alignment.Shadows.InvariantRegion.header_invariance_I

/-! ## `InvariantRegion.header.invariance.R` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.InvariantRegion.header_invariance_R

sa_claim "InvariantRegion.header.invariance.R" group "InvariantRegion"
  text "The state variables of the single-type static SIR edge-based compartmental model (EBCM) remain in a physically meaningful region for all t ≥ 0 (for the correct field below; this is not proved here — the file records only pointwise sign conditions on the right-hand side): [...] * R ≥ 0, non-decreasing"
  impl

end Alignment.Shadows.InvariantRegion.header_invariance_R

/-! ## `InvariantRegion.header.invariance.S` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.InvariantRegion.header_invariance_S

sa_claim "InvariantRegion.header.invariance.S" group "InvariantRegion"
  text "The state variables of the single-type static SIR edge-based compartmental model (EBCM) remain in a physically meaningful region for all t ≥ 0 (for the correct field below; this is not proved here — the file records only pointwise sign conditions on the right-hand side): [...] * S = ψ(θ) ∈ [0, 1] — susceptible fraction"
  impl

end Alignment.Shadows.InvariantRegion.header_invariance_S

/-! ## `InvariantRegion.header.invariance.phi` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.InvariantRegion.header_invariance_phi

sa_claim "InvariantRegion.header.invariance.phi" group "InvariantRegion"
  text "The state variables of the single-type static SIR edge-based compartmental model (EBCM) remain in a physically meaningful region for all t ≥ 0 (for the correct field below; this is not proved here — the file records only pointwise sign conditions on the right-hand side): [...] * φ_I, φ_R ≥ 0 — excess-degree fractions"
  impl

end Alignment.Shadows.InvariantRegion.header_invariance_phi

/-! ## `InvariantRegion.header.invariance.theta` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.InvariantRegion.header_invariance_theta

sa_claim "InvariantRegion.header.invariance.theta" group "InvariantRegion"
  text "The state variables of the single-type static SIR edge-based compartmental model (EBCM) remain in a physically meaningful region for all t ≥ 0 (for the correct field below; this is not proved here — the file records only pointwise sign conditions on the right-hand side): [...] * θ ∈ [0, 1] — edge survival probability"
  impl

end Alignment.Shadows.InvariantRegion.header_invariance_theta

/-! ## `InvariantRegion.header.model` (registry status `informal`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.InvariantRegion.header_model

sa_claim "InvariantRegion.header.model" group "InvariantRegion"
  text "The expanded single-type SIR EBCM (Volz 2008, Miller 2011) has ODE variables θ, φ_I, φ_R, R with the vector field: dθ/dt = −β φ_I dφ_I/dt = β φ_I ψ″(θ) / ψ′(1) − (β + γ) φ_I dφ_R/dt = γ φ_I dR/dt = γ (1 − ψ(θ) − R) (The φ_I equation follows from φ_I = θ − φ_S − φ_R with φ_S = ψ′(θ)/ψ′(1); it is the form the Julia builders integrate. Several statements below were written for the incorrect form (β φ_I / θ)(ψ′(θ) / ψ′(1)) − (β + γ) φ_I; the corresponding statements for the correct form are `phi_I_dot_correct_*`.) Derived observables (algebraic, not ODE variables): S = ψ(θ) I = 1 − S − R ← by definition; so S + I + R = 1 identically φ_S = ψ′(θ)/ψ′(1)"
  impl

end Alignment.Shadows.InvariantRegion.header_model

/-! ## `InvariantRegion.header.thetaFace.b` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.InvariantRegion.header_thetaFace_b

sa_claim "InvariantRegion.header.thetaFace.b" group "InvariantRegion"
  text "This constraint follows from θ = φ_S + φ_I + φ_R with φ_S, φ_R ≥ 0 (`phi_I_le_theta`)."
  impl

end Alignment.Shadows.InvariantRegion.header_thetaFace_b

/-! ## `InvariantRegion.header.thetaFace.c` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.InvariantRegion.header_thetaFace_c

sa_claim "InvariantRegion.header.thetaFace.c" group "InvariantRegion"
  text "The factor 1/θ in the φ_I equation used in this file is an artefact of an incorrect form; the correct equation dφ_I/dt = β φ_I ψ″(θ)/ψ′(1) − (β + γ) φ_I has no singularity at θ = 0."
  impl

end Alignment.Shadows.InvariantRegion.header_thetaFace_c

/-! ## `InvariantRegion.phiIDotFactors.b` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.InvariantRegion.phiIDotFactors_b

sa_claim "InvariantRegion.phiIDotFactors.b" group "InvariantRegion"
  text "so along a solution φ_I keeps its sign and {φ_I = 0} is invariant; the sign of dφ_I/dt also depends on the second factor. [...] here we record the factorization for the form (β φ_I / θ)(ψ′(θ)/ψ′(1)) − (β + γ) φ_I used in this file (the correct field is `phi_I_dot_correct_factors`)."
  impl

end Alignment.Shadows.InvariantRegion.phiIDotFactors_b
