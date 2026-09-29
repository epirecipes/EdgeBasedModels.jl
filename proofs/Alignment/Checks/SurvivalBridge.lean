import Alignment.Registry
import Alignment.Shadows.SurvivalBridge
import EBCMCategory.ClosureTheorem
import Mathlib.Tactic.Ring

/-!
# Checkers: group `SurvivalBridge`

This file holds the registrations, bridges, forward and backward checkers and failure records for
the implemented claims of `EBCMCategory/SurvivalBridge.lean`. The claim
`header.kappaInvariant-b` also cites `EBCMCategory/ClosureTheorem.lean`. The shadows are in
`Alignment/Shadows/SurvivalBridge.lean`, written blind.

Policy.

* A check is proved only when the shadow is an instance, projection or logical consequence of
  the implementation's statement, and `h` supplies the content.
* Definitional unfolding is free. This covers `<` on ℚ, which is `Rat.blt a b = true`, and
  structure eta for `VolzState`.
* Kernel evaluation of closed rational arithmetic (`rfl` under `with_unfolding_all`) is used in
  three places only:
  - to name the witness of an existential implementation in a backward check;
  - to discharge closed side conditions (`0 < 2`, `1/2 < 1`, NB(2, 1/2) moments) when a shadow
    is instantiated;
  - to derive `c ≠ 0` from `0 < c`, in `ne_zero_of_pos`: rewriting `0 < c` along `c = 0` gives
    `Rat.blt 0 0 = true`, i.e. `false = true`.
* Two bridges (claim `R46c`) identify the trusted `edgeModel` / `nodeModel` with the text's two
  R₀ formulas. They contain only re-association, i.e. `T·(a/b) = T·a/b` and `(β/(β+γ))·κ = β·κ/(β+γ)`.
  The Poisson-specific content (`κ²/κ = κ`) stays in the implementation.
* The recurring misalignments are listed below.
  - Existentials implement universal family claims (`R43`, `R44`, `R49`).
  - A moment identity at u = 1 implements dynamical or function-level claims (`R47`, `R49`,
    the function-level readings of `R42` to `R44` and `kappaInvariant-b`).
  - Only the left inverse of the Volz ↔ DSA change is proved (right inverse and surjectivity
    fail).
  - For the claims whose shadows use `ψ'(θ) > 0`, the implementation covers `ψ' ≠ 0`, including
    negative values (the backward check fails).
-/

namespace Alignment.Checks.SurvivalBridge

/-- `Bool → Prop`: `false ↦ False`, `true ↦ True` (plain data recursor of `Bool`). -/
def propOfBool (b : Bool) : Prop := Bool.rec (motive := fun _ => Prop) False True b

/-- `false = true` is absurd: transport `True` along `propOfBool`. -/
theorem false_of_false_eq_true (e : false = true) : False :=
  Eq.mpr (congrArg propOfBool e) trivial

/-- `0 < c → c ≠ 0` on ℚ, by unfolding only. Rewriting `0 < c` along `c = 0` gives `0 < 0`,
which is definitionally `Rat.blt 0 0 = true`, i.e. `false = true` (closed kernel evaluation). -/
theorem ne_zero_of_pos {c : ℚ} (hc : 0 < c) : c ≠ 0 := fun e =>
  have h00 : (0 : ℚ) < 0 := Eq.mp (congrArg (fun x : ℚ => (0 : ℚ) < x) e) hc
  have hft : false = true := by with_unfolding_all exact h00
  false_of_false_eq_true hft

/-- Separate two rationals by a threshold `t`: `a ≥ t` and `b < t` (as `Rat.blt` values). -/
theorem ne_of_blt {a b t : ℚ} (ha : Rat.blt a t = false) (hb : Rat.blt b t = true) : a ≠ b :=
  fun e => false_of_false_eq_true ((ha.symm.trans (congrArg (fun x => Rat.blt x t) e)).trans hb)

/-- A left inverse gives injectivity (pure equational logic). -/
theorem injOfLeftInv (c : ℚ) (hc : c ≠ 0)
    (li : ∀ v : VolzState, dsaToVolz (volzToDSA v c) c hc = v) :
    Function.Injective (fun v : VolzState => volzToDSA v c) := by
  intro v₁ v₂ e
  exact (li v₁).symm.trans ((congrArg (fun d => dsaToVolz d c hc) e).trans (li v₂))

/-- PGF data with the Binomial(3, 1/2) moments: ψ'(1) = 3/2, ψ''(1) = 3/2 (κ = 2/3). -/
def binom3 : PGFData := ⟨3 / 2, 3 / 2, by norm_num, by norm_num⟩

/-- PGF data with the NB(2, 1/2) moments: ψ'(1) = 2, ψ''(1) = 6 (κ = 3/2). -/
def negBin2 : PGFData := ⟨2, 6, by norm_num, by norm_num⟩

/-- PGF data with ψ'(1) = 10, ψ''(1) = 200 (κ = 2, dispersion index 11). -/
def mix10 : PGFData := ⟨10, 200, by norm_num, by norm_num⟩

end Alignment.Checks.SurvivalBridge

/-! ## `SurvivalBridge.header.kappaInvariant-b` -/
namespace Alignment.Shadows.SurvivalBridge.header_kappaInvariant_b
open Alignment.Checks.SurvivalBridge

sa_claim "SurvivalBridge.header.kappaInvariant-b" group "SurvivalBridge" required
  text "* κ = (n-1)/n for Binomial(n,p) * κ = 1 for Poisson(λ) * κ = (r+1)/r for NegBin(r,p)"
  impl binomial_closure_ratio poisson_closure_ratio negbin_general_closure_ode

sa_fail_forward "SurvivalBridge.header.kappaInvariant-b" 1 "S1 needs the real-function identity kappaAt (binomialPGF n q) θ = deriv (deriv ψ) θ * ψ θ / (deriv ψ θ)^2 = (n-1)/n for ψ(u) = (1-q+qu)^n, every n ≥ 1, 0 < q ≤ 1 and θ ∈ (0,1]. The impl conjunct binomial_closure_ratio is a ℚ statement about the record PGFEval.mk (w^(n+2)) ((n+2)p w^(n+1)) ((n+2)(n+1)p^2 w^n). There w > 0 is a free scalar, and the derivative values are supplied as expressions, not computed from a PGF with deriv. It covers only n+2 ≥ 2 trials, so n = 1 (κ = 0) is missing, and the passage from Mathlib deriv on ℝ to these ℚ expressions is calculus, not structure."
sa_fail_forward "SurvivalBridge.header.kappaInvariant-b" 2 "S2 needs kappaAt (poissonPGF ℓ) θ = 1 on (0,1] for the real function ψ(u) = exp(ℓ(u-1)) with Mathlib deriv. The impl conjunct poisson_closure_ratio states closureRatio (PGFEval.mk ψ (λψ) (λ²ψ)) = 1 over ℚ with a free ψ > 0 and the derivatives ψ' = λψ, ψ'' = λ²ψ supplied, not derived. It never mentions exp, deriv or ℝ."
sa_fail_forward "SurvivalBridge.header.kappaInvariant-b" 3 "S3 needs kappaAt (negBinPGF r q) θ = (r+1)/r on (0,1] for real r > 0 and ψ(u) = ((1-q)/(1-qu))^r. The impl conjunct negbin_general_closure_ode is the polynomial identity (m+1)(m+2)p²c^(m+1)w^(m+3)·c^(m+1)w^(m+1) = ((m+2)/(m+1))((m+1)p c^(m+1)w^(m+2))² over ℚ in free p, c, w. It covers only integer r = m+1 and has the ODE form ψ''ψ = κψ'², not a ratio. It has no deriv and no PGF function, and non-integer r is not covered."
sa_fail_forward "SurvivalBridge.header.kappaInvariant-b" 4 "S4 needs PGFData.closureKappa ψ = (n-1)/n for every PGFData with Binomial(n,q) moments (mean nq, secondFactorial n(n-1)q²), n ≥ 1. No impl conjunct mentions closureKappa or PGFData. binomial_closure_ratio is about PGFEval.closureRatio of an explicit record in a free w, for n+2 ≥ 2 only. Matching it (at w = 1, n = n'+2) with n(n-1)q²/(nq)² is field algebra (1^k = 1, casts, cancellation), not structure, and n = 1 is not covered."
sa_fail_forward "SurvivalBridge.header.kappaInvariant-b" 5 "S5 needs PGFData.closureKappa (PGFData.poisson ℓ h) = 1, i.e. ℓ²/ℓ² = 1 in ℚ. The impl conjunct poisson_closure_ratio is about PGFEval.closureRatio: (λ²ψ)ψ/(λψ)² = 1 for a free ψ > 0. Even at ψ := 1, the terms (ℓ²·1)·1/(ℓ·1)² and ℓ²/ℓ² are not definitionally equal for a variable ℓ (Rat.mul normalises through gcd), so the step needs ring normalisation. No trusted definition is misread, so no bridge applies."
sa_fail_forward "SurvivalBridge.header.kappaInvariant-b" 6 "S6 needs PGFData.closureKappa ψ = (r+1)/r for every PGFData with NB(r,q) moments (mean rq/(1-q), secondFactorial r(r+1)q²/(1-q)²) and every rational r > 0. The impl conjunct negbin_general_closure_ode is an ODE-form polynomial identity in free p, c, w for integer r = m+1 only. It mentions neither closureKappa nor moments, so non-integer r and the ratio form are not covered."
sa_fail_backward "SurvivalBridge.header.kappaInvariant-b" "sa_impl% is the conjunction of three ℚ statements about explicit PGFEval records and polynomial identities in free scalars: binomial_closure_ratio (every w > 0, p > 0), poisson_closure_ratio (every psi_val > 0) and negbin_general_closure_ode (every p, c, w). S1-S3 are about real PGF functions through Mathlib deriv, and S4-S6 are about PGFData.closureKappa of moment data. None mentions PGFEval.closureRatio at a free point w or these polynomials, so the impl conjuncts cannot be obtained from the shadows by structure. That would need deriv evaluation, ℝ→ℚ transfer and field algebra."

end Alignment.Shadows.SurvivalBridge.header_kappaInvariant_b

/-! ## table.R42 -/
namespace Alignment.Shadows.SurvivalBridge.table_R42

sa_claim "SurvivalBridge.table.R42" group "SurvivalBridge" required
  text "| 42 | Poisson ⇒ κ(1) = 1 (κ ≡ 1 on an interval iff Poisson) |"
  impl poisson_kappa_eq_one

@[sa_forward "SurvivalBridge.table.R42" 1]
theorem fwd1 (h : sa_impl% "SurvivalBridge.table.R42") : S1 := fun lam hl => h lam hl

sa_fail_forward "SurvivalBridge.table.R42" 2 "impl poisson_kappa_eq_one is about the two-moment record: closureKappa (poisson λ) = 1, i.e. κ(1) = 1. S2 (the real Poisson PGF e^{λ(u−1)} has κ(u) = ψ''ψ/ψ'² = 1 at every u) is a statement about derivatives of the real PGF that impl does not make."

sa_fail_forward "SurvivalBridge.table.R42" 3 "S3 (κ ≡ 1 on an interval forces Poisson weights: the converse, KKR Theorem 1) is not stated by impl, which says only that the Poisson record has κ(1) = 1."

@[sa_backward "SurvivalBridge.table.R42"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) : sa_impl% "SurvivalBridge.table.R42" :=
  fun lam hl => s1 lam hl

end Alignment.Shadows.SurvivalBridge.table_R42

/-! ## table.R43 -/
namespace Alignment.Shadows.SurvivalBridge.table_R43

sa_claim "SurvivalBridge.table.R43" group "SurvivalBridge" required
  text "| 43 | Some record has κ(1) < 1 (Binomial: κ ≡ (n-1)/n) |"
  impl binomial_kappa_lt_one

@[sa_forward "SurvivalBridge.table.R43" 1]
theorem fwd1 (h : sa_impl% "SurvivalBridge.table.R43") : S1 := h

sa_fail_forward "SurvivalBridge.table.R43" 2 "impl binomial_kappa_lt_one is the existential ∃ ψ, closureKappa ψ < 1 (its witness, the Binomial(3, 1/2) record, appears only in its proof). S2 (the real binomial PGF has κ(u) ≡ (n−1)/n on (0,1]) is a statement about derivatives of real PGFs that impl does not make."

sa_fail_forward "SurvivalBridge.table.R43" 3 "S3 (the binomial record of any n ≥ 1, p > 0 has closureKappa (n−1)/n) is universal over n and p. impl is a single existential with an unnamed witness, so it does not give S3."

@[sa_backward "SurvivalBridge.table.R43"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) : sa_impl% "SurvivalBridge.table.R43" := s1

end Alignment.Shadows.SurvivalBridge.table_R43

/-! ## table.R44 (`a > b` unfolds to `b < a`) -/
namespace Alignment.Shadows.SurvivalBridge.table_R44

sa_claim "SurvivalBridge.table.R44" group "SurvivalBridge" required
  text "| 44 | Some record has κ(1) > 1 (NegBin: κ ≡ (r+1)/r) |"
  impl negbin_kappa_gt_one

@[sa_forward "SurvivalBridge.table.R44" 1]
theorem fwd1 (h : sa_impl% "SurvivalBridge.table.R44") : S1 := h

sa_fail_forward "SurvivalBridge.table.R44" 2 "impl negbin_kappa_gt_one is the existential ∃ ψ, closureKappa ψ > 1 (witness NegBin(2, 1/2), only in its proof). S2 (the real negative-binomial PGF has κ(u) ≡ (r+1)/r on [0,1]) is about derivatives of real PGFs, which impl does not mention."

sa_fail_forward "SurvivalBridge.table.R44" 3 "S3 (the negative-binomial record of any r > 0, c ∈ (0,1) has closureKappa (r+1)/r) is universal over r and c. impl is a single existential with an unnamed witness, so it does not give S3."

@[sa_backward "SurvivalBridge.table.R44"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) : sa_impl% "SurvivalBridge.table.R44" := s1

end Alignment.Shadows.SurvivalBridge.table_R44

/-! ## `SurvivalBridge.table.R45` -/
namespace Alignment.Shadows.SurvivalBridge.table_R45
open Alignment.Checks.SurvivalBridge

sa_claim "SurvivalBridge.table.R45" group "SurvivalBridge" required
  text "| 45 | The Volz ↔ DSA variable change is invertible |"
  impl volz_dsa_roundtrip

/-- Left inverse: the impl verbatim, arguments reordered. -/
@[sa_forward "SurvivalBridge.table.R45" 1]
theorem fwd1 (h : sa_impl% "SurvivalBridge.table.R45") : S1 := fun c hc v => h v c hc

sa_fail_forward "SurvivalBridge.table.R45" 2 "S2 is the right inverse volzToDSA (dsaToVolz d c h) c = d (DSA → Volz → DSA). The impl volz_dsa_roundtrip states only the left inverse dsaToVolz (volzToDSA v ψ') ψ' h = v. The right inverse needs (x/c)·c = x in the x_SI and x_SS components (field algebra, div_mul_cancel), and the impl does not provide it."

/-- Injectivity from the impl's left inverse. -/
@[sa_forward "SurvivalBridge.table.R45" 3]
theorem fwd3 (h : sa_impl% "SurvivalBridge.table.R45") : S3 := fun c hc =>
  injOfLeftInv c hc (fun v => h v c hc)

sa_fail_forward "SurvivalBridge.table.R45" 4 "S4 (volzToDSA · c is surjective for c ≠ 0) needs, for each DSA state d, a Volz state v with volzToDSA v c = d, i.e. a right inverse ((x/c)·c = x). The impl gives only the left inverse, which yields injectivity (S3) but not surjectivity."

@[sa_backward "SurvivalBridge.table.R45"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) (_s4 : S4) : sa_impl% "SurvivalBridge.table.R45" :=
  fun v ψ' hψ => s1 ψ' hψ v

end Alignment.Shadows.SurvivalBridge.table_R45

/-! ## table.R47 -/
namespace Alignment.Shadows.SurvivalBridge.table_R47

sa_claim "SurvivalBridge.table.R47" group "SurvivalBridge" required
  text "| 47 | Poisson ⇒ κ(1) = 1 (DSA has mass-action form, rescaled) |"
  impl poisson_closure_is_one

@[sa_forward "SurvivalBridge.table.R47" 1]
theorem fwd1 (h : sa_impl% "SurvivalBridge.table.R47") : S1 := fun μ hμ => h μ hμ

sa_fail_forward "SurvivalBridge.table.R47" 2 "impl poisson_closure_is_one states only closureKappa (poisson μ) = 1. S2 (the Poisson DSA survival equation has the rescaled mass-action form) is a statement about the DSA ODE (KKR Eq. 33), which impl does not mention; the Result 47 docstring says so ('The Lean theorem proves only that the Poisson record has closureKappa = 1')."

@[sa_backward "SurvivalBridge.table.R47"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "SurvivalBridge.table.R47" := fun μ hμ => s1 μ hμ

end Alignment.Shadows.SurvivalBridge.table_R47

/-! ## `SurvivalBridge.table.R48` -/
namespace Alignment.Shadows.SurvivalBridge.table_R48
open Alignment.Checks.SurvivalBridge

sa_claim "SurvivalBridge.table.R48" group "SurvivalBridge" required
  text "| 48 | PT closure constant κ = excess/degree ratio |"
  impl closure_kappa_eq_second_over_mean_sq

sa_fail_forward "SurvivalBridge.table.R48" 1 "The impl states closureKappa ψ = secondFactorial/mean^2, which is definitional (proved by rfl). S1 needs closureKappa ψ = excessDegree ψ / mean = (secondFactorial/mean)/mean, the 'excess/degree ratio'. The step a/m^2 = (a/m)/m is field algebra (div_div, sq) and is not definitional in ℚ for a variable m (Rat.mul and Rat.inv normalise through gcd). The impl does not state the excess/degree form. A bridge closureKappa ψ = excessDegree ψ / ψ.mean would be the claim itself and would leave h unused."
sa_fail_forward "SurvivalBridge.table.R48" 2 "S2 needs closureKappa ψ = secondFactorial/mean/mean. The impl gives secondFactorial/mean^2. The gap a/m^2 = a/m/m is ring and field normalisation in ℚ, not definitional for a variable m, and the impl does not state the iterated-quotient (excess ÷ degree) form."

/-- The impl is definitional: `closureKappa` unfolds to `secondFactorial / mean ^ 2`. -/
@[sa_backward "SurvivalBridge.table.R48"]
theorem bwd (_s1 : S1) (_s2 : S2) : sa_impl% "SurvivalBridge.table.R48" := fun _ => rfl

end Alignment.Shadows.SurvivalBridge.table_R48

/-! ## `SurvivalBridge.table.R49` -/
namespace Alignment.Shadows.SurvivalBridge.table_R49
open Alignment.Checks.SurvivalBridge

sa_claim "SurvivalBridge.table.R49" group "SurvivalBridge" required
  text "| 49 | Non-PT distributions: κ(t) varies, closure is approximate|"
  impl nonPT_closure_varies

sa_fail_forward "SurvivalBridge.table.R49" 1 "S1 is universal over non-PT degree distributions p with positive mean: κ(θ) = ψ''ψ/ψ'² of the real series PGF takes two different values on (0,1). The impl nonPT_closure_varies is ∃ ψ : PGFData, closureKappa ψ ≠ 1 ∧ dispersionIndex ψ ≠ 1, one moment record with no θ, no PGF function, no PT predicate and no universal quantifier. Its proof witness ⟨10, 200⟩ even has geometric (NB(1), PT) moments, since secondFactorial = 2·mean²."
sa_fail_forward "SurvivalBridge.table.R49" 2 "S2 says that for every non-PT distribution no constant κ gives ψ''ψ/ψ'² = κ on (0,1), i.e. the closure is inexact. It is universal and function-level. The impl only asserts that some PGFData has closureKappa ≠ 1 and dispersionIndex ≠ 1. It has no closure exactness notion, no θ-dependence and no PT notion."

/-- The impl is a closed existential. Its witness is ⟨10, 200⟩, with closureKappa = 2 and
dispersionIndex = 11. Both are separated from 1 by the threshold 3/2 (closed kernel
evaluation of `Rat.blt`). -/
@[sa_backward "SurvivalBridge.table.R49"]
theorem bwd (_s1 : S1) (_s2 : S2) : sa_impl% "SurvivalBridge.table.R49" :=
  ⟨mix10, ne_of_blt (t := 3 / 2) (by with_unfolding_all exact rfl) (by with_unfolding_all exact rfl),
    ne_of_blt (t := 3 / 2) (by with_unfolding_all exact rfl) (by with_unfolding_all exact rfl)⟩

end Alignment.Shadows.SurvivalBridge.table_R49

/-! ## `SurvivalBridge.table.R50` -/
namespace Alignment.Shadows.SurvivalBridge.table_R50
open Alignment.Checks.SurvivalBridge

sa_claim "SurvivalBridge.table.R50" group "SurvivalBridge" required
  text "| 50 | Volz-DSA equivalence holds for ANY degree distribution |"
  impl volz_dsa_equiv_general

/-- Every scale c > 0 is the mean of some PGF data (the Poisson data with mean c). Its `mean`
is definitionally c, so the impl at that record is the left inverse at c. -/
@[sa_forward "SurvivalBridge.table.R50" 1]
theorem fwd1 (h : sa_impl% "SurvivalBridge.table.R50") : S1 := fun c hc hne v =>
  h (PGFData.poisson c hc) hne v

sa_fail_forward "SurvivalBridge.table.R50" 2 "S2 is the right inverse volzToDSA (dsaToVolz d c h) c = d for c > 0. The impl volz_dsa_equiv_general proves only the left inverse dsaToVolz (volzToDSA v ψ.mean) ψ.mean h = v. The right inverse needs (x/c)·c = x (field algebra), which the impl does not state."
sa_fail_forward "SurvivalBridge.table.R50" 3 "S3 needs Volz θ(t) = DSA x_θ(t), for t ≥ 0, for every pair of solutions of the Volz (paper eqs. 6-7) and DSA (eqs. 8-9) ODEs and every finite-variance degree distribution. The impl volz_dsa_equiv_general is only the static state-space identity dsaToVolz (volzToDSA v ψ.mean) ψ.mean h = v, for one VolzState record with the scale ψ'(1) = ψ.mean. It has no ODE, trajectory or time, and no equivalence of dynamics."
sa_fail_forward "SurvivalBridge.table.R50" 4 "S4 needs the Volz x_S(t) = ψ(θ(t)) to equal the DSA x_S(t) for all solutions of the two ODE systems. The impl is a static left-inverse identity on VolzState records and mentions no ODE, solution or trajectory."
sa_fail_forward "SurvivalBridge.table.R50" 5 "S5 needs the Volz and DSA infected fractions x_I(t) to agree for all solutions of the two ODE systems. The impl is a static left-inverse identity on VolzState records and mentions no ODE, solution or trajectory."
sa_fail_backward "SurvivalBridge.table.R50" "The impl quantifies over every ψ : PGFData with the hypothesis ψ.mean ≠ 0 and uses the scale ψ.mean. S1 and S2 give the round trip only for scales with 0 < c, and 0 < ψ.mean does not follow from ψ.mean ≠ 0 in ℚ. The only other route is the data invariant ψ.mean_pos, a proof extracted from data, which structural proofs may not use. S3-S5 are ODE statements and do not help. The impl follows from S1 only modulo the PGFData invariant, so this is an audit limitation, not a stronger claim: mathematically S1 implies the impl."

end Alignment.Shadows.SurvivalBridge.table_R50

/-! ## volzState-b (the implementation's `ψ' ≠ 0` argument is supplied from `0 < θ·d` by
`ne_zero_of_pos`: rewriting to `0 < 0` gives the closed `Rat.blt 0 0 = true`, i.e. `false = true`) -/
namespace Alignment.Shadows.SurvivalBridge.volzState_b

open Alignment.Checks.SurvivalBridge

sa_claim "SurvivalBridge.volzState-b" group "SurvivalBridge" required
  text "This is invertible whenever θ·ψ'(θ) > 0."
  impl volz_dsa_roundtrip

@[sa_forward "SurvivalBridge.volzState-b" 1]
theorem fwd1 (h : sa_impl% "SurvivalBridge.volzState-b") : S1 :=
  fun v d hpos => h v (v.θ * d) (ne_zero_of_pos hpos)

sa_fail_forward "SurvivalBridge.volzState-b" 2 "S2 (DSA → Volz → DSA is the identity) is dsa_volz_roundtrip, which is not in this claim's impl list. impl volz_dsa_roundtrip is the other composite (Volz → DSA → Volz) and does not give it."

sa_fail_backward "SurvivalBridge.volzState-b" "impl holds for every nonzero scalar factor ψ' (including negative factors, and states with θ = 0). The shadows state the round trips only for factors of the form θ·d with θ·d > 0, so impl does not follow for an arbitrary ψ' ≠ 0: impl is stronger than the text's 'invertible whenever θ·ψ'(θ) > 0'."

end Alignment.Shadows.SurvivalBridge.volzState_b

/-! ## `SurvivalBridge.R42` -/
namespace Alignment.Shadows.SurvivalBridge.R42
open Alignment.Checks.SurvivalBridge

sa_claim "SurvivalBridge.R42" group "SurvivalBridge" required
  text "**Result 42.** For Poisson, κ = 1. This is because ψ''(1) = κ² and ψ'(1) = κ, so κ = κ²/κ² = 1."
  impl poisson_kappa_eq_one

@[sa_forward "SurvivalBridge.R42" 1]
theorem fwd1 (h : sa_impl% "SurvivalBridge.R42") : S1 := fun κ hκ => h κ hκ

sa_fail_forward "SurvivalBridge.R42" 2 "SHADOW?: S2 ((PGFData.poisson κ hκ).secondFactorial = κ²) restates the definition of the operation under test: PGFData.poisson sets secondFactorial := κ ^ 2 (DataTypes: 'Key property: ψ''(1) = κ²'). It holds by rfl, so no wrong implementation theorem can falsify it, and any forward proof ignores h (vacuous). The impl states only closureKappa (PGFData.poisson κ hκ) = 1. The text 'This is because ψ''(1) = κ² [...]' justifies κ = 1 from the Poisson PGF. A falsifiable reading is the function-level fact deriv (deriv (poissonPGF κ)) 1 = κ² for ψ(u) = e^{κ(u-1)}, which the impl does not state either: in the library ψ''(1) = κ² is built in, not derived."
sa_fail_forward "SurvivalBridge.R42" 3 "SHADOW?: S3 ((PGFData.poisson κ hκ).mean = κ) restates the definition of PGFData.poisson ('The Poisson PGF with mean κ': mean := κ). It holds by rfl, cannot be falsified by an implementation theorem, and any forward proof ignores h (vacuous). The impl states only closureKappa (PGFData.poisson κ hκ) = 1. The clause 'ψ'(1) = κ' of the text is part of a justification, and a falsifiable reading, deriv (poissonPGF κ) 1 = κ, is function-level and not stated by the impl."

@[sa_backward "SurvivalBridge.R42"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) : sa_impl% "SurvivalBridge.R42" :=
  fun κ hκ => s1 κ hκ

end Alignment.Shadows.SurvivalBridge.R42

/-! ## `SurvivalBridge.R43a` -/
namespace Alignment.Shadows.SurvivalBridge.R43a
open Alignment.Checks.SurvivalBridge

sa_claim "SurvivalBridge.R43a" group "SurvivalBridge" required
  text "**Result 43.** For Binomial(n, p), κ = (n-1)/n < 1."
  impl binomial_kappa_lt_one

sa_fail_forward "SurvivalBridge.R43a" 1 "S1 needs closureKappa ψ = (n-1)/n for every PGFData with Binomial(n,q) moments (mean nq, secondFactorial n(n-1)q²), n ≥ 1, 0 < q ≤ 1. The impl binomial_kappa_lt_one is the bare existential ∃ ψ, closureKappa ψ < 1. It has no Binomial family, no n or q and no value (n-1)/n, and an existential cannot give the universal family statement."
sa_fail_forward "SurvivalBridge.R43a" 2 "S2 needs closureKappa ψ < 1 for every PGFData with Binomial(n,q) moments. The impl only asserts one unnamed ψ with closureKappa ψ < 1 (existential), and nothing ties it to Binomial moments."

/-- The impl is a closed existential. Its witness is the Binomial(3, 1/2) moment record
(κ = 2/3 < 1, closed kernel evaluation). S2 at n = 3 would need `1 ≤ 3 : ℕ`, which only
`Nat.le` constructors (library constants) can prove. -/
@[sa_backward "SurvivalBridge.R43a"]
theorem bwd (_s1 : S1) (_s2 : S2) : sa_impl% "SurvivalBridge.R43a" :=
  ⟨binom3, by with_unfolding_all exact rfl⟩

end Alignment.Shadows.SurvivalBridge.R43a

/-! ## `SurvivalBridge.R44a` -/
namespace Alignment.Shadows.SurvivalBridge.R44a
open Alignment.Checks.SurvivalBridge

sa_claim "SurvivalBridge.R44a" group "SurvivalBridge" required
  text "**Result 44.** For NegBin(r, p), κ = (r+1)/r > 1."
  impl negbin_kappa_gt_one

sa_fail_forward "SurvivalBridge.R44a" 1 "S1 needs closureKappa ψ = (r+1)/r for every PGFData with NB(r,q) moments (mean rq/(1-q), secondFactorial r(r+1)q²/(1-q)²), r > 0, 0 < q < 1. The impl negbin_kappa_gt_one is the bare existential ∃ ψ, closureKappa ψ > 1. It has no negative-binomial family, no r or q and no value (r+1)/r, and an existential cannot give the universal family statement."
sa_fail_forward "SurvivalBridge.R44a" 2 "S2 needs 1 < closureKappa ψ for every PGFData with NB(r,q) moments. The impl only asserts one unnamed ψ with closureKappa ψ > 1 (existential), and nothing ties it to NB moments."

/-- S2 at NB(2, 1/2): the record ⟨2, 6⟩ has the NB moments (closed kernel evaluation), and S2
supplies `1 < closureKappa`. -/
@[sa_backward "SurvivalBridge.R44a"]
theorem bwd (_s1 : S1) (s2 : S2) : sa_impl% "SurvivalBridge.R44a" :=
  ⟨negBin2, s2 2 (1 / 2) (by with_unfolding_all exact rfl) (by with_unfolding_all exact rfl)
    (by with_unfolding_all exact rfl) negBin2 (by with_unfolding_all exact rfl)
    (by with_unfolding_all exact rfl)⟩

end Alignment.Shadows.SurvivalBridge.R44a

/-! ## `SurvivalBridge.R45a` -/
namespace Alignment.Shadows.SurvivalBridge.R45a
open Alignment.Checks.SurvivalBridge

sa_claim "SurvivalBridge.R45a" group "SurvivalBridge" required
  text "**Result 45.** The round-trip Volz → DSA → Volz is the identity."
  impl volz_dsa_roundtrip

@[sa_forward "SurvivalBridge.R45a" 1]
theorem fwd1 (h : sa_impl% "SurvivalBridge.R45a") : S1 := fun c hc v =>
  congrArg VolzState.θ (h v c hc)

@[sa_forward "SurvivalBridge.R45a" 2]
theorem fwd2 (h : sa_impl% "SurvivalBridge.R45a") : S2 := fun c hc v =>
  congrArg VolzState.p_I (h v c hc)

@[sa_forward "SurvivalBridge.R45a" 3]
theorem fwd3 (h : sa_impl% "SurvivalBridge.R45a") : S3 := fun c hc v =>
  congrArg VolzState.p_S (h v c hc)

/-- Reassemble the round trip from its components. The round trip unfolds to
`⟨v.θ, v.p_I * ψ' / ψ', v.p_S * ψ' / ψ'⟩`, `v` is `⟨v.θ, v.p_I, v.p_S⟩` by structure eta, and the
θ component is definitional. -/
@[sa_backward "SurvivalBridge.R45a"]
theorem bwd (_s1 : S1) (s2 : S2) (s3 : S3) : sa_impl% "SurvivalBridge.R45a" := by
  intro v ψ' hψ
  have e2 : v.p_I * ψ' / ψ' = v.p_I := s2 ψ' hψ v
  have e3 : v.p_S * ψ' / ψ' = v.p_S := s3 ψ' hψ v
  exact (congrArg (fun a => VolzState.mk v.θ a (v.p_S * ψ' / ψ')) e2).trans
    (congrArg (fun b => VolzState.mk v.θ v.p_I b) e3)

end Alignment.Shadows.SurvivalBridge.R45a

/-! ## R45b -/
namespace Alignment.Shadows.SurvivalBridge.R45b

sa_claim "SurvivalBridge.R45b" group "SurvivalBridge" required
  text "Together with `dsa_volz_roundtrip`, the variable change is a bijection of state spaces for every nonzero scalar factor."
  impl volz_dsa_roundtrip

sa_fail_forward "SurvivalBridge.R45b" 1 "S1 (volzToDSA · c is a bijection) needs surjectivity, i.e. the other round trip DSA → Volz → DSA (dsa_volz_roundtrip). The text names that theorem ('Together with dsa_volz_roundtrip'), but it is not in this claim's impl list. impl volz_dsa_roundtrip gives only a left inverse, hence only injectivity."

@[sa_forward "SurvivalBridge.R45b" 2]
theorem fwd2 (h : sa_impl% "SurvivalBridge.R45b") : S2 := fun c hc v => h v c hc

sa_fail_forward "SurvivalBridge.R45b" 3 "S3 (Function.RightInverse, i.e. DSA → Volz → DSA is the identity) is dsa_volz_roundtrip, which is not in impl. volz_dsa_roundtrip is the other composite."

@[sa_backward "SurvivalBridge.R45b"]
theorem bwd (_s1 : S1) (s2 : S2) (_s3 : S3) : sa_impl% "SurvivalBridge.R45b" :=
  fun v c hc => s2 c hc v

end Alignment.Shadows.SurvivalBridge.R45b

/-! ## R46c (the edge and node R₀ of the Poisson record unfold to the shadow's two sides) -/
namespace Alignment.Shadows.SurvivalBridge.R46c

sa_claim "SurvivalBridge.R46c" group "SurvivalBridge" required
  text "Here we prove the algebraic identity that, for Poisson degrees, the EBCM R₀ T·ψ''(1)/ψ'(1) equals T·μ, where μ = mean degree (the `nodeModel` value). The DSA model is equivalent to Volz's for every degree law, so its R₀ is also T·ψ''(1)/ψ'(1)."
  impl survival_map_R0_poisson

/-- Bridge (reviewed in `Alignment.ReviewedBridges`; kept unchanged so that its review record and
hash stay valid). The trusted `edgeModel p ψ` is the EBCM with R₀ given by the text's formula
T·ψ''(1)/ψ'(1), with T = β/(β+γ), ψ''(1) = `secondFactorial` and ψ'(1) = `mean`. The trusted body
is `⟨4, transmissibility p * excessDegree ψ⟩`, i.e. `⟨4, β/(β+γ) * (sf/mean)⟩`. The bridge only
re-associates `T * (a/b) = T * a / b`, and `dim` is kept as in the definition. The current
checkers do not need it: the re-authored S1 is stated in the definitional grouping. -/
@[sa_bridge "SurvivalBridge.R46c"]
theorem bridge_edgeModel (p : SIRParams) (ψ : PGFData) :
    edgeModel p ψ = { dim := 4, R0 := p.β / (p.β + p.γ) * ψ.secondFactorial / ψ.mean } := by
  unfold edgeModel SIRParams.transmissibility PGFData.excessDegree
  rw [mul_div_assoc]

/-- Bridge (reviewed in `Alignment.ReviewedBridges`; kept unchanged). The trusted `nodeModel p κ`
has R₀ given by the text's DSA formula β·μ/(β+γ), with μ = κ. The trusted body is
`⟨3, transmissibility p * κ⟩`, i.e. `⟨3, β/(β+γ) * κ⟩`. The bridge only rewrites
`(β/(β+γ))·κ = β·κ/(β+γ)`, and `dim` is kept as in the definition. Not used by the current
checkers. -/
@[sa_bridge "SurvivalBridge.R46c"]
theorem bridge_nodeModel (p : SIRParams) (κ : ℚ) :
    nodeModel p κ = { dim := 3, R0 := p.β * κ / (p.β + p.γ) } := by
  unfold nodeModel SIRParams.transmissibility
  rw [div_mul_eq_mul_div]

@[sa_forward "SurvivalBridge.R46c" 1]
theorem fwd1 (h : sa_impl% "SurvivalBridge.R46c") : S1 := fun p μ hμ => h p μ hμ

sa_fail_forward "SurvivalBridge.R46c" 2 "S2 ((nodeModel p μ).R0 = T·μ) is the definition of nodeModel (rfl). impl survival_map_R0_poisson states only the equality of the two R₀ values for the Poisson record, so a checker could only prove S2 without h (vacuous)."

sa_fail_forward "SurvivalBridge.R46c" 3 "S3 ((edgeModel p ψ).R0 = T·ψ''(1)/ψ'(1) for every record) is the definition of edgeModel (rfl). impl is about the Poisson record only, so a checker could only prove S3 without h (vacuous)."

@[sa_backward "SurvivalBridge.R46c"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) : sa_impl% "SurvivalBridge.R46c" :=
  fun p κ hκ => s1 p κ hκ

end Alignment.Shadows.SurvivalBridge.R46c

/-! ## R47a -/
namespace Alignment.Shadows.SurvivalBridge.R47a

sa_claim "SurvivalBridge.R47a" group "SurvivalBridge" required
  text "**Result 47.** For Poisson networks (κ=1), the DSA survival equation has the form of the classical mass-action SIR survival equation, with rescaled rates. From Eq (33) of the paper, with κ=1: -dS/dt = β̃(S - S²) + γ̃·S·log(S) + ρ̃·S This has the form of the mass-action SIR survival equation of KhudaBukhsh et al. (2020), with β̃ = μβ, γ̃ = β + γ and ρ̃ = βμρ. The Lean theorem proves only that the Poisson record has closureKappa = 1."
  impl poisson_closure_is_one

@[sa_forward "SurvivalBridge.R47a" 1]
theorem fwd1 (h : sa_impl% "SurvivalBridge.R47a") : S1 := fun μ hμ => h μ hμ

sa_fail_forward "SurvivalBridge.R47a" 2 "impl poisson_closure_is_one states only closureKappa (poisson μ) = 1 (the text: 'The Lean theorem proves only that the Poisson record has closureKappa = 1'). S2 (the Poisson DSA survival equation −dS/dt = β̃(S − S²) + γ̃ S log S + ρ̃ S with the stated rescaled rates) is not stated."

sa_fail_forward "SurvivalBridge.R47a" 3 "S3 (the mass-action SIR survival equation has the same form) is about the mass-action ODE, which impl does not mention."

@[sa_backward "SurvivalBridge.R47a"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) : sa_impl% "SurvivalBridge.R47a" :=
  fun μ hμ => s1 μ hμ

end Alignment.Shadows.SurvivalBridge.R47a

/-! ## `SurvivalBridge.R47b` -/
namespace Alignment.Shadows.SurvivalBridge.R47b
open Alignment.Checks.SurvivalBridge

sa_claim "SurvivalBridge.R47b" group "SurvivalBridge" required
  text "The proof is that the Poisson PGF ψ(u) = e^{λ(u-1)} satisfies ψ''·ψ/(ψ')² = 1 identically, which eliminates all network-structure terms."
  impl poisson_closure_is_one

sa_fail_forward "SurvivalBridge.R47b" 1 "S1 is the real-function identity kappaAt (poissonPGF ℓ) u = ψ''(u)ψ(u)/ψ'(u)² = 1 for every u ∈ ℝ and ℓ > 0, where ψ(u) = exp(ℓ(u-1)) and the derivatives are Mathlib deriv. The impl poisson_closure_is_one is the ℚ moment identity closureKappa (PGFData.poisson κ hκ) = 1 at u = 1 only, and there ψ''(1) = κ² is built into the definition of PGFData.poisson. There is no function, no derivative and nothing 'identically' in u."
sa_fail_backward "SurvivalBridge.R47b" "The impl (∀ κ > 0 in ℚ, closureKappa (PGFData.poisson κ hκ) = 1, i.e. κ²/κ² = 1) cannot be obtained from S1 by structure. S1 is about Real.exp and deriv on ℝ and never mentions PGFData or closureKappa. Linking them needs deriv evaluation at u = 1, the moment definitions and a ℚ→ℝ cast argument."

end Alignment.Shadows.SurvivalBridge.R47b

/-! ## `SurvivalBridge.R48a` -/
namespace Alignment.Shadows.SurvivalBridge.R48a
open Alignment.Checks.SurvivalBridge

sa_claim "SurvivalBridge.R48a" group "SurvivalBridge" required
  text "**Result 48.** The closure parameter κ equals the dispersion-scaled ratio: κ = secondFactorial / mean²."
  impl closure_kappa_eq_second_over_mean_sq

@[sa_forward "SurvivalBridge.R48a" 1]
theorem fwd1 (h : sa_impl% "SurvivalBridge.R48a") : S1 := fun ψ => h ψ

@[sa_backward "SurvivalBridge.R48a"]
theorem bwd (s1 : S1) : sa_impl% "SurvivalBridge.R48a" := fun ψ => s1 ψ

end Alignment.Shadows.SurvivalBridge.R48a

/-! ## R49a -/
namespace Alignment.Shadows.SurvivalBridge.R49a

sa_claim "SurvivalBridge.R49a" group "SurvivalBridge" required
  text "**Result 49.** Some degree record has closure constant κ(1) ≠ 1 and dispersion index ≠ 1. A two-moment record cannot show that a law is non-PT. For a non-PT law such as ψ(u) = (1 + u²)/2, κ(θ) = (1 + θ²)/(2θ²) varies with θ, making the pairwise closure approximate rather than exact."
  impl nonPT_closure_varies

@[sa_forward "SurvivalBridge.R49a" 1]
theorem fwd1 (h : sa_impl% "SurvivalBridge.R49a") : S1 := h

sa_fail_forward "SurvivalBridge.R49a" 2 "impl nonPT_closure_varies is an existential about two-moment records. S2 (the non-PT law (1 + u²)/2 has the same record as Poisson(1): ψ'(1) = 1 and ψ''(1) = 1, as real derivatives) is about the real PGF psiMix, which impl does not mention."

sa_fail_forward "SurvivalBridge.R49a" 3 "S3 (κ(θ) = (1 + θ²)/(2θ²) for ψ = (1 + u²)/2) is a computation with real derivatives of psiMix that impl does not make."

sa_fail_forward "SurvivalBridge.R49a" 4 "S4 (κ(θ) of (1 + u²)/2 takes two different values on (0,1]) is not stated by impl, which concerns only records (κ(1) ≠ 1 and dispersion ≠ 1 for some record)."

@[sa_backward "SurvivalBridge.R49a"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) (_s4 : S4) : sa_impl% "SurvivalBridge.R49a" := s1

end Alignment.Shadows.SurvivalBridge.R49a

/-! ## `SurvivalBridge.R50a` -/
namespace Alignment.Shadows.SurvivalBridge.R50a
open Alignment.Checks.SurvivalBridge

sa_claim "SurvivalBridge.R50a" group "SurvivalBridge" required
  text "**Result 50.** The Volz ↔ DSA equivalence holds for ANY degree distribution with finite variance — not just PT distributions."
  impl volz_dsa_equiv_general

/-- Every scale c > 0 is the mean of the Poisson data with mean c, whose `mean` is
definitionally c. -/
@[sa_forward "SurvivalBridge.R50a" 1]
theorem fwd1 (h : sa_impl% "SurvivalBridge.R50a") : S1 := fun c hc hne v =>
  h (PGFData.poisson c hc) hne v

sa_fail_forward "SurvivalBridge.R50a" 2 "S2 is the right inverse volzToDSA (dsaToVolz d c h) c = d for c > 0. The impl volz_dsa_equiv_general proves only the left inverse dsaToVolz (volzToDSA v ψ.mean) ψ.mean h = v. The right inverse needs (x/c)·c = x (field algebra), which the impl does not state."
sa_fail_forward "SurvivalBridge.R50a" 3 "S3 needs Volz θ(t) = DSA x_θ(t) for all solutions of the Volz (paper eqs. 6-7) and DSA (eqs. 8-9) ODEs, for every finite-variance degree distribution. The impl is a static state-space identity for VolzState records with the scale ψ.mean = ψ'(1), not ψ'(θ). It has no ODE, trajectory or time, and the variance plays no role."
sa_fail_forward "SurvivalBridge.R50a" 4 "S4 needs the Volz x_S(t) = ψ(θ(t)) to equal the DSA x_S(t) along solutions of the two ODE systems. The impl is a static left-inverse identity on VolzState records and mentions no ODE or trajectory."
sa_fail_forward "SurvivalBridge.R50a" 5 "S5 needs the Volz and DSA infected fractions x_I(t) to agree along solutions of the two ODE systems. The impl is a static left-inverse identity on VolzState records and mentions no ODE or trajectory."
sa_fail_backward "SurvivalBridge.R50a" "The impl quantifies over every ψ : PGFData with the hypothesis ψ.mean ≠ 0 and uses the scale ψ.mean. S1 and S2 give the round trip only for scales with 0 < c, and 0 < ψ.mean does not follow from ψ.mean ≠ 0 in ℚ. The only other route is the data invariant ψ.mean_pos, a proof extracted from data, which structural proofs may not use. S3-S5 are ODE statements. The impl follows from S1 only modulo the PGFData invariant, so this is an audit limitation, not a stronger claim."

end Alignment.Shadows.SurvivalBridge.R50a

/-! ## R50b -/
namespace Alignment.Shadows.SurvivalBridge.R50b

open Alignment.Checks.SurvivalBridge

sa_claim "SurvivalBridge.R50b" group "SurvivalBridge" required
  text "The variable change x_{SI} = p_I · θ · ψ'(θ) is well-defined and invertible whenever θ·ψ'(θ) > 0,"
  impl volz_dsa_roundtrip

sa_fail_forward "SurvivalBridge.R50b" 1 "S1 ((volzToDSA v (θ·d)).x_SI = p_I·(θ·d)) is the definition of volzToDSA (rfl). impl volz_dsa_roundtrip states only the round trip, so a checker could only prove S1 without h (vacuous)."

@[sa_forward "SurvivalBridge.R50b" 2]
theorem fwd2 (h : sa_impl% "SurvivalBridge.R50b") : S2 :=
  fun v d hpos => h v (v.θ * d) (ne_zero_of_pos hpos)

sa_fail_forward "SurvivalBridge.R50b" 3 "S3 (DSA → Volz → DSA is the identity when x_θ·d > 0) is an instance of dsa_volz_roundtrip, which is not in this claim's impl list. volz_dsa_roundtrip is the other composite."

sa_fail_backward "SurvivalBridge.R50b" "impl holds for every nonzero factor ψ'. S2 gives the round trip only for factors θ·d with θ·d > 0, so impl does not follow for negative factors or states with θ = 0. impl is stronger than 'invertible whenever θ·ψ'(θ) > 0'."

end Alignment.Shadows.SurvivalBridge.R50b

/-! ## R50e -/
namespace Alignment.Shadows.SurvivalBridge.R50e

sa_claim "SurvivalBridge.R50e" group "SurvivalBridge" required
  text "This is formalised here only as the round trip of Result 45 with the scalar factor ψ'(1) = mean degree, so it needs only ψ'(1) ≠ 0 and no condition on κ. It is a statement about one linear rescaling, not about the ODE systems."
  impl volz_dsa_roundtrip

sa_fail_forward "SurvivalBridge.R50e" 1 "SHADOW?: S1 states the round trip DSA → Volz → DSA (volzToDSA (dsaToVolz x ψ'(1)) ψ'(1) = x). The text says 'formalised here only as the round trip of Result 45 with the scalar factor ψ'(1)', and Result 45 is, by its docstring, 'The round-trip Volz → DSA → Volz is the identity' (volz_dsa_roundtrip, the registered impl). The shadow uses the other composite, dsa_volz_roundtrip, which impl does not give. The Volz → DSA → Volz reading at factor ψ'(1) would be an instance of impl."

sa_fail_backward "SurvivalBridge.R50e" "S1 is the DSA → Volz → DSA round trip at the factor ψ'(1) of a record. impl is the Volz → DSA → Volz round trip for every nonzero factor. The composites differ, and S1 covers only positive factors that are record means, so impl does not follow from S1."

end Alignment.Shadows.SurvivalBridge.R50e

/-! ## dsaVolzRoundtrip -/
namespace Alignment.Shadows.SurvivalBridge.dsaVolzRoundtrip

sa_claim "SurvivalBridge.dsaVolzRoundtrip" group "SurvivalBridge" required
  text "The round-trip DSA → Volz → DSA is the identity."
  impl dsa_volz_roundtrip

@[sa_forward "SurvivalBridge.dsaVolzRoundtrip" 1]
theorem fwd1 (h : sa_impl% "SurvivalBridge.dsaVolzRoundtrip") : S1 := fun x c hc => h x c hc

@[sa_backward "SurvivalBridge.dsaVolzRoundtrip"]
theorem bwd (s1 : S1) : sa_impl% "SurvivalBridge.dsaVolzRoundtrip" := fun d ψ' h => s1 d ψ' h

end Alignment.Shadows.SurvivalBridge.dsaVolzRoundtrip

/-! ## `SurvivalBridge.R46b` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.SurvivalBridge.R46b

sa_claim "SurvivalBridge.R46b" group "SurvivalBridge"
  text "For any PGF, if we define S = ψ(θ) and differentiate, with x_{SI} = p_I · θ · ψ'(θ) as in Kiss, Kenah & Rempała (2023, App. B): dS/dt = ψ'(θ) · dθ/dt = ψ'(θ) · (-β·p_I·θ) = -β · x_{SI} So the DSA equation ẋ_S = -β·x_{SI} is the chain rule applied to S = ψ(θ). This chain-rule computation is not formalised here."
  impl

end Alignment.Shadows.SurvivalBridge.R46b

/-! ## `SurvivalBridge.R48c` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.SurvivalBridge.R48c

sa_claim "SurvivalBridge.R48c" group "SurvivalBridge"
  text "For a PT law (κ(θ) constant), the value of κ determines the family: * κ < 1: Binomial(n, p) with n = 1/(1-κ); this needs 1/(1-κ) ∈ ℕ, so κ ∈ [0, 1) is realised only for κ = (n-1)/n * κ = 1: Poisson(λ) * κ > 1: NegBin(r, p) with r = 1/(κ-1)"
  impl

end Alignment.Shadows.SurvivalBridge.R48c

/-! ## `SurvivalBridge.R49b` (registry status `informal`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.SurvivalBridge.R49b

sa_claim "SurvivalBridge.R49b" group "SurvivalBridge"
  text "Witness: the record mean 10, ψ''(1) = 200 (κ(1) = 2, dispersion 11). It is the record of the geometric law (NegBin with r = 1), which is PT; the bimodal law with 80% degree 4 and 20% degree 34 has mean 10 but ψ''(1) = 234."
  impl

end Alignment.Shadows.SurvivalBridge.R49b

/-! ## `SurvivalBridge.closureKappa-c` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.SurvivalBridge.closureKappa_c

sa_claim "SurvivalBridge.closureKappa-c" group "SurvivalBridge"
  text "The function κ(θ) = ψ''(θ)ψ(θ)/ψ'(θ)² is constant in θ iff the degree distribution is Poisson-type; `closureKappa` records only its value κ(1), which does not determine the family: ψ(u) = (1 + u²)/2 has κ(1) = 1 but is not Poisson."
  impl

end Alignment.Shadows.SurvivalBridge.closureKappa_c

/-! ## `SurvivalBridge.header.categorical.eta` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.SurvivalBridge.header_categorical_eta

sa_claim "SurvivalBridge.header.categorical.eta" group "SurvivalBridge"
  text "They are related by the change of variables x_θ = θ, x_{SI} = p_I · θ · ψ'(θ), x_{SS} = p_S · θ · ψ'(θ) (Kiss, Kenah & Rempała 2023, App. B), which is invertible when θ·ψ'(θ) > 0."
  impl

end Alignment.Shadows.SurvivalBridge.header_categorical_eta

/-! ## `SurvivalBridge.table.R46` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.SurvivalBridge.table_R46

sa_claim "SurvivalBridge.table.R46" group "SurvivalBridge"
  text "| 46 | S = ψ(θ) gives dS/dt = −β x_SI (chain rule; informal) |"
  impl

end Alignment.Shadows.SurvivalBridge.table_R46

/-! ## `SurvivalBridge.volzState-a` (registry status `informal`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.SurvivalBridge.volzState_a

sa_claim "SurvivalBridge.volzState-a" group "SurvivalBridge"
  text "They are related by (Kiss, Kenah & Rempała 2023, App. B): x_{SI} = p_I · θ · ψ'(θ) x_{SS} = p_S · θ · ψ'(θ) The maps `volzToDSA`/`dsaToVolz` below multiply and divide by an arbitrary scalar factor `psi_prime`; this change of variables is the instance `psi_prime := θ·ψ'(θ)`."
  impl

end Alignment.Shadows.SurvivalBridge.volzState_a
