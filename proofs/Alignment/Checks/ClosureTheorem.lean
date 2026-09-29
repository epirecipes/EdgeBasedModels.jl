import Alignment.Registry
import Alignment.Shadows.ClosureTheorem

/-!
# Checkers: group `ClosureTheorem`

Registrations, forward / backward checkers and failure records for the claims of
`EBCMCategory/ClosureTheorem.lean`. The shadows are in `Alignment/Shadows/ClosureTheorem.lean`
(written blind). No bridges are used: the shadows name the operations under test directly
(`PGFEval.closureRatio`, `PGFData.closureKappa`, `PGFData.poisson`), and the misalignments found
are not about definitions. They concern

* the *form* of the statement (ratio `closureRatio ⟨ψ, ψ', ψ''⟩ = κ` against ODE `ψ''ψ = κψ'²`);
  passing between the two needs division by `ψ'² ≠ 0`, which is field reasoning (the content of
  Result 51 itself), not structural;
* the *parametrisation* of the NegBin records (`c^r w^r`, `p c^r w^(r+1)`, … in free `p, c, w`
  against the closed forms `(c/D)^r`, `(1−c)c^r/D^(r+1)`, … with `D = 1 − (1 − c)θ`), which agree
  only after field algebra;
* the *domain* (the implementations' identities hold for all rationals, or under `2 ≤ n`,
  `0 < p`, `0 < w`, while the shadows use the distribution ranges);
* the *analytic* readings (real PGFs with `deriv`), which no implementation touches.

Policy. A check is proved only when the shadow is an instance, projection or logical consequence
of the implementation's statement and `h` supplies the content. Kernel evaluation of closed
rational arithmetic (`rfl` under `with_unfolding_all`) is used only where the shadow is
existential and the checker must name a witness: the witness is the mixture ψ = 1/2 + θ²/2
(weights w₀ = w₂ = 1/2) at θ = 1 and θ = 1/2, whose (ψ, ψ', ψ'') evaluate to exactly the two
literal records of `nonPT_closure_ratio_varies`, and the inequality itself comes from `h`.
Ordered arithmetic (`mul_pos`, `Nat.le` constructors, order lemmas on ℚ) is not structural;
failures that come only from this are marked in their reasons as audit limitations.
-/

namespace Alignment.Checks.ClosureTheorem
open Alignment.Shadows.ClosureTheorem

/-- Weights of the non-PT mixture ψ(θ) = 1/2 + θ²/2 as a finitely supported degree distribution:
w₀ = w₂ = 1/2, all other weights 0 (support in `Finset.range 3`). -/
def wMix : ℕ → ℚ
  | 0 => 1 / 2
  | 2 => 1 / 2
  | _ => 0

/-- The mixture weights are nonnegative (closed kernel evaluation in each case). -/
theorem wMix_nonneg : ∀ k, 0 ≤ wMix k
  | 0 => by with_unfolding_all exact rfl
  | 1 => by with_unfolding_all exact rfl
  | 2 => by with_unfolding_all exact rfl
  | _ + 3 => by with_unfolding_all exact rfl

end Alignment.Checks.ClosureTheorem

/-! ## `ClosureTheorem.header.verificationStrategy`

`sa_impl%` is `poisson ∧ binomial ∧ negbin ∧ nonPT`. The Poisson identity is literally S1. The
witness pair θ = 1, θ = 1/2 of S4 evaluates (closed rational arithmetic, kernel `rfl` under
`with_unfolding_all`) to exactly the two literal records of `nonPT_closure_ratio_varies`, and the
inequality comes from `h`. The binomial and negative-binomial identities are stated in shifted
parametrisations (`n + 2` trials; `m + 1` successes with a free `p`), and moving between these and
the shadows' `n`, `r` needs `Nat.cast` lemmas. -/
namespace Alignment.Shadows.ClosureTheorem.header_verificationStrategy

sa_claim "ClosureTheorem.header.verificationStrategy" group "ClosureTheorem" required
  text "We check the sufficiency identities for PT families: for each PT family, the values psi(theta), psi'(theta), psi''(theta) of its PGF, written as monomials in free scalars, satisfy psi'' psi = kappa (psi')^2 as ring identities. The necessity direction of KKR Theorem 1 (only PT laws have constant kappa) is not formalised; we only exhibit one non-PT law, psi = 1/2 + theta^2/2, whose ratio kappa(theta) takes two different values."
  impl poisson_closure_ode binomial_closure_ode negbin_general_closure_ode nonPT_closure_ratio_varies

@[sa_forward "ClosureTheorem.header.verificationStrategy" 1]
theorem fwd1 (h : sa_impl% "ClosureTheorem.header.verificationStrategy") : S1 :=
  fun lam E => h.1 lam E

sa_fail_forward "ClosureTheorem.header.verificationStrategy" 2 "impl binomial_closure_ode is stated for n + 2 trials: ((↑n+2)(↑n+1)p²wⁿ)w^(n+2) = ((↑n+1)/(↑n+2))((↑n+2)p w^(n+1))². S2 is for every n ≥ 1 with casts ↑n, ↑n - 1 and exponents n - 2, n - 1. impl does not cover n = 1, and instantiating it at n - 2 for n ≥ 2 needs Nat.cast_add / Nat.cast_sub and Nat.sub_add_cancel, which are library lemmas, not structural. (For n ≥ 2 the identities agree mathematically.)"

sa_fail_forward "ClosureTheorem.header.verificationStrategy" 3 "impl negbin_general_closure_ode is stated for m + 1 successes with a free p: ((↑m+1)(↑m+2)p²c^(m+1)w^(m+3))(c^(m+1)w^(m+1)) = ((↑m+2)/(↑m+1))((↑m+1)p c^(m+1)w^(m+2))². S3 is the instance p = 1 - c at r = m + 1, but getting it for a variable r ≥ 1 needs a case split on r with Nat.le elimination and ((m+1 : ℕ) : ℚ) = ↑m + 1 (Nat.cast_succ; not definitional in ℚ). That is not structural, though impl implies S3 mathematically."

@[sa_forward "ClosureTheorem.header.verificationStrategy" 4]
theorem fwd4 (h : sa_impl% "ClosureTheorem.header.verificationStrategy") : S4 := by
  refine ⟨1, by with_unfolding_all exact rfl, 1 / 2, by with_unfolding_all exact rfl,
    by with_unfolding_all exact rfl, by with_unfolding_all exact rfl, ?_⟩
  with_unfolding_all exact h.2.2.2

sa_fail_backward "ClosureTheorem.header.verificationStrategy" "impl is more general than the shadows in two conjuncts. (1) negbin_general_closure_ode holds for a free p, while S3 fixes p = 1 - c, so S3 gives only the instances p = 1 - c. (2) nonPT_closure_ratio_varies names the two records ⟨1,1,1⟩ and ⟨5/8,1/2,1⟩, while S4 only asserts that some pair θ₁, θ₂ ∈ (0,1] exists, and the existential does not identify the pair. Also, S2 → binomial_closure_ode at n + 2 needs Nat.cast_add (not structural)."

end Alignment.Shadows.ClosureTheorem.header_verificationStrategy

/-! ## `ClosureTheorem.table.R52` -/
namespace Alignment.Shadows.ClosureTheorem.table_R52

sa_claim "ClosureTheorem.table.R52" group "ClosureTheorem" required
  text "| 52 | Poisson closure ODE: kappa = 1 at every theta |"
  impl poisson_closure_ratio

sa_fail_forward "ClosureTheorem.table.R52" 1 "impl poisson_closure_ratio is the ratio form closureRatio <E, lam*E, lam^2*E> = 1, i.e. (lam^2 E) E / (lam E)^2 = 1. S1 is the ODE form (lam^2 E) E = 1 * (lam E)^2. Going from the ratio to the ODE needs field reasoning (div_eq_iff with (lam E)^2 /= 0, the content of Result 51), which is not structural and is not a definition bridge. The ODE form is poisson_closure_ode (Result 52), which is not in this claim's impl list."
sa_fail_forward "ClosureTheorem.table.R52" 2 "impl is a statement over Q in which psi = psi_val is a free positive rational and psi' = lam*psi, psi'' = lam^2*psi are supplied as expressions (free-scalar abstraction). S2 requires the real Poisson PGF t => exp(lam(t-1)) to satisfy deriv (deriv psi) theta * psi theta = 1 * (deriv psi theta)^2 for theta in [0,1]. impl has no real functions or derivatives."
sa_fail_backward "ClosureTheorem.table.R52" "impl's ratio form closureRatio <psi, lam psi, lam^2 psi> = 1 does not follow structurally from S1's ODE form (it needs division by (lam psi)^2 /= 0, field reasoning), and S2 is a statement over R with deriv that cannot give the Q statement."

end Alignment.Shadows.ClosureTheorem.table_R52

/-! ## `ClosureTheorem.table.R53` -/
namespace Alignment.Shadows.ClosureTheorem.table_R53

sa_claim "ClosureTheorem.table.R53" group "ClosureTheorem" required
  text "| 53 | Binomial(n+2) closure ODE: kappa = (n+1)/(n+2) |"
  impl binomial_closure_ratio

sa_fail_forward "ClosureTheorem.table.R53" 1 "impl binomial_closure_ratio is the ratio form closureRatio <w^(n+2), (n+2) p w^(n+1), (n+2)(n+1) p^2 w^n> = (n+1)/(n+2) under 0 < p and 0 < w. S1 is the ODE form psi'' psi = ((n+1)/(n+2)) psi'^2 for every p in [0,1] and theta in [0,1]. This includes p = 0 and w = 1-p+p*theta = 0 (p = 1, theta = 0), which impl excludes. Going from the ratio to the ODE also needs field reasoning (division by psi'^2), which is not structural."
sa_fail_forward "ClosureTheorem.table.R53" 2 "impl is over Q with w a free positive rational standing for 1-p+p*theta, and psi', psi'' supplied as expressions. S2 requires the real Binomial(n+2,p) PGF to satisfy the closure ODE with deriv (deriv psi). impl has no real functions or derivatives."
sa_fail_backward "ClosureTheorem.table.R53" "impl is stronger than S1: it covers all p > 0 and w > 0 independently (including p > 1 and w > 1), while S1 covers only p in [0,1] with w = 1-p+p*theta in [1-p, 1]. impl's ratio form also needs division from S1's ODE form, which is not structural. S2 is over R."

end Alignment.Shadows.ClosureTheorem.table_R53

/-! ## `ClosureTheorem.table.R54` -/
namespace Alignment.Shadows.ClosureTheorem.table_R54

sa_claim "ClosureTheorem.table.R54" group "ClosureTheorem" required
  text "| 54 | NegBin(2) closure ODE: kappa = 3/2 at every theta |"
  impl negbin2_closure_ratio

sa_fail_forward "ClosureTheorem.table.R54" 1 "impl negbin2_closure_ratio is the ratio form closureRatio <c^2 w^2, 2 p c^2 w^3, 6 p^2 c^2 w^4> = 3/2 for free p, c, w > 0. S1 is the ODE form psi'' psi = (3/2) psi'^2 for the closed forms (c/D)^2, 2(1-c)c^2/D^3, 6(1-c)^2 c^2/D^4 with D = 1-(1-c)theta. To identify them one needs p := 1-c, w := 1/D and field algebra ((c/D)^2 = c^2 (1/D)^2, x/D^k = x (1/D)^k). Going from the ratio to the ODE needs division by psi'^2. Neither step is structural."
sa_fail_forward "ClosureTheorem.table.R54" 2 "impl is over Q with free p, c, w and psi, psi', psi'' supplied as expressions. S2 requires the real NegBin(2,c) PGF (c/(1-(1-c)t))^2 to satisfy the closure ODE with deriv. impl has no real functions or derivatives."
sa_fail_backward "ClosureTheorem.table.R54" "impl is stronger and in a different parametrisation: it covers independent positive p, c, w (not tied by p = 1-c and w = 1/(1-p*theta)), while S1 gives only the closed-form ODE for c in (0,1) and theta in [0,1]. The records also differ syntactically, and the ratio form needs division from the ODE form. S2 is over R."

end Alignment.Shadows.ClosureTheorem.table_R54

/-! ## `ClosureTheorem.table.R55` -/
namespace Alignment.Shadows.ClosureTheorem.table_R55

sa_claim "ClosureTheorem.table.R55" group "ClosureTheorem" required
  text "| 55 | NegBin(3) closure ODE: kappa = 4/3 at every theta |"
  impl negbin3_closure_ratio

sa_fail_forward "ClosureTheorem.table.R55" 1 "impl negbin3_closure_ratio is the ratio form closureRatio <c^3 w^3, 3 p c^3 w^4, 12 p^2 c^3 w^5> = 4/3 for free p, c, w > 0. S1 is the ODE form psi'' psi = (4/3) psi'^2 for the closed forms (c/D)^3, 3(1-c)c^3/D^4, 12(1-c)^2 c^3/D^5 with D = 1-(1-c)theta. To identify them one needs p := 1-c, w := 1/D and field algebra ((c/D)^3 = c^3 (1/D)^3, x/D^k = x (1/D)^k). Going from the ratio to the ODE needs division by psi'^2. Neither step is structural."
sa_fail_forward "ClosureTheorem.table.R55" 2 "impl is over Q with free p, c, w and psi, psi', psi'' supplied as expressions. S2 requires the real NegBin(3,c) PGF (c/(1-(1-c)t))^3 to satisfy the closure ODE with deriv. impl has no real functions or derivatives."
sa_fail_backward "ClosureTheorem.table.R55" "impl is stronger and in a different parametrisation: it covers independent positive p, c, w (not tied by p = 1-c and w = 1/(1-p*theta)), while S1 gives only the closed-form ODE for c in (0,1) and theta in [0,1]. The records also differ syntactically, and the ratio form needs division from the ODE form. S2 is over R."

end Alignment.Shadows.ClosureTheorem.table_R55

/-! ## `ClosureTheorem.table.R56` -/
namespace Alignment.Shadows.ClosureTheorem.table_R56

sa_claim "ClosureTheorem.table.R56" group "ClosureTheorem" required
  text "| 56 | General NegBin ODE algebraic identity |"
  impl negbin_general_closure_ode

sa_fail_forward "ClosureTheorem.table.R56" 1 "impl negbin_general_closure_ode states ((m+1)(m+2)p^2 c^(m+1) w^(m+3))(c^(m+1) w^(m+1)) = ((m+2)/(m+1))((m+1) p c^(m+1) w^(m+2))^2 in free p, c, w. S1 needs the identity for the NegBin(m+1) closed forms psi = (c/D)^(m+1), psi' = (m+1)(1-c)c^(m+1)/D^(m+2), psi'' = (m+1)(m+2)(1-c)^2 c^(m+1)/D^(m+3) with D = 1-(1-c)theta. With p := 1-c, w := 1/D the two statements agree only up to field algebra ((c/D)^k = c^k (1/D)^k, x/D^k = x (1/D)^k), which is not structural. No trusted definition is involved, so no bridge applies."
sa_fail_backward "ClosureTheorem.table.R56" "impl is a ring identity for every m and all p, c, w in Q. S1 gives it only for the NegBin closed forms with c in (0,1) and theta in [0,1], in a different parametrisation. So impl is strictly more general than S1."

end Alignment.Shadows.ClosureTheorem.table_R56

/-! ## `ClosureTheorem.table.R57` -/
namespace Alignment.Shadows.ClosureTheorem.table_R57
open Alignment.Shadows.ClosureTheorem Alignment.Checks.ClosureTheorem

sa_claim "ClosureTheorem.table.R57" group "ClosureTheorem" required
  text "| 57 | Non-PT counterexample: kappa varies with theta |"
  impl nonPT_closure_ratio_varies

/-- The same witness as `header_verificationStrategy.fwd4`: the mixture (1/2, 0, 1/2) at θ = 1 and
θ = 1/2, whose records evaluate to the impl's literal records. The inequality is `h`. -/
@[sa_forward "ClosureTheorem.table.R57" 1]
theorem fwd1 (h : sa_impl% "ClosureTheorem.table.R57") : S1 := by
  unfold S1 nonPTexists
  refine ⟨3, wMix, wMix_nonneg, ?_, 1, 1 / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · with_unfolding_all exact rfl
  · with_unfolding_all exact rfl
  · with_unfolding_all exact rfl
  · with_unfolding_all exact rfl
  · with_unfolding_all exact rfl
  · with_unfolding_all exact rfl
  · with_unfolding_all exact rfl
  · with_unfolding_all exact rfl
  · with_unfolding_all exact rfl
  · with_unfolding_all exact h

sa_fail_backward "ClosureTheorem.table.R57" "impl asserts that two specific literal records (1,1,1) and (5/8,1/2,1) have different closure ratios. S1 only asserts that some finitely supported distribution has a closure ratio that differs at some theta_1, theta_2. This does not determine the impl's records."

end Alignment.Shadows.ClosureTheorem.table_R57

/-! ## `ClosureTheorem.table.R58` -/
namespace Alignment.Shadows.ClosureTheorem.table_R58

sa_claim "ClosureTheorem.table.R58" group "ClosureTheorem" required
  text "| 58 | Connection: closureRatio at theta=1 = closureKappa |"
  impl closure_ratio_at_one'

/-- The records agree up to their proof fields (proof irrelevance). -/
@[sa_forward "ClosureTheorem.table.R58" 1]
theorem fwd1 (h : sa_impl% "ClosureTheorem.table.R58") : S1 := fun ψ => h ψ

@[sa_backward "ClosureTheorem.table.R58"]
theorem bwd (s1 : S1) : sa_impl% "ClosureTheorem.table.R58" := fun ψ => s1 ψ

end Alignment.Shadows.ClosureTheorem.table_R58

/-! ## `ClosureTheorem.table.R59` -/
namespace Alignment.Shadows.ClosureTheorem.table_R59

sa_claim "ClosureTheorem.table.R59" group "ClosureTheorem" required
  text "| 59 | Trichotomy kappa < 1, = 1, > 1 (not a classification) |"
  impl pt_classification_exhaustive

sa_fail_forward "ClosureTheorem.table.R59" 1 "impl pt_classification_exhaustive gives the trichotomy only under the hypothesis 0 < κ. For d : PGFData, closureKappa d = ψ''(1)/ψ'(1)² can be 0 (secondFactorial_nonneg allows ψ''(1) = 0, e.g. the 1-regular record), and where it is positive, proving 0 < closureKappa d needs div_pos and the data invariants. So S1 does not follow from h for every record."

sa_fail_forward "ClosureTheorem.table.R59" 2 "impl pt_classification_exhaustive needs 0 < κ. PGFEval constrains only ψ > 0 and ψ' > 0, so closureRatio e = ψ''ψ/ψ'² is ≤ 0 whenever ψ'' ≤ 0. For those e, S2 does not follow from h; impl is weaker than S2 (a trichotomy for every rational)."

sa_fail_backward "ClosureTheorem.table.R59" "impl quantifies over a free rational κ > 0. The shadows give the trichotomy only for closureKappa d = ψ''(1)/ψ'(1)² and closureRatio e = ψ''ψ/ψ'². To hit an arbitrary κ one instantiates, e.g., d = ⟨1, κ⟩ with closureKappa = κ/1², and κ/1² = κ needs div_one/one_pow, which are not definitional for a variable κ in ℚ. Not structurally derivable (mathematically S1 implies impl)."

end Alignment.Shadows.ClosureTheorem.table_R59

/-! ## `ClosureTheorem.R51` -/
namespace Alignment.Shadows.ClosureTheorem.R51

sa_claim "ClosureTheorem.R51" group "ClosureTheorem" required
  text "**Result 51.** If psi'' psi = kappa (psi')^2 at a point, then the closure ratio equals kappa at that point."
  impl closure_ode_gives_ratio

@[sa_forward "ClosureTheorem.R51" 1]
theorem fwd1 (h : sa_impl% "ClosureTheorem.R51") : S1 := fun e κ hode => h e κ hode

@[sa_backward "ClosureTheorem.R51"]
theorem bwd (s1 : S1) : sa_impl% "ClosureTheorem.R51" := fun e κ hode => s1 e κ hode

end Alignment.Shadows.ClosureTheorem.R51

/-! ## `ClosureTheorem.R52` -/
namespace Alignment.Shadows.ClosureTheorem.R52

sa_claim "ClosureTheorem.R52" group "ClosureTheorem" required
  text "**Result 52.** Poisson ODE identity."
  impl poisson_closure_ode

/-- impl is the identity for all `lam, psi_val`; S1 is its restriction to `lam > 0, E > 0`. -/
@[sa_forward "ClosureTheorem.R52" 1]
theorem fwd1 (h : sa_impl% "ClosureTheorem.R52") : S1 := fun lam E _ _ => h lam E

sa_fail_forward "ClosureTheorem.R52" 2 "impl is a ring identity over Q in which psi = psi_val is a free rational and psi' = lam*psi, psi'' = lam^2*psi are chosen expressions (free-scalar abstraction). S2 requires the real Poisson PGF t => exp(lam(t-1)) to satisfy deriv (deriv psi) theta * psi theta = 1 * (deriv psi theta)^2 for theta in [0,1]. impl has no real functions or derivatives."
sa_fail_backward "ClosureTheorem.R52" "impl is stronger than S1: it is the identity for all lam, psi_val in Q, while S1 gives it only under 0 < lam and 0 < E. The cases lam <= 0 or psi_val <= 0 cannot be derived structurally, and S2 is over R."

end Alignment.Shadows.ClosureTheorem.R52

/-! ## `ClosureTheorem.poissonClosureRatio` -/
namespace Alignment.Shadows.ClosureTheorem.poissonClosureRatio

sa_claim "ClosureTheorem.poissonClosureRatio" group "ClosureTheorem" required
  text "Poisson has constant closure ratio kappa = 1."
  impl poisson_closure_ratio

/-- Same record as impl, up to the proof field `0 < lam * E` (proof irrelevance). -/
@[sa_forward "ClosureTheorem.poissonClosureRatio" 1]
theorem fwd1 (h : sa_impl% "ClosureTheorem.poissonClosureRatio") : S1 :=
  fun lam E hlam hψ _ => h lam E hlam hψ

sa_fail_forward "ClosureTheorem.poissonClosureRatio" 2 "impl is over Q with psi = psi_val a free positive rational and psi', psi'' supplied as lam*psi, lam^2*psi (free-scalar abstraction, 'constant' rendered as for all psi_val > 0). S2 requires the actual ratio deriv (deriv psi) theta * psi theta / (deriv psi theta)^2 of the real Poisson PGF exp(lam(t-1)) to equal 1 for theta in [0,1]. impl has no real functions or derivatives."
sa_fail_backward "ClosureTheorem.poissonClosureRatio" "Audit limitation only. S1 is the impl's statement except that it takes 0 < lam*E as a separate hypothesis hpsi'. impl assumes only 0 < lam and 0 < psi_val and builds the record with mul_pos. Supplying hpsi' needs the library lemma mul_pos, which is not structural. There is no semantic gap in S1 => impl. S2 (over R) cannot help."

end Alignment.Shadows.ClosureTheorem.poissonClosureRatio

/-! ## `ClosureTheorem.R53` -/
namespace Alignment.Shadows.ClosureTheorem.R53
open Alignment.Shadows.ClosureTheorem

sa_claim "ClosureTheorem.R53" group "ClosureTheorem" required
  text "**Result 53.** Binomial ODE identity, general in n."
  impl binomial_closure_ode

/-- Instance `w := 1 − p + pθ` of impl (`bPsi*` unfold to impl's expressions). -/
@[sa_forward "ClosureTheorem.R53" 1]
theorem fwd1 (h : sa_impl% "ClosureTheorem.R53") : S1 :=
  fun n p θ _ _ _ _ => h n p (1 - p + p * θ)

sa_fail_forward "ClosureTheorem.R53" 2 "impl is a ring identity over Q in which w is a free rational standing for 1-p+p*theta, and psi', psi'' are chosen expressions. S2 requires the real Binomial(n+2,p) PGF (1-p+p t)^(n+2) to satisfy the closure ODE with deriv (deriv psi) at every theta in [0,1]. impl has no real functions or derivatives."
sa_fail_backward "ClosureTheorem.R53" "impl is stronger than S1: it is the identity for all p, w in Q, while S1 gives it only for p in [0,1] and w = 1-p+p*theta with theta in [0,1]. S2 is over R."

end Alignment.Shadows.ClosureTheorem.R53

/-! ## `ClosureTheorem.binomialClosureRatio` -/
namespace Alignment.Shadows.ClosureTheorem.binomialClosureRatio

sa_claim "ClosureTheorem.binomialClosureRatio" group "ClosureTheorem" required
  text "Binomial(n+2, p) has constant closure ratio (n+1)/(n+2)."
  impl binomial_closure_ratio

sa_fail_forward "ClosureTheorem.binomialClosureRatio" 1 "Audit limitation (no semantic gap in this direction). impl needs the hypotheses 0 < p and 0 < w. S1 supplies 0 <= p <= 1, 0 <= theta <= 1, 0 < psi and 0 < psi'. With w := 1-p+p*theta the records agree definitionally. But 0 < p (from 0 < (n+2) p w^(n+1)) and 0 < 1-p+p*theta (from p <= 1, theta >= 0 and 0 < w^(n+2)) need order reasoning on Q, which is not structural."
sa_fail_forward "ClosureTheorem.binomialClosureRatio" 2 "impl is over Q with w a free positive rational and psi, psi', psi'' supplied as expressions ('constant' rendered as for all w > 0). S2 requires the actual ratio of the real Binomial(n+2,p) PGF and its deriv to equal (n+1)/(n+2) at every theta in [0,1] where deriv psi theta /= 0. impl has no real functions or derivatives."
sa_fail_backward "ClosureTheorem.binomialClosureRatio" "impl is stronger than S1: it covers all p > 0 and w > 0 independently (including p > 1 and w > 1), while S1 covers only p in [0,1] with w = 1-p+p*theta in [1-p, 1]. S1's extra hypotheses 0 < psi and 0 < psi' would also need order lemmas to discharge. S2 is over R."

end Alignment.Shadows.ClosureTheorem.binomialClosureRatio

/-! ## `ClosureTheorem.R54` -/
namespace Alignment.Shadows.ClosureTheorem.R54

sa_claim "ClosureTheorem.R54" group "ClosureTheorem" required
  text "**Result 54.** NegBin(2) ODE identity."
  impl negbin2_closure_ode

sa_fail_forward "ClosureTheorem.R54" 1 "impl negbin2_closure_ode is the identity (6 p^2 c^2 w^4)(c^2 w^2) = (3/2)(2 p c^2 w^3)^2 in free p, c, w. S1 needs it for the NegBin(2) closed forms: 6(1-c)^2 c^2/D^4 * (c/D)^2 = (3/2)(2(1-c)c^2/D^3)^2 with D = 1-(1-c)theta. With p := 1-c, w := 1/D the sides agree only up to field algebra ((c/D)^2 = c^2 (1/D)^2, x/D^k = x (1/D)^k), which is not structural. No trusted definition is involved, so no bridge applies."
sa_fail_forward "ClosureTheorem.R54" 2 "impl is a ring identity over Q with free p, c, w. S2 requires the real NegBin(2,c) PGF (c/(1-(1-c)t))^2 to satisfy the closure ODE with deriv at every theta in [0,1]. impl has no real functions or derivatives."
sa_fail_backward "ClosureTheorem.R54" "impl is stronger than S1 and in a different parametrisation: it is the identity for all p, c, w in Q, while S1 gives only the closed-form identity for c in (0,1) and theta in [0,1]. S2 is over R."

end Alignment.Shadows.ClosureTheorem.R54

/-! ## `ClosureTheorem.negbin2ClosureRatio` -/
namespace Alignment.Shadows.ClosureTheorem.negbin2ClosureRatio

sa_claim "ClosureTheorem.negbin2ClosureRatio" group "ClosureTheorem" required
  text "NegBin(2) has constant closure ratio 3/2."
  impl negbin2_closure_ratio

sa_fail_forward "ClosureTheorem.negbin2ClosureRatio" 1 "impl gives closureRatio <c^2 w^2, 2 p c^2 w^3, 6 p^2 c^2 w^4> = 3/2 for free positive p, c, w. S1 needs closureRatio of the closed-form record <(c/D)^2, 2(1-c)c^2/D^3, 6(1-c)^2 c^2/D^4> with D = 1-(1-c)theta. No instantiation makes the records definitionally equal: (c/D)^2 = c^2 (1/D)^2 and x/D^k = x (1/D)^k are field algebra. impl's hypotheses 0 < 1-c and 0 < 1/D would also need order reasoning. Neither is structural."
sa_fail_forward "ClosureTheorem.negbin2ClosureRatio" 2 "impl is over Q with free p, c, w and psi, psi', psi'' supplied as expressions. S2 requires the actual ratio of the real NegBin(2,c) PGF and its deriv to equal 3/2 at every theta in [0,1]. impl has no real functions or derivatives."
sa_fail_backward "ClosureTheorem.negbin2ClosureRatio" "impl ranges over independent positive p, c, w (not tied by p = 1-c and w = 1/(1-p*theta)). This is not covered by S1, whose closed-form records also differ syntactically from impl's. S2 is over R."

end Alignment.Shadows.ClosureTheorem.negbin2ClosureRatio

/-! ## `ClosureTheorem.R55` -/
namespace Alignment.Shadows.ClosureTheorem.R55

sa_claim "ClosureTheorem.R55" group "ClosureTheorem" required
  text "**Result 55.** NegBin(3) ODE identity."
  impl negbin3_closure_ode

sa_fail_forward "ClosureTheorem.R55" 1 "impl negbin3_closure_ode is the identity (12 p^2 c^3 w^5)(c^3 w^3) = (4/3)(3 p c^3 w^4)^2 in free p, c, w. S1 needs it for the NegBin(3) closed forms: 12(1-c)^2 c^3/D^5 * (c/D)^3 = (4/3)(3(1-c)c^3/D^4)^2 with D = 1-(1-c)theta. With p := 1-c, w := 1/D the sides agree only up to field algebra ((c/D)^3 = c^3 (1/D)^3, x/D^k = x (1/D)^k), which is not structural. No trusted definition is involved, so no bridge applies."
sa_fail_forward "ClosureTheorem.R55" 2 "impl is a ring identity over Q with free p, c, w. S2 requires the real NegBin(3,c) PGF (c/(1-(1-c)t))^3 to satisfy the closure ODE with deriv at every theta in [0,1]. impl has no real functions or derivatives."
sa_fail_backward "ClosureTheorem.R55" "impl is stronger than S1 and in a different parametrisation: it is the identity for all p, c, w in Q, while S1 gives only the closed-form identity for c in (0,1) and theta in [0,1]. S2 is over R."

end Alignment.Shadows.ClosureTheorem.R55

/-! ## `ClosureTheorem.negbin3ClosureRatio` -/
namespace Alignment.Shadows.ClosureTheorem.negbin3ClosureRatio

sa_claim "ClosureTheorem.negbin3ClosureRatio" group "ClosureTheorem" required
  text "NegBin(3) has constant closure ratio 4/3."
  impl negbin3_closure_ratio

sa_fail_forward "ClosureTheorem.negbin3ClosureRatio" 1 "impl gives closureRatio <c^3 w^3, 3 p c^3 w^4, 12 p^2 c^3 w^5> = 4/3 for free positive p, c, w. S1 needs closureRatio of the closed-form record <(c/D)^3, 3(1-c)c^3/D^4, 12(1-c)^2 c^3/D^5> with D = 1-(1-c)theta. No instantiation makes the records definitionally equal: (c/D)^3 = c^3 (1/D)^3 and x/D^k = x (1/D)^k are field algebra. impl's hypotheses 0 < 1-c and 0 < 1/D would also need order reasoning. Neither is structural."
sa_fail_forward "ClosureTheorem.negbin3ClosureRatio" 2 "impl is over Q with free p, c, w and psi, psi', psi'' supplied as expressions. S2 requires the actual ratio of the real NegBin(3,c) PGF and its deriv to equal 4/3 at every theta in [0,1]. impl has no real functions or derivatives."
sa_fail_backward "ClosureTheorem.negbin3ClosureRatio" "impl ranges over independent positive p, c, w (not tied by p = 1-c and w = 1/(1-p*theta)). This is not covered by S1, whose closed-form records also differ syntactically from impl's. S2 is over R."

end Alignment.Shadows.ClosureTheorem.negbin3ClosureRatio

/-! ## `ClosureTheorem.R56` -/
namespace Alignment.Shadows.ClosureTheorem.R56

sa_claim "ClosureTheorem.R56" group "ClosureTheorem" required
  text "**Result 56.** General NegBin(m+1) ODE identity."
  impl negbin_general_closure_ode

sa_fail_forward "ClosureTheorem.R56" 1 "impl negbin_general_closure_ode states ((m+1)(m+2)p^2 c^(m+1) w^(m+3))(c^(m+1) w^(m+1)) = ((m+2)/(m+1))((m+1) p c^(m+1) w^(m+2))^2 in free p, c, w. S1 needs the identity for the NegBin(m+1) closed forms psi = (c/D)^(m+1), psi' = (m+1)(1-c)c^(m+1)/D^(m+2), psi'' = (m+1)(m+2)(1-c)^2 c^(m+1)/D^(m+3) with D = 1-(1-c)theta. With p := 1-c, w := 1/D the two statements agree only up to field algebra ((c/D)^k = c^k (1/D)^k, x/D^k = x (1/D)^k), which is not structural. No trusted definition is involved, so no bridge applies."
sa_fail_forward "ClosureTheorem.R56" 2 "impl is a ring identity over Q with free p, c, w. S2 requires the real NegBin(m+1,c) PGF (c/(1-(1-c)t))^(m+1) to satisfy the closure ODE with deriv at every theta in [0,1]. impl has no real functions or derivatives."
sa_fail_backward "ClosureTheorem.R56" "impl is stronger than S1 and in a different parametrisation: it is the identity for every m and all p, c, w in Q, while S1 gives only the closed-form identity for c in (0,1) and theta in [0,1]. S2 is over R."

end Alignment.Shadows.ClosureTheorem.R56

/-! ## `ClosureTheorem.R57` -/
namespace Alignment.Shadows.ClosureTheorem.R57

sa_claim "ClosureTheorem.R57" group "ClosureTheorem" required
  text "**Result 57.** Non-PT: mixture psi = 1/2 + theta^2/2 has varying kappa."
  impl nonPT_closure_ratio_varies

/-- θ₁ = 1, θ₂ = 1/2: the mixture records ⟨1/2 + θ²/2, θ, 1⟩ evaluate (closed kernel arithmetic)
to the impl's literal records ⟨1, 1, 1⟩ and ⟨5/8, 1/2, 1⟩. The inequality is `h`. -/
@[sa_forward "ClosureTheorem.R57" 1]
theorem fwd1 (h : sa_impl% "ClosureTheorem.R57") : S1 := by
  unfold S1 variesAlg
  refine ⟨1, 1 / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · with_unfolding_all exact rfl
  · with_unfolding_all exact rfl
  · with_unfolding_all exact rfl
  · with_unfolding_all exact rfl
  · with_unfolding_all exact rfl
  · with_unfolding_all exact rfl
  · with_unfolding_all exact h

sa_fail_forward "ClosureTheorem.R57" 2 "impl only asserts closureRatio <1,1,1> /= closureRatio <5/8,1/2,1>. S2 says that no constant kappa satisfies the ODE form 1*(1/2+theta^2/2) = kappa*theta^2 on (0,1]. From a hypothetical kappa one gets closureRatio <1,1,1> = kappa*1^2/1^2 and closureRatio <5/8,1/2,1> = kappa*(1/2)^2/(1/2)^2. Identifying both with kappa needs field cancellation, which is not structural. The non-PT property (in ODE form) is not stated by impl."
sa_fail_forward "ClosureTheorem.R57" 3 "impl is about two literal rational records, with no real function or derivative. S3 requires the actual ratio deriv (deriv mixR) theta * mixR theta / (deriv mixR theta)^2 of the real function 1/2 + t^2/2 to take two different values on (0,1]. impl does not relate its records to the derivatives of the mixture."
sa_fail_backward "ClosureTheorem.R57" "impl is an inequality between two specific literal records (1,1,1) and (5/8,1/2,1). S1 and S3 are existential (some theta_1, theta_2) and S2 is a negation. None of them determines the impl's records."

end Alignment.Shadows.ClosureTheorem.R57

/-! ## `ClosureTheorem.R58` -/
namespace Alignment.Shadows.ClosureTheorem.R58

sa_claim "ClosureTheorem.R58" group "ClosureTheorem" required
  text "**Result 58.** At theta = 1, closureRatio = closureKappa."
  impl closure_ratio_at_one'

/-- The records agree up to their proof fields (proof irrelevance). -/
@[sa_forward "ClosureTheorem.R58" 1]
theorem fwd1 (h : sa_impl% "ClosureTheorem.R58") : S1 := fun ψ => h ψ

@[sa_backward "ClosureTheorem.R58"]
theorem bwd (s1 : S1) : sa_impl% "ClosureTheorem.R58" := fun ψ => s1 ψ

end Alignment.Shadows.ClosureTheorem.R58

/-! ## `ClosureTheorem.R59` -/
namespace Alignment.Shadows.ClosureTheorem.R59

sa_claim "ClosureTheorem.R59" group "ClosureTheorem" required
  text "**Result 59.** Trichotomy: kappa < 1, = 1, or > 1."
  impl pt_classification_exhaustive

sa_fail_forward "ClosureTheorem.R59" 1 "impl pt_classification_exhaustive has the hypothesis 0 < kap (unused in its proof, but part of the statement). S1 is the trichotomy for every kappa in Q, and the Result 59 text states no range. So impl gives nothing for kappa <= 0 (the range 'kappa > 0' appears only in the header-table row 59, a separate claim)."

@[sa_backward "ClosureTheorem.R59"]
theorem bwd (s1 : S1) : sa_impl% "ClosureTheorem.R59" := fun κ _ => s1 κ

end Alignment.Shadows.ClosureTheorem.R59

/-! ## `ClosureTheorem.binomialKappaDeterminesN` -/
namespace Alignment.Shadows.ClosureTheorem.binomialKappaDeterminesN

sa_claim "ClosureTheorem.binomialKappaDeterminesN" group "ClosureTheorem" required
  text "For Binomial, kappa = (n-1)/n < 1."
  impl binomial_kappa_determines_n'

sa_fail_forward "ClosureTheorem.binomialKappaDeterminesN" 1 "impl binomial_kappa_determines_n' only states (n-1)/n < 1 for n >= 2. It says nothing about closureKappa of the Binomial PGFData <n p, n(n-1) p^2>, so the identification kappa = (n-1)/n (S1) is not in impl."
sa_fail_forward "ClosureTheorem.binomialKappaDeterminesN" 2 "impl requires 2 <= n. S2 requires ((n:Q)-1)/n < 1 for every n >= 1, so n = 1 (Binomial(1,p), kappa = 0) is not covered by impl. For n >= 2 there is also an audit limitation: the impl hypothesis 2 <= n cannot be produced structurally from 0 < n (Nat.le constructors are library theorems)."
sa_fail_backward "ClosureTheorem.binomialKappaDeterminesN" "Audit limitation only. S2 => impl is semantically immediate (n >= 2 implies n >= 1), but S2 needs the hypothesis 0 < n. Obtaining it from impl's 2 <= n needs a Nat order lemma (Nat.le 2 n => Nat.le 1 n), which is not structural. S1 (closureKappa) cannot supply it."

end Alignment.Shadows.ClosureTheorem.binomialKappaDeterminesN

/-! ## `ClosureTheorem.binomialRecoverN` -/
namespace Alignment.Shadows.ClosureTheorem.binomialRecoverN

sa_claim "ClosureTheorem.binomialRecoverN" group "ClosureTheorem" required
  text "For Binomial, 1/(1 - (n-1)/n) = n."
  impl binomial_recover_n'

sa_fail_forward "ClosureTheorem.binomialRecoverN" 1 "impl requires 2 <= n. S1 requires 1/(1 - ((n:Q)-1)/n) = n for every n >= 1 (a Binomial has n >= 1 trials), so n = 1 is not covered by impl. For n >= 2 there is also an audit limitation: the impl hypothesis 2 <= n cannot be produced structurally from 0 < n (Nat.le constructors are library theorems)."
sa_fail_backward "ClosureTheorem.binomialRecoverN" "Audit limitation only. S1 => impl is semantically immediate (n >= 2 implies n >= 1), but S1 needs the hypothesis 0 < n. Obtaining it from impl's 2 <= n needs a Nat order lemma (Nat.le 2 n => Nat.le 1 n), which is not structural."

end Alignment.Shadows.ClosureTheorem.binomialRecoverN

/-! ## `ClosureTheorem.negbinKappaDeterminesR` -/
namespace Alignment.Shadows.ClosureTheorem.negbinKappaDeterminesR

sa_claim "ClosureTheorem.negbinKappaDeterminesR" group "ClosureTheorem" required
  text "For NegBin, kappa > 1 gives r = 1/(kappa-1) > 0."
  impl negbin_kappa_determines_r'

@[sa_forward "ClosureTheorem.negbinKappaDeterminesR" 1]
theorem fwd1 (h : sa_impl% "ClosureTheorem.negbinKappaDeterminesR") : S1 := fun κ hκ => h κ hκ

sa_fail_forward "ClosureTheorem.negbinKappaDeterminesR" 2 "impl negbin_kappa_determines_r' only proves 0 < 1/(kappa-1) for kappa > 1. S2 requires recovery of the NegBin parameter: kappa = (r+1)/r with r > 0 implies r = 1/(kappa-1). impl mentions neither r nor the relation kappa = (r+1)/r."

@[sa_backward "ClosureTheorem.negbinKappaDeterminesR"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "ClosureTheorem.negbinKappaDeterminesR" :=
  fun κ hκ => s1 κ hκ

end Alignment.Shadows.ClosureTheorem.negbinKappaDeterminesR

/-! ## `ClosureTheorem.poissonKappaIsOne` -/
namespace Alignment.Shadows.ClosureTheorem.poissonKappaIsOne

sa_claim "ClosureTheorem.poissonKappaIsOne" group "ClosureTheorem" required
  text "Poisson matches Result 42 from SurvivalBridge."
  impl poisson_kappa_is_one'

@[sa_forward "ClosureTheorem.poissonKappaIsOne" 1]
theorem fwd1 (h : sa_impl% "ClosureTheorem.poissonKappaIsOne") : S1 := fun lam hlam => h lam hlam

@[sa_backward "ClosureTheorem.poissonKappaIsOne"]
theorem bwd (s1 : S1) : sa_impl% "ClosureTheorem.poissonKappaIsOne" :=
  fun lam hlam => s1 lam hlam

end Alignment.Shadows.ClosureTheorem.poissonKappaIsOne
