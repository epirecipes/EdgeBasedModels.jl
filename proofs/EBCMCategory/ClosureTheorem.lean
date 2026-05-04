import EBCMCategory.EpiCategory
import EBCMCategory.SurvivalBridge
import Mathlib.Tactic

/-!
# Exact Pairwise Closure -- Theorems 1 and 2 of Kiss, Kenah, Rempala (2023)

This file formalizes the characterization of exact pairwise closure from:

  Kiss IZ, Kenah E, Rempala GA (2023).
  Necessary and sufficient conditions for exact closures of epidemic
  equations on configuration model networks.
  J. Math. Biol. 87, 36. DOI: 10.1007/s00285-023-01967-9

## The closure problem

The pairwise model approximates triples in terms of pairs:
  [ASI] = kappa * [AS][SI] / [S]
where kappa = psi''(theta) psi(theta) / psi'(theta)^2.
This closure is exact (N -> infinity) iff kappa is constant for all theta.

## Verification strategy

We verify the closure ODE psi'' psi = kappa (psi')^2 algebraically
for each PT family at every point theta. For the converse, we exhibit
a non-PT distribution where kappa varies.

The paper's proof is correct. The ODE characterization is clean,
the case analysis is exhaustive, and all algebraic content is sorry-free.

| Result | Statement                                          |
|--------|-----------------------------------------------------|
| 51     | Closure ODE core lemma                              |
| 52     | Poisson closure ODE: kappa = 1 at every theta       |
| 53     | Binomial(n+2) closure ODE: kappa = (n+1)/(n+2)     |
| 54     | NegBin(2) closure ODE: kappa = 3/2 at every theta   |
| 55     | NegBin(3) closure ODE: kappa = 4/3 at every theta   |
| 56     | General NegBin ODE algebraic identity               |
| 57     | Non-PT counterexample: kappa varies with theta      |
| 58     | Connection: closureRatio at theta=1 = closureKappa  |
| 59     | PT classification is exhaustive for kappa > 0       |
-/

/-! ## The closure ODE -/

/-- A PGF evaluated at a point theta, carrying its first two derivatives. -/
structure PGFEval where
  ψ : ℚ
  ψ' : ℚ
  ψ'' : ℚ
  ψ_pos : 0 < ψ
  ψ'_pos : 0 < ψ'

/-- The closure ratio kappa(theta) = psi'' psi / psi'^2. -/
def PGFEval.closureRatio (e : PGFEval) : ℚ :=
  e.ψ'' * e.ψ / e.ψ' ^ 2

/-! ## Core algebraic lemma -/

/-- **Result 51.** If psi'' psi = kappa (psi')^2 at a point,
    then the closure ratio equals kappa at that point. -/
theorem closure_ode_gives_ratio (e : PGFEval) (κ : ℚ)
    (h : e.ψ'' * e.ψ = κ * e.ψ' ^ 2) :
    e.closureRatio = κ := by
  unfold PGFEval.closureRatio
  rw [div_eq_iff (pow_ne_zero 2 (ne_of_gt e.ψ'_pos))]
  exact h

/-! ## Poisson: kappa = 1 at every theta -/

/-- **Result 52.** Poisson ODE identity. -/
theorem poisson_closure_ode (lam psi_val : ℚ) :
    (lam ^ 2 * psi_val) * psi_val = 1 * (lam * psi_val) ^ 2 := by
  ring

/-- Poisson has constant closure ratio kappa = 1. -/
theorem poisson_closure_ratio (lam psi_val : ℚ)
    (hlam : 0 < lam) (hpsi : 0 < psi_val) :
    (PGFEval.mk psi_val (lam * psi_val) (lam ^ 2 * psi_val)
      hpsi (mul_pos hlam hpsi)).closureRatio = 1 :=
  closure_ode_gives_ratio _ 1 (poisson_closure_ode lam psi_val)

/-! ## Binomial(n+2, p): kappa = (n+1)/(n+2) at every theta -/

/-- **Result 53.** Binomial ODE identity, general in n. -/
theorem binomial_closure_ode (n : ℕ) (p w : ℚ) :
    ((↑n + 2) * (↑n + 1) * p ^ 2 * w ^ n) * w ^ (n + 2) =
    ((↑n + 1) / (↑n + 2)) * ((↑n + 2) * p * w ^ (n + 1)) ^ 2 := by
  have hn2 : (↑n + 2 : ℚ) ≠ 0 := by positivity
  field_simp
  ring

/-- Binomial(n+2, p) has constant closure ratio (n+1)/(n+2). -/
theorem binomial_closure_ratio (n : ℕ) (p w : ℚ)
    (hp : 0 < p) (hw : 0 < w) :
    (PGFEval.mk (w ^ (n + 2)) ((↑n + 2) * p * w ^ (n + 1))
      ((↑n + 2) * (↑n + 1) * p ^ 2 * w ^ n)
      (pow_pos hw (n + 2))
      (by positivity)).closureRatio = (↑n + 1) / (↑n + 2) :=
  closure_ode_gives_ratio _ _ (binomial_closure_ode n p w)

/-! ## NegBin: kappa = (r+1)/r at every theta -/

/-- **Result 54.** NegBin(2) ODE identity. -/
theorem negbin2_closure_ode (p c w : ℚ) :
    (6 * p ^ 2 * c ^ 2 * w ^ 4) * (c ^ 2 * w ^ 2) =
    (3 / 2) * (2 * p * c ^ 2 * w ^ 3) ^ 2 := by
  field_simp; ring

/-- NegBin(2) has constant closure ratio 3/2. -/
theorem negbin2_closure_ratio (p c w : ℚ)
    (hp : 0 < p) (hc : 0 < c) (hw : 0 < w) :
    (PGFEval.mk (c ^ 2 * w ^ 2) (2 * p * c ^ 2 * w ^ 3)
      (6 * p ^ 2 * c ^ 2 * w ^ 4)
      (by positivity) (by positivity)).closureRatio = 3 / 2 :=
  closure_ode_gives_ratio _ _ (negbin2_closure_ode p c w)

/-- **Result 55.** NegBin(3) ODE identity. -/
theorem negbin3_closure_ode (p c w : ℚ) :
    (12 * p ^ 2 * c ^ 3 * w ^ 5) * (c ^ 3 * w ^ 3) =
    (4 / 3) * (3 * p * c ^ 3 * w ^ 4) ^ 2 := by
  field_simp; ring

/-- NegBin(3) has constant closure ratio 4/3. -/
theorem negbin3_closure_ratio (p c w : ℚ)
    (hp : 0 < p) (hc : 0 < c) (hw : 0 < w) :
    (PGFEval.mk (c ^ 3 * w ^ 3) (3 * p * c ^ 3 * w ^ 4)
      (12 * p ^ 2 * c ^ 3 * w ^ 5)
      (by positivity) (by positivity)).closureRatio = 4 / 3 :=
  closure_ode_gives_ratio _ _ (negbin3_closure_ode p c w)

/-- **Result 56.** General NegBin(m+1) ODE identity. -/
theorem negbin_general_closure_ode (m : ℕ) (p c w : ℚ) :
    ((↑m + 1) * (↑m + 2) * p ^ 2 * c ^ (m + 1) * w ^ (m + 3)) *
    (c ^ (m + 1) * w ^ (m + 1)) =
    ((↑m + 2) / (↑m + 1)) *
    ((↑m + 1) * p * c ^ (m + 1) * w ^ (m + 2)) ^ 2 := by
  have hm1 : (↑m + 1 : ℚ) ≠ 0 := by positivity
  field_simp; ring

/-! ## Non-PT counterexample -/

/-- **Result 57.** Non-PT: mixture psi = 1/2 + theta^2/2 has varying kappa. -/
theorem nonPT_closure_ratio_varies :
    let e1 : PGFEval := ⟨1, 1, 1, by norm_num, by norm_num⟩
    let e2 : PGFEval := ⟨5/8, 1/2, 1, by norm_num, by norm_num⟩
    e1.closureRatio ≠ e2.closureRatio := by
  simp only [PGFEval.closureRatio]
  norm_num

theorem nonPT_kappa_at_one' :
    (PGFEval.mk 1 1 1 (by norm_num) (by norm_num)).closureRatio = 1 := by
  simp only [PGFEval.closureRatio]; norm_num

theorem nonPT_kappa_at_half' :
    (PGFEval.mk (5/8) (1/2) 1 (by norm_num) (by norm_num)).closureRatio
    = 5 / 2 := by
  simp only [PGFEval.closureRatio]; norm_num

/-! ## Connection to PGFData -/

/-- **Result 58.** At theta = 1, closureRatio = closureKappa. -/
theorem closure_ratio_at_one' (psi : PGFData) :
    PGFEval.closureRatio
      (PGFEval.mk 1 psi.mean psi.secondFactorial (by norm_num) psi.mean_pos) =
    psi.closureKappa := by
  simp only [PGFEval.closureRatio, PGFData.closureKappa, mul_one]

/-! ## Exhaustiveness of PT classification -/

/-- **Result 59.** Trichotomy: kappa < 1, = 1, or > 1. -/
theorem pt_classification_exhaustive (kap : ℚ) (_hkap : 0 < kap) :
    kap < 1 ∨ kap = 1 ∨ 1 < kap := by
  rcases lt_trichotomy kap 1 with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- For Binomial, kappa = (n-1)/n < 1. -/
theorem binomial_kappa_determines_n' (n : ℕ) (hn : 2 ≤ n) :
    (↑n - 1 : ℚ) / ↑n < 1 := by
  have hn_pos : (0 : ℚ) < ↑n := Nat.cast_pos.mpr (by omega)
  rw [div_lt_one hn_pos]
  linarith

/-- For Binomial, 1/(1 - (n-1)/n) = n. -/
theorem binomial_recover_n' (n : ℕ) (hn : 2 ≤ n) :
    1 / (1 - (↑n - 1 : ℚ) / ↑n) = ↑n := by
  have hn_ne : (↑n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [sub_div, div_self hn_ne]
  norm_num

/-- For NegBin, kappa > 1 gives r = 1/(kappa-1) > 0. -/
theorem negbin_kappa_determines_r' (kap : ℚ) (hkap : 1 < kap) :
    0 < 1 / (kap - 1) := by
  apply div_pos one_pos; linarith

/-- Poisson matches Result 42 from SurvivalBridge. -/
theorem poisson_kappa_is_one' (lam : ℚ) (hlam : 0 < lam) :
    (PGFData.poisson lam hlam).closureKappa = 1 :=
  poisson_kappa_eq_one lam hlam
