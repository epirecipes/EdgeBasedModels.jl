import Alignment.Registry
import EBCMCategory.ClosureTheorem
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Blind shadow sets: group `ClosureTheorem`

Written blind, from the claim texts in `Alignment/claims_blind.yaml`, `Alignment/DataTypes/ClosureTheorem.md`,
`Alignment/README.md` and `Alignment/Example/ExampleShadows.lean` only (plus background on
Poisson-type (PT) degree distributions from the paper `papers/1703.06328v3.md`, §5.2).

Vocabulary used:
* `PGFEval` ("a PGF evaluated at a point θ, carrying its first two derivatives") and
  `PGFEval.closureRatio` ("the closure ratio κ(θ) = ψ''ψ/ψ'²");
* `PGFData` (ψ'(1) = `mean`, ψ''(1) = `secondFactorial`), `PGFData.closureKappa`
  ("κ = ψ''(1)ψ(1)/ψ'(1)²") and `PGFData.poisson`.

Family PGFs (DataTypes §(c)): Poisson(λ) ψ(θ) = e^{λ(θ−1)}; Binomial(N, p) ψ(θ) = (1 − p + pθ)^N;
NegBin(r, c) ψ(θ) = (c/(1 − (1 − c)θ))^r; mixture ψ(θ) = 1/2 + θ²/2.

Two readings recur (AMBIGUITY, both kept as separate shadows for the Result-level claims):
* **algebraic**: ψ, ψ', ψ'' at θ are the closed-form (textbook) derivative expressions of the
  family's PGF, and the identity is an identity of rationals ("We verify the closure ODE …
  algebraically", module header);
* **analytic** (VOCAB-GAP): ψ is the family's PGF as a real function and ψ', ψ'' are its actual
  derivatives (`deriv`). `PGFEval` cannot express this: nothing ties `ψ'`/`ψ''` to derivatives.

Domains (text: Binomial/NegBin/Poisson *distributions*, PGF argument θ ∈ [0,1]): λ > 0;
0 ≤ p ≤ 1; 0 < c < 1; 0 ≤ θ ≤ 1. Over ℚ the Poisson value ψ(θ) = e^{λ(θ−1)} is written as a free
positive number `E` (it takes every positive value as θ ranges over ℝ). Where a closure *ratio* is
taken, the point must have ψ > 0 and ψ' > 0 (the `PGFEval` invariants), resp. ψ'(θ) ≠ 0.

Re-authored blind (second pass, from the current claim texts, `DataTypes/*.md`, the README,
`SA-PASS_SKILL.md`, `Example/ExampleShadows.lean` and background papers only): the blocks marked
"(re-authored blind)" or "(blind)" near the end of this file (with any `Shared2` helper
namespace). Ids of that pass not formalised (remarks on proof status, on which notions the library
defines, or cited results needing models the vocabulary lacks): `header.paperProofCorrect`,
`header.sorryFree`.
-/

namespace Alignment.Shadows.ClosureTheorem

/-! ## Shared helpers: closed forms over ℚ (algebraic reading) -/

/-- Binomial(n+2, p) PGF at θ: ψ(θ) = (1 − p + pθ)^(n+2). -/
def bPsi (n : ℕ) (p θ : ℚ) : ℚ := (1 - p + p * θ) ^ (n + 2)
/-- Binomial(n+2, p): ψ'(θ) = (n+2)·p·(1 − p + pθ)^(n+1). -/
def bPsi1 (n : ℕ) (p θ : ℚ) : ℚ := ((n : ℚ) + 2) * p * (1 - p + p * θ) ^ (n + 1)
/-- Binomial(n+2, p): ψ''(θ) = (n+2)(n+1)·p²·(1 − p + pθ)^n. -/
def bPsi2 (n : ℕ) (p θ : ℚ) : ℚ := ((n : ℚ) + 2) * ((n : ℚ) + 1) * p ^ 2 * (1 - p + p * θ) ^ n

/-- NegBin(2, c) PGF at θ: ψ(θ) = (c/(1 − (1 − c)θ))². -/
def nb2Psi (c θ : ℚ) : ℚ := (c / (1 - (1 - c) * θ)) ^ 2
/-- NegBin(2, c): ψ'(θ) = 2(1 − c)c²/(1 − (1 − c)θ)³. -/
def nb2Psi1 (c θ : ℚ) : ℚ := 2 * (1 - c) * c ^ 2 / (1 - (1 - c) * θ) ^ 3
/-- NegBin(2, c): ψ''(θ) = 6(1 − c)²c²/(1 − (1 − c)θ)⁴. -/
def nb2Psi2 (c θ : ℚ) : ℚ := 6 * (1 - c) ^ 2 * c ^ 2 / (1 - (1 - c) * θ) ^ 4

/-- NegBin(3, c) PGF at θ: ψ(θ) = (c/(1 − (1 − c)θ))³. -/
def nb3Psi (c θ : ℚ) : ℚ := (c / (1 - (1 - c) * θ)) ^ 3
/-- NegBin(3, c): ψ'(θ) = 3(1 − c)c³/(1 − (1 − c)θ)⁴. -/
def nb3Psi1 (c θ : ℚ) : ℚ := 3 * (1 - c) * c ^ 3 / (1 - (1 - c) * θ) ^ 4
/-- NegBin(3, c): ψ''(θ) = 12(1 − c)²c³/(1 − (1 − c)θ)⁵. -/
def nb3Psi2 (c θ : ℚ) : ℚ := 12 * (1 - c) ^ 2 * c ^ 3 / (1 - (1 - c) * θ) ^ 5

/-- NegBin(m+1, c) PGF at θ: ψ(θ) = (c/(1 − (1 − c)θ))^(m+1). -/
def nbmPsi (m : ℕ) (c θ : ℚ) : ℚ := (c / (1 - (1 - c) * θ)) ^ (m + 1)
/-- NegBin(m+1, c): ψ'(θ) = (m+1)(1 − c)c^(m+1)/(1 − (1 − c)θ)^(m+2). -/
def nbmPsi1 (m : ℕ) (c θ : ℚ) : ℚ :=
  ((m : ℚ) + 1) * (1 - c) * c ^ (m + 1) / (1 - (1 - c) * θ) ^ (m + 2)
/-- NegBin(m+1, c): ψ''(θ) = (m+1)(m+2)(1 − c)²c^(m+1)/(1 − (1 − c)θ)^(m+3). -/
def nbmPsi2 (m : ℕ) (c θ : ℚ) : ℚ :=
  ((m : ℚ) + 1) * ((m : ℚ) + 2) * (1 - c) ^ 2 * c ^ (m + 1) / (1 - (1 - c) * θ) ^ (m + 3)

/-- PGF of a finitely supported degree distribution with weights `w k` on k < N, at θ:
ψ(θ) = ∑ w_k θ^k. -/
def fPsi (N : ℕ) (w : ℕ → ℚ) (θ : ℚ) : ℚ := ∑ k ∈ Finset.range N, w k * θ ^ k
/-- Its exact (termwise) first derivative: ψ'(θ) = ∑ k w_k θ^(k−1). -/
def fPsi1 (N : ℕ) (w : ℕ → ℚ) (θ : ℚ) : ℚ := ∑ k ∈ Finset.range N, (k : ℚ) * w k * θ ^ (k - 1)
/-- Its exact (termwise) second derivative: ψ''(θ) = ∑ k(k−1) w_k θ^(k−2). -/
def fPsi2 (N : ℕ) (w : ℕ → ℚ) (θ : ℚ) : ℚ :=
  ∑ k ∈ Finset.range N, (k : ℚ) * ((k : ℚ) - 1) * w k * θ ^ (k - 2)

/-! ## Shared helpers: real PGFs and derivatives (analytic reading, VOCAB-GAP) -/

-- VOCAB-GAP: `PGFData`/`PGFEval` hold numbers only; the PGF as a function and its derivatives
-- are stated with `Real.exp` and `deriv`.

/-- Poisson(λ) PGF as a real function: ψ(t) = e^{λ(t−1)}. -/
noncomputable def poisR (lam : ℝ) : ℝ → ℝ := fun t => Real.exp (lam * (t - 1))
/-- Binomial(n+2, p) PGF as a real function: ψ(t) = (1 − p + pt)^(n+2). -/
def binR (n : ℕ) (p : ℝ) : ℝ → ℝ := fun t => (1 - p + p * t) ^ (n + 2)
/-- NegBin(r, c) PGF as a real function (integer r): ψ(t) = (c/(1 − (1 − c)t))^r. -/
noncomputable def nbR (r : ℕ) (c : ℝ) : ℝ → ℝ := fun t => (c / (1 - (1 - c) * t)) ^ r
/-- The non-PT mixture PGF ψ(t) = 1/2 + t²/2 as a real function. -/
noncomputable def mixR : ℝ → ℝ := fun t => 1 / 2 + t ^ 2 / 2

/-- The closure ODE ψ''ψ = κ(ψ')² at θ, with the actual derivatives of ψ. -/
def odeR (ψ : ℝ → ℝ) (κ θ : ℝ) : Prop := deriv (deriv ψ) θ * ψ θ = κ * deriv ψ θ ^ 2

/-- The closure ratio κ(θ) = ψ''(θ)ψ(θ)/ψ'(θ)² with the actual derivatives of ψ. -/
noncomputable def ratioR (ψ : ℝ → ℝ) (θ : ℝ) : ℝ := deriv (deriv ψ) θ * ψ θ / deriv ψ θ ^ 2

/-! ## Shared statements -/

/-- Poisson closure ODE, algebraic: with E = ψ(θ) > 0, ψ' = λE, ψ'' = λ²E, ψ''ψ = 1·(ψ')². -/
def poisODEalg : Prop :=
  ∀ lam E : ℚ, 0 < lam → 0 < E → (lam ^ 2 * E) * E = 1 * (lam * E) ^ 2

/-- Poisson closure ODE, analytic: the Poisson PGF satisfies ψ''ψ = 1·(ψ')² at every θ ∈ [0,1]. -/
def poisODEan : Prop :=
  ∀ lam : ℝ, 0 < lam → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → odeR (poisR lam) 1 θ

/-- Binomial(n+2, p) closure ODE, algebraic: ψ''ψ = ((n+1)/(n+2))(ψ')² at every θ ∈ [0,1]. -/
def binODEalg : Prop :=
  ∀ (n : ℕ) (p θ : ℚ), 0 ≤ p → p ≤ 1 → 0 ≤ θ → θ ≤ 1 →
    bPsi2 n p θ * bPsi n p θ = ((n : ℚ) + 1) / ((n : ℚ) + 2) * bPsi1 n p θ ^ 2

/-- Binomial(n+2, p) closure ODE, analytic. -/
def binODEan : Prop :=
  ∀ (n : ℕ) (p : ℝ), 0 ≤ p → p ≤ 1 → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
    odeR (binR n p) (((n : ℝ) + 1) / ((n : ℝ) + 2)) θ

/-- NegBin(2) closure ODE, algebraic: ψ''ψ = (3/2)(ψ')² at every θ ∈ [0,1]. -/
def nb2ODEalg : Prop :=
  ∀ c θ : ℚ, 0 < c → c < 1 → 0 ≤ θ → θ ≤ 1 →
    nb2Psi2 c θ * nb2Psi c θ = 3 / 2 * nb2Psi1 c θ ^ 2

/-- NegBin(2) closure ODE, analytic. -/
def nb2ODEan : Prop :=
  ∀ c : ℝ, 0 < c → c < 1 → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → odeR (nbR 2 c) (3 / 2) θ

/-- NegBin(3) closure ODE, algebraic: ψ''ψ = (4/3)(ψ')² at every θ ∈ [0,1]. -/
def nb3ODEalg : Prop :=
  ∀ c θ : ℚ, 0 < c → c < 1 → 0 ≤ θ → θ ≤ 1 →
    nb3Psi2 c θ * nb3Psi c θ = 4 / 3 * nb3Psi1 c θ ^ 2

/-- NegBin(3) closure ODE, analytic. -/
def nb3ODEan : Prop :=
  ∀ c : ℝ, 0 < c → c < 1 → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → odeR (nbR 3 c) (4 / 3) θ

/-- General NegBin(m+1) closure ODE, algebraic: ψ''ψ = ((m+2)/(m+1))(ψ')², every m, θ ∈ [0,1]. -/
def nbmODEalg : Prop :=
  ∀ (m : ℕ) (c θ : ℚ), 0 < c → c < 1 → 0 ≤ θ → θ ≤ 1 →
    nbmPsi2 m c θ * nbmPsi m c θ = ((m : ℚ) + 2) / ((m : ℚ) + 1) * nbmPsi1 m c θ ^ 2

/-- General NegBin(m+1) closure ODE, analytic. -/
def nbmODEan : Prop :=
  ∀ (m : ℕ) (c : ℝ), 0 < c → c < 1 → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
    odeR (nbR (m + 1) c) (((m : ℝ) + 2) / ((m : ℝ) + 1)) θ

/-- Existence of a non-PT degree distribution (finitely supported, weights ≥ 0 summing to 1)
whose closure ratio takes two different values at two points θ₁, θ₂ ∈ [0,1]. -/
def nonPTexists : Prop :=
  ∃ (N : ℕ) (w : ℕ → ℚ), (∀ k, 0 ≤ w k) ∧ (∑ k ∈ Finset.range N, w k) = 1 ∧
    ∃ (θ₁ θ₂ : ℚ) (h₁ : 0 < fPsi N w θ₁) (h₁' : 0 < fPsi1 N w θ₁)
      (h₂ : 0 < fPsi N w θ₂) (h₂' : 0 < fPsi1 N w θ₂),
      0 ≤ θ₁ ∧ θ₁ ≤ 1 ∧ 0 ≤ θ₂ ∧ θ₂ ≤ 1 ∧
      PGFEval.closureRatio ⟨fPsi N w θ₁, fPsi1 N w θ₁, fPsi2 N w θ₁, h₁, h₁'⟩ ≠
        PGFEval.closureRatio ⟨fPsi N w θ₂, fPsi1 N w θ₂, fPsi2 N w θ₂, h₂, h₂'⟩

/-- At θ = 1 (ψ(1) = 1, ψ'(1) = mean, ψ''(1) = secondFactorial) the closure ratio is the
closure parameter `closureKappa`. -/
def ratioAtOne : Prop :=
  ∀ ψ : PGFData,
    PGFEval.closureRatio ⟨1, ψ.mean, ψ.secondFactorial, one_pos, ψ.mean_pos⟩ =
      PGFData.closureKappa ψ

end Alignment.Shadows.ClosureTheorem

/-! ## `ClosureTheorem.table.R52`

Text: "| 52 | Poisson closure ODE: kappa = 1 at every theta |"
-- AMBIGUITY: ψ, ψ', ψ'' read (a) algebraically (closed forms, S1) and (b) analytically (actual
-- derivatives of e^{λ(θ−1)}, S2; VOCAB-GAP). Both required. -/
namespace Alignment.Shadows.ClosureTheorem.table_R52
open Alignment.Shadows.ClosureTheorem

@[sa_reference "ClosureTheorem.table.R52"] def T : Prop := poisODEalg ∧ poisODEan
@[sa_shadow "ClosureTheorem.table.R52" 1] def S1 : Prop := poisODEalg
@[sa_shadow "ClosureTheorem.table.R52" 2] def S2 : Prop := poisODEan
@[sa_ref_forward "ClosureTheorem.table.R52" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "ClosureTheorem.table.R52" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "ClosureTheorem.table.R52"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.ClosureTheorem.table_R52

/-! ## `ClosureTheorem.table.R53`

Text: "| 53 | Binomial(n+2) closure ODE: kappa = (n+1)/(n+2) |"
-- AMBIGUITY: algebraic (S1) vs analytic (S2, VOCAB-GAP) reading of ψ', ψ''. Both required.
-- The row does not say "at every theta"; read as at every θ ∈ [0,1] (row 52/54 style). -/
namespace Alignment.Shadows.ClosureTheorem.table_R53
open Alignment.Shadows.ClosureTheorem

@[sa_reference "ClosureTheorem.table.R53"] def T : Prop := binODEalg ∧ binODEan
@[sa_shadow "ClosureTheorem.table.R53" 1] def S1 : Prop := binODEalg
@[sa_shadow "ClosureTheorem.table.R53" 2] def S2 : Prop := binODEan
@[sa_ref_forward "ClosureTheorem.table.R53" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "ClosureTheorem.table.R53" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "ClosureTheorem.table.R53"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.ClosureTheorem.table_R53

/-! ## `ClosureTheorem.table.R54`

Text: "| 54 | NegBin(2) closure ODE: kappa = 3/2 at every theta |"
-- AMBIGUITY: algebraic (S1) vs analytic (S2, VOCAB-GAP). Both required. -/
namespace Alignment.Shadows.ClosureTheorem.table_R54
open Alignment.Shadows.ClosureTheorem

@[sa_reference "ClosureTheorem.table.R54"] def T : Prop := nb2ODEalg ∧ nb2ODEan
@[sa_shadow "ClosureTheorem.table.R54" 1] def S1 : Prop := nb2ODEalg
@[sa_shadow "ClosureTheorem.table.R54" 2] def S2 : Prop := nb2ODEan
@[sa_ref_forward "ClosureTheorem.table.R54" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "ClosureTheorem.table.R54" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "ClosureTheorem.table.R54"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.ClosureTheorem.table_R54

/-! ## `ClosureTheorem.table.R55`

Text: "| 55 | NegBin(3) closure ODE: kappa = 4/3 at every theta |"
-- AMBIGUITY: algebraic (S1) vs analytic (S2, VOCAB-GAP). Both required. -/
namespace Alignment.Shadows.ClosureTheorem.table_R55
open Alignment.Shadows.ClosureTheorem

@[sa_reference "ClosureTheorem.table.R55"] def T : Prop := nb3ODEalg ∧ nb3ODEan
@[sa_shadow "ClosureTheorem.table.R55" 1] def S1 : Prop := nb3ODEalg
@[sa_shadow "ClosureTheorem.table.R55" 2] def S2 : Prop := nb3ODEan
@[sa_ref_forward "ClosureTheorem.table.R55" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "ClosureTheorem.table.R55" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "ClosureTheorem.table.R55"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.ClosureTheorem.table_R55

/-! ## `ClosureTheorem.table.R56`

Text: "| 56 | General NegBin ODE algebraic identity |"
"algebraic" is explicit: only the algebraic reading.
-- AMBIGUITY: "General NegBin" read as NegBin(r) for every positive integer r = m+1 (as in
-- Result 56 "General NegBin(m+1)"), with κ = (m+2)/(m+1). -/
namespace Alignment.Shadows.ClosureTheorem.table_R56
open Alignment.Shadows.ClosureTheorem

@[sa_reference "ClosureTheorem.table.R56"] def T : Prop := nbmODEalg
@[sa_shadow "ClosureTheorem.table.R56" 1] def S1 : Prop := nbmODEalg
@[sa_ref_forward "ClosureTheorem.table.R56" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "ClosureTheorem.table.R56"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.ClosureTheorem.table_R56

/-! ## `ClosureTheorem.table.R57`

Text: "| 57 | Non-PT counterexample: kappa varies with theta |"
-- AMBIGUITY: the row names no distribution; read existentially (some degree distribution whose
-- closure ratio takes different values at two θ ∈ [0,1]). ψ', ψ'' are the exact termwise
-- derivatives of the polynomial PGF, so no analytic variant is needed. -/
namespace Alignment.Shadows.ClosureTheorem.table_R57
open Alignment.Shadows.ClosureTheorem

@[sa_reference "ClosureTheorem.table.R57"] def T : Prop := nonPTexists
@[sa_shadow "ClosureTheorem.table.R57" 1] def S1 : Prop := nonPTexists
@[sa_ref_forward "ClosureTheorem.table.R57" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "ClosureTheorem.table.R57"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.ClosureTheorem.table_R57

/-! ## `ClosureTheorem.table.R58`

Text: "| 58 | Connection: closureRatio at theta=1 = closureKappa |"
A PGF at θ = 1 has ψ(1) = 1, ψ'(1) = `mean`, ψ''(1) = `secondFactorial`. -/
namespace Alignment.Shadows.ClosureTheorem.table_R58
open Alignment.Shadows.ClosureTheorem

@[sa_reference "ClosureTheorem.table.R58"] def T : Prop := ratioAtOne
@[sa_shadow "ClosureTheorem.table.R58" 1] def S1 : Prop := ratioAtOne
@[sa_ref_forward "ClosureTheorem.table.R58" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "ClosureTheorem.table.R58"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.ClosureTheorem.table_R58

/-! ## `ClosureTheorem.R51`

Text: "**Result 51.** If psi'' psi = kappa (psi')^2 at a point, then the closure ratio equals kappa
at that point."
A PGF evaluated at a point is a `PGFEval`; the closure ratio is `PGFEval.closureRatio`. -/
namespace Alignment.Shadows.ClosureTheorem.R51

@[sa_reference "ClosureTheorem.R51"]
def T : Prop := ∀ (e : PGFEval) (κ : ℚ), e.ψ'' * e.ψ = κ * e.ψ' ^ 2 → e.closureRatio = κ
@[sa_shadow "ClosureTheorem.R51" 1]
def S1 : Prop := ∀ (e : PGFEval) (κ : ℚ), e.ψ'' * e.ψ = κ * e.ψ' ^ 2 → e.closureRatio = κ
@[sa_ref_forward "ClosureTheorem.R51" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "ClosureTheorem.R51"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.ClosureTheorem.R51

/-! ## `ClosureTheorem.R52`

Text: "**Result 52.** Poisson ODE identity."
-- AMBIGUITY: κ is not stated; read as the closure ODE ψ''ψ = κ(ψ')² with κ = 1 at every θ (header
-- table row 52). ψ', ψ'' read algebraically (S1) and analytically (S2, VOCAB-GAP). -/
namespace Alignment.Shadows.ClosureTheorem.R52
open Alignment.Shadows.ClosureTheorem

@[sa_reference "ClosureTheorem.R52"] def T : Prop := poisODEalg ∧ poisODEan
@[sa_shadow "ClosureTheorem.R52" 1] def S1 : Prop := poisODEalg
@[sa_shadow "ClosureTheorem.R52" 2] def S2 : Prop := poisODEan
@[sa_ref_forward "ClosureTheorem.R52" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "ClosureTheorem.R52" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "ClosureTheorem.R52"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.ClosureTheorem.R52

/-! ## `ClosureTheorem.poissonClosureRatio`

Text: "Poisson has constant closure ratio kappa = 1."
"constant" = the same value 1 at every θ.
-- AMBIGUITY: algebraic (S1: `closureRatio` of the Poisson closed forms at every valid point) vs
-- analytic (S2, VOCAB-GAP: ψ''ψ/ψ'² of e^{λ(θ−1)} at every θ ∈ [0,1]). Both required. -/
namespace Alignment.Shadows.ClosureTheorem.poissonClosureRatio
open Alignment.Shadows.ClosureTheorem

/-- Algebraic: E = ψ(θ) = e^{λ(θ−1)} > 0, ψ' = λE, ψ'' = λ²E. -/
def ratioAlg : Prop :=
  ∀ lam E : ℚ, 0 < lam → ∀ (hψ : 0 < E) (hψ' : 0 < lam * E),
    PGFEval.closureRatio ⟨E, lam * E, lam ^ 2 * E, hψ, hψ'⟩ = 1
/-- Analytic (VOCAB-GAP). -/
def ratioAn : Prop :=
  ∀ lam : ℝ, 0 < lam → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ratioR (poisR lam) θ = 1

@[sa_reference "ClosureTheorem.poissonClosureRatio"] def T : Prop := ratioAlg ∧ ratioAn
@[sa_shadow "ClosureTheorem.poissonClosureRatio" 1] def S1 : Prop := ratioAlg
@[sa_shadow "ClosureTheorem.poissonClosureRatio" 2] def S2 : Prop := ratioAn
@[sa_ref_forward "ClosureTheorem.poissonClosureRatio" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "ClosureTheorem.poissonClosureRatio" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "ClosureTheorem.poissonClosureRatio"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.ClosureTheorem.poissonClosureRatio

/-! ## `ClosureTheorem.R53`

Text: "**Result 53.** Binomial ODE identity, general in n."
-- AMBIGUITY: κ and the parametrisation are not stated; read as the header table row 53:
-- Binomial(n+2, p) satisfies ψ''ψ = ((n+1)/(n+2))(ψ')² at every θ, for every n ∈ ℕ ("general in
-- n"); the degenerate trial counts 0 and 1 are not required. ψ', ψ'' algebraic (S1) and analytic
-- (S2, VOCAB-GAP). -/
namespace Alignment.Shadows.ClosureTheorem.R53
open Alignment.Shadows.ClosureTheorem

@[sa_reference "ClosureTheorem.R53"] def T : Prop := binODEalg ∧ binODEan
@[sa_shadow "ClosureTheorem.R53" 1] def S1 : Prop := binODEalg
@[sa_shadow "ClosureTheorem.R53" 2] def S2 : Prop := binODEan
@[sa_ref_forward "ClosureTheorem.R53" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "ClosureTheorem.R53" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "ClosureTheorem.R53"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.ClosureTheorem.R53

/-! ## `ClosureTheorem.binomialClosureRatio`

Text: "Binomial(n+2, p) has constant closure ratio (n+1)/(n+2)."
-- AMBIGUITY: algebraic (S1) vs analytic (S2, VOCAB-GAP). Both required. The ratio is only
-- required where it is defined (ψ > 0, ψ' > 0, resp. ψ'(θ) ≠ 0). -/
namespace Alignment.Shadows.ClosureTheorem.binomialClosureRatio
open Alignment.Shadows.ClosureTheorem

/-- Algebraic: closure ratio of the Binomial(n+2, p) closed forms at θ ∈ [0,1]. -/
def ratioAlg : Prop :=
  ∀ (n : ℕ) (p θ : ℚ), 0 ≤ p → p ≤ 1 → 0 ≤ θ → θ ≤ 1 →
    ∀ (hψ : 0 < bPsi n p θ) (hψ' : 0 < bPsi1 n p θ),
      PGFEval.closureRatio ⟨bPsi n p θ, bPsi1 n p θ, bPsi2 n p θ, hψ, hψ'⟩ =
        ((n : ℚ) + 1) / ((n : ℚ) + 2)
/-- Analytic (VOCAB-GAP). -/
def ratioAn : Prop :=
  ∀ (n : ℕ) (p : ℝ), 0 ≤ p → p ≤ 1 → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → deriv (binR n p) θ ≠ 0 →
    ratioR (binR n p) θ = ((n : ℝ) + 1) / ((n : ℝ) + 2)

@[sa_reference "ClosureTheorem.binomialClosureRatio"] def T : Prop := ratioAlg ∧ ratioAn
@[sa_shadow "ClosureTheorem.binomialClosureRatio" 1] def S1 : Prop := ratioAlg
@[sa_shadow "ClosureTheorem.binomialClosureRatio" 2] def S2 : Prop := ratioAn
@[sa_ref_forward "ClosureTheorem.binomialClosureRatio" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "ClosureTheorem.binomialClosureRatio" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "ClosureTheorem.binomialClosureRatio"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.ClosureTheorem.binomialClosureRatio

/-! ## `ClosureTheorem.R54`

Text: "**Result 54.** NegBin(2) ODE identity."
-- AMBIGUITY: κ not stated; read as κ = 3/2 at every θ (header table row 54). Algebraic (S1) and
-- analytic (S2, VOCAB-GAP) readings. -/
namespace Alignment.Shadows.ClosureTheorem.R54
open Alignment.Shadows.ClosureTheorem

@[sa_reference "ClosureTheorem.R54"] def T : Prop := nb2ODEalg ∧ nb2ODEan
@[sa_shadow "ClosureTheorem.R54" 1] def S1 : Prop := nb2ODEalg
@[sa_shadow "ClosureTheorem.R54" 2] def S2 : Prop := nb2ODEan
@[sa_ref_forward "ClosureTheorem.R54" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "ClosureTheorem.R54" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "ClosureTheorem.R54"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.ClosureTheorem.R54

/-! ## `ClosureTheorem.negbin2ClosureRatio`

Text: "NegBin(2) has constant closure ratio 3/2."
-- AMBIGUITY: algebraic (S1) vs analytic (S2, VOCAB-GAP). Both required. -/
namespace Alignment.Shadows.ClosureTheorem.negbin2ClosureRatio
open Alignment.Shadows.ClosureTheorem

/-- Algebraic: closure ratio of the NegBin(2, c) closed forms at θ ∈ [0,1]. -/
def ratioAlg : Prop :=
  ∀ c θ : ℚ, 0 < c → c < 1 → 0 ≤ θ → θ ≤ 1 →
    ∀ (hψ : 0 < nb2Psi c θ) (hψ' : 0 < nb2Psi1 c θ),
      PGFEval.closureRatio ⟨nb2Psi c θ, nb2Psi1 c θ, nb2Psi2 c θ, hψ, hψ'⟩ = 3 / 2
/-- Analytic (VOCAB-GAP). -/
def ratioAn : Prop :=
  ∀ c : ℝ, 0 < c → c < 1 → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ratioR (nbR 2 c) θ = 3 / 2

@[sa_reference "ClosureTheorem.negbin2ClosureRatio"] def T : Prop := ratioAlg ∧ ratioAn
@[sa_shadow "ClosureTheorem.negbin2ClosureRatio" 1] def S1 : Prop := ratioAlg
@[sa_shadow "ClosureTheorem.negbin2ClosureRatio" 2] def S2 : Prop := ratioAn
@[sa_ref_forward "ClosureTheorem.negbin2ClosureRatio" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "ClosureTheorem.negbin2ClosureRatio" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "ClosureTheorem.negbin2ClosureRatio"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.ClosureTheorem.negbin2ClosureRatio

/-! ## `ClosureTheorem.R55`

Text: "**Result 55.** NegBin(3) ODE identity."
-- AMBIGUITY: κ not stated; read as κ = 4/3 at every θ (header table row 55). Algebraic (S1) and
-- analytic (S2, VOCAB-GAP) readings. -/
namespace Alignment.Shadows.ClosureTheorem.R55
open Alignment.Shadows.ClosureTheorem

@[sa_reference "ClosureTheorem.R55"] def T : Prop := nb3ODEalg ∧ nb3ODEan
@[sa_shadow "ClosureTheorem.R55" 1] def S1 : Prop := nb3ODEalg
@[sa_shadow "ClosureTheorem.R55" 2] def S2 : Prop := nb3ODEan
@[sa_ref_forward "ClosureTheorem.R55" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "ClosureTheorem.R55" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "ClosureTheorem.R55"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.ClosureTheorem.R55

/-! ## `ClosureTheorem.negbin3ClosureRatio`

Text: "NegBin(3) has constant closure ratio 4/3."
-- AMBIGUITY: algebraic (S1) vs analytic (S2, VOCAB-GAP). Both required. -/
namespace Alignment.Shadows.ClosureTheorem.negbin3ClosureRatio
open Alignment.Shadows.ClosureTheorem

/-- Algebraic: closure ratio of the NegBin(3, c) closed forms at θ ∈ [0,1]. -/
def ratioAlg : Prop :=
  ∀ c θ : ℚ, 0 < c → c < 1 → 0 ≤ θ → θ ≤ 1 →
    ∀ (hψ : 0 < nb3Psi c θ) (hψ' : 0 < nb3Psi1 c θ),
      PGFEval.closureRatio ⟨nb3Psi c θ, nb3Psi1 c θ, nb3Psi2 c θ, hψ, hψ'⟩ = 4 / 3
/-- Analytic (VOCAB-GAP). -/
def ratioAn : Prop :=
  ∀ c : ℝ, 0 < c → c < 1 → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ratioR (nbR 3 c) θ = 4 / 3

@[sa_reference "ClosureTheorem.negbin3ClosureRatio"] def T : Prop := ratioAlg ∧ ratioAn
@[sa_shadow "ClosureTheorem.negbin3ClosureRatio" 1] def S1 : Prop := ratioAlg
@[sa_shadow "ClosureTheorem.negbin3ClosureRatio" 2] def S2 : Prop := ratioAn
@[sa_ref_forward "ClosureTheorem.negbin3ClosureRatio" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "ClosureTheorem.negbin3ClosureRatio" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "ClosureTheorem.negbin3ClosureRatio"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.ClosureTheorem.negbin3ClosureRatio

/-! ## `ClosureTheorem.R56`

Text: "**Result 56.** General NegBin(m+1) ODE identity."
-- AMBIGUITY: κ not stated; read as κ = (m+2)/(m+1) (NegBin(r) has κ = (r+1)/r; rows 54-55 are
-- the cases m = 1, 2), for every m ∈ ℕ and every θ. Algebraic (S1) and analytic (S2, VOCAB-GAP)
-- readings. -/
namespace Alignment.Shadows.ClosureTheorem.R56
open Alignment.Shadows.ClosureTheorem

@[sa_reference "ClosureTheorem.R56"] def T : Prop := nbmODEalg ∧ nbmODEan
@[sa_shadow "ClosureTheorem.R56" 1] def S1 : Prop := nbmODEalg
@[sa_shadow "ClosureTheorem.R56" 2] def S2 : Prop := nbmODEan
@[sa_ref_forward "ClosureTheorem.R56" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "ClosureTheorem.R56" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "ClosureTheorem.R56"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.ClosureTheorem.R56

/-! ## `ClosureTheorem.R57`

Text: "**Result 57.** Non-PT: mixture psi = 1/2 + theta^2/2 has varying kappa."
Closed forms: ψ = 1/2 + θ²/2, ψ' = θ, ψ'' = 1, so κ(θ) = (1/2 + θ²/2)/θ² on (0,1].
-- AMBIGUITY: "has varying kappa" read existentially (κ(θ₁) ≠ κ(θ₂) for some θ₁, θ₂ ∈ (0,1]),
-- algebraically (S1) and analytically (S3, VOCAB-GAP); "Non-PT" read as: no constant κ satisfies
-- the closure ODE at every θ ∈ (0,1] (S2). -/
namespace Alignment.Shadows.ClosureTheorem.R57
open Alignment.Shadows.ClosureTheorem

/-- Algebraic: the closure ratio of the mixture takes two different values on (0,1]. -/
def variesAlg : Prop :=
  ∃ (θ₁ θ₂ : ℚ) (h₁ : 0 < 1 / 2 + θ₁ ^ 2 / 2) (h₁' : 0 < θ₁)
    (h₂ : 0 < 1 / 2 + θ₂ ^ 2 / 2) (h₂' : 0 < θ₂),
    θ₁ ≤ 1 ∧ θ₂ ≤ 1 ∧
    PGFEval.closureRatio ⟨1 / 2 + θ₁ ^ 2 / 2, θ₁, 1, h₁, h₁'⟩ ≠
      PGFEval.closureRatio ⟨1 / 2 + θ₂ ^ 2 / 2, θ₂, 1, h₂, h₂'⟩
/-- Algebraic: the mixture is not PT (no constant κ with ψ''ψ = κ(ψ')² on (0,1]). -/
def notPTAlg : Prop :=
  ¬ ∃ κ : ℚ, ∀ θ : ℚ, 0 < θ → θ ≤ 1 → 1 * (1 / 2 + θ ^ 2 / 2) = κ * θ ^ 2
/-- Analytic (VOCAB-GAP): the closure ratio of the real function 1/2 + t²/2 varies on (0,1]. -/
def variesAn : Prop :=
  ∃ θ₁ θ₂ : ℝ, 0 < θ₁ ∧ θ₁ ≤ 1 ∧ 0 < θ₂ ∧ θ₂ ≤ 1 ∧ ratioR mixR θ₁ ≠ ratioR mixR θ₂

@[sa_reference "ClosureTheorem.R57"] def T : Prop := variesAlg ∧ notPTAlg ∧ variesAn
@[sa_shadow "ClosureTheorem.R57" 1] def S1 : Prop := variesAlg
@[sa_shadow "ClosureTheorem.R57" 2] def S2 : Prop := notPTAlg
@[sa_shadow "ClosureTheorem.R57" 3] def S3 : Prop := variesAn
@[sa_ref_forward "ClosureTheorem.R57" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "ClosureTheorem.R57" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "ClosureTheorem.R57" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "ClosureTheorem.R57"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.ClosureTheorem.R57

/-! ## `ClosureTheorem.R58`

Text: "**Result 58.** At theta = 1, closureRatio = closureKappa." -/
namespace Alignment.Shadows.ClosureTheorem.R58
open Alignment.Shadows.ClosureTheorem

@[sa_reference "ClosureTheorem.R58"] def T : Prop := ratioAtOne
@[sa_shadow "ClosureTheorem.R58" 1] def S1 : Prop := ratioAtOne
@[sa_ref_forward "ClosureTheorem.R58" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "ClosureTheorem.R58"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.ClosureTheorem.R58

/-! ## `ClosureTheorem.R59`

Text: "**Result 59.** Trichotomy: kappa < 1, = 1, or > 1."
-- AMBIGUITY: no range for κ is stated here (the header row 59 adds "for kappa > 0"); the text's
-- generality (every κ) is kept. "Trichotomy" read as the disjunction (at least one holds). -/
namespace Alignment.Shadows.ClosureTheorem.R59

@[sa_reference "ClosureTheorem.R59"] def T : Prop := ∀ κ : ℚ, κ < 1 ∨ κ = 1 ∨ 1 < κ
@[sa_shadow "ClosureTheorem.R59" 1] def S1 : Prop := ∀ κ : ℚ, κ < 1 ∨ κ = 1 ∨ 1 < κ
@[sa_ref_forward "ClosureTheorem.R59" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "ClosureTheorem.R59"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.ClosureTheorem.R59

/-! ## `ClosureTheorem.binomialKappaDeterminesN`

Text: "For Binomial, kappa = (n-1)/n < 1."
Binomial(n, p): mean ψ'(1) = np, second factorial moment ψ''(1) = n(n−1)p².
-- AMBIGUITY: "kappa" of a distribution read as its closure parameter `closureKappa` (κ at θ = 1).
-- The chain "κ = (n−1)/n < 1" is split into its two links (S1, S2); n ≥ 1, 0 < p ≤ 1. -/
namespace Alignment.Shadows.ClosureTheorem.binomialKappaDeterminesN

/-- κ of Binomial(n, p) is (n−1)/n. -/
def kappaEq : Prop :=
  ∀ (n : ℕ) (p : ℚ), 0 < p → p ≤ 1 →
    ∀ (hm : 0 < (n : ℚ) * p) (hs : 0 ≤ (n : ℚ) * ((n : ℚ) - 1) * p ^ 2),
      PGFData.closureKappa ⟨(n : ℚ) * p, (n : ℚ) * ((n : ℚ) - 1) * p ^ 2, hm, hs⟩ =
        ((n : ℚ) - 1) / n
/-- (n−1)/n < 1 for every number of trials n ≥ 1. -/
def ltOne : Prop := ∀ n : ℕ, 0 < n → ((n : ℚ) - 1) / n < 1

@[sa_reference "ClosureTheorem.binomialKappaDeterminesN"] def T : Prop := kappaEq ∧ ltOne
@[sa_shadow "ClosureTheorem.binomialKappaDeterminesN" 1] def S1 : Prop := kappaEq
@[sa_shadow "ClosureTheorem.binomialKappaDeterminesN" 2] def S2 : Prop := ltOne
@[sa_ref_forward "ClosureTheorem.binomialKappaDeterminesN" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "ClosureTheorem.binomialKappaDeterminesN" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "ClosureTheorem.binomialKappaDeterminesN"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.ClosureTheorem.binomialKappaDeterminesN

/-! ## `ClosureTheorem.binomialRecoverN`

Text: "For Binomial, 1/(1 - (n-1)/n) = n."
n is the number of trials of a Binomial, so n ≥ 1 (for n = 0 the left side is not n in ℚ). -/
namespace Alignment.Shadows.ClosureTheorem.binomialRecoverN

@[sa_reference "ClosureTheorem.binomialRecoverN"]
def T : Prop := ∀ n : ℕ, 0 < n → 1 / (1 - ((n : ℚ) - 1) / n) = n
@[sa_shadow "ClosureTheorem.binomialRecoverN" 1]
def S1 : Prop := ∀ n : ℕ, 0 < n → 1 / (1 - ((n : ℚ) - 1) / n) = n
@[sa_ref_forward "ClosureTheorem.binomialRecoverN" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "ClosureTheorem.binomialRecoverN"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.ClosureTheorem.binomialRecoverN

/-! ## `ClosureTheorem.negbinKappaDeterminesR`

Text: "For NegBin, kappa > 1 gives r = 1/(kappa-1) > 0."
NegBin(r) has closure constant κ = (r+1)/r (rows 54-56: 3/2, 4/3, (m+2)/(m+1)); r is real, r > 0.
-- AMBIGUITY: "gives r = 1/(κ−1)" read (i) as defining r := 1/(κ−1), whose positivity for κ > 1 is
-- the claim (S1), and (ii) as recovery of the NegBin parameter: if κ = (r+1)/r with r > 0 and
-- κ > 1, then r = 1/(κ−1) (S2). Both required. -/
namespace Alignment.Shadows.ClosureTheorem.negbinKappaDeterminesR

/-- κ > 1 ⇒ 1/(κ−1) > 0. -/
def rPos : Prop := ∀ κ : ℚ, 1 < κ → 0 < 1 / (κ - 1)
/-- The NegBin parameter r is recovered from κ = (r+1)/r as r = 1/(κ−1). -/
def rRecover : Prop := ∀ r κ : ℚ, 0 < r → κ = (r + 1) / r → 1 < κ → r = 1 / (κ - 1)

@[sa_reference "ClosureTheorem.negbinKappaDeterminesR"] def T : Prop := rPos ∧ rRecover
@[sa_shadow "ClosureTheorem.negbinKappaDeterminesR" 1] def S1 : Prop := rPos
@[sa_shadow "ClosureTheorem.negbinKappaDeterminesR" 2] def S2 : Prop := rRecover
@[sa_ref_forward "ClosureTheorem.negbinKappaDeterminesR" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "ClosureTheorem.negbinKappaDeterminesR" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "ClosureTheorem.negbinKappaDeterminesR"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.ClosureTheorem.negbinKappaDeterminesR

/-! ## `ClosureTheorem.poissonKappaIsOne`

Text: "Poisson matches Result 42 from SurvivalBridge."
Result 42 is not visible to the blind author. The checkable part is read as: the Poisson case of
the classification (κ = 1) agrees with the SurvivalBridge closure parameter of the Poisson PGF,
i.e. `closureKappa (PGFData.poisson λ hλ) = 1` for every mean λ > 0.
-- AMBIGUITY: "matches Result 42" read as equality of the Poisson κ with the value 1; the content
-- of Result 42 itself cannot be checked blind. -/
namespace Alignment.Shadows.ClosureTheorem.poissonKappaIsOne

@[sa_reference "ClosureTheorem.poissonKappaIsOne"]
def T : Prop := ∀ (lam : ℚ) (h : 0 < lam), PGFData.closureKappa (PGFData.poisson lam h) = 1
@[sa_shadow "ClosureTheorem.poissonKappaIsOne" 1]
def S1 : Prop := ∀ (lam : ℚ) (h : 0 < lam), PGFData.closureKappa (PGFData.poisson lam h) = 1
@[sa_ref_forward "ClosureTheorem.poissonKappaIsOne" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "ClosureTheorem.poissonKappaIsOne"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.ClosureTheorem.poissonKappaIsOne

noncomputable section

/-! ## `ClosureTheorem.header.verificationStrategy` (re-authored blind)

Text: "We check the sufficiency identities for PT families: for each PT family, the values
psi(theta), psi'(theta), psi''(theta) of its PGF, written as monomials in free scalars, satisfy
psi'' psi = kappa (psi')^2 as ring identities. The necessity direction of KKR Theorem 1 (only PT
laws have constant kappa) is not formalised; we only exhibit one non-PT law,
psi = 1/2 + theta^2/2, whose ratio kappa(theta) takes two different values."

PT families (DataTypes): Poisson(λ) `ψ = e^{λ(θ−1)}`, Binomial(n, p) `ψ = (1 − p + pθ)^n`,
NegBin(r, c) `ψ = (c/(1 − (1 − c)θ))^r`. As monomials in free scalars:
* Poisson, `E = e^{λ(θ−1)}`: `ψ = E`, `ψ' = λE`, `ψ'' = λ²E`, κ = 1;
* Binomial, `u = 1 − p + pθ`: `ψ = uⁿ`, `ψ' = n p uⁿ⁻¹`, `ψ'' = n(n−1)p² uⁿ⁻²`, κ = (n−1)/n;
* NegBin, `w = 1/(1 − (1 − c)θ)`: `ψ = cʳwʳ`, `ψ' = r(1−c)cʳwʳ⁺¹`, `ψ'' = r(r+1)(1−c)²cʳwʳ⁺²`,
  κ = (r+1)/r.
The non-PT law `ψ = 1/2 + θ²/2` has `ψ' = θ`, `ψ'' = 1`; its ratio is `PGFEval.closureRatio` of
these values. The remark that the necessity direction is not formalised is not a proposition. -/
namespace Alignment.Shadows.ClosureTheorem.header_verificationStrategy

/-- The values of the non-PT law `ψ = 1/2 + θ²/2` at `θ > 0`: `(1/2 + θ²/2, θ, 1)`. -/
def mixEval (θ : ℚ) (h : 0 < θ) : PGFEval := ⟨1 / 2 + θ ^ 2 / 2, θ, 1, by positivity, h⟩

-- AMBIGUITY: "kappa" for each family is not given; read as the family constants
-- 1 (Poisson), (n−1)/n (binomial), (r+1)/r (negative binomial), with n, r ≥ 1.
-- AMBIGUITY: "takes two different values" read over θ ∈ (0, 1] (arguments of a PGF).
@[sa_reference "ClosureTheorem.header.verificationStrategy"]
def T : Prop :=
  (∀ lam E : ℚ, (lam ^ 2 * E) * E = 1 * (lam * E) ^ 2) ∧
  (∀ (n : ℕ) (p u : ℚ), 1 ≤ n →
      ((n : ℚ) * ((n : ℚ) - 1) * p ^ 2 * u ^ (n - 2)) * u ^ n =
        (((n : ℚ) - 1) / n) * ((n : ℚ) * p * u ^ (n - 1)) ^ 2) ∧
  (∀ (r : ℕ) (c w : ℚ), 1 ≤ r →
      ((r : ℚ) * ((r : ℚ) + 1) * (1 - c) ^ 2 * c ^ r * w ^ (r + 2)) * (c ^ r * w ^ r) =
        (((r : ℚ) + 1) / r) * ((r : ℚ) * (1 - c) * c ^ r * w ^ (r + 1)) ^ 2) ∧
  (∃ (θ₁ : ℚ) (h₁ : 0 < θ₁) (θ₂ : ℚ) (h₂ : 0 < θ₂), θ₁ ≤ 1 ∧ θ₂ ≤ 1 ∧
      (mixEval θ₁ h₁).closureRatio ≠ (mixEval θ₂ h₂).closureRatio)

/-- S1: Poisson sufficiency identity `ψ''ψ = 1·(ψ')²`. -/
@[sa_shadow "ClosureTheorem.header.verificationStrategy" 1]
def S1 : Prop := ∀ lam E : ℚ, (lam ^ 2 * E) * E = 1 * (lam * E) ^ 2
/-- S2: binomial sufficiency identity `ψ''ψ = ((n−1)/n)·(ψ')²`. -/
@[sa_shadow "ClosureTheorem.header.verificationStrategy" 2]
def S2 : Prop :=
  ∀ (n : ℕ) (p u : ℚ), 1 ≤ n →
    ((n : ℚ) * ((n : ℚ) - 1) * p ^ 2 * u ^ (n - 2)) * u ^ n =
      (((n : ℚ) - 1) / n) * ((n : ℚ) * p * u ^ (n - 1)) ^ 2
/-- S3: negative-binomial sufficiency identity `ψ''ψ = ((r+1)/r)·(ψ')²`. -/
@[sa_shadow "ClosureTheorem.header.verificationStrategy" 3]
def S3 : Prop :=
  ∀ (r : ℕ) (c w : ℚ), 1 ≤ r →
    ((r : ℚ) * ((r : ℚ) + 1) * (1 - c) ^ 2 * c ^ r * w ^ (r + 2)) * (c ^ r * w ^ r) =
      (((r : ℚ) + 1) / r) * ((r : ℚ) * (1 - c) * c ^ r * w ^ (r + 1)) ^ 2
/-- S4: the ratio κ(θ) of the non-PT law `1/2 + θ²/2` takes two different values on (0, 1]. -/
@[sa_shadow "ClosureTheorem.header.verificationStrategy" 4]
def S4 : Prop :=
  ∃ (θ₁ : ℚ) (h₁ : 0 < θ₁) (θ₂ : ℚ) (h₂ : 0 < θ₂), θ₁ ≤ 1 ∧ θ₂ ≤ 1 ∧
    (mixEval θ₁ h₁).closureRatio ≠ (mixEval θ₂ h₂).closureRatio

@[sa_ref_forward "ClosureTheorem.header.verificationStrategy" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t.1
@[sa_ref_forward "ClosureTheorem.header.verificationStrategy" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2.1
@[sa_ref_forward "ClosureTheorem.header.verificationStrategy" 3] theorem ref_fwd3 : T → S3 :=
  fun t => t.2.2.1
@[sa_ref_forward "ClosureTheorem.header.verificationStrategy" 4] theorem ref_fwd4 : T → S4 :=
  fun t => t.2.2.2
@[sa_complete "ClosureTheorem.header.verificationStrategy"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.ClosureTheorem.header_verificationStrategy

/-! ## `ClosureTheorem.table.R59` (re-authored blind)

Text: "| 59 | Trichotomy kappa < 1, = 1, > 1 (not a classification) |"

The text is itself an instance of order trichotomy ("not a classification": it does not say which
laws fall in which case), so no formalisation can be falsified by a value of κ; the shadows only
fix which κ is meant. -/
namespace Alignment.Shadows.ClosureTheorem.table_R59

-- AMBIGUITY: "kappa" may be the closure parameter of a degree distribution
-- (`PGFData.closureKappa`) or the pointwise ratio κ(θ) (`PGFEval.closureRatio`); both required.
@[sa_reference "ClosureTheorem.table.R59"]
def T : Prop :=
  (∀ d : PGFData, d.closureKappa < 1 ∨ d.closureKappa = 1 ∨ 1 < d.closureKappa) ∧
  (∀ e : PGFEval, e.closureRatio < 1 ∨ e.closureRatio = 1 ∨ 1 < e.closureRatio)

/-- S1: trichotomy for the closure parameter of a degree distribution. -/
@[sa_shadow "ClosureTheorem.table.R59" 1]
def S1 : Prop := ∀ d : PGFData, d.closureKappa < 1 ∨ d.closureKappa = 1 ∨ 1 < d.closureKappa
/-- S2: trichotomy for the pointwise closure ratio. -/
@[sa_shadow "ClosureTheorem.table.R59" 2]
def S2 : Prop := ∀ e : PGFEval, e.closureRatio < 1 ∨ e.closureRatio = 1 ∨ 1 < e.closureRatio

@[sa_ref_forward "ClosureTheorem.table.R59" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "ClosureTheorem.table.R59" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "ClosureTheorem.table.R59"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.ClosureTheorem.table_R59

end
