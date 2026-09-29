import Alignment.Registry
import EBCMCategory.DegreeCorrelation
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Blind shadow sets: group `DegreeCorrelation`

Written blind (SA-PASS role 2). The author read only the blind registry entries
(`claims_blind.yaml`, fields `id, group, source, text`), `Alignment/DataTypes/DegreeCorrelation.md`,
`Alignment/README.md`, `Alignment/Example/ExampleShadows.lean` and `SA-PASS_SKILL.md`, and used
`#check` only on the data types and operations listed in the DataTypes file.

Vocabulary (from `DataTypes/DegreeCorrelation.md`):
* `DegreeMomentData` with fields `mean` (⟨k⟩ = ψ'(1)) and `secondMoment` (⟨k²⟩); operations
  `secondFactorial` (⟨k(k-1)⟩), `excessDegree` (⟨k²-k⟩/⟨k⟩) and `uncorrelated_R0 T ψ`
  (R₀ for an uncorrelated network, first argument the transmissibility T).
* `TwoDegreeData` with fields `k1 k2 p1 p2 r`; operations `meanDeg` (⟨k⟩), `q1`, `q2`
  (excess-degree probabilities), `C11 C12 C21 C22` (entries of the 2×2 mixing matrix C),
  `trC`, `detC` (trace, determinant of C) and `secondMom` (⟨k²⟩).

Conventions used throughout:
* The transmissibility is written `Tr` (to avoid clashing with the reference constant `T`).
  The text puts no range on it, so it is quantified over all reals.
* "Neutral mixing" is `d.r = 0`; "full assortativity" is `d.r = 1`.
* The matrix C is `Cmat d = !![d.C11, d.C12; d.C21, d.C22]`; an eigenvalue of C is
  `Module.End.HasEigenvalue (Matrix.toLin' (Cmat d)) μ` (real eigenvalues).
* Where the text spells out a formula for a notion (q_l = l·p_l/⟨k⟩, ⟨k⟩ = k₁p₁ + k₂p₂,
  ⟨k²-k⟩ = ⟨k²⟩ - ⟨k⟩), that formula is part of what the text asserts and gets its own shadow in
  primitive terms, so that a mis-defined operation is caught (via a bridge) rather than hidden.

Re-authored blind (second pass, from the current claim texts, `DataTypes/*.md`, the README,
`SA-PASS_SKILL.md`, `Example/ExampleShadows.lean` and background papers only): the blocks marked
"(re-authored blind)" or "(blind)" near the end of this file (with any `Shared2` helper
namespace).
-/

namespace Alignment.Shadows.DegreeCorrelation

/-- The 2×2 mixing matrix C, assembled from its four entries (operations under test). -/
noncomputable def Cmat (d : TwoDegreeData) : Matrix (Fin 2) (Fin 2) ℝ := !![d.C11, d.C12; d.C21, d.C22]

/-- Poisson probability mass function with mean κ, in primitive terms:
p_k = e^{-κ}·κ^k / k!. -/
noncomputable def poissonPMF (κ : ℝ) (k : ℕ) : ℝ := Real.exp (-κ) * κ ^ k / (k.factorial : ℝ)

end Alignment.Shadows.DegreeCorrelation

/-! ## `DegreeCorrelation.R79-sec` -/

namespace Alignment.Shadows.DegreeCorrelation.R79_sec

/-! Blind text: "The excess-degree probability q_l = l·p_l/⟨k⟩ is a valid distribution."

"Valid distribution" = every entry is nonnegative and the entries sum to 1. A degree
distribution is p : ℕ → ℝ with p_l ≥ 0 and Σ_l p_l = 1; its mean ⟨k⟩ = Σ_l l·p_l is assumed
positive (otherwise q_l is undefined). Sums are Mathlib `HasSum`, so infinite supports
(e.g. Poisson) are included. -/

-- VOCAB-GAP: DataTypes has no general degree distribution p_l (only the two-degree
-- `TwoDegreeData`); the general statement uses `p : ℕ → ℝ` and `HasSum`.
-- AMBIGUITY: "The excess-degree probability q_l = l·p_l/⟨k⟩ is a valid distribution" read
-- (i) for every degree distribution, general degree l (S1, S2: the text's generality), and
-- (ii) for the module's two-degree excess-degree probabilities `TwoDegreeData.q1`, `q2`
-- (the only excess-degree probabilities in the vocabulary; S3-S5). Both are required.

/-- Intended statement: for every degree distribution with positive mean, q_l = l·p_l/⟨k⟩ is
nonnegative and sums to 1; and the two-degree q₁, q₂ are nonnegative and sum to 1. -/
@[sa_reference "DegreeCorrelation.R79-sec"]
def T : Prop :=
  (∀ (p : ℕ → ℝ) (m : ℝ), (∀ l, 0 ≤ p l) → HasSum p 1 →
      HasSum (fun l : ℕ => (l : ℝ) * p l) m → 0 < m →
      (∀ l : ℕ, 0 ≤ (l : ℝ) * p l / m) ∧ HasSum (fun l : ℕ => (l : ℝ) * p l / m) 1) ∧
    (∀ d : TwoDegreeData, 0 ≤ d.q1) ∧ (∀ d : TwoDegreeData, 0 ≤ d.q2) ∧
    (∀ d : TwoDegreeData, d.q1 + d.q2 = 1)

/-- S1: general degree distribution, q_l ≥ 0 for every degree l. -/
@[sa_shadow "DegreeCorrelation.R79-sec" 1]
def S1 : Prop :=
  ∀ (p : ℕ → ℝ) (m : ℝ), (∀ l, 0 ≤ p l) → HasSum p 1 →
    HasSum (fun l : ℕ => (l : ℝ) * p l) m → 0 < m → ∀ l : ℕ, 0 ≤ (l : ℝ) * p l / m

/-- S2: general degree distribution, Σ_l q_l = 1. -/
@[sa_shadow "DegreeCorrelation.R79-sec" 2]
def S2 : Prop :=
  ∀ (p : ℕ → ℝ) (m : ℝ), (∀ l, 0 ≤ p l) → HasSum p 1 →
    HasSum (fun l : ℕ => (l : ℝ) * p l) m → 0 < m → HasSum (fun l : ℕ => (l : ℝ) * p l / m) 1

/-- S3: two-degree network, q₁ ≥ 0. -/
@[sa_shadow "DegreeCorrelation.R79-sec" 3]
def S3 : Prop := ∀ d : TwoDegreeData, 0 ≤ d.q1

/-- S4: two-degree network, q₂ ≥ 0. -/
@[sa_shadow "DegreeCorrelation.R79-sec" 4]
def S4 : Prop := ∀ d : TwoDegreeData, 0 ≤ d.q2

/-- S5: two-degree network, q₁ + q₂ = 1. -/
@[sa_shadow "DegreeCorrelation.R79-sec" 5]
def S5 : Prop := ∀ d : TwoDegreeData, d.q1 + d.q2 = 1

@[sa_ref_forward "DegreeCorrelation.R79-sec" 1]
theorem ref_fwd_1 : T → S1 := fun t p m h0 h1 h2 h3 => (t.1 p m h0 h1 h2 h3).1

@[sa_ref_forward "DegreeCorrelation.R79-sec" 2]
theorem ref_fwd_2 : T → S2 := fun t p m h0 h1 h2 h3 => (t.1 p m h0 h1 h2 h3).2

@[sa_ref_forward "DegreeCorrelation.R79-sec" 3]
theorem ref_fwd_3 : T → S3 := fun t => t.2.1

@[sa_ref_forward "DegreeCorrelation.R79-sec" 4]
theorem ref_fwd_4 : T → S4 := fun t => t.2.2.1

@[sa_ref_forward "DegreeCorrelation.R79-sec" 5]
theorem ref_fwd_5 : T → S5 := fun t => t.2.2.2

@[sa_complete "DegreeCorrelation.R79-sec"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T :=
  ⟨fun p m h0 h1 h2 h3 => ⟨s1 p m h0 h1 h2 h3, s2 p m h0 h1 h2 h3⟩, s3, s4, s5⟩

end Alignment.Shadows.DegreeCorrelation.R79_sec

/-! ## `DegreeCorrelation.R79b` -/

namespace Alignment.Shadows.DegreeCorrelation.R79b

/-! Blind text: "For a two-degree network with degrees k₁, k₂ and fractions p₁, p₂: the
excess-degree probabilities q₁ = k₁·p₁/⟨k⟩ and q₂ = k₂·p₂/⟨k⟩ sum to 1 when
⟨k⟩ = k₁·p₁ + k₂·p₂." -/

-- AMBIGUITY: "q₁ = k₁·p₁/⟨k⟩ and q₂ = k₂·p₂/⟨k⟩ sum to 1 when ⟨k⟩ = k₁·p₁ + k₂·p₂" read
-- (i) as a statement about the module's operations q₁, q₂ (`TwoDegreeData.q1/q2`, S1), and
-- (ii) literally, with the stated formulas and the stated condition on ⟨k⟩ as a hypothesis
-- (S2, primitive terms). Both are required.

/-- Intended statement: q₁ + q₂ = 1 for the operations, and for the explicit formulas whenever
⟨k⟩ = k₁p₁ + k₂p₂. -/
@[sa_reference "DegreeCorrelation.R79b"]
def T : Prop :=
  (∀ d : TwoDegreeData, d.q1 + d.q2 = 1) ∧
    (∀ (d : TwoDegreeData) (m : ℝ), m = d.k1 * d.p1 + d.k2 * d.p2 →
      d.k1 * d.p1 / m + d.k2 * d.p2 / m = 1)

/-- S1: the excess-degree probabilities (operations) sum to 1. -/
@[sa_shadow "DegreeCorrelation.R79b" 1]
def S1 : Prop := ∀ d : TwoDegreeData, d.q1 + d.q2 = 1

/-- S2: the explicit formulas k₁p₁/⟨k⟩ and k₂p₂/⟨k⟩ sum to 1 when ⟨k⟩ = k₁p₁ + k₂p₂. -/
@[sa_shadow "DegreeCorrelation.R79b" 2]
def S2 : Prop :=
  ∀ (d : TwoDegreeData) (m : ℝ), m = d.k1 * d.p1 + d.k2 * d.p2 →
    d.k1 * d.p1 / m + d.k2 * d.p2 / m = 1

@[sa_ref_forward "DegreeCorrelation.R79b" 1]
theorem ref_fwd_1 : T → S1 := fun t => t.1

@[sa_ref_forward "DegreeCorrelation.R79b" 2]
theorem ref_fwd_2 : T → S2 := fun t => t.2

@[sa_complete "DegreeCorrelation.R79b"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.DegreeCorrelation.R79b

/-! ## `DegreeCorrelation.R80-sec` -/

namespace Alignment.Shadows.DegreeCorrelation.R80_sec

/-! Blind text: "For neutral mixing, R₀ = T · ⟨k²-k⟩/⟨k⟩ = T · ψ''(1)/ψ'(1)."

R₀ for neutral (uncorrelated) mixing is the operation `uncorrelated_R0 T ψ`. The chain is split
into its two equalities, each stated against R₀. ⟨k²-k⟩ = ⟨k²⟩ - ⟨k⟩ (linearity of the
expectation) in terms of the fields `secondMoment` and `mean`. -/

-- VOCAB-GAP: `DegreeMomentData` carries no PGF ψ. ψ''(1) is represented by the second
-- factorial moment `secondFactorial` (ψ''(1) = ⟨k(k-1)⟩) and ψ'(1) by the field `mean`.

/-- Intended statement: for every transmissibility and every moment data, R₀ equals
T·(⟨k²⟩-⟨k⟩)/⟨k⟩ and equals T·ψ''(1)/ψ'(1). -/
@[sa_reference "DegreeCorrelation.R80-sec"]
def T : Prop :=
  ∀ (Tr : ℝ) (ψ : DegreeMomentData),
    uncorrelated_R0 Tr ψ = Tr * ((ψ.secondMoment - ψ.mean) / ψ.mean) ∧
      uncorrelated_R0 Tr ψ = Tr * (ψ.secondFactorial / ψ.mean)

/-- S1: R₀ = T · ⟨k²-k⟩/⟨k⟩ in primitive terms. -/
@[sa_shadow "DegreeCorrelation.R80-sec" 1]
def S1 : Prop :=
  ∀ (Tr : ℝ) (ψ : DegreeMomentData),
    uncorrelated_R0 Tr ψ = Tr * ((ψ.secondMoment - ψ.mean) / ψ.mean)

/-- S2: R₀ = T · ψ''(1)/ψ'(1). -/
@[sa_shadow "DegreeCorrelation.R80-sec" 2]
def S2 : Prop :=
  ∀ (Tr : ℝ) (ψ : DegreeMomentData), uncorrelated_R0 Tr ψ = Tr * (ψ.secondFactorial / ψ.mean)

@[sa_ref_forward "DegreeCorrelation.R80-sec" 1]
theorem ref_fwd_1 : T → S1 := fun t Tr ψ => (t Tr ψ).1

@[sa_ref_forward "DegreeCorrelation.R80-sec" 2]
theorem ref_fwd_2 : T → S2 := fun t Tr ψ => (t Tr ψ).2

@[sa_complete "DegreeCorrelation.R80-sec"]
theorem complete (s1 : S1) (s2 : S2) : T := fun Tr ψ => ⟨s1 Tr ψ, s2 Tr ψ⟩

end Alignment.Shadows.DegreeCorrelation.R80_sec

/-! ## `DegreeCorrelation.uncorrelatedR0Formula` -/

namespace Alignment.Shadows.DegreeCorrelation.uncorrelatedR0Formula

/-! Blind text: "R₀ = T·(⟨k²⟩ - ⟨k⟩)/⟨k⟩ is the explicit formula."

R₀ is the uncorrelated R₀ (`uncorrelated_R0`); ⟨k²⟩, ⟨k⟩ are the fields `secondMoment`, `mean`.
A single atomic requirement. -/

/-- Intended statement: for every transmissibility and every moment data,
R₀ = T·(⟨k²⟩ - ⟨k⟩)/⟨k⟩. -/
@[sa_reference "DegreeCorrelation.uncorrelatedR0Formula"]
def T : Prop :=
  ∀ (Tr : ℝ) (ψ : DegreeMomentData),
    uncorrelated_R0 Tr ψ = Tr * (ψ.secondMoment - ψ.mean) / ψ.mean

/-- S1: the whole statement. -/
@[sa_shadow "DegreeCorrelation.uncorrelatedR0Formula" 1]
def S1 : Prop :=
  ∀ (Tr : ℝ) (ψ : DegreeMomentData),
    uncorrelated_R0 Tr ψ = Tr * (ψ.secondMoment - ψ.mean) / ψ.mean

@[sa_ref_forward "DegreeCorrelation.uncorrelatedR0Formula" 1]
theorem ref_fwd_1 : T → S1 := fun t => t

@[sa_complete "DegreeCorrelation.uncorrelatedR0Formula"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DegreeCorrelation.uncorrelatedR0Formula

/-! ## `DegreeCorrelation.meanDegPos` -/

namespace Alignment.Shadows.DegreeCorrelation.meanDegPos

/-! Blind text: "Mean degree is positive." -/

-- AMBIGUITY: "Mean degree" read as the two-degree mean degree `TwoDegreeData.meanDeg`
-- (⟨k⟩ = k₁p₁ + k₂p₂); the positivity of `DegreeMomentData.mean` is a structure field
-- (`mean_pos`), not a claim.

/-- Intended statement: every two-degree network has positive mean degree. -/
@[sa_reference "DegreeCorrelation.meanDegPos"]
def T : Prop := ∀ d : TwoDegreeData, 0 < d.meanDeg

/-- S1: the whole statement. -/
@[sa_shadow "DegreeCorrelation.meanDegPos" 1]
def S1 : Prop := ∀ d : TwoDegreeData, 0 < d.meanDeg

@[sa_ref_forward "DegreeCorrelation.meanDegPos" 1]
theorem ref_fwd_1 : T → S1 := fun t => t

@[sa_complete "DegreeCorrelation.meanDegPos"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DegreeCorrelation.meanDegPos

/-! ## `DegreeCorrelation.R83-sec` -/

namespace Alignment.Shadows.DegreeCorrelation.R83_sec

/-! Blind text: "Setting r = 0 in the mixing matrix gives C_{kl} = k·q_l = k·l·p_l/⟨k⟩, which is
the neutral (uncorrelated) mixing matrix."

For the 2×2 mixing matrix (degree classes k₁, k₂): at r = 0 each entry C_{kl} equals k·q_l
(S1-S4) and equals k·(l·p_l/⟨k⟩) (S5-S8, the formula for q_l substituted; ⟨k⟩ is `meanDeg`).
"which is the neutral mixing matrix" identifies this matrix by name and adds no content. -/

-- VOCAB-GAP: the mixing matrix exists in the vocabulary only for two degree classes
-- (`TwoDegreeData.C11 … C22`); the general C_{kl} is stated for that 2×2 case.

/-- Intended statement: at r = 0, C_{kl} = k·q_l = k·(l·p_l/⟨k⟩) for all four entries. -/
@[sa_reference "DegreeCorrelation.R83-sec"]
def T : Prop :=
  ∀ d : TwoDegreeData, d.r = 0 →
    d.C11 = d.k1 * d.q1 ∧ d.C12 = d.k1 * d.q2 ∧ d.C21 = d.k2 * d.q1 ∧ d.C22 = d.k2 * d.q2 ∧
      d.C11 = d.k1 * (d.k1 * d.p1 / d.meanDeg) ∧ d.C12 = d.k1 * (d.k2 * d.p2 / d.meanDeg) ∧
      d.C21 = d.k2 * (d.k1 * d.p1 / d.meanDeg) ∧ d.C22 = d.k2 * (d.k2 * d.p2 / d.meanDeg)

/-- S1: r = 0 → C₁₁ = k₁·q₁. -/
@[sa_shadow "DegreeCorrelation.R83-sec" 1]
def S1 : Prop := ∀ d : TwoDegreeData, d.r = 0 → d.C11 = d.k1 * d.q1

/-- S2: r = 0 → C₁₂ = k₁·q₂. -/
@[sa_shadow "DegreeCorrelation.R83-sec" 2]
def S2 : Prop := ∀ d : TwoDegreeData, d.r = 0 → d.C12 = d.k1 * d.q2

/-- S3: r = 0 → C₂₁ = k₂·q₁. -/
@[sa_shadow "DegreeCorrelation.R83-sec" 3]
def S3 : Prop := ∀ d : TwoDegreeData, d.r = 0 → d.C21 = d.k2 * d.q1

/-- S4: r = 0 → C₂₂ = k₂·q₂. -/
@[sa_shadow "DegreeCorrelation.R83-sec" 4]
def S4 : Prop := ∀ d : TwoDegreeData, d.r = 0 → d.C22 = d.k2 * d.q2

/-- S5: r = 0 → C₁₁ = k₁·(k₁·p₁/⟨k⟩). -/
@[sa_shadow "DegreeCorrelation.R83-sec" 5]
def S5 : Prop := ∀ d : TwoDegreeData, d.r = 0 → d.C11 = d.k1 * (d.k1 * d.p1 / d.meanDeg)

/-- S6: r = 0 → C₁₂ = k₁·(k₂·p₂/⟨k⟩). -/
@[sa_shadow "DegreeCorrelation.R83-sec" 6]
def S6 : Prop := ∀ d : TwoDegreeData, d.r = 0 → d.C12 = d.k1 * (d.k2 * d.p2 / d.meanDeg)

/-- S7: r = 0 → C₂₁ = k₂·(k₁·p₁/⟨k⟩). -/
@[sa_shadow "DegreeCorrelation.R83-sec" 7]
def S7 : Prop := ∀ d : TwoDegreeData, d.r = 0 → d.C21 = d.k2 * (d.k1 * d.p1 / d.meanDeg)

/-- S8: r = 0 → C₂₂ = k₂·(k₂·p₂/⟨k⟩). -/
@[sa_shadow "DegreeCorrelation.R83-sec" 8]
def S8 : Prop := ∀ d : TwoDegreeData, d.r = 0 → d.C22 = d.k2 * (d.k2 * d.p2 / d.meanDeg)

@[sa_ref_forward "DegreeCorrelation.R83-sec" 1]
theorem ref_fwd_1 : T → S1 := fun t d h => (t d h).1

@[sa_ref_forward "DegreeCorrelation.R83-sec" 2]
theorem ref_fwd_2 : T → S2 := fun t d h => (t d h).2.1

@[sa_ref_forward "DegreeCorrelation.R83-sec" 3]
theorem ref_fwd_3 : T → S3 := fun t d h => (t d h).2.2.1

@[sa_ref_forward "DegreeCorrelation.R83-sec" 4]
theorem ref_fwd_4 : T → S4 := fun t d h => (t d h).2.2.2.1

@[sa_ref_forward "DegreeCorrelation.R83-sec" 5]
theorem ref_fwd_5 : T → S5 := fun t d h => (t d h).2.2.2.2.1

@[sa_ref_forward "DegreeCorrelation.R83-sec" 6]
theorem ref_fwd_6 : T → S6 := fun t d h => (t d h).2.2.2.2.2.1

@[sa_ref_forward "DegreeCorrelation.R83-sec" 7]
theorem ref_fwd_7 : T → S7 := fun t d h => (t d h).2.2.2.2.2.2.1

@[sa_ref_forward "DegreeCorrelation.R83-sec" 8]
theorem ref_fwd_8 : T → S8 := fun t d h => (t d h).2.2.2.2.2.2.2

@[sa_complete "DegreeCorrelation.R83-sec"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) (s7 : S7)
    (s8 : S8) : T :=
  fun d h => ⟨s1 d h, s2 d h, s3 d h, s4 d h, s5 d h, s6 d h, s7 d h, s8 d h⟩

end Alignment.Shadows.DegreeCorrelation.R83_sec

/-! ## `DegreeCorrelation.R83a` … `R83d` -/

namespace Alignment.Shadows.DegreeCorrelation.R83a

/-! Blind text: "**Result 83a.** When r=0, C₁₁ = k₁·q₁ (neutral mixing)." -/

/-- Intended statement: for every two-degree network with r = 0, C₁₁ = k₁·q₁. -/
@[sa_reference "DegreeCorrelation.R83a"]
def T : Prop := ∀ d : TwoDegreeData, d.r = 0 → d.C11 = d.k1 * d.q1

/-- S1: the whole statement. -/
@[sa_shadow "DegreeCorrelation.R83a" 1]
def S1 : Prop := ∀ d : TwoDegreeData, d.r = 0 → d.C11 = d.k1 * d.q1

@[sa_ref_forward "DegreeCorrelation.R83a" 1]
theorem ref_fwd_1 : T → S1 := fun t => t

@[sa_complete "DegreeCorrelation.R83a"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DegreeCorrelation.R83a

namespace Alignment.Shadows.DegreeCorrelation.R83b

/-! Blind text: "**Result 83b.** When r=0, C₁₂ = k₁·q₂ (neutral mixing)." -/

/-- Intended statement: for every two-degree network with r = 0, C₁₂ = k₁·q₂. -/
@[sa_reference "DegreeCorrelation.R83b"]
def T : Prop := ∀ d : TwoDegreeData, d.r = 0 → d.C12 = d.k1 * d.q2

/-- S1: the whole statement. -/
@[sa_shadow "DegreeCorrelation.R83b" 1]
def S1 : Prop := ∀ d : TwoDegreeData, d.r = 0 → d.C12 = d.k1 * d.q2

@[sa_ref_forward "DegreeCorrelation.R83b" 1]
theorem ref_fwd_1 : T → S1 := fun t => t

@[sa_complete "DegreeCorrelation.R83b"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DegreeCorrelation.R83b

namespace Alignment.Shadows.DegreeCorrelation.R83c

/-! Blind text: "**Result 83c.** When r=0, C₂₁ = k₂·q₁ (neutral mixing)." -/

/-- Intended statement: for every two-degree network with r = 0, C₂₁ = k₂·q₁. -/
@[sa_reference "DegreeCorrelation.R83c"]
def T : Prop := ∀ d : TwoDegreeData, d.r = 0 → d.C21 = d.k2 * d.q1

/-- S1: the whole statement. -/
@[sa_shadow "DegreeCorrelation.R83c" 1]
def S1 : Prop := ∀ d : TwoDegreeData, d.r = 0 → d.C21 = d.k2 * d.q1

@[sa_ref_forward "DegreeCorrelation.R83c" 1]
theorem ref_fwd_1 : T → S1 := fun t => t

@[sa_complete "DegreeCorrelation.R83c"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DegreeCorrelation.R83c

namespace Alignment.Shadows.DegreeCorrelation.R83d

/-! Blind text: "**Result 83d.** When r=0, C₂₂ = k₂·q₂ (neutral mixing)." -/

/-- Intended statement: for every two-degree network with r = 0, C₂₂ = k₂·q₂. -/
@[sa_reference "DegreeCorrelation.R83d"]
def T : Prop := ∀ d : TwoDegreeData, d.r = 0 → d.C22 = d.k2 * d.q2

/-- S1: the whole statement. -/
@[sa_shadow "DegreeCorrelation.R83d" 1]
def S1 : Prop := ∀ d : TwoDegreeData, d.r = 0 → d.C22 = d.k2 * d.q2

@[sa_ref_forward "DegreeCorrelation.R83d" 1]
theorem ref_fwd_1 : T → S1 := fun t => t

@[sa_complete "DegreeCorrelation.R83d"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DegreeCorrelation.R83d

/-! ## `DegreeCorrelation.R83e` -/

namespace Alignment.Shadows.DegreeCorrelation.R83e

/-! Blind text: "**Result 83e.** Under neutral mixing (r=0), the row sums of C equal the degree:
C₁₁ + C₁₂ = k₁·(q₁ + q₂)." -/

-- AMBIGUITY: the prose "the row sums of C equal the degree" and the displayed equation
-- "C₁₁ + C₁₂ = k₁·(q₁ + q₂)" can be read as (i) the displayed equation only (S1), or (ii) also
-- the prose assertion that both row sums equal their degree, C₁₁ + C₁₂ = k₁ and
-- C₂₁ + C₂₂ = k₂ (S2, S3). Both are required.

/-- Intended statement: at r = 0, C₁₁ + C₁₂ = k₁·(q₁ + q₂), and the row sums of C equal the
degrees k₁, k₂. -/
@[sa_reference "DegreeCorrelation.R83e"]
def T : Prop :=
  ∀ d : TwoDegreeData, d.r = 0 →
    d.C11 + d.C12 = d.k1 * (d.q1 + d.q2) ∧ d.C11 + d.C12 = d.k1 ∧ d.C21 + d.C22 = d.k2

/-- S1: r = 0 → C₁₁ + C₁₂ = k₁·(q₁ + q₂) (the displayed equation). -/
@[sa_shadow "DegreeCorrelation.R83e" 1]
def S1 : Prop := ∀ d : TwoDegreeData, d.r = 0 → d.C11 + d.C12 = d.k1 * (d.q1 + d.q2)

/-- S2: r = 0 → row 1 sums to the degree k₁. -/
@[sa_shadow "DegreeCorrelation.R83e" 2]
def S2 : Prop := ∀ d : TwoDegreeData, d.r = 0 → d.C11 + d.C12 = d.k1

/-- S3: r = 0 → row 2 sums to the degree k₂. -/
@[sa_shadow "DegreeCorrelation.R83e" 3]
def S3 : Prop := ∀ d : TwoDegreeData, d.r = 0 → d.C21 + d.C22 = d.k2

@[sa_ref_forward "DegreeCorrelation.R83e" 1]
theorem ref_fwd_1 : T → S1 := fun t d h => (t d h).1

@[sa_ref_forward "DegreeCorrelation.R83e" 2]
theorem ref_fwd_2 : T → S2 := fun t d h => (t d h).2.1

@[sa_ref_forward "DegreeCorrelation.R83e" 3]
theorem ref_fwd_3 : T → S3 := fun t d h => (t d h).2.2

@[sa_complete "DegreeCorrelation.R83e"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := fun d h => ⟨s1 d h, s2 d h, s3 d h⟩

end Alignment.Shadows.DegreeCorrelation.R83e

/-! ## `DegreeCorrelation.R83f` -/

namespace Alignment.Shadows.DegreeCorrelation.R83f

/-! Blind text: "**Result 83f.** And q₁ + q₂ = 1, so the neutral row sum equals k₁." -/

-- AMBIGUITY: "And q₁ + q₂ = 1" is read unconditionally (q₁, q₂ do not involve r and the
-- sentence states no condition); "the neutral row sum equals k₁" is read under r = 0 for row 1.

/-- Intended statement: q₁ + q₂ = 1 for every two-degree network, and at r = 0 the first row
sum C₁₁ + C₁₂ equals k₁. -/
@[sa_reference "DegreeCorrelation.R83f"]
def T : Prop :=
  (∀ d : TwoDegreeData, d.q1 + d.q2 = 1) ∧
    (∀ d : TwoDegreeData, d.r = 0 → d.C11 + d.C12 = d.k1)

/-- S1: q₁ + q₂ = 1. -/
@[sa_shadow "DegreeCorrelation.R83f" 1]
def S1 : Prop := ∀ d : TwoDegreeData, d.q1 + d.q2 = 1

/-- S2: under neutral mixing the (first) row sum equals k₁. -/
@[sa_shadow "DegreeCorrelation.R83f" 2]
def S2 : Prop := ∀ d : TwoDegreeData, d.r = 0 → d.C11 + d.C12 = d.k1

@[sa_ref_forward "DegreeCorrelation.R83f" 1]
theorem ref_fwd_1 : T → S1 := fun t => t.1

@[sa_ref_forward "DegreeCorrelation.R83f" 2]
theorem ref_fwd_2 : T → S2 := fun t => t.2

@[sa_complete "DegreeCorrelation.R83f"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.DegreeCorrelation.R83f

/-! ## `DegreeCorrelation.R84-sec` -/

namespace Alignment.Shadows.DegreeCorrelation.R84_sec

/-! Blind text: "For a Poisson degree distribution with mean κ, ⟨k²⟩ = κ² + κ, so
⟨k²-k⟩/⟨k⟩ = κ, and R₀ = T·κ under neutral mixing."

Three requirements: the Poisson second moment (S1, primitive: Σ_k k²·e^{-κ}κ^k/k! = κ² + κ);
the excess degree ⟨k²-k⟩/⟨k⟩ (operation `excessDegree`) of moment data with ⟨k⟩ = κ and
⟨k²⟩ = κ² + κ equals κ (S2); and the neutral-mixing R₀ (`uncorrelated_R0`) of such data equals
T·κ (S3). The Poisson parameter κ is positive. -/

-- VOCAB-GAP: DataTypes has no Poisson distribution. S1 states the Poisson pmf explicitly and
-- uses `HasSum`; in S2, S3 a Poisson degree distribution with mean κ is represented by
-- `DegreeMomentData` with `mean = κ` and `secondMoment = κ² + κ` (the moments asserted in S1).

/-- Intended statement: the Poisson(κ) second moment is κ² + κ; moment data with mean κ and
second moment κ² + κ has excess degree κ and neutral-mixing R₀ = T·κ. -/
@[sa_reference "DegreeCorrelation.R84-sec"]
def T : Prop :=
  (∀ κ : ℝ, 0 < κ → HasSum (fun k : ℕ => (k : ℝ) ^ 2 * poissonPMF κ k) (κ ^ 2 + κ)) ∧
    (∀ κ : ℝ, 0 < κ → ∀ ψ : DegreeMomentData, ψ.mean = κ → ψ.secondMoment = κ ^ 2 + κ →
      ψ.excessDegree = κ) ∧
    (∀ Tr κ : ℝ, 0 < κ → ∀ ψ : DegreeMomentData, ψ.mean = κ → ψ.secondMoment = κ ^ 2 + κ →
      uncorrelated_R0 Tr ψ = Tr * κ)

/-- S1: for Poisson(κ), ⟨k²⟩ = Σ_k k²·p_k = κ² + κ. -/
@[sa_shadow "DegreeCorrelation.R84-sec" 1]
def S1 : Prop :=
  ∀ κ : ℝ, 0 < κ → HasSum (fun k : ℕ => (k : ℝ) ^ 2 * poissonPMF κ k) (κ ^ 2 + κ)

/-- S2: so ⟨k²-k⟩/⟨k⟩ = κ. -/
@[sa_shadow "DegreeCorrelation.R84-sec" 2]
def S2 : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ ψ : DegreeMomentData, ψ.mean = κ → ψ.secondMoment = κ ^ 2 + κ →
    ψ.excessDegree = κ

/-- S3: and R₀ = T·κ under neutral mixing. -/
@[sa_shadow "DegreeCorrelation.R84-sec" 3]
def S3 : Prop :=
  ∀ Tr κ : ℝ, 0 < κ → ∀ ψ : DegreeMomentData, ψ.mean = κ → ψ.secondMoment = κ ^ 2 + κ →
    uncorrelated_R0 Tr ψ = Tr * κ

@[sa_ref_forward "DegreeCorrelation.R84-sec" 1]
theorem ref_fwd_1 : T → S1 := fun t => t.1

@[sa_ref_forward "DegreeCorrelation.R84-sec" 2]
theorem ref_fwd_2 : T → S2 := fun t => t.2.1

@[sa_ref_forward "DegreeCorrelation.R84-sec" 3]
theorem ref_fwd_3 : T → S3 := fun t => t.2.2

@[sa_complete "DegreeCorrelation.R84-sec"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.DegreeCorrelation.R84_sec

/-! ## `DegreeCorrelation.R84` -/

namespace Alignment.Shadows.DegreeCorrelation.R84

/-! Blind text: "**Result 84.** Poisson excess degree equals the mean." -/

-- VOCAB-GAP: no Poisson constructor for `DegreeMomentData`; a Poisson degree distribution
-- with mean κ > 0 is represented by moment data with `mean = κ` and `secondMoment = κ² + κ`.
-- "the mean" is κ (= ψ.mean by hypothesis).

/-- Intended statement: the excess degree of Poisson moment data with mean κ equals κ. -/
@[sa_reference "DegreeCorrelation.R84"]
def T : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ ψ : DegreeMomentData, ψ.mean = κ → ψ.secondMoment = κ ^ 2 + κ →
    ψ.excessDegree = κ

/-- S1: the whole statement. -/
@[sa_shadow "DegreeCorrelation.R84" 1]
def S1 : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ ψ : DegreeMomentData, ψ.mean = κ → ψ.secondMoment = κ ^ 2 + κ →
    ψ.excessDegree = κ

@[sa_ref_forward "DegreeCorrelation.R84" 1]
theorem ref_fwd_1 : T → S1 := fun t => t

@[sa_complete "DegreeCorrelation.R84"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DegreeCorrelation.R84

/-! ## `DegreeCorrelation.R84b` -/

namespace Alignment.Shadows.DegreeCorrelation.R84b

/-! Blind text: "**Result 84b.** For Poisson, R₀ = T·κ." -/

-- VOCAB-GAP: as for R84, Poisson(κ) is represented by moment data with `mean = κ` and
-- `secondMoment = κ² + κ`; R₀ is the neutral-mixing R₀ `uncorrelated_R0` (the Poisson
-- section's R₀ is "under neutral mixing").

/-- Intended statement: for every transmissibility T and every Poisson moment data with mean
κ > 0, R₀ = T·κ. -/
@[sa_reference "DegreeCorrelation.R84b"]
def T : Prop :=
  ∀ Tr κ : ℝ, 0 < κ → ∀ ψ : DegreeMomentData, ψ.mean = κ → ψ.secondMoment = κ ^ 2 + κ →
    uncorrelated_R0 Tr ψ = Tr * κ

/-- S1: the whole statement. -/
@[sa_shadow "DegreeCorrelation.R84b" 1]
def S1 : Prop :=
  ∀ Tr κ : ℝ, 0 < κ → ∀ ψ : DegreeMomentData, ψ.mean = κ → ψ.secondMoment = κ ^ 2 + κ →
    uncorrelated_R0 Tr ψ = Tr * κ

@[sa_ref_forward "DegreeCorrelation.R84b" 1]
theorem ref_fwd_1 : T → S1 := fun t => t

@[sa_complete "DegreeCorrelation.R84b"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DegreeCorrelation.R84b

/-! ## `DegreeCorrelation.R85-sec` -/

namespace Alignment.Shadows.DegreeCorrelation.R85_sec

/-! Blind text: "Any valid conditional degree distribution must satisfy: (a) Σ_l Q(l|k) = 1 for
all k (normalization) (b) Σ_k k·p_k·Q(l|k) = l·p_l (detailed balance) We verify these for the
2×2 case."

The general sentence defines what "valid" requires; the checkable content is "We verify these
for the 2×2 case": the conditional degree distribution of the 2×2 mixing model satisfies (a)
for k = k₁, k₂ and (b) for l = k₁, k₂. -/

-- VOCAB-GAP: no Q(l|k) exists in Lean. Following the text's own identifications (R85a:
-- "normalization of Q(·|k₁): C₁₁ + C₁₂ = k₁"; R85c: "k₁·p₁·Q(1|1) + k₂·p₂·Q(1|2) = k₁·p₁,
-- i.e., p₁·C₁₁ + p₂·C₂₁ = k₁·p₁"), k·Q(l|k) = C_{kl}. So (a) becomes Σ_l C_{kl} = k and (b)
-- becomes Σ_k p_k·C_{kl} = l·p_l.
-- AMBIGUITY: "Any valid conditional degree distribution must satisfy" read as the 2×2
-- verification announced by "We verify these for the 2×2 case"; the general conditions are a
-- definition of validity and are not separately checkable here.

/-- Intended statement: for every two-degree network, both rows of C satisfy normalization and
both columns satisfy detailed balance. -/
@[sa_reference "DegreeCorrelation.R85-sec"]
def T : Prop :=
  ∀ d : TwoDegreeData,
    d.C11 + d.C12 = d.k1 ∧ d.C21 + d.C22 = d.k2 ∧
      d.p1 * d.C11 + d.p2 * d.C21 = d.k1 * d.p1 ∧ d.p1 * d.C12 + d.p2 * d.C22 = d.k2 * d.p2

/-- S1: normalization of Q(·|k₁). -/
@[sa_shadow "DegreeCorrelation.R85-sec" 1]
def S1 : Prop := ∀ d : TwoDegreeData, d.C11 + d.C12 = d.k1

/-- S2: normalization of Q(·|k₂). -/
@[sa_shadow "DegreeCorrelation.R85-sec" 2]
def S2 : Prop := ∀ d : TwoDegreeData, d.C21 + d.C22 = d.k2

/-- S3: detailed balance for l = k₁. -/
@[sa_shadow "DegreeCorrelation.R85-sec" 3]
def S3 : Prop := ∀ d : TwoDegreeData, d.p1 * d.C11 + d.p2 * d.C21 = d.k1 * d.p1

/-- S4: detailed balance for l = k₂. -/
@[sa_shadow "DegreeCorrelation.R85-sec" 4]
def S4 : Prop := ∀ d : TwoDegreeData, d.p1 * d.C12 + d.p2 * d.C22 = d.k2 * d.p2

@[sa_ref_forward "DegreeCorrelation.R85-sec" 1]
theorem ref_fwd_1 : T → S1 := fun t d => (t d).1

@[sa_ref_forward "DegreeCorrelation.R85-sec" 2]
theorem ref_fwd_2 : T → S2 := fun t d => (t d).2.1

@[sa_ref_forward "DegreeCorrelation.R85-sec" 3]
theorem ref_fwd_3 : T → S3 := fun t d => (t d).2.2.1

@[sa_ref_forward "DegreeCorrelation.R85-sec" 4]
theorem ref_fwd_4 : T → S4 := fun t d => (t d).2.2.2

@[sa_complete "DegreeCorrelation.R85-sec"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T :=
  fun d => ⟨s1 d, s2 d, s3 d, s4 d⟩

end Alignment.Shadows.DegreeCorrelation.R85_sec

/-! ## `DegreeCorrelation.R85a` … `R85d` -/

namespace Alignment.Shadows.DegreeCorrelation.R85a

/-! Blind text: "**Result 85a.** Row 1 of the mixing matrix sums to k₁ (normalization of
Q(·|k₁)): C₁₁ + C₁₂ = k₁." (for every r) -/

/-- Intended statement: for every two-degree network, C₁₁ + C₁₂ = k₁. -/
@[sa_reference "DegreeCorrelation.R85a"]
def T : Prop := ∀ d : TwoDegreeData, d.C11 + d.C12 = d.k1

/-- S1: the whole statement. -/
@[sa_shadow "DegreeCorrelation.R85a" 1]
def S1 : Prop := ∀ d : TwoDegreeData, d.C11 + d.C12 = d.k1

@[sa_ref_forward "DegreeCorrelation.R85a" 1]
theorem ref_fwd_1 : T → S1 := fun t => t

@[sa_complete "DegreeCorrelation.R85a"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DegreeCorrelation.R85a

namespace Alignment.Shadows.DegreeCorrelation.R85b

/-! Blind text: "**Result 85b.** Row 2 sums to k₂." (row 2 of the mixing matrix, every r) -/

/-- Intended statement: for every two-degree network, C₂₁ + C₂₂ = k₂. -/
@[sa_reference "DegreeCorrelation.R85b"]
def T : Prop := ∀ d : TwoDegreeData, d.C21 + d.C22 = d.k2

/-- S1: the whole statement. -/
@[sa_shadow "DegreeCorrelation.R85b" 1]
def S1 : Prop := ∀ d : TwoDegreeData, d.C21 + d.C22 = d.k2

@[sa_ref_forward "DegreeCorrelation.R85b" 1]
theorem ref_fwd_1 : T → S1 := fun t => t

@[sa_complete "DegreeCorrelation.R85b"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DegreeCorrelation.R85b

namespace Alignment.Shadows.DegreeCorrelation.R85c

/-! Blind text: "**Result 85c.** Detailed balance column 1: k₁·p₁·Q(1|1) + k₂·p₂·Q(1|2) = k₁·p₁,
i.e., p₁·C₁₁ + p₂·C₂₁ = k₁·p₁." -/

-- VOCAB-GAP: no Q(l|k) in Lean; the text itself identifies the Q-form with the C-form ("i.e."),
-- which is stated (k·Q(l|k) = C_{kl}).

/-- Intended statement: for every two-degree network, p₁·C₁₁ + p₂·C₂₁ = k₁·p₁. -/
@[sa_reference "DegreeCorrelation.R85c"]
def T : Prop := ∀ d : TwoDegreeData, d.p1 * d.C11 + d.p2 * d.C21 = d.k1 * d.p1

/-- S1: the whole statement. -/
@[sa_shadow "DegreeCorrelation.R85c" 1]
def S1 : Prop := ∀ d : TwoDegreeData, d.p1 * d.C11 + d.p2 * d.C21 = d.k1 * d.p1

@[sa_ref_forward "DegreeCorrelation.R85c" 1]
theorem ref_fwd_1 : T → S1 := fun t => t

@[sa_complete "DegreeCorrelation.R85c"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DegreeCorrelation.R85c

namespace Alignment.Shadows.DegreeCorrelation.R85d

/-! Blind text: "**Result 85d.** Detailed balance column 2: p₁·C₁₂ + p₂·C₂₂ = k₂·p₂." -/

/-- Intended statement: for every two-degree network, p₁·C₁₂ + p₂·C₂₂ = k₂·p₂. -/
@[sa_reference "DegreeCorrelation.R85d"]
def T : Prop := ∀ d : TwoDegreeData, d.p1 * d.C12 + d.p2 * d.C22 = d.k2 * d.p2

/-- S1: the whole statement. -/
@[sa_shadow "DegreeCorrelation.R85d" 1]
def S1 : Prop := ∀ d : TwoDegreeData, d.p1 * d.C12 + d.p2 * d.C22 = d.k2 * d.p2

@[sa_ref_forward "DegreeCorrelation.R85d" 1]
theorem ref_fwd_1 : T → S1 := fun t => t

@[sa_complete "DegreeCorrelation.R85d"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DegreeCorrelation.R85d

/-! ## `DegreeCorrelation.R86a` -/

namespace Alignment.Shadows.DegreeCorrelation.R86a

/-! Blind text: "**Result 86a.** The trace of C decomposes as:
tr(C) = k₁·r + k₂·r + (1-r)·(k₁·q₁ + k₂·q₂)." (tr(C) is the operation `trC`) -/

/-- Intended statement: for every two-degree network,
tr(C) = k₁·r + k₂·r + (1-r)·(k₁·q₁ + k₂·q₂). -/
@[sa_reference "DegreeCorrelation.R86a"]
def T : Prop :=
  ∀ d : TwoDegreeData,
    d.trC = d.k1 * d.r + d.k2 * d.r + (1 - d.r) * (d.k1 * d.q1 + d.k2 * d.q2)

/-- S1: the whole statement. -/
@[sa_shadow "DegreeCorrelation.R86a" 1]
def S1 : Prop :=
  ∀ d : TwoDegreeData,
    d.trC = d.k1 * d.r + d.k2 * d.r + (1 - d.r) * (d.k1 * d.q1 + d.k2 * d.q2)

@[sa_ref_forward "DegreeCorrelation.R86a" 1]
theorem ref_fwd_1 : T → S1 := fun t => t

@[sa_complete "DegreeCorrelation.R86a"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DegreeCorrelation.R86a

/-! ## `DegreeCorrelation.R86b` -/

namespace Alignment.Shadows.DegreeCorrelation.R86b

/-! Blind text: "**Result 86b.** The sum k₁·q₁ + k₂·q₂ = ⟨k²⟩/⟨k⟩ (second moment over mean)."
(⟨k²⟩ is `secondMom`, ⟨k⟩ is `meanDeg`) -/

/-- Intended statement: for every two-degree network, k₁·q₁ + k₂·q₂ = ⟨k²⟩/⟨k⟩. -/
@[sa_reference "DegreeCorrelation.R86b"]
def T : Prop := ∀ d : TwoDegreeData, d.k1 * d.q1 + d.k2 * d.q2 = d.secondMom / d.meanDeg

/-- S1: the whole statement. -/
@[sa_shadow "DegreeCorrelation.R86b" 1]
def S1 : Prop := ∀ d : TwoDegreeData, d.k1 * d.q1 + d.k2 * d.q2 = d.secondMom / d.meanDeg

@[sa_ref_forward "DegreeCorrelation.R86b" 1]
theorem ref_fwd_1 : T → S1 := fun t => t

@[sa_complete "DegreeCorrelation.R86b"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DegreeCorrelation.R86b

/-! ## `DegreeCorrelation.R86c` -/

namespace Alignment.Shadows.DegreeCorrelation.R86c

/-! Blind text: "**Result 86c.** Under neutral mixing (r=0), the trace equals ⟨k²⟩/⟨k⟩." -/

/-- Intended statement: for every two-degree network with r = 0, tr(C) = ⟨k²⟩/⟨k⟩. -/
@[sa_reference "DegreeCorrelation.R86c"]
def T : Prop := ∀ d : TwoDegreeData, d.r = 0 → d.trC = d.secondMom / d.meanDeg

/-- S1: the whole statement. -/
@[sa_shadow "DegreeCorrelation.R86c" 1]
def S1 : Prop := ∀ d : TwoDegreeData, d.r = 0 → d.trC = d.secondMom / d.meanDeg

@[sa_ref_forward "DegreeCorrelation.R86c" 1]
theorem ref_fwd_1 : T → S1 := fun t => t

@[sa_complete "DegreeCorrelation.R86c"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DegreeCorrelation.R86c

/-! ## `DegreeCorrelation.R86d-1` -/

namespace Alignment.Shadows.DegreeCorrelation.R86d_1

/-! Blind text: "**Result 86d.** Under full assortativity (r=1), the trace equals k₁ + k₂." -/

/-- Intended statement: for every two-degree network with r = 1, tr(C) = k₁ + k₂. -/
@[sa_reference "DegreeCorrelation.R86d-1"]
def T : Prop := ∀ d : TwoDegreeData, d.r = 1 → d.trC = d.k1 + d.k2

/-- S1: the whole statement. -/
@[sa_shadow "DegreeCorrelation.R86d-1" 1]
def S1 : Prop := ∀ d : TwoDegreeData, d.r = 1 → d.trC = d.k1 + d.k2

@[sa_ref_forward "DegreeCorrelation.R86d-1" 1]
theorem ref_fwd_1 : T → S1 := fun t => t

@[sa_complete "DegreeCorrelation.R86d-1"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DegreeCorrelation.R86d_1

/-! ## `DegreeCorrelation.R86d-2` -/

namespace Alignment.Shadows.DegreeCorrelation.R86d_2

/-! Blind text: "This means each degree class only infects its own kind." (following R86d, full
assortativity r = 1) -/

-- AMBIGUITY: "each degree class only infects its own kind" read as: under r = 1 there is no
-- cross-class mixing, i.e. both off-diagonal entries of C vanish (C₁₂ = 0, C₂₁ = 0).

/-- Intended statement: under r = 1, C₁₂ = 0 and C₂₁ = 0. -/
@[sa_reference "DegreeCorrelation.R86d-2"]
def T : Prop := ∀ d : TwoDegreeData, d.r = 1 → d.C12 = 0 ∧ d.C21 = 0

/-- S1: class 1 does not reach class 2 (C₁₂ = 0). -/
@[sa_shadow "DegreeCorrelation.R86d-2" 1]
def S1 : Prop := ∀ d : TwoDegreeData, d.r = 1 → d.C12 = 0

/-- S2: class 2 does not reach class 1 (C₂₁ = 0). -/
@[sa_shadow "DegreeCorrelation.R86d-2" 2]
def S2 : Prop := ∀ d : TwoDegreeData, d.r = 1 → d.C21 = 0

@[sa_ref_forward "DegreeCorrelation.R86d-2" 1]
theorem ref_fwd_1 : T → S1 := fun t d h => (t d h).1

@[sa_ref_forward "DegreeCorrelation.R86d-2" 2]
theorem ref_fwd_2 : T → S2 := fun t d h => (t d h).2

@[sa_complete "DegreeCorrelation.R86d-2"]
theorem complete (s1 : S1) (s2 : S2) : T := fun d h => ⟨s1 d h, s2 d h⟩

end Alignment.Shadows.DegreeCorrelation.R86d_2

/-! ## `DegreeCorrelation.R86e` -/

namespace Alignment.Shadows.DegreeCorrelation.R86e

/-! Blind text: "**Result 86e.** Under full assortativity (r=1), the off-diagonal entries
vanish." -/

/-- Intended statement: under r = 1, C₁₂ = 0 and C₂₁ = 0. -/
@[sa_reference "DegreeCorrelation.R86e"]
def T : Prop := ∀ d : TwoDegreeData, d.r = 1 → d.C12 = 0 ∧ d.C21 = 0

/-- S1: C₁₂ = 0. -/
@[sa_shadow "DegreeCorrelation.R86e" 1]
def S1 : Prop := ∀ d : TwoDegreeData, d.r = 1 → d.C12 = 0

/-- S2: C₂₁ = 0. -/
@[sa_shadow "DegreeCorrelation.R86e" 2]
def S2 : Prop := ∀ d : TwoDegreeData, d.r = 1 → d.C21 = 0

@[sa_ref_forward "DegreeCorrelation.R86e" 1]
theorem ref_fwd_1 : T → S1 := fun t d h => (t d h).1

@[sa_ref_forward "DegreeCorrelation.R86e" 2]
theorem ref_fwd_2 : T → S2 := fun t d h => (t d h).2

@[sa_complete "DegreeCorrelation.R86e"]
theorem complete (s1 : S1) (s2 : S2) : T := fun d h => ⟨s1 d h, s2 d h⟩

end Alignment.Shadows.DegreeCorrelation.R86e

/-! ## `DegreeCorrelation.R86f-1` -/

namespace Alignment.Shadows.DegreeCorrelation.R86f_1

/-! Blind text: "**Result 86f.** Under full assortativity, det(C) = k₁·k₂" (full assortativity is
r = 1, as in R86d/R86e) -/

/-- Intended statement: for every two-degree network with r = 1, det(C) = k₁·k₂. -/
@[sa_reference "DegreeCorrelation.R86f-1"]
def T : Prop := ∀ d : TwoDegreeData, d.r = 1 → d.detC = d.k1 * d.k2

/-- S1: the whole statement. -/
@[sa_shadow "DegreeCorrelation.R86f-1" 1]
def S1 : Prop := ∀ d : TwoDegreeData, d.r = 1 → d.detC = d.k1 * d.k2

@[sa_ref_forward "DegreeCorrelation.R86f-1" 1]
theorem ref_fwd_1 : T → S1 := fun t => t

@[sa_complete "DegreeCorrelation.R86f-1"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DegreeCorrelation.R86f_1

/-! ## `DegreeCorrelation.R86g-1` -/

namespace Alignment.Shadows.DegreeCorrelation.R86g_1

/-! Blind text: "**Result 86g.** Under neutral mixing (r=0), det(C) = 0." -/

/-- Intended statement: for every two-degree network with r = 0, det(C) = 0. -/
@[sa_reference "DegreeCorrelation.R86g-1"]
def T : Prop := ∀ d : TwoDegreeData, d.r = 0 → d.detC = 0

/-- S1: the whole statement. -/
@[sa_shadow "DegreeCorrelation.R86g-1" 1]
def S1 : Prop := ∀ d : TwoDegreeData, d.r = 0 → d.detC = 0

@[sa_ref_forward "DegreeCorrelation.R86g-1" 1]
theorem ref_fwd_1 : T → S1 := fun t => t

@[sa_complete "DegreeCorrelation.R86g-1"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DegreeCorrelation.R86g_1

/-! ## `DegreeCorrelation.R86h-1` -/

namespace Alignment.Shadows.DegreeCorrelation.R86h_1

/-! Blind text: "**Result 86h.** Under neutral mixing (r=0), the largest eigenvalue of C equals
tr(C) = k₁·q₁ + k₂·q₂ = ⟨k²⟩/⟨k⟩, since the other eigenvalue is 0 (det = 0)."

Under r = 0: "the largest eigenvalue of C equals tr(C)" = tr(C) is an eigenvalue of C (S1) and
no eigenvalue exceeds it (S2); the chain tr(C) = k₁q₁ + k₂q₂ (S3) and tr(C) = ⟨k²⟩/⟨k⟩ (S4);
"the other eigenvalue is 0" = 0 is an eigenvalue (S5) and every eigenvalue is tr(C) or 0 (S6);
"(det = 0)" = det(C) = 0 (S7). C is `Cmat d`, tr(C) is `trC`, det(C) is `detC`. -/

-- VOCAB-GAP: the vocabulary has no eigenvalue notion for C; eigenvalues are Mathlib's
-- `Module.End.HasEigenvalue (Matrix.toLin' (Cmat d)) μ` (real eigenvalues; "largest" is with
-- respect to ≤ on ℝ).
-- AMBIGUITY: "since the other eigenvalue is 0" read as asserting both that 0 is an eigenvalue
-- (S5) and that the eigenvalues of C are exactly tr(C) and 0 (S6); the justification clause
-- "(det = 0)" is also asserted (S7).

/-- Intended statement (all under r = 0): tr(C) is the largest eigenvalue of C,
tr(C) = k₁q₁ + k₂q₂ = ⟨k²⟩/⟨k⟩, the other eigenvalue is 0, and det(C) = 0. -/
@[sa_reference "DegreeCorrelation.R86h-1"]
def T : Prop :=
  ∀ d : TwoDegreeData, d.r = 0 →
    Module.End.HasEigenvalue (Matrix.toLin' (Cmat d)) d.trC ∧
      (∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (Cmat d)) μ → μ ≤ d.trC) ∧
      d.trC = d.k1 * d.q1 + d.k2 * d.q2 ∧
      d.trC = d.secondMom / d.meanDeg ∧
      Module.End.HasEigenvalue (Matrix.toLin' (Cmat d)) 0 ∧
      (∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (Cmat d)) μ → μ = d.trC ∨ μ = 0) ∧
      d.detC = 0

/-- S1: r = 0 → tr(C) is an eigenvalue of C. -/
@[sa_shadow "DegreeCorrelation.R86h-1" 1]
def S1 : Prop :=
  ∀ d : TwoDegreeData, d.r = 0 → Module.End.HasEigenvalue (Matrix.toLin' (Cmat d)) d.trC

/-- S2: r = 0 → every eigenvalue of C is at most tr(C). -/
@[sa_shadow "DegreeCorrelation.R86h-1" 2]
def S2 : Prop :=
  ∀ d : TwoDegreeData, d.r = 0 →
    ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (Cmat d)) μ → μ ≤ d.trC

/-- S3: r = 0 → tr(C) = k₁·q₁ + k₂·q₂. -/
@[sa_shadow "DegreeCorrelation.R86h-1" 3]
def S3 : Prop := ∀ d : TwoDegreeData, d.r = 0 → d.trC = d.k1 * d.q1 + d.k2 * d.q2

/-- S4: r = 0 → tr(C) = ⟨k²⟩/⟨k⟩. -/
@[sa_shadow "DegreeCorrelation.R86h-1" 4]
def S4 : Prop := ∀ d : TwoDegreeData, d.r = 0 → d.trC = d.secondMom / d.meanDeg

/-- S5: r = 0 → 0 is an eigenvalue of C. -/
@[sa_shadow "DegreeCorrelation.R86h-1" 5]
def S5 : Prop :=
  ∀ d : TwoDegreeData, d.r = 0 → Module.End.HasEigenvalue (Matrix.toLin' (Cmat d)) 0

/-- S6: r = 0 → every eigenvalue of C is tr(C) or 0. -/
@[sa_shadow "DegreeCorrelation.R86h-1" 6]
def S6 : Prop :=
  ∀ d : TwoDegreeData, d.r = 0 →
    ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (Cmat d)) μ → μ = d.trC ∨ μ = 0

/-- S7: r = 0 → det(C) = 0. -/
@[sa_shadow "DegreeCorrelation.R86h-1" 7]
def S7 : Prop := ∀ d : TwoDegreeData, d.r = 0 → d.detC = 0

@[sa_ref_forward "DegreeCorrelation.R86h-1" 1]
theorem ref_fwd_1 : T → S1 := fun t d h => (t d h).1

@[sa_ref_forward "DegreeCorrelation.R86h-1" 2]
theorem ref_fwd_2 : T → S2 := fun t d h => (t d h).2.1

@[sa_ref_forward "DegreeCorrelation.R86h-1" 3]
theorem ref_fwd_3 : T → S3 := fun t d h => (t d h).2.2.1

@[sa_ref_forward "DegreeCorrelation.R86h-1" 4]
theorem ref_fwd_4 : T → S4 := fun t d h => (t d h).2.2.2.1

@[sa_ref_forward "DegreeCorrelation.R86h-1" 5]
theorem ref_fwd_5 : T → S5 := fun t d h => (t d h).2.2.2.2.1

@[sa_ref_forward "DegreeCorrelation.R86h-1" 6]
theorem ref_fwd_6 : T → S6 := fun t d h => (t d h).2.2.2.2.2.1

@[sa_ref_forward "DegreeCorrelation.R86h-1" 7]
theorem ref_fwd_7 : T → S7 := fun t d h => (t d h).2.2.2.2.2.2

@[sa_complete "DegreeCorrelation.R86h-1"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) (s7 : S7) : T :=
  fun d h => ⟨s1 d h, s2 d h, s3 d h, s4 d h, s5 d h, s6 d h, s7 d h⟩

end Alignment.Shadows.DegreeCorrelation.R86h_1

/-! ## `DegreeCorrelation.R86h-2` -/

namespace Alignment.Shadows.DegreeCorrelation.R86h_2

/-! Blind text: "The eigenvalues of a 2×2 matrix with trace τ and det 0 are τ and 0."

A general fact about every real 2×2 matrix M with trace τ and determinant 0: τ is an eigenvalue
(S1), 0 is an eigenvalue (S2), and there are no others (S3). Eigenvalues are
`Module.End.HasEigenvalue (Matrix.toLin' M) μ`. -/

-- AMBIGUITY: "are τ and 0" read as set equality of the (real) eigenvalues with {τ, 0}:
-- both are eigenvalues (S1, S2) and every eigenvalue is one of them (S3).

/-- Intended statement: for every real 2×2 matrix with trace τ and determinant 0, the
eigenvalues are exactly τ and 0. -/
@[sa_reference "DegreeCorrelation.R86h-2"]
def T : Prop :=
  ∀ (M : Matrix (Fin 2) (Fin 2) ℝ) (τ : ℝ), M.trace = τ → M.det = 0 →
    Module.End.HasEigenvalue (Matrix.toLin' M) τ ∧
      Module.End.HasEigenvalue (Matrix.toLin' M) 0 ∧
      (∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' M) μ → μ = τ ∨ μ = 0)

/-- S1: τ is an eigenvalue. -/
@[sa_shadow "DegreeCorrelation.R86h-2" 1]
def S1 : Prop :=
  ∀ (M : Matrix (Fin 2) (Fin 2) ℝ) (τ : ℝ), M.trace = τ → M.det = 0 →
    Module.End.HasEigenvalue (Matrix.toLin' M) τ

/-- S2: 0 is an eigenvalue. -/
@[sa_shadow "DegreeCorrelation.R86h-2" 2]
def S2 : Prop :=
  ∀ (M : Matrix (Fin 2) (Fin 2) ℝ) (τ : ℝ), M.trace = τ → M.det = 0 →
    Module.End.HasEigenvalue (Matrix.toLin' M) 0

/-- S3: every eigenvalue is τ or 0. -/
@[sa_shadow "DegreeCorrelation.R86h-2" 3]
def S3 : Prop :=
  ∀ (M : Matrix (Fin 2) (Fin 2) ℝ) (τ : ℝ), M.trace = τ → M.det = 0 →
    ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' M) μ → μ = τ ∨ μ = 0

@[sa_ref_forward "DegreeCorrelation.R86h-2" 1]
theorem ref_fwd_1 : T → S1 := fun t M τ h1 h2 => (t M τ h1 h2).1

@[sa_ref_forward "DegreeCorrelation.R86h-2" 2]
theorem ref_fwd_2 : T → S2 := fun t M τ h1 h2 => (t M τ h1 h2).2.1

@[sa_ref_forward "DegreeCorrelation.R86h-2" 3]
theorem ref_fwd_3 : T → S3 := fun t M τ h1 h2 => (t M τ h1 h2).2.2

@[sa_complete "DegreeCorrelation.R86h-2"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T :=
  fun M τ h1 h2 => ⟨s1 M τ h1 h2, s2 M τ h1 h2, s3 M τ h1 h2⟩

end Alignment.Shadows.DegreeCorrelation.R86h_2

noncomputable section

/-! ## `DegreeCorrelation.R82` (re-authored blind)

Text: "For a two-degree network with degrees k₁, k₂, degree fractions p₁, p₂, and assortative
parameter r ∈ [0,1]: C = [[k₁·(r + (1-r)·q₁), k₁·(1-r)·q₂], [k₂·(1-r)·q₁, k₂·(r + (1-r)·q₂)]] where
q_i = k_i·p_i/⟨k⟩ are the excess-degree probabilities. [...] **Result 82.** The four entries of the
2×2 mixing matrix C_{kl} = k·Q(l|k) (not the next-generation matrix; see `TwoDegreeData.K11`)."

The entries are the operations `TwoDegreeData.C11 … C22`; `q_i` and `⟨k⟩ = k₁p₁ + k₂p₂` are
written in primitive terms. "Not the next-generation matrix" is read as: the mixing matrix differs
from `K_{kl} = (k − 1)·Q(l|k)` (DegreeCorrelation §K), for every two-degree network. -/
namespace Alignment.Shadows.DegreeCorrelation.R82

/-- `⟨k⟩ = k₁p₁ + k₂p₂`. -/
def meanK (d : TwoDegreeData) : ℝ := d.k1 * d.p1 + d.k2 * d.p2
/-- `q₁ = k₁p₁/⟨k⟩`. -/
def qp1 (d : TwoDegreeData) : ℝ := d.k1 * d.p1 / meanK d
/-- `q₂ = k₂p₂/⟨k⟩`. -/
def qp2 (d : TwoDegreeData) : ℝ := d.k2 * d.p2 / meanK d
/-- The next-generation matrix `K_{kl} = (k − 1)·Q(l|k)` of the assortative family. -/
def Kprim (d : TwoDegreeData) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(d.k1 - 1) * (d.r + (1 - d.r) * qp1 d), (d.k1 - 1) * ((1 - d.r) * qp2 d);
     (d.k2 - 1) * ((1 - d.r) * qp1 d), (d.k2 - 1) * (d.r + (1 - d.r) * qp2 d)]

@[sa_reference "DegreeCorrelation.R82"]
def T : Prop :=
  (∀ d : TwoDegreeData, d.C11 = d.k1 * (d.r + (1 - d.r) * qp1 d)) ∧
  (∀ d : TwoDegreeData, d.C12 = d.k1 * (1 - d.r) * qp2 d) ∧
  (∀ d : TwoDegreeData, d.C21 = d.k2 * (1 - d.r) * qp1 d) ∧
  (∀ d : TwoDegreeData, d.C22 = d.k2 * (d.r + (1 - d.r) * qp2 d)) ∧
  (∀ d : TwoDegreeData, !![d.C11, d.C12; d.C21, d.C22] ≠ Kprim d)

/-- S1: `C₁₁ = k₁(r + (1−r)q₁)`. -/
@[sa_shadow "DegreeCorrelation.R82" 1]
def S1 : Prop := ∀ d : TwoDegreeData, d.C11 = d.k1 * (d.r + (1 - d.r) * qp1 d)
/-- S2: `C₁₂ = k₁(1−r)q₂`. -/
@[sa_shadow "DegreeCorrelation.R82" 2]
def S2 : Prop := ∀ d : TwoDegreeData, d.C12 = d.k1 * (1 - d.r) * qp2 d
/-- S3: `C₂₁ = k₂(1−r)q₁`. -/
@[sa_shadow "DegreeCorrelation.R82" 3]
def S3 : Prop := ∀ d : TwoDegreeData, d.C21 = d.k2 * (1 - d.r) * qp1 d
/-- S4: `C₂₂ = k₂(r + (1−r)q₂)`. -/
@[sa_shadow "DegreeCorrelation.R82" 4]
def S4 : Prop := ∀ d : TwoDegreeData, d.C22 = d.k2 * (d.r + (1 - d.r) * qp2 d)
/-- S5: the mixing matrix is not the next-generation matrix. -/
@[sa_shadow "DegreeCorrelation.R82" 5]
def S5 : Prop := ∀ d : TwoDegreeData, !![d.C11, d.C12; d.C21, d.C22] ≠ Kprim d

@[sa_ref_forward "DegreeCorrelation.R82" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "DegreeCorrelation.R82" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "DegreeCorrelation.R82" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "DegreeCorrelation.R82" 4] theorem ref_fwd4 : T → S4 := fun t => t.2.2.2.1
@[sa_ref_forward "DegreeCorrelation.R82" 5] theorem ref_fwd5 : T → S5 := fun t => t.2.2.2.2
@[sa_complete "DegreeCorrelation.R82"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T := ⟨s1, s2, s3, s4, s5⟩

end Alignment.Shadows.DegreeCorrelation.R82

/-! ## `DegreeCorrelation.R86-sec` (re-authored blind)

Text: "For the 2×2 mixing matrix, the eigenvalues can be expressed via the trace and determinant.
These identities concern the mixing matrix C; the spectral R₀ uses K_{kl} = (k-1)·Q(l|k) =
C_{kl} - Q(l|k) instead (see the section on K below)."

"Expressed via the trace and determinant" is read as the characteristic equation
`μ² − tr C·μ + det C = 0` with the operations `TwoDegreeData.trC`, `TwoDegreeData.detC` (both
directions). `Q(l|k) = r·δₗₖ + (1 − r)·q_l` with `q_l = l·p_l/⟨k⟩` in primitive terms; the identity
`(k−1)·Q(l|k) = C_{kl} − Q(l|k)` is required entrywise of the mixing matrix `C11 … C22`. -/
namespace Alignment.Shadows.DegreeCorrelation.R86_sec

/-- The mixing matrix from its four entries. -/
def Cm (d : TwoDegreeData) : Matrix (Fin 2) (Fin 2) ℝ := !![d.C11, d.C12; d.C21, d.C22]
/-- `⟨k⟩ = k₁p₁ + k₂p₂`. -/
def meanK (d : TwoDegreeData) : ℝ := d.k1 * d.p1 + d.k2 * d.p2
/-- `Q(l|k)` as a matrix (row k, column l). -/
def Qm (d : TwoDegreeData) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![d.r + (1 - d.r) * (d.k1 * d.p1 / meanK d), (1 - d.r) * (d.k2 * d.p2 / meanK d);
     (1 - d.r) * (d.k1 * d.p1 / meanK d), d.r + (1 - d.r) * (d.k2 * d.p2 / meanK d)]
/-- `K_{kl} = (k − 1)·Q(l|k)`. -/
def Km (d : TwoDegreeData) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(d.k1 - 1) * Qm d 0 0, (d.k1 - 1) * Qm d 0 1; (d.k2 - 1) * Qm d 1 0, (d.k2 - 1) * Qm d 1 1]

@[sa_reference "DegreeCorrelation.R86-sec"]
def T : Prop :=
  (∀ (d : TwoDegreeData) (μ : ℝ), Module.End.HasEigenvalue (Matrix.toLin' (Cm d)) μ →
      μ ^ 2 - d.trC * μ + d.detC = 0) ∧
  (∀ (d : TwoDegreeData) (μ : ℝ), μ ^ 2 - d.trC * μ + d.detC = 0 →
      Module.End.HasEigenvalue (Matrix.toLin' (Cm d)) μ) ∧
  (∀ d : TwoDegreeData, Km d = Cm d - Qm d)

/-- S1: every eigenvalue of C solves `μ² − tr C·μ + det C = 0`. -/
@[sa_shadow "DegreeCorrelation.R86-sec" 1]
def S1 : Prop :=
  ∀ (d : TwoDegreeData) (μ : ℝ), Module.End.HasEigenvalue (Matrix.toLin' (Cm d)) μ →
    μ ^ 2 - d.trC * μ + d.detC = 0
/-- S2: every real root of `μ² − tr C·μ + det C` is an eigenvalue of C. -/
@[sa_shadow "DegreeCorrelation.R86-sec" 2]
def S2 : Prop :=
  ∀ (d : TwoDegreeData) (μ : ℝ), μ ^ 2 - d.trC * μ + d.detC = 0 →
    Module.End.HasEigenvalue (Matrix.toLin' (Cm d)) μ
/-- S3: `K = C − Q` entrywise, with `K_{kl} = (k−1)Q(l|k)`. -/
@[sa_shadow "DegreeCorrelation.R86-sec" 3]
def S3 : Prop := ∀ d : TwoDegreeData, Km d = Cm d - Qm d

@[sa_ref_forward "DegreeCorrelation.R86-sec" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "DegreeCorrelation.R86-sec" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "DegreeCorrelation.R86-sec" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "DegreeCorrelation.R86-sec"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.DegreeCorrelation.R86_sec

/-! ## `DegreeCorrelation.neutralDetK` (blind)

Text: "Under neutral mixing (r = 0), det K = 0: K has rank one."

`K_{kl} = (k − 1)·Q(l|k)` with `Q(l|k) = r·δₗₖ + (1 − r)·q_l` and the excess-degree probabilities
`TwoDegreeData.q1`, `q2`. -- AMBIGUITY: "K has rank one": when k₁ = k₂ = 1, K = 0 has rank 0, so
the claim is read as "rank at most one", the meaning of det K = 0 for a 2×2 matrix. -/
namespace Alignment.Shadows.DegreeCorrelation.neutralDetK

/-- `K = (k − 1)·Q` for the assortative family with the trusted `q₁`, `q₂`. -/
def Kq (d : TwoDegreeData) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(d.k1 - 1) * (d.r + (1 - d.r) * d.q1), (d.k1 - 1) * ((1 - d.r) * d.q2);
     (d.k2 - 1) * ((1 - d.r) * d.q1), (d.k2 - 1) * (d.r + (1 - d.r) * d.q2)]

@[sa_reference "DegreeCorrelation.neutralDetK"]
def T : Prop :=
  (∀ d : TwoDegreeData, d.r = 0 → (Kq d).det = 0) ∧
  (∀ d : TwoDegreeData, d.r = 0 → (Kq d).rank ≤ 1)

/-- S1: at r = 0, det K = 0. -/
@[sa_shadow "DegreeCorrelation.neutralDetK" 1]
def S1 : Prop := ∀ d : TwoDegreeData, d.r = 0 → (Kq d).det = 0
/-- S2: at r = 0, K has rank at most one. -/
@[sa_shadow "DegreeCorrelation.neutralDetK" 2]
def S2 : Prop := ∀ d : TwoDegreeData, d.r = 0 → (Kq d).rank ≤ 1

@[sa_ref_forward "DegreeCorrelation.neutralDetK" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "DegreeCorrelation.neutralDetK" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "DegreeCorrelation.neutralDetK"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.DegreeCorrelation.neutralDetK

/-! ## `DegreeCorrelation.neutralTraceK` (blind)

Text: "Under neutral mixing (r = 0), tr K = ⟨k(k−1)⟩/⟨k⟩."

`K` as in `neutralDetK`; `⟨k(k−1)⟩ = p₁k₁(k₁−1) + p₂k₂(k₂−1)` and `⟨k⟩ = p₁k₁ + p₂k₂` in primitive
terms. -/
namespace Alignment.Shadows.DegreeCorrelation.neutralTraceK

/-- `K = (k − 1)·Q` for the assortative family with the trusted `q₁`, `q₂`. -/
def Kq (d : TwoDegreeData) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(d.k1 - 1) * (d.r + (1 - d.r) * d.q1), (d.k1 - 1) * ((1 - d.r) * d.q2);
     (d.k2 - 1) * ((1 - d.r) * d.q1), (d.k2 - 1) * (d.r + (1 - d.r) * d.q2)]

@[sa_reference "DegreeCorrelation.neutralTraceK"]
def T : Prop :=
  ∀ d : TwoDegreeData, d.r = 0 →
    (Kq d).trace = (d.p1 * d.k1 * (d.k1 - 1) + d.p2 * d.k2 * (d.k2 - 1)) / (d.p1 * d.k1 + d.p2 * d.k2)

/-- S1: at r = 0, `tr K = ⟨k(k−1)⟩/⟨k⟩`. -/
@[sa_shadow "DegreeCorrelation.neutralTraceK" 1]
def S1 : Prop :=
  ∀ d : TwoDegreeData, d.r = 0 →
    (Kq d).trace = (d.p1 * d.k1 * (d.k1 - 1) + d.p2 * d.k2 * (d.k2 - 1)) / (d.p1 * d.k1 + d.p2 * d.k2)

@[sa_ref_forward "DegreeCorrelation.neutralTraceK" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "DegreeCorrelation.neutralTraceK"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DegreeCorrelation.neutralTraceK

/-! ## `DegreeCorrelation.neutralTraceCSubTraceK` (blind)

Text: "Under neutral mixing (r = 0), tr C − tr K = 1: the mixing matrix C = k·Q overstates the
largest eigenvalue of the next-generation matrix by one."

`tr C` is the operation `TwoDegreeData.trC`; `C` is built from `C11 … C22`; `K` as in
`neutralDetK`. "Largest eigenvalue" = the largest real eigenvalue of `Matrix.toLin'`.
-- AMBIGUITY: degrees are read as at least 1 for the eigenvalue statement (S2); for degrees in
(0, 1) the trace of the rank-one K is negative and its largest eigenvalue is 0. -/
namespace Alignment.Shadows.DegreeCorrelation.neutralTraceCSubTraceK

/-- The mixing matrix from its four entries. -/
def Cm (d : TwoDegreeData) : Matrix (Fin 2) (Fin 2) ℝ := !![d.C11, d.C12; d.C21, d.C22]
/-- `K = (k − 1)·Q` for the assortative family with the trusted `q₁`, `q₂`. -/
def Kq (d : TwoDegreeData) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(d.k1 - 1) * (d.r + (1 - d.r) * d.q1), (d.k1 - 1) * ((1 - d.r) * d.q2);
     (d.k2 - 1) * ((1 - d.r) * d.q1), (d.k2 - 1) * (d.r + (1 - d.r) * d.q2)]
/-- `μ` is the largest real eigenvalue of `A`. -/
def IsLargestEig (A : Matrix (Fin 2) (Fin 2) ℝ) (μ : ℝ) : Prop :=
  Module.End.HasEigenvalue (Matrix.toLin' A) μ ∧
    ∀ ν : ℝ, Module.End.HasEigenvalue (Matrix.toLin' A) ν → ν ≤ μ

@[sa_reference "DegreeCorrelation.neutralTraceCSubTraceK"]
def T : Prop :=
  (∀ d : TwoDegreeData, d.r = 0 → d.trC - (Kq d).trace = 1) ∧
  (∀ (d : TwoDegreeData) (μ ν : ℝ), d.r = 0 → 1 ≤ d.k1 → 1 ≤ d.k2 → IsLargestEig (Cm d) μ →
      IsLargestEig (Kq d) ν → μ = ν + 1)

/-- S1: at r = 0, `tr C − tr K = 1`. -/
@[sa_shadow "DegreeCorrelation.neutralTraceCSubTraceK" 1]
def S1 : Prop := ∀ d : TwoDegreeData, d.r = 0 → d.trC - (Kq d).trace = 1
/-- S2: at r = 0, the largest eigenvalue of C exceeds that of K by one. -/
@[sa_shadow "DegreeCorrelation.neutralTraceCSubTraceK" 2]
def S2 : Prop :=
  ∀ (d : TwoDegreeData) (μ ν : ℝ), d.r = 0 → 1 ≤ d.k1 → 1 ≤ d.k2 → IsLargestEig (Cm d) μ →
    IsLargestEig (Kq d) ν → μ = ν + 1

@[sa_ref_forward "DegreeCorrelation.neutralTraceCSubTraceK" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t.1
@[sa_ref_forward "DegreeCorrelation.neutralTraceCSubTraceK" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2
@[sa_complete "DegreeCorrelation.neutralTraceCSubTraceK"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.DegreeCorrelation.neutralTraceCSubTraceK

end
