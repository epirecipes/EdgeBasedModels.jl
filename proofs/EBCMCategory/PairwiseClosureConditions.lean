import Mathlib.Tactic

/-!
# PairwiseClosureConditions — What normalized pairwise closures do and do not guarantee

This file isolates a small algebraic fact that is central to the clustered
pairwise closures used in node-based epidemic models.

If a closed triple is written in the form

  `[ASI]_A = B * p_A`

where `B = (n - 1)[SI]` is a nonnegative base term and the weights `p_A` satisfy

  * `∑_A p_A = 1`,
  * `p_A ≥ 0` for every state `A`,

then two things follow:

  1. the total triple mass is conserved: `∑_A [ASI]_A = B`,
  2. each triple count is nonnegative.

The first conclusion only needs normalization. The second additionally needs
pointwise nonnegativity of the weights. This is exactly the distinction that
matters for auditing clustered pairwise closures: conservation alone does not
imply positivity.
-/

open scoped BigOperators

namespace PairwiseClosureConditions

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The triple contribution associated to state `a` under a normalized closure. -/
def tripleTerm (base : ℚ) (p : α → ℚ) (a : α) : ℚ :=
  base * p a

/-- Convex mixing between an unclustered and clustered weight. This is the
algebraic shape used by Barnard-style improved closures. -/
def convexMix (φ x y : ℚ) : ℚ :=
  (1 - φ) * x + φ * y

/-- Keeling-style multiplicative clustering factor. -/
def keelingFactor (φ corr : ℚ) : ℚ :=
  (1 - φ) + φ * corr

/-- Barnard-style mixed weights: a convex combination of two normalized
families of weights. -/
def barnardWeights (φ : ℚ) (p_uc p_c : α → ℚ) (a : α) : ℚ :=
  convexMix φ (p_uc a) (p_c a)

/-- Keeling-style reweighted probabilities: the baseline weight `p a` is
multiplied by a correlation correction. -/
def keelingWeights (φ : ℚ) (p corr : α → ℚ) (a : α) : ℚ :=
  p a * keelingFactor φ (corr a)

/-- Normalization of the closure weights is enough to conserve the total triple
mass. No sign condition on `p` is needed for this statement. -/
theorem triple_mass_conserved
    (base : ℚ) (p : α → ℚ)
    (hnorm : ∑ a, p a = 1) :
    ∑ a, tripleTerm base p a = base := by
  calc
    ∑ a, tripleTerm base p a = ∑ a, base * p a := by
      rfl
    _ = base * ∑ a, p a := by
      rw [Finset.mul_sum]
    _ = base := by
      rw [hnorm, mul_one]

/-- If the base term and all closure weights are nonnegative, then every closed
triple term is nonnegative. -/
theorem triple_term_nonneg
    (base : ℚ) (p : α → ℚ) (a : α)
    (hbase : 0 ≤ base)
    (hp : ∀ b, 0 ≤ p b) :
    0 ≤ tripleTerm base p a := by
  exact mul_nonneg hbase (hp a)

/-- Under nonnegative normalized weights, each individual closure weight lies in
`[0,1]`. -/
theorem weight_in_unit_interval
    (p : α → ℚ) (a : α)
    (hp : ∀ b, 0 ≤ p b)
    (hnorm : ∑ b, p b = 1) :
    0 ≤ p a ∧ p a ≤ 1 := by
  constructor
  · exact hp a
  · have hle_sum : p a ≤ ∑ b, p b := by
      simpa using
        (Finset.single_le_sum
          (f := fun b => p b)
          (by
            intro b hb
            exact hp b)
          (Finset.mem_univ a))
    simpa [hnorm] using hle_sum

/-- If some closure weight is negative and the base term is strictly positive,
then the corresponding closed triple is negative. This shows why mass
conservation alone cannot certify positivity. -/
theorem negative_weight_gives_negative_triple
    (base : ℚ) (p : α → ℚ) (a : α)
    (hbase : 0 < base)
    (hpneg : p a < 0) :
    tripleTerm base p a < 0 := by
  exact mul_neg_of_pos_of_neg hbase hpneg

/-- A packaged version of the safe regime: normalized nonnegative weights yield
both total-mass conservation and pointwise nonnegativity of the triple terms. -/
theorem normalized_nonnegative_closure_safe
    (base : ℚ) (p : α → ℚ)
    (hbase : 0 ≤ base)
    (hp : ∀ a, 0 ≤ p a)
    (hnorm : ∑ a, p a = 1) :
    (∑ a, tripleTerm base p a = base) ∧ (∀ a, 0 ≤ tripleTerm base p a) := by
  constructor
  · exact triple_mass_conserved base p hnorm
  · intro a
    exact triple_term_nonneg base p a hbase hp

/-- A convex mixture of nonnegative weights is nonnegative. -/
theorem convexMix_nonneg
    (φ x y : ℚ)
    (hφ0 : 0 ≤ φ)
    (hφ1 : φ ≤ 1)
    (hx : 0 ≤ x)
    (hy : 0 ≤ y) :
    0 ≤ convexMix φ x y := by
  unfold convexMix
  have h1mφ : 0 ≤ 1 - φ := sub_nonneg.mpr hφ1
  exact add_nonneg (mul_nonneg h1mφ hx) (mul_nonneg hφ0 hy)

/-- A convex mixture of normalized weight families is normalized. This is the
key algebraic fact behind Barnard's improved closure. -/
theorem barnardWeights_normalized
    (φ : ℚ) (p_uc p_c : α → ℚ)
    (huc : ∑ a, p_uc a = 1)
    (hc : ∑ a, p_c a = 1) :
    ∑ a, barnardWeights φ p_uc p_c a = 1 := by
  calc
    ∑ a, barnardWeights φ p_uc p_c a
        = ∑ a, ((1 - φ) * p_uc a + φ * p_c a) := by
            simp [barnardWeights, convexMix]
    _ = ∑ a, (1 - φ) * p_uc a + ∑ a, φ * p_c a := by
          rw [Finset.sum_add_distrib]
    _ = (1 - φ) * ∑ a, p_uc a + φ * ∑ a, p_c a := by
          rw [Finset.mul_sum, Finset.mul_sum]
    _ = (1 - φ) * 1 + φ * 1 := by rw [huc, hc]
    _ = 1 := by ring

/-- Barnard-style mixed weights stay nonnegative when both the unclustered and
clustered probability models are pointwise nonnegative. -/
theorem barnardWeights_nonneg
    (φ : ℚ) (p_uc p_c : α → ℚ)
    (hφ0 : 0 ≤ φ)
    (hφ1 : φ ≤ 1)
    (huc : ∀ a, 0 ≤ p_uc a)
    (hc : ∀ a, 0 ≤ p_c a) :
    ∀ a, 0 ≤ barnardWeights φ p_uc p_c a := by
  intro a
  exact convexMix_nonneg φ (p_uc a) (p_c a) hφ0 hφ1 (huc a) (hc a)

/-- Barnard-style closures are safe whenever both constituent probability models
are normalized and nonnegative. -/
theorem barnard_style_closure_safe
    (base φ : ℚ) (p_uc p_c : α → ℚ)
    (hbase : 0 ≤ base)
    (hφ0 : 0 ≤ φ)
    (hφ1 : φ ≤ 1)
    (huc_nonneg : ∀ a, 0 ≤ p_uc a)
    (hc_nonneg : ∀ a, 0 ≤ p_c a)
    (huc_norm : ∑ a, p_uc a = 1)
    (hc_norm : ∑ a, p_c a = 1) :
    (∑ a, tripleTerm base (barnardWeights φ p_uc p_c) a = base) ∧
      (∀ a, 0 ≤ tripleTerm base (barnardWeights φ p_uc p_c) a) := by
  apply normalized_nonnegative_closure_safe
  · exact hbase
  · exact barnardWeights_nonneg φ p_uc p_c hφ0 hφ1 huc_nonneg hc_nonneg
  · exact barnardWeights_normalized φ p_uc p_c huc_norm hc_norm

/-- If the Keeling correlation correction stays nonnegative, then the Keeling
weight factor is nonnegative. -/
theorem keelingFactor_nonneg
    (φ corr : ℚ)
    (hφ0 : 0 ≤ φ)
    (hφ1 : φ ≤ 1)
    (hcorr : 0 ≤ corr) :
    0 ≤ keelingFactor φ corr := by
  unfold keelingFactor
  have h1mφ : 0 ≤ 1 - φ := sub_nonneg.mpr hφ1
  exact add_nonneg h1mφ (mul_nonneg hφ0 hcorr)

/-- If the baseline weights and the correlation correction are both
nonnegative, then the Keeling-reweighted weights are nonnegative. -/
theorem keelingWeights_nonneg
    (φ : ℚ) (p corr : α → ℚ)
    (hφ0 : 0 ≤ φ)
    (hφ1 : φ ≤ 1)
    (hp : ∀ a, 0 ≤ p a)
    (hcorr : ∀ a, 0 ≤ corr a) :
    ∀ a, 0 ≤ keelingWeights φ p corr a := by
  intro a
  unfold keelingWeights
  exact mul_nonneg (hp a) (keelingFactor_nonneg φ (corr a) hφ0 hφ1 (hcorr a))

/-- Keeling-style closures are safe only after an *additional normalization
theorem* is supplied. Positivity follows from nonnegative baseline weights and
nonnegative correlation corrections, but conservation must be assumed
separately. -/
theorem keeling_style_closure_safe
    (base φ : ℚ) (p corr : α → ℚ)
    (hbase : 0 ≤ base)
    (hφ0 : 0 ≤ φ)
    (hφ1 : φ ≤ 1)
    (hp : ∀ a, 0 ≤ p a)
    (hcorr : ∀ a, 0 ≤ corr a)
    (hnorm : ∑ a, keelingWeights φ p corr a = 1) :
    (∑ a, tripleTerm base (keelingWeights φ p corr) a = base) ∧
      (∀ a, 0 ≤ tripleTerm base (keelingWeights φ p corr) a) := by
  apply normalized_nonnegative_closure_safe
  · exact hbase
  · exact keelingWeights_nonneg φ p corr hφ0 hφ1 hp hcorr
  · exact hnorm

end PairwiseClosureConditions
