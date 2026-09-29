import Mathlib.Tactic

/-!
# EpiCategory — Categories of epidemiological models

This file defines scalar records motivated by two informal classes of
epidemic models; no categorical structure is formalised:

* **Node** models: ODE systems on population-level state spaces (S, I, R)
* **Edge** models: ODE systems on edge-probability state spaces (θ, φ, R),
  parameterised by a probability generating function (PGF)

Neither class is defined as a category. Both kinds of model are values of
the single record `EpiModel`, which stores only a state-space dimension
and an R₀. No ODE, morphism or composition is formalised. The only order
is the preorder `M₁ ≤ M₂ iff M₁.dim ≤ M₂.dim`; "refinement" below means
"has at least as many state variables" and nothing more.

## References

* Miller, Slim, Volz (2012). Edge-based compartmental modelling.
  J. R. Soc. Interface 9, 890–906.
-/

/-! ## PGF abstraction -/

/-- Abstract probability generating function data.
    A PGF ψ of a degree distribution is characterised by:
    * `mean` = ψ'(1): the mean degree κ
    * `secondFactorial` = ψ''(1): the second factorial moment
    * `mean_pos`: the mean degree is positive -/
structure PGFData where
  mean : ℚ
  secondFactorial : ℚ
  mean_pos : 0 < mean
  secondFactorial_nonneg : 0 ≤ secondFactorial

namespace PGFData

/-- The excess degree ratio: ψ''(1)/ψ'(1). -/
def excessDegree (ψ : PGFData) : ℚ := ψ.secondFactorial / ψ.mean

/-- Degree variance: Var(k) = ψ''(1) + ψ'(1) - (ψ'(1))². -/
def variance (ψ : PGFData) : ℚ :=
  ψ.secondFactorial + ψ.mean - ψ.mean ^ 2

/-- The Poisson PGF with mean κ. Key property: ψ''(1) = κ². -/
def poisson (κ : ℚ) (hκ : 0 < κ) : PGFData where
  mean := κ
  secondFactorial := κ ^ 2
  mean_pos := hκ
  secondFactorial_nonneg := by positivity

/-- **Result 1.** For Poisson, the excess degree equals the mean degree. -/
theorem poisson_excess_eq_mean (κ : ℚ) (hκ : 0 < κ) :
    (poisson κ hκ).excessDegree = κ := by
  simp [excessDegree, poisson]
  field_simp

/-- **Result 2.** For Poisson, the variance equals the mean (equidispersion). -/
theorem poisson_variance_eq_mean (κ : ℚ) (hκ : 0 < κ) :
    (poisson κ hκ).variance = κ := by
  simp only [variance, poisson]
  ring

/-- Index of dispersion: σ²/κ. Poisson ⇒ dispersion index 1
    (`poisson_dispersion_eq_one`). The converse is false for degree
    distributions: the law with P(0) = P(2) = 1/2, ψ(u) = (1 + u²)/2, has
    mean 1 and variance 1 but is not Poisson. -/
def dispersionIndex (ψ : PGFData) : ℚ := ψ.variance / ψ.mean

/-- A `PGFData` record has dispersion index 1 iff it is the Poisson record
    of its own mean, i.e. iff ψ''(1) = ψ'(1)². This is a statement about
    two-moment records, not about degree distributions: the record of the
    non-Poisson law ψ(u) = (1 + u²)/2 (ψ'(1) = 1, ψ''(1) = 1) is `poisson 1`. -/
theorem dispersionIndex_eq_one_iff (ψ : PGFData) :
    ψ.dispersionIndex = 1 ↔ ψ = poisson ψ.mean ψ.mean_pos := by
  obtain ⟨m, s, hm, hs⟩ := ψ
  simp only [dispersionIndex, variance, poisson, mk.injEq, true_and]
  rw [div_eq_one_iff_eq hm.ne']
  constructor <;> intro h <;> linarith

end PGFData

/-! ## Epidemic model parameters -/

/-- Transmission and recovery parameters for an SIR model. -/
structure SIRParams where
  β : ℚ   -- transmission rate
  γ : ℚ   -- recovery rate
  β_pos : 0 < β
  γ_pos : 0 < γ

namespace SIRParams

/-- Transmissibility across a single edge: T = β/(β+γ). -/
def transmissibility (p : SIRParams) : ℚ :=
  p.β / (p.β + p.γ)

/-- Transmissibility is positive. -/
theorem transmissibility_pos (p : SIRParams) : 0 < p.transmissibility := by
  simp only [transmissibility]
  apply div_pos p.β_pos
  linarith [p.β_pos, p.γ_pos]

/-- Transmissibility is less than 1. -/
theorem transmissibility_lt_one (p : SIRParams) : p.transmissibility < 1 := by
  simp [transmissibility]
  rw [div_lt_one (by linarith [p.β_pos, p.γ_pos])]
  linarith [p.γ_pos]

end SIRParams

/-! ## The refinement preorder on model dimension -/

/-- An epidemic model, characterised abstractly by its state-space dimension
    (a proxy for information content) and R₀ (a shared observable). -/
structure EpiModel where
  dim : ℕ
  R0 : ℚ

instance : LE EpiModel := ⟨fun m₁ m₂ => m₁.dim ≤ m₂.dim⟩

instance : Preorder EpiModel where
  le := (· ≤ ·)
  le_refl _ := Nat.le_refl _
  le_trans _ _ _ := Nat.le_trans

/-- A node-based SIR model: 3 state variables (S, I, R). -/
def nodeModel (p : SIRParams) (κ : ℚ) : EpiModel where
  dim := 3
  R0 := p.transmissibility * κ

/-- An edge-based SIR model: 4 state variables (θ, φ_I, R + algebraic φ_S). -/
def edgeModel (p : SIRParams) (ψ : PGFData) : EpiModel where
  dim := 4
  R0 := p.transmissibility * ψ.excessDegree

/-- **Result 3.** The edge model always refines the node model. -/
theorem edge_refines_node (p : SIRParams) (ψ : PGFData) :
    nodeModel p ψ.mean ≤ edgeModel p ψ := by
  show 3 ≤ 4
  omega

/-- **Result 4.** For Poisson networks, both models compute the same R₀. -/
theorem poisson_R0_agree (p : SIRParams) (κ : ℚ) (hκ : 0 < κ) :
    (nodeModel p κ).R0 = (edgeModel p (PGFData.poisson κ hκ)).R0 := by
  simp [nodeModel, edgeModel, PGFData.poisson_excess_eq_mean]
