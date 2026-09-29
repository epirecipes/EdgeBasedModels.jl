import Alignment.Registry
import EBCMCategory.SurvivalBridge
import Mathlib.Probability.Distributions.Poisson
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Blind shadow sets for group `SurvivalBridge`

Written blind: this author read only the claim texts in `claims_blind.yaml`,
`Alignment/DataTypes/SurvivalBridge.md`, `Alignment/README.md`, `SA-PASS_SKILL.md`,
`Alignment/Example/ExampleShadows.lean`, and the source paper
`papers/s00285-023-01967-9.md` (Kiss, Kenah, Rempała 2023, "Necessary and sufficient conditions
for exact closures of epidemic equations on configuration model networks"). That paper supplies the
Volz model (eqs. (6)-(7)), the DSA model (eqs. (8)-(9)), the Poisson-type (PT) family (Table 1),
the closure invariant (17) and the survival equation (33).

The vocabulary is as follows.
* *Data level* (ℚ): `PGFData` (only ψ'(1) = `mean` and ψ''(1) = `secondFactorial`) and the
  operations under test `PGFData.closureKappa`, `PGFData.excessDegree`, `PGFData.dispersionIndex`,
  `PGFData.poisson`, `SIRParams.transmissibility`, `volzToDSA`, `dsaToVolz`.
* *Function level* (ℝ, VOCAB-GAP): the DataTypes cannot express a PGF away from u = 1, derivatives
  in θ, or ODE trajectories. These are written below with Mathlib primitives (`deriv`, `tsum`,
  `HasSum`, `HasDerivWithinAt`, `Real.exp`, `Real.log`, `Real.rpow`).

Re-authored blind (second pass, from the current claim texts, `DataTypes/*.md`, the README,
`SA-PASS_SKILL.md`, `Example/ExampleShadows.lean` and background papers only): the blocks marked
"(re-authored blind)" or "(blind)" near the end of this file (with any `Shared2` helper
namespace). Ids of that pass not formalised (remarks on proof status, on which notions the library
defines, or cited results needing models the vocabulary lacks): `R46a`,
`header.categorical.colimit`, `header.categorical.naturalIso`, `header.categorical.pairwiseIso`.
-/

noncomputable section

namespace Alignment.Shadows.SurvivalBridge

/-! ## Shared helpers (function level; VOCAB-GAP) -/

/-- The closure invariant κ(θ) = ψ''(θ)·ψ(θ)/ψ'(θ)² of a function ψ (paper eq. (17)). -/
def kappaAt (ψ : ℝ → ℝ) (θ : ℝ) : ℝ :=
  deriv (deriv ψ) θ * ψ θ / (deriv ψ θ) ^ 2

/-- Poisson(ℓ) PGF: ψ(u) = e^{ℓ(u-1)}. -/
def poissonPGF (ℓ : ℝ) : ℝ → ℝ := fun u => Real.exp (ℓ * (u - 1))

/-- Binomial(n, q) PGF: ψ(u) = (1 - q + q·u)^n. -/
def binomialPGF (n : ℕ) (q : ℝ) : ℝ → ℝ := fun u => (1 - q + q * u) ^ n

/-- Negative binomial NB(r, q) PGF (paper Table 2 parametrisation): ψ(u) = ((1-q)/(1-q·u))^r. -/
def negBinPGF (r q : ℝ) : ℝ → ℝ := fun u => ((1 - q) / (1 - q * u)) ^ r

/-- `p` is a degree distribution (a probability mass function on ℕ). -/
def IsDegreeDist (p : ℕ → ℝ) : Prop := (∀ k, 0 ≤ p k) ∧ HasSum p 1

/-- The PGF of a degree distribution: ψ(u) = Σ_k p_k u^k. -/
def pgf (p : ℕ → ℝ) (u : ℝ) : ℝ := ∑' k : ℕ, p k * u ^ k

/-- ψ'(u) as a series: Σ_k (k+1) p_{k+1} u^k (meaningful up to and including u = 1). -/
def pgfD1 (p : ℕ → ℝ) (u : ℝ) : ℝ := ∑' k : ℕ, ((k : ℝ) + 1) * p (k + 1) * u ^ k

/-- ψ''(u) as a series: Σ_k (k+2)(k+1) p_{k+2} u^k (finite at u = 1 under finite variance). -/
def pgfD2 (p : ℕ → ℝ) (u : ℝ) : ℝ := ∑' k : ℕ, ((k : ℝ) + 2) * ((k : ℝ) + 1) * p (k + 2) * u ^ k

/-- ψ is a Poisson PGF on [0,1]. -/
def IsPoissonOn (ψ : ℝ → ℝ) : Prop :=
  ∃ ℓ : ℝ, 0 < ℓ ∧ ∀ u ∈ Set.Icc (0 : ℝ) 1, ψ u = poissonPGF ℓ u

/-- ψ is a Binomial PGF on [0,1]. -/
def IsBinomialOn (ψ : ℝ → ℝ) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧ ∀ u ∈ Set.Icc (0 : ℝ) 1, ψ u = binomialPGF n q u

/-- ψ is a negative binomial PGF on [0,1]. -/
def IsNegBinOn (ψ : ℝ → ℝ) : Prop :=
  ∃ r q : ℝ, 0 < r ∧ 0 < q ∧ q < 1 ∧ ∀ u ∈ Set.Icc (0 : ℝ) 1, ψ u = negBinPGF r q u

/-- ψ belongs to the Poisson-type family (Poisson, Binomial, or Negative Binomial). -/
def IsPTFamily (ψ : ℝ → ℝ) : Prop := IsPoissonOn ψ ∨ IsBinomialOn ψ ∨ IsNegBinOn ψ

/-- The closure invariant of the distribution `p` equals the constant κ for all θ ∈ (0,1). -/
def HasConstKappa (p : ℕ → ℝ) (κ : ℝ) : Prop :=
  ∀ θ ∈ Set.Ioo (0 : ℝ) 1, kappaAt (pgf p) θ = κ

/-- `ψ` holds the first two factorial moments of the distribution `p`:
ψ.mean = Σ k p_k and ψ.secondFactorial = Σ k(k-1) p_k. -/
def MomentsOf (ψ : PGFData) (p : ℕ → ℝ) : Prop :=
  HasSum (fun k : ℕ => (k : ℝ) * p k) (ψ.mean : ℝ) ∧
    HasSum (fun k : ℕ => (k : ℝ) * ((k : ℝ) - 1) * p k) (ψ.secondFactorial : ℝ)

/-! ### κ values of the PT families -/

/-- Function level: the Poisson invariant is identically 1 on θ ∈ (0,1]. -/
def PoissonKappaFn : Prop :=
  ∀ ℓ : ℝ, 0 < ℓ → ∀ θ ∈ Set.Ioc (0 : ℝ) 1, kappaAt (poissonPGF ℓ) θ = 1

/-- Function level: the Binomial(n,q) invariant is identically (n-1)/n on θ ∈ (0,1]. -/
def BinomKappaFn : Prop :=
  ∀ (n : ℕ) (q : ℝ), 1 ≤ n → 0 < q → q ≤ 1 → ∀ θ ∈ Set.Ioc (0 : ℝ) 1,
    kappaAt (binomialPGF n q) θ = ((n : ℝ) - 1) / n

/-- Function level: the Binomial(n,q) invariant is < 1 on θ ∈ (0,1]. -/
def BinomKappaFnLt : Prop :=
  ∀ (n : ℕ) (q : ℝ), 1 ≤ n → 0 < q → q ≤ 1 → ∀ θ ∈ Set.Ioc (0 : ℝ) 1,
    kappaAt (binomialPGF n q) θ < 1

/-- Function level: the NB(r,q) invariant is identically (r+1)/r on θ ∈ (0,1]. -/
def NegBinKappaFn : Prop :=
  ∀ r q : ℝ, 0 < r → 0 < q → q < 1 → ∀ θ ∈ Set.Ioc (0 : ℝ) 1,
    kappaAt (negBinPGF r q) θ = (r + 1) / r

/-- Function level: the NB(r,q) invariant is > 1 on θ ∈ (0,1]. -/
def NegBinKappaFnGt : Prop :=
  ∀ r q : ℝ, 0 < r → 0 < q → q < 1 → ∀ θ ∈ Set.Ioc (0 : ℝ) 1,
    1 < kappaAt (negBinPGF r q) θ

/-- Data level: for the Poisson PGF data with mean ℓ, closureKappa = 1. -/
def PoissonKappaData : Prop :=
  ∀ (ℓ : ℚ) (h : 0 < ℓ), PGFData.closureKappa (PGFData.poisson ℓ h) = 1

/-- Data level (VOCAB-GAP: there is no Binomial constructor, so "Binomial(n,q)" is written as
PGF data with the Binomial moments ψ'(1) = nq and ψ''(1) = n(n-1)q²): closureKappa = (n-1)/n. -/
def BinomKappaData : Prop :=
  ∀ (n : ℕ) (q : ℚ), 1 ≤ n → 0 < q → q ≤ 1 → ∀ ψ : PGFData,
    ψ.mean = (n : ℚ) * q → ψ.secondFactorial = (n : ℚ) * ((n : ℚ) - 1) * q ^ 2 →
    PGFData.closureKappa ψ = ((n : ℚ) - 1) / n

/-- Data level: Binomial moments give closureKappa < 1. -/
def BinomKappaDataLt : Prop :=
  ∀ (n : ℕ) (q : ℚ), 1 ≤ n → 0 < q → q ≤ 1 → ∀ ψ : PGFData,
    ψ.mean = (n : ℚ) * q → ψ.secondFactorial = (n : ℚ) * ((n : ℚ) - 1) * q ^ 2 →
    PGFData.closureKappa ψ < 1

/-- Data level (VOCAB-GAP: no NB constructor; NB(r,q) moments ψ'(1) = rq/(1-q) and
ψ''(1) = r(r+1)q²/(1-q)²): closureKappa = (r+1)/r. -/
def NegBinKappaData : Prop :=
  ∀ r q : ℚ, 0 < r → 0 < q → q < 1 → ∀ ψ : PGFData,
    ψ.mean = r * q / (1 - q) → ψ.secondFactorial = r * (r + 1) * q ^ 2 / (1 - q) ^ 2 →
    PGFData.closureKappa ψ = (r + 1) / r

/-- Data level: NB moments give closureKappa > 1. -/
def NegBinKappaDataGt : Prop :=
  ∀ r q : ℚ, 0 < r → 0 < q → q < 1 → ∀ ψ : PGFData,
    ψ.mean = r * q / (1 - q) → ψ.secondFactorial = r * (r + 1) * q ^ 2 / (1 - q) ^ 2 →
    1 < PGFData.closureKappa ψ

/-! ### Converse directions within the PT setting (function level) -/

/-- A degree distribution (positive mean, i.e. p₀ < 1) whose invariant is the constant κ = 1 is
Poisson. -/
def PoissonFromKappa : Prop :=
  ∀ (p : ℕ → ℝ) (κ : ℝ), IsDegreeDist p → p 0 < 1 → HasConstKappa p κ → κ = 1 →
    IsPoissonOn (pgf p)

/-- A degree distribution whose invariant is a constant κ < 1 is Binomial(n,q) with κ = (n-1)/n. -/
def BinomFromKappa : Prop :=
  ∀ (p : ℕ → ℝ) (κ : ℝ), IsDegreeDist p → p 0 < 1 → HasConstKappa p κ → κ < 1 →
    ∃ n : ℕ, 1 ≤ n ∧ ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧
      (∀ u ∈ Set.Icc (0 : ℝ) 1, pgf p u = binomialPGF n q u) ∧ κ = ((n : ℝ) - 1) / n

/-- A degree distribution whose invariant is a constant κ > 1 is NB(r,q) with κ = (r+1)/r. -/
def NegBinFromKappa : Prop :=
  ∀ (p : ℕ → ℝ) (κ : ℝ), IsDegreeDist p → p 0 < 1 → HasConstKappa p κ → 1 < κ →
    ∃ r q : ℝ, 0 < r ∧ 0 < q ∧ q < 1 ∧
      (∀ u ∈ Set.Icc (0 : ℝ) 1, pgf p u = negBinPGF r q u) ∧ κ = (r + 1) / r

/-! ### Non-PT distributions (function level) -/

/-- For every non-PT degree distribution (positive mean), κ(θ) takes two different values on (0,1). -/
def KappaVaries : Prop :=
  ∀ p : ℕ → ℝ, IsDegreeDist p → p 0 < 1 → ¬ IsPTFamily (pgf p) →
    ∃ θ₁ ∈ Set.Ioo (0 : ℝ) 1, ∃ θ₂ ∈ Set.Ioo (0 : ℝ) 1, kappaAt (pgf p) θ₁ ≠ kappaAt (pgf p) θ₂

/-- For every non-PT degree distribution, no constant κ makes the pairwise closure factor
ψ''(θ)ψ(θ)/ψ'(θ)² = κ exact on (0,1), so the closure is only approximate. -/
def ClosureInexact : Prop :=
  ∀ p : ℕ → ℝ, IsDegreeDist p → p 0 < 1 → ¬ IsPTFamily (pgf p) → ¬ ∃ κ : ℝ, HasConstKappa p κ

/-! ### ODE models (function level; VOCAB-GAP: no ODE flows in the DataTypes)

Trajectories are functions ℝ → ℝ, and the equations are required for t ≥ 0 (one-sided at 0). -/

/-- DSA model (paper §2.4, eqs. (8)-(9)) with ψ' = `d1`, ψ'' = `d2`, rates β, γ, mean degree μ
and initial infected fraction ρ. -/
def IsDSASolution (d1 d2 : ℝ → ℝ) (β γ μ ρ : ℝ) (xθ xSS xSI xS xI : ℝ → ℝ) : Prop :=
  xS 0 = 1 ∧ xθ 0 = 1 ∧ xI 0 = ρ ∧ xSS 0 = μ ∧ xSI 0 = μ * ρ ∧
  ∀ t : ℝ, 0 ≤ t →
    HasDerivWithinAt xθ (-β * xSI t / d1 (xθ t)) (Set.Ici 0) t ∧
    HasDerivWithinAt xSS (-2 * β * xSI t * xSS t * (d2 (xθ t) / d1 (xθ t) ^ 2)) (Set.Ici 0) t ∧
    HasDerivWithinAt xSI
      (xSI t * (β * (xSS t - xSI t) * (d2 (xθ t) / d1 (xθ t) ^ 2) - (β + γ))) (Set.Ici 0) t ∧
    HasDerivWithinAt xS (-β * xSI t) (Set.Ici 0) t ∧
    HasDerivWithinAt xI (β * xSI t - γ * xI t) (Set.Ici 0) t

/-- Volz model (paper §2.3, eqs. (6)-(7)) with PGF ψ, ψ' = `d1`, ψ'' = `d2`. -/
def IsVolzSolution (ψ d1 d2 : ℝ → ℝ) (β γ ρ : ℝ) (θ pI pS xS xI : ℝ → ℝ) : Prop :=
  θ 0 = 1 ∧ pS 0 = 1 ∧ pI 0 = ρ ∧ xI 0 = ρ ∧ (∀ t : ℝ, xS t = ψ (θ t)) ∧
  ∀ t : ℝ, 0 ≤ t →
    HasDerivWithinAt θ (-β * pI t * θ t) (Set.Ici 0) t ∧
    HasDerivWithinAt pI
      (β * pS t * pI t * θ t * (d2 (θ t) / d1 (θ t)) - β * pI t * (1 - pI t) - γ * pI t)
      (Set.Ici 0) t ∧
    HasDerivWithinAt pS (β * pS t * pI t * (1 - θ t * (d2 (θ t) / d1 (θ t)))) (Set.Ici 0) t ∧
    HasDerivWithinAt xI (β * pI t * θ t * d1 (θ t) - γ * xI t) (Set.Ici 0) t

/-- Classical mass-action SIR with transmission b, recovery g, S(0) = 1 and I(0) = r. -/
def IsMassActionSIR (b g r : ℝ) (S I : ℝ → ℝ) : Prop :=
  S 0 = 1 ∧ I 0 = r ∧ ∀ t : ℝ, 0 ≤ t →
    HasDerivWithinAt S (-b * S t * I t) (Set.Ici 0) t ∧
    HasDerivWithinAt I (b * S t * I t - g * I t) (Set.Ici 0) t

/-- Right-hand side of the κ = 1 survival equation: β̃(S - S²) + γ̃·S·log S + ρ̃·S. -/
def survivalRHS1 (bt gt rt s : ℝ) : ℝ := bt * (s - s ^ 2) + gt * s * Real.log s + rt * s

/-- For Poisson(μ) degrees, every DSA solution's susceptible fraction satisfies
-dS/dt = β̃(S - S²) + γ̃·S·log S + ρ̃·S, with the constants of paper eq. (33):
β̃ = μβ, γ̃ = β + γ, ρ̃ = βμρ. -/
def DSAPoissonSurvival : Prop :=
  ∀ β γ μ ρ : ℝ, 0 < β → 0 < γ → 0 < μ → 0 < ρ →
  ∀ xθ xSS xSI xS xI : ℝ → ℝ,
    IsDSASolution (deriv (poissonPGF μ)) (deriv (deriv (poissonPGF μ))) β γ μ ρ xθ xSS xSI xS xI →
    ∀ t : ℝ, 0 ≤ t →
      HasDerivWithinAt xS (-(survivalRHS1 (μ * β) (β + γ) (β * μ * ρ) (xS t))) (Set.Ici 0) t

/-- The mass-action SIR survival equation: the S of a classical mass-action SIR solution satisfies
-dS/dt = b(S - S²) + g·S·log S + (b·r)·S, i.e. the κ = 1 form with β̃ = b, γ̃ = g, ρ̃ = b·r. -/
def MassActionSurvival : Prop :=
  ∀ b g r : ℝ, 0 < b → 0 < g → 0 < r → ∀ S I : ℝ → ℝ, IsMassActionSIR b g r S I →
    ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt S (-(survivalRHS1 b g (b * r) (S t))) (Set.Ici 0) t

/-- For Poisson(μ) degrees, the DSA susceptible trajectory coincides with the S of the mass-action
SIR with transmission μβ, recovery β + γ and I(0) = ρ. -/
def DSAPoissonEqMassAction : Prop :=
  ∀ β γ μ ρ : ℝ, 0 < β → 0 < γ → 0 < μ → 0 < ρ →
  ∀ xθ xSS xSI xS xI : ℝ → ℝ,
    IsDSASolution (deriv (poissonPGF μ)) (deriv (deriv (poissonPGF μ))) β γ μ ρ xθ xSS xSI xS xI →
    ∀ S I : ℝ → ℝ, IsMassActionSIR (μ * β) (β + γ) ρ S I →
    ∀ t : ℝ, 0 ≤ t → xS t = S t

/-- Standing hypotheses for comparing the two models: a degree distribution with positive mean
and finite variance, positive rates and initial fraction, a Volz solution and a DSA solution
(with μ = ψ'(1)). -/
def VolzDSAHyp (p : ℕ → ℝ) (β γ ρ : ℝ) (θ pI pS xSV xIV xθ xSS xSI xSD xID : ℝ → ℝ) : Prop :=
  IsDegreeDist p ∧ p 0 < 1 ∧ Summable (fun k : ℕ => (k : ℝ) ^ 2 * p k) ∧
  0 < β ∧ 0 < γ ∧ 0 < ρ ∧
  IsVolzSolution (pgf p) (pgfD1 p) (pgfD2 p) β γ ρ θ pI pS xSV xIV ∧
  IsDSASolution (pgfD1 p) (pgfD2 p) β γ (pgfD1 p 1) ρ xθ xSS xSI xSD xID

/-- Dynamic equivalence, θ: Volz θ(t) = DSA x_θ(t) for every degree distribution. -/
def VolzDSATheta : Prop :=
  ∀ (p : ℕ → ℝ) (β γ ρ : ℝ) (θ pI pS xSV xIV xθ xSS xSI xSD xID : ℝ → ℝ),
    VolzDSAHyp p β γ ρ θ pI pS xSV xIV xθ xSS xSI xSD xID → ∀ t : ℝ, 0 ≤ t → θ t = xθ t

/-- Dynamic equivalence, susceptibles: the Volz x_S(t) equals the DSA x_S(t). -/
def VolzDSASus : Prop :=
  ∀ (p : ℕ → ℝ) (β γ ρ : ℝ) (θ pI pS xSV xIV xθ xSS xSI xSD xID : ℝ → ℝ),
    VolzDSAHyp p β γ ρ θ pI pS xSV xIV xθ xSS xSI xSD xID → ∀ t : ℝ, 0 ≤ t → xSV t = xSD t

/-- Dynamic equivalence, infecteds: the Volz x_I(t) equals the DSA x_I(t). -/
def VolzDSAInf : Prop :=
  ∀ (p : ℕ → ℝ) (β γ ρ : ℝ) (θ pI pS xSV xIV xθ xSS xSI xSD xID : ℝ → ℝ),
    VolzDSAHyp p β γ ρ θ pI pS xSV xIV xθ xSS xSI xSD xID → ∀ t : ℝ, 0 ≤ t → xIV t = xID t

/-! ### Volz ↔ DSA variable change (data level; `c` is the value ψ'(θ)) -/

/-- Volz → DSA → Volz is the identity whenever c ≠ 0. -/
def LeftInvNe : Prop :=
  ∀ (c : ℚ) (h : c ≠ 0) (v : VolzState), dsaToVolz (volzToDSA v c) c h = v

/-- DSA → Volz → DSA is the identity whenever c ≠ 0. -/
def RightInvNe : Prop :=
  ∀ (c : ℚ) (h : c ≠ 0) (d : DSAState), volzToDSA (dsaToVolz d c h) c = d

/-- Volz → DSA is injective whenever c ≠ 0. -/
def InjNe : Prop := ∀ c : ℚ, c ≠ 0 → Function.Injective (fun v : VolzState => volzToDSA v c)

/-- Volz → DSA is surjective whenever c ≠ 0. -/
def SurjNe : Prop := ∀ c : ℚ, c ≠ 0 → Function.Surjective (fun v : VolzState => volzToDSA v c)

/-- Volz → DSA → Volz is the identity whenever c > 0. -/
def LeftInvPos : Prop :=
  ∀ c : ℚ, 0 < c → ∀ (h : c ≠ 0) (v : VolzState), dsaToVolz (volzToDSA v c) c h = v

/-- DSA → Volz → DSA is the identity whenever c > 0. -/
def RightInvPos : Prop :=
  ∀ c : ℚ, 0 < c → ∀ (h : c ≠ 0) (d : DSAState), volzToDSA (dsaToVolz d c h) c = d

/-- Volz → DSA is injective whenever c > 0. -/
def InjPos : Prop := ∀ c : ℚ, 0 < c → Function.Injective (fun v : VolzState => volzToDSA v c)

/-- Volz → DSA is surjective whenever c > 0. -/
def SurjPos : Prop := ∀ c : ℚ, 0 < c → Function.Surjective (fun v : VolzState => volzToDSA v c)

end Alignment.Shadows.SurvivalBridge

/-! ## `SurvivalBridge.header.kappaInvariant-b` -/
namespace Alignment.Shadows.SurvivalBridge.header_kappaInvariant_b

/-
Blind text: "* κ = (n-1)/n for Binomial(n,p) * κ = 1 for Poisson(λ) * κ = (r+1)/r for NegBin(r,p)"

The κ here is the header's invariant κ = ψ''(θ)ψ(θ)/ψ'(θ)², which is constant in θ for PT
distributions.
-- AMBIGUITY: "κ = …" read as (a) the invariant, as a function of θ ∈ (0,1], is identically the
--   stated constant (S1-S3, function level); and (b) the closure parameter of the PGF data at
--   u = 1 (`PGFData.closureKappa`) takes the stated value (S4-S6). Both are required.
-- AMBIGUITY: NegBin(r,p) parametrisation. We use the paper's ψ(u) = ((1-p)/(1-pu))^r; the other
--   convention is p ↦ 1-p, and since p ranges over all of (0,1) the statements are equivalent.
-- VOCAB-GAP: (a) needs PGFs as functions and derivatives; (b) needs Binomial/NB PGF data, written
--   through their moments because there is no Binomial or NB constructor.
-/

@[sa_reference "SurvivalBridge.header.kappaInvariant-b"]
def T : Prop :=
  BinomKappaFn ∧ PoissonKappaFn ∧ NegBinKappaFn ∧ BinomKappaData ∧ PoissonKappaData ∧
    NegBinKappaData

/-- S1: Binomial(n,p): κ(θ) = (n-1)/n for all θ ∈ (0,1]. -/
@[sa_shadow "SurvivalBridge.header.kappaInvariant-b" 1] def S1 : Prop := BinomKappaFn
/-- S2: Poisson(λ): κ(θ) = 1 for all θ ∈ (0,1]. -/
@[sa_shadow "SurvivalBridge.header.kappaInvariant-b" 2] def S2 : Prop := PoissonKappaFn
/-- S3: NegBin(r,p): κ(θ) = (r+1)/r for all θ ∈ (0,1]. -/
@[sa_shadow "SurvivalBridge.header.kappaInvariant-b" 3] def S3 : Prop := NegBinKappaFn
/-- S4: Binomial PGF data: closureKappa = (n-1)/n. -/
@[sa_shadow "SurvivalBridge.header.kappaInvariant-b" 4] def S4 : Prop := BinomKappaData
/-- S5: Poisson PGF data: closureKappa = 1. -/
@[sa_shadow "SurvivalBridge.header.kappaInvariant-b" 5] def S5 : Prop := PoissonKappaData
/-- S6: NB PGF data: closureKappa = (r+1)/r. -/
@[sa_shadow "SurvivalBridge.header.kappaInvariant-b" 6] def S6 : Prop := NegBinKappaData

@[sa_ref_forward "SurvivalBridge.header.kappaInvariant-b" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t.1
@[sa_ref_forward "SurvivalBridge.header.kappaInvariant-b" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2.1
@[sa_ref_forward "SurvivalBridge.header.kappaInvariant-b" 3] theorem ref_fwd3 : T → S3 :=
  fun t => t.2.2.1
@[sa_ref_forward "SurvivalBridge.header.kappaInvariant-b" 4] theorem ref_fwd4 : T → S4 :=
  fun t => t.2.2.2.1
@[sa_ref_forward "SurvivalBridge.header.kappaInvariant-b" 5] theorem ref_fwd5 : T → S5 :=
  fun t => t.2.2.2.2.1
@[sa_ref_forward "SurvivalBridge.header.kappaInvariant-b" 6] theorem ref_fwd6 : T → S6 :=
  fun t => t.2.2.2.2.2
@[sa_complete "SurvivalBridge.header.kappaInvariant-b"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) : T :=
  ⟨s1, s2, s3, s4, s5, s6⟩

end Alignment.Shadows.SurvivalBridge.header_kappaInvariant_b

/-! ## `SurvivalBridge.table.R45` -/
namespace Alignment.Shadows.SurvivalBridge.table_R45

/-
Blind text: "| 45 | The Volz ↔ DSA variable change is invertible |"

No condition is stated. The DSA → Volz map needs ψ'(θ) = c ≠ 0, so the most general meaningful
condition, c ≠ 0, is used.
-- AMBIGUITY: "invertible" is read as (a) the two variable changes being mutual inverses (S1, S2),
--   and (b) the Volz → DSA map being a bijection (S3 injective, S4 surjective).
-/

@[sa_reference "SurvivalBridge.table.R45"]
def T : Prop := LeftInvNe ∧ RightInvNe ∧ InjNe ∧ SurjNe

/-- S1: Volz → DSA → Volz is the identity (c ≠ 0). -/
@[sa_shadow "SurvivalBridge.table.R45" 1] def S1 : Prop := LeftInvNe
/-- S2: DSA → Volz → DSA is the identity (c ≠ 0). -/
@[sa_shadow "SurvivalBridge.table.R45" 2] def S2 : Prop := RightInvNe
/-- S3: Volz → DSA is injective (c ≠ 0). -/
@[sa_shadow "SurvivalBridge.table.R45" 3] def S3 : Prop := InjNe
/-- S4: Volz → DSA is surjective (c ≠ 0). -/
@[sa_shadow "SurvivalBridge.table.R45" 4] def S4 : Prop := SurjNe

@[sa_ref_forward "SurvivalBridge.table.R45" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "SurvivalBridge.table.R45" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "SurvivalBridge.table.R45" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "SurvivalBridge.table.R45" 4] theorem ref_fwd4 : T → S4 := fun t => t.2.2.2
@[sa_complete "SurvivalBridge.table.R45"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.SurvivalBridge.table_R45

/-! ## `SurvivalBridge.table.R48` -/
namespace Alignment.Shadows.SurvivalBridge.table_R48

/-
Blind text: "| 48 | PT closure constant κ = excess/degree ratio |"

-- AMBIGUITY: "excess/degree ratio" is read as (mean excess degree) / (mean degree), where the mean
--   excess degree is ψ''(1)/ψ'(1) and the mean degree is ψ'(1). This matches the closureKappa
--   docstring. The alternative reading "κ = the DataTypes' excess degree ratio ψ''(1)/ψ'(1)" is
--   rejected, because the slash denotes the quotient excess ÷ degree.
--   The requirement is stated through the vocabulary (`excessDegree`, S1) and in primitive terms
--   (S2).
-- VOCAB-GAP: "PT" cannot be expressed on PGF data, so the identity is required for all PGF data.
-/

@[sa_reference "SurvivalBridge.table.R48"]
def T : Prop :=
  (∀ ψ : PGFData, PGFData.closureKappa ψ = PGFData.excessDegree ψ / ψ.mean) ∧
    (∀ ψ : PGFData, PGFData.closureKappa ψ = ψ.secondFactorial / ψ.mean / ψ.mean)

/-- S1: κ = excessDegree / mean. -/
@[sa_shadow "SurvivalBridge.table.R48" 1] def S1 : Prop :=
  ∀ ψ : PGFData, PGFData.closureKappa ψ = PGFData.excessDegree ψ / ψ.mean
/-- S2: κ = (ψ''(1)/ψ'(1)) / ψ'(1) in primitive terms. -/
@[sa_shadow "SurvivalBridge.table.R48" 2] def S2 : Prop :=
  ∀ ψ : PGFData, PGFData.closureKappa ψ = ψ.secondFactorial / ψ.mean / ψ.mean

@[sa_ref_forward "SurvivalBridge.table.R48" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "SurvivalBridge.table.R48" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "SurvivalBridge.table.R48"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.SurvivalBridge.table_R48

/-! ## `SurvivalBridge.table.R49` -/
namespace Alignment.Shadows.SurvivalBridge.table_R49

/-
Blind text: "| 49 | Non-PT distributions: κ(t) varies, closure is approximate|"

-- AMBIGUITY: "κ(t)" is time dependence through θ(t). It is formalised as dependence on
--   θ ∈ (0,1): κ takes two different values (S1). "closure is approximate" means no constant κ
--   makes the closure identity exact on (0,1) (S2; the paper's criterion (17)).
--   "Non-PT" means not Poisson, Binomial or NB. The statement is universal over such distributions
--   with positive mean.
-- VOCAB-GAP: no pairwise model or exactness notion, and no PGFs as functions.
-/

@[sa_reference "SurvivalBridge.table.R49"]
def T : Prop := KappaVaries ∧ ClosureInexact

/-- S1: for non-PT distributions κ(θ) is not constant (two different values). -/
@[sa_shadow "SurvivalBridge.table.R49" 1] def S1 : Prop := KappaVaries
/-- S2: for non-PT distributions no constant κ makes the closure exact. -/
@[sa_shadow "SurvivalBridge.table.R49" 2] def S2 : Prop := ClosureInexact

@[sa_ref_forward "SurvivalBridge.table.R49" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "SurvivalBridge.table.R49" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "SurvivalBridge.table.R49"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.SurvivalBridge.table_R49

/-! ## `SurvivalBridge.table.R50` -/
namespace Alignment.Shadows.SurvivalBridge.table_R50

/-
Blind text: "| 50 | Volz-DSA equivalence holds for ANY degree distribution |"

-- AMBIGUITY: "equivalence" is read as
--   (a) the state-space variable change: for every value c = ψ'(θ) > 0 that a degree distribution
--       with positive mean produces, the two changes are mutual inverses (S1, S2);
--   (b) the dynamics: for every degree distribution, every Volz solution and every DSA solution
--       (paper eqs. (6)-(9)) give the same θ, x_S and x_I (S3, S4, S5).
-- AMBIGUITY: "ANY degree distribution" keeps well-posedness conditions: positive mean, and finite
--   variance so that ψ''(1) in the ODEs at t = 0 is finite (this matches Result 50).
-- VOCAB-GAP: (b) needs ODE trajectories and PGFs as functions.
-/

@[sa_reference "SurvivalBridge.table.R50"]
def T : Prop := LeftInvPos ∧ RightInvPos ∧ VolzDSATheta ∧ VolzDSASus ∧ VolzDSAInf

/-- S1: Volz → DSA → Volz is the identity (c > 0). -/
@[sa_shadow "SurvivalBridge.table.R50" 1] def S1 : Prop := LeftInvPos
/-- S2: DSA → Volz → DSA is the identity (c > 0). -/
@[sa_shadow "SurvivalBridge.table.R50" 2] def S2 : Prop := RightInvPos
/-- S3: Volz θ equals DSA x_θ, for any degree distribution. -/
@[sa_shadow "SurvivalBridge.table.R50" 3] def S3 : Prop := VolzDSATheta
/-- S4: Volz x_S equals DSA x_S, for any degree distribution. -/
@[sa_shadow "SurvivalBridge.table.R50" 4] def S4 : Prop := VolzDSASus
/-- S5: Volz x_I equals DSA x_I, for any degree distribution. -/
@[sa_shadow "SurvivalBridge.table.R50" 5] def S5 : Prop := VolzDSAInf

@[sa_ref_forward "SurvivalBridge.table.R50" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "SurvivalBridge.table.R50" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "SurvivalBridge.table.R50" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "SurvivalBridge.table.R50" 4] theorem ref_fwd4 : T → S4 := fun t => t.2.2.2.1
@[sa_ref_forward "SurvivalBridge.table.R50" 5] theorem ref_fwd5 : T → S5 := fun t => t.2.2.2.2
@[sa_complete "SurvivalBridge.table.R50"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T := ⟨s1, s2, s3, s4, s5⟩

end Alignment.Shadows.SurvivalBridge.table_R50

/-! ## `SurvivalBridge.R42` -/
namespace Alignment.Shadows.SurvivalBridge.R42

/-
Blind text: "**Result 42.** For Poisson, κ = 1. This is because ψ''(1) = κ² and ψ'(1) = κ, so
κ = κ²/κ² = 1."

-- AMBIGUITY: "κ" is overloaded. In "ψ''(1) = κ², ψ'(1) = κ" it is the Poisson mean (the argument
--   of `PGFData.poisson`). In "κ = 1" it is the closure parameter (`closureKappa`). The
--   justification clause asserts two facts about the Poisson PGF data, and these are required
--   too (S2, S3). The text evaluates at u = 1, so it is read at the data level.
-/

@[sa_reference "SurvivalBridge.R42"]
def T : Prop :=
  ∀ (κ : ℚ) (hκ : 0 < κ),
    PGFData.closureKappa (PGFData.poisson κ hκ) = 1 ∧
      (PGFData.poisson κ hκ).secondFactorial = κ ^ 2 ∧ (PGFData.poisson κ hκ).mean = κ

/-- S1: the Poisson PGF data has closure parameter 1. -/
@[sa_shadow "SurvivalBridge.R42" 1] def S1 : Prop :=
  ∀ (κ : ℚ) (hκ : 0 < κ), PGFData.closureKappa (PGFData.poisson κ hκ) = 1
/-- S2: ψ''(1) = κ² for the Poisson PGF with mean κ. -/
@[sa_shadow "SurvivalBridge.R42" 2] def S2 : Prop :=
  ∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).secondFactorial = κ ^ 2
/-- S3: ψ'(1) = κ for the Poisson PGF with mean κ. -/
@[sa_shadow "SurvivalBridge.R42" 3] def S3 : Prop :=
  ∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).mean = κ

@[sa_ref_forward "SurvivalBridge.R42" 1] theorem ref_fwd1 : T → S1 :=
  fun t κ hκ => (t κ hκ).1
@[sa_ref_forward "SurvivalBridge.R42" 2] theorem ref_fwd2 : T → S2 :=
  fun t κ hκ => (t κ hκ).2.1
@[sa_ref_forward "SurvivalBridge.R42" 3] theorem ref_fwd3 : T → S3 :=
  fun t κ hκ => (t κ hκ).2.2
@[sa_complete "SurvivalBridge.R42"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T :=
  fun κ hκ => ⟨s1 κ hκ, s2 κ hκ, s3 κ hκ⟩

end Alignment.Shadows.SurvivalBridge.R42

/-! ## `SurvivalBridge.R43a` -/
namespace Alignment.Shadows.SurvivalBridge.R43a

/-
Blind text: "**Result 43.** For Binomial(n, p), κ = (n-1)/n < 1."

This is universal over Binomial(n,p) with n ≥ 1 and p ∈ (0,1]. p > 0 is forced by the positive mean.
-- VOCAB-GAP: there is no Binomial PGF data constructor, so Binomial(n,p) is PGF data with
--   ψ'(1) = np and ψ''(1) = n(n-1)p². "κ" is the closure parameter `closureKappa`.
-/

@[sa_reference "SurvivalBridge.R43a"]
def T : Prop := BinomKappaData ∧ BinomKappaDataLt

/-- S1: κ = (n-1)/n. -/
@[sa_shadow "SurvivalBridge.R43a" 1] def S1 : Prop := BinomKappaData
/-- S2: κ < 1. -/
@[sa_shadow "SurvivalBridge.R43a" 2] def S2 : Prop := BinomKappaDataLt

@[sa_ref_forward "SurvivalBridge.R43a" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "SurvivalBridge.R43a" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "SurvivalBridge.R43a"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.SurvivalBridge.R43a

/-! ## `SurvivalBridge.R44a` -/
namespace Alignment.Shadows.SurvivalBridge.R44a

/-
Blind text: "**Result 44.** For NegBin(r, p), κ = (r+1)/r > 1."

This is universal over r > 0 and p ∈ (0,1).
-- AMBIGUITY: NB parametrisation. We use ψ'(1) = rp/(1-p) and ψ''(1) = r(r+1)p²/(1-p)²; the other
--   convention is p ↦ 1-p, which is equivalent under the universal quantifier.
-- VOCAB-GAP: there is no NB PGF data constructor, so NB PGF data is given through its moments.
-/

@[sa_reference "SurvivalBridge.R44a"]
def T : Prop := NegBinKappaData ∧ NegBinKappaDataGt

/-- S1: κ = (r+1)/r. -/
@[sa_shadow "SurvivalBridge.R44a" 1] def S1 : Prop := NegBinKappaData
/-- S2: κ > 1. -/
@[sa_shadow "SurvivalBridge.R44a" 2] def S2 : Prop := NegBinKappaDataGt

@[sa_ref_forward "SurvivalBridge.R44a" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "SurvivalBridge.R44a" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "SurvivalBridge.R44a"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.SurvivalBridge.R44a

/-! ## `SurvivalBridge.R45a` -/
namespace Alignment.Shadows.SurvivalBridge.R45a

/-
Blind text: "**Result 45.** The round-trip Volz → DSA → Volz is the identity."

This holds for every Volz state and every value c = ψ'(θ) ≠ 0, the condition the DSA → Volz map
needs. The identity is split into its three components.
-/

@[sa_reference "SurvivalBridge.R45a"]
def T : Prop := ∀ (c : ℚ) (h : c ≠ 0) (v : VolzState), dsaToVolz (volzToDSA v c) c h = v

/-- S1: the θ component survives the round trip. -/
@[sa_shadow "SurvivalBridge.R45a" 1] def S1 : Prop :=
  ∀ (c : ℚ) (h : c ≠ 0) (v : VolzState), (dsaToVolz (volzToDSA v c) c h).θ = v.θ
/-- S2: the p_I component survives the round trip. -/
@[sa_shadow "SurvivalBridge.R45a" 2] def S2 : Prop :=
  ∀ (c : ℚ) (h : c ≠ 0) (v : VolzState), (dsaToVolz (volzToDSA v c) c h).p_I = v.p_I
/-- S3: the p_S component survives the round trip. -/
@[sa_shadow "SurvivalBridge.R45a" 3] def S3 : Prop :=
  ∀ (c : ℚ) (h : c ≠ 0) (v : VolzState), (dsaToVolz (volzToDSA v c) c h).p_S = v.p_S

@[sa_ref_forward "SurvivalBridge.R45a" 1] theorem ref_fwd1 : T → S1 :=
  fun t c h v => congrArg VolzState.θ (t c h v)
@[sa_ref_forward "SurvivalBridge.R45a" 2] theorem ref_fwd2 : T → S2 :=
  fun t c h v => congrArg VolzState.p_I (t c h v)
@[sa_ref_forward "SurvivalBridge.R45a" 3] theorem ref_fwd3 : T → S3 :=
  fun t c h v => congrArg VolzState.p_S (t c h v)
@[sa_complete "SurvivalBridge.R45a"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := by
  intro c h v
  have e1 := s1 c h v
  have e2 := s2 c h v
  have e3 := s3 c h v
  revert e1 e2 e3
  generalize dsaToVolz (volzToDSA v c) c h = w
  cases w
  cases v
  intro e1 e2 e3
  dsimp only at e1 e2 e3
  subst e1 e2 e3
  rfl

end Alignment.Shadows.SurvivalBridge.R45a

/-! ## `SurvivalBridge.R47b` -/
namespace Alignment.Shadows.SurvivalBridge.R47b

/-
Blind text: "The proof is that the Poisson PGF ψ(u) = e^{λ(u-1)} satisfies ψ''·ψ/(ψ')² = 1
identically, which eliminates all network-structure terms."

-- AMBIGUITY: "identically" means for every real u, since ψ is given by a formula on ℝ.
--   "which eliminates all network-structure terms" is an explanatory gloss and is not formalised.
-- VOCAB-GAP: PGF data cannot express ψ(u) for u ≠ 1 or derivatives in u.
-/

@[sa_reference "SurvivalBridge.R47b"]
def T : Prop := ∀ ℓ : ℝ, 0 < ℓ → ∀ u : ℝ, kappaAt (poissonPGF ℓ) u = 1

/-- S1: ψ''ψ/(ψ')² = 1 at every u, for the Poisson PGF with any λ > 0. -/
@[sa_shadow "SurvivalBridge.R47b" 1] def S1 : Prop :=
  ∀ ℓ : ℝ, 0 < ℓ → ∀ u : ℝ, kappaAt (poissonPGF ℓ) u = 1

@[sa_ref_forward "SurvivalBridge.R47b" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SurvivalBridge.R47b"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SurvivalBridge.R47b

/-! ## `SurvivalBridge.R48a` -/
namespace Alignment.Shadows.SurvivalBridge.R48a

/-
Blind text: "**Result 48.** The closure parameter κ equals the dispersion-scaled ratio:
κ = secondFactorial / mean²."

-- AMBIGUITY: "dispersion-scaled ratio" is read as a name for the formula after the colon. No
--   separate dispersion-index identity is required.
-/

@[sa_reference "SurvivalBridge.R48a"]
def T : Prop := ∀ ψ : PGFData, PGFData.closureKappa ψ = ψ.secondFactorial / ψ.mean ^ 2

/-- S1: κ = ψ''(1)/ψ'(1)² for all PGF data. -/
@[sa_shadow "SurvivalBridge.R48a" 1] def S1 : Prop :=
  ∀ ψ : PGFData, PGFData.closureKappa ψ = ψ.secondFactorial / ψ.mean ^ 2

@[sa_ref_forward "SurvivalBridge.R48a" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SurvivalBridge.R48a"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SurvivalBridge.R48a

/-! ## `SurvivalBridge.R50a` -/
namespace Alignment.Shadows.SurvivalBridge.R50a

/-
Blind text: "**Result 50.** The Volz ↔ DSA equivalence holds for ANY degree distribution with finite
variance — not just PT distributions."

-- AMBIGUITY: "equivalence" is read as for table.R50:
--   (a) the variable changes are mutual inverses for every c = ψ'(θ) > 0 (S1, S2);
--   (b) for every degree distribution with finite variance (and positive mean), Volz and DSA
--       solutions (paper eqs. (6)-(9)) agree in θ, x_S and x_I (S3, S4, S5).
--   "not just PT distributions" is emphasis. The universal statement contains no PT hypothesis.
-- VOCAB-GAP: (b) needs ODE trajectories and PGFs as functions.
-/

@[sa_reference "SurvivalBridge.R50a"]
def T : Prop := LeftInvPos ∧ RightInvPos ∧ VolzDSATheta ∧ VolzDSASus ∧ VolzDSAInf

/-- S1: Volz → DSA → Volz is the identity (c > 0). -/
@[sa_shadow "SurvivalBridge.R50a" 1] def S1 : Prop := LeftInvPos
/-- S2: DSA → Volz → DSA is the identity (c > 0). -/
@[sa_shadow "SurvivalBridge.R50a" 2] def S2 : Prop := RightInvPos
/-- S3: Volz θ equals DSA x_θ (any finite-variance degree distribution). -/
@[sa_shadow "SurvivalBridge.R50a" 3] def S3 : Prop := VolzDSATheta
/-- S4: Volz x_S equals DSA x_S. -/
@[sa_shadow "SurvivalBridge.R50a" 4] def S4 : Prop := VolzDSASus
/-- S5: Volz x_I equals DSA x_I. -/
@[sa_shadow "SurvivalBridge.R50a" 5] def S5 : Prop := VolzDSAInf

@[sa_ref_forward "SurvivalBridge.R50a" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "SurvivalBridge.R50a" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "SurvivalBridge.R50a" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "SurvivalBridge.R50a" 4] theorem ref_fwd4 : T → S4 := fun t => t.2.2.2.1
@[sa_ref_forward "SurvivalBridge.R50a" 5] theorem ref_fwd5 : T → S5 := fun t => t.2.2.2.2
@[sa_complete "SurvivalBridge.R50a"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T := ⟨s1, s2, s3, s4, s5⟩

end Alignment.Shadows.SurvivalBridge.R50a

/-! ## Shared notions for the re-authored SurvivalBridge blocks (blind)

Not registered; inlined by the audit. PGFs are real functions `ψ : ℝ → ℝ`; the closure ratio is
`κ(θ) = ψ″(θ)ψ(θ)/ψ′(θ)²`. Family records (moment data of the text's PT families):
binomial(n, p): ψ′(1) = np, ψ″(1) = n(n−1)p²; negative binomial(r, c) with
ψ(u) = (c/(1 − (1−c)u))^r: ψ′(1) = r(1−c)/c, ψ″(1) = r(r+1)((1−c)/c)². The Poisson DSA system is
the DSA model of Kiss, Kenah & Rempała (2023, §2.4, `papers/s00285-023-01967-9.md`) for
ψ(u) = e^{μ(u−1)}, with the paper's initial conditions x_S(0) = x_θ(0) = 1, x_SS(0) = μ,
x_SI(0) = μρ. -/
namespace Alignment.Shadows.SurvivalBridge.Shared2

/-- The closure ratio `κ(θ) = ψ″(θ)ψ(θ)/ψ′(θ)²` of a PGF. -/
def kappaFn (ψ : ℝ → ℝ) (θ : ℝ) : ℝ := iteratedDeriv 2 ψ θ * ψ θ / deriv ψ θ ^ 2
/-- The non-PT law `ψ(u) = (1 + u²)/2`. -/
def psiMix (u : ℝ) : ℝ := (1 + u ^ 2) / 2
/-- Binomial PGF `(1 − p + p u)^n`. -/
def psiBin (n : ℕ) (p : ℝ) (u : ℝ) : ℝ := (1 - p + p * u) ^ n
/-- Negative binomial PGF `(c/(1 − (1−c)u))^r`. -/
def psiNB (r c : ℝ) (u : ℝ) : ℝ := (c / (1 - (1 - c) * u)) ^ r

/-- Moment record of Binomial(n, p). -/
def binRec (n : ℕ) (p : ℚ) (hn : 1 ≤ n) (hp : 0 < p) : PGFData :=
  ⟨(n : ℚ) * p, (n : ℚ) * ((n : ℚ) - 1) * p ^ 2,
    by
      have h1 : (1 : ℚ) ≤ n := by exact_mod_cast hn
      positivity,
    by
      have h1 : (1 : ℚ) ≤ n := by exact_mod_cast hn
      have h2 : (0 : ℚ) ≤ (n : ℚ) - 1 := by linarith
      positivity⟩
/-- Moment record of NegBin(r, c). -/
def nbRec (r c : ℚ) (hr : 0 < r) (hc0 : 0 < c) (hc1 : c < 1) : PGFData :=
  ⟨r * (1 - c) / c, r * (r + 1) * ((1 - c) / c) ^ 2,
    by
      have h : 0 < 1 - c := by linarith
      positivity,
    by
      have h : 0 < 1 - c := by linarith
      positivity⟩

/-- ψ′ and ψ″ of the Poisson PGF `e^{μ(u−1)}`. -/
def dpsiP (μ : ℝ) (u : ℝ) : ℝ := μ * Real.exp (μ * (u - 1))
def ddpsiP (μ : ℝ) (u : ℝ) : ℝ := μ ^ 2 * Real.exp (μ * (u - 1))

/-- `(x_θ, x_SS, x_SI, x_S)` solves the DSA model for the Poisson PGF with mean μ. -/
def IsPoisDSA (β γ μ : ℝ) (xθ xSS xSI xS : ℝ → ℝ) : Prop :=
  ∀ t : ℝ,
    HasDerivAt xθ (-β * xSI t / dpsiP μ (xθ t)) t ∧
    HasDerivAt xSS (-2 * β * xSI t * xSS t * ddpsiP μ (xθ t) / dpsiP μ (xθ t) ^ 2) t ∧
    HasDerivAt xSI
      (xSI t * (β * (xSS t - xSI t) * ddpsiP μ (xθ t) / dpsiP μ (xθ t) ^ 2 - (β + γ))) t ∧
    HasDerivAt xS (-β * xSI t) t

/-- For Poisson degrees (κ = 1) the DSA survival function satisfies
`−Ṡ = β̃(S − S²) + γ̃ S log S + ρ̃ S` with β̃ = μβ, γ̃ = β + γ, ρ̃ = βμρ. -/
def PoisDSASurvival : Prop :=
  ∀ (p : SIRParams) (μ : ℚ) (ρ : ℝ) (xθ xSS xSI xS : ℝ → ℝ), 0 < μ → 0 ≤ ρ →
    IsPoisDSA (p.β : ℝ) (p.γ : ℝ) (μ : ℝ) xθ xSS xSI xS →
    xS 0 = 1 → xθ 0 = 1 → xSS 0 = (μ : ℝ) → xSI 0 = (μ : ℝ) * ρ →
    ∀ t : ℝ, HasDerivAt xS
      (-(((μ : ℝ) * p.β) * (xS t - xS t ^ 2) + ((p.β : ℝ) + p.γ) * xS t * Real.log (xS t) +
        (p.β : ℝ) * μ * ρ * xS t)) t

/-- The classical mass-action SIR survival equation (KhudaBukhsh et al. 2020): for mass-action
SIR with rates b, g, S(0) = 1 and I(0) = r, `−Ṡ = b(S − S²) + g S log S + b r S`. -/
def MassActionSurvival : Prop :=
  ∀ (b g r : ℝ) (S I : ℝ → ℝ), 0 < b → 0 < g → 0 ≤ r → S 0 = 1 → I 0 = r →
    (∀ t, HasDerivAt S (-b * S t * I t) t) → (∀ t, HasDerivAt I (b * S t * I t - g * I t) t) →
    (∀ t, 0 < S t) →
    ∀ t : ℝ, HasDerivAt S (-(b * (S t - S t ^ 2) + g * S t * Real.log (S t) + b * r * S t)) t

/-- The chain rule of Result 46: with `S = ψ(θ)`, `θ̇ = −β p_I θ` and `x_SI = p_I θ ψ′(θ)`,
`Ṡ = −β x_SI`. -/
def ChainRule46 : Prop :=
  ∀ (ψ ψ' : ℝ → ℝ) (β : ℝ) (θ pI : ℝ → ℝ) (t : ℝ), HasDerivAt ψ (ψ' (θ t)) (θ t) →
    HasDerivAt θ (-β * pI t * θ t) t →
    HasDerivAt (fun s => ψ (θ s)) (-β * (pI t * θ t * ψ' (θ t))) t

end Alignment.Shadows.SurvivalBridge.Shared2

/-! ## `SurvivalBridge.R45b` (re-authored blind)

Text: "Together with `dsa_volz_roundtrip`, the variable change is a bijection of state spaces for
every nonzero scalar factor."

S1: `v ↦ volzToDSA v c` is bijective for every `c ≠ 0`; S2, S3: its inverse is `dsaToVolz · c`
(both round trips). -/
namespace Alignment.Shadows.SurvivalBridge.R45b

@[sa_reference "SurvivalBridge.R45b"]
def T : Prop :=
  (∀ c : ℚ, c ≠ 0 → Function.Bijective (fun v : VolzState => volzToDSA v c)) ∧
  (∀ (c : ℚ) (hc : c ≠ 0), Function.LeftInverse (fun x => dsaToVolz x c hc) (fun v => volzToDSA v c)) ∧
  (∀ (c : ℚ) (hc : c ≠ 0), Function.RightInverse (fun x => dsaToVolz x c hc) (fun v => volzToDSA v c))

/-- S1: the variable change is a bijection for every nonzero factor. -/
@[sa_shadow "SurvivalBridge.R45b" 1]
def S1 : Prop := ∀ c : ℚ, c ≠ 0 → Function.Bijective (fun v : VolzState => volzToDSA v c)
/-- S2: Volz → DSA → Volz is the identity. -/
@[sa_shadow "SurvivalBridge.R45b" 2]
def S2 : Prop :=
  ∀ (c : ℚ) (hc : c ≠ 0), Function.LeftInverse (fun x => dsaToVolz x c hc) (fun v => volzToDSA v c)
/-- S3: DSA → Volz → DSA is the identity. -/
@[sa_shadow "SurvivalBridge.R45b" 3]
def S3 : Prop :=
  ∀ (c : ℚ) (hc : c ≠ 0), Function.RightInverse (fun x => dsaToVolz x c hc) (fun v => volzToDSA v c)

@[sa_ref_forward "SurvivalBridge.R45b" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "SurvivalBridge.R45b" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "SurvivalBridge.R45b" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "SurvivalBridge.R45b"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.SurvivalBridge.R45b

/-! ## `SurvivalBridge.R46b` (blind)

Text: "For any PGF, if we define S = ψ(θ) and differentiate, with x_{SI} = p_I · θ · ψ'(θ) as in
Kiss, Kenah & Rempała (2023, App. B): dS/dt = ψ'(θ) · dθ/dt = ψ'(θ) · (-β·p_I·θ) = -β · x_{SI} So
the DSA equation ẋ_S = -β·x_{SI} is the chain rule applied to S = ψ(θ). This chain-rule
computation is not formalised here."

The chain-rule computation itself (Shared2.ChainRule46), for any differentiable ψ; the remark that
it is not formalised describes the library. -/
namespace Alignment.Shadows.SurvivalBridge.R46b

open Alignment.Shadows.SurvivalBridge.Shared2

@[sa_reference "SurvivalBridge.R46b"]
def T : Prop := ChainRule46

/-- S1: `d/dt ψ(θ) = −β x_SI` with `x_SI = p_I θ ψ′(θ)`. -/
@[sa_shadow "SurvivalBridge.R46b" 1]
def S1 : Prop := ChainRule46

@[sa_ref_forward "SurvivalBridge.R46b" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SurvivalBridge.R46b"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SurvivalBridge.R46b

/-! ## `SurvivalBridge.R46c` (re-authored blind)

Text: "Here we prove the algebraic identity that, for Poisson degrees, the EBCM R₀ T·ψ''(1)/ψ'(1)
equals T·μ, where μ = mean degree (the `nodeModel` value). The DSA model is equivalent to Volz's for
every degree law, so its R₀ is also T·ψ''(1)/ψ'(1)."

T = β/(β+γ). S1: for the Poisson record, `T·ψ''(1)/ψ'(1) = T·μ`; S2: `T·μ` is the `nodeModel` R₀;
S3: the EBCM R₀ (`edgeModel`) is `T·ψ''(1)/ψ'(1)`. The DSA model has no R₀ in the vocabulary; the
last sentence is not formalised. -/
namespace Alignment.Shadows.SurvivalBridge.R46c

@[sa_reference "SurvivalBridge.R46c"]
def T : Prop :=
  (∀ (p : SIRParams) (μ : ℚ) (hμ : 0 < μ),
      p.β / (p.β + p.γ) *
          ((PGFData.poisson μ hμ).secondFactorial / (PGFData.poisson μ hμ).mean) =
        p.β / (p.β + p.γ) * μ) ∧
  (∀ (p : SIRParams) (μ : ℚ), (nodeModel p μ).R0 = p.β / (p.β + p.γ) * μ) ∧
  (∀ (p : SIRParams) (ψ : PGFData),
      (edgeModel p ψ).R0 = p.β / (p.β + p.γ) * (ψ.secondFactorial / ψ.mean))

/-- S1: for Poisson degrees, `T·ψ''(1)/ψ'(1) = T·μ`. -/
@[sa_shadow "SurvivalBridge.R46c" 1]
def S1 : Prop :=
  ∀ (p : SIRParams) (μ : ℚ) (hμ : 0 < μ),
    p.β / (p.β + p.γ) * ((PGFData.poisson μ hμ).secondFactorial / (PGFData.poisson μ hμ).mean) =
      p.β / (p.β + p.γ) * μ
/-- S2: `T·μ` is the node model's R₀. -/
@[sa_shadow "SurvivalBridge.R46c" 2]
def S2 : Prop := ∀ (p : SIRParams) (μ : ℚ), (nodeModel p μ).R0 = p.β / (p.β + p.γ) * μ
/-- S3: the EBCM R₀ is `T·ψ''(1)/ψ'(1)`. -/
@[sa_shadow "SurvivalBridge.R46c" 3]
def S3 : Prop :=
  ∀ (p : SIRParams) (ψ : PGFData),
    (edgeModel p ψ).R0 = p.β / (p.β + p.γ) * (ψ.secondFactorial / ψ.mean)

@[sa_ref_forward "SurvivalBridge.R46c" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "SurvivalBridge.R46c" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "SurvivalBridge.R46c" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "SurvivalBridge.R46c"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.SurvivalBridge.R46c

/-! ## `SurvivalBridge.R47a` (re-authored blind)

Text: "**Result 47.** For Poisson networks (κ=1), the DSA survival equation has the form of the
classical mass-action SIR survival equation, with rescaled rates. From Eq (33) of the paper, with
κ=1: -dS/dt = β̃(S - S²) + γ̃·S·log(S) + ρ̃·S This has the form of the mass-action SIR survival
equation of KhudaBukhsh et al. (2020), with β̃ = μβ, γ̃ = β + γ and ρ̃ = βμρ. The Lean theorem proves
only that the Poisson record has closureKappa = 1."

S1: Poisson ⇒ κ = 1 (`closureKappa`); S2: the Poisson DSA survival function satisfies Eq (33) with
κ = 1 and the rescaled rates (Shared2.PoisDSASurvival); S3: that is the mass-action SIR survival
equation (Shared2.MassActionSurvival). The last sentence describes the implementation. -/
namespace Alignment.Shadows.SurvivalBridge.R47a

open Alignment.Shadows.SurvivalBridge.Shared2

@[sa_reference "SurvivalBridge.R47a"]
def T : Prop :=
  (∀ (μ : ℚ) (hμ : 0 < μ), (PGFData.poisson μ hμ).closureKappa = 1) ∧ PoisDSASurvival ∧
    MassActionSurvival

/-- S1: the Poisson record has κ = 1. -/
@[sa_shadow "SurvivalBridge.R47a" 1]
def S1 : Prop := ∀ (μ : ℚ) (hμ : 0 < μ), (PGFData.poisson μ hμ).closureKappa = 1
/-- S2: the Poisson DSA survival equation with rescaled rates. -/
@[sa_shadow "SurvivalBridge.R47a" 2]
def S2 : Prop := PoisDSASurvival
/-- S3: the mass-action SIR survival equation has the same form. -/
@[sa_shadow "SurvivalBridge.R47a" 3]
def S3 : Prop := MassActionSurvival

@[sa_ref_forward "SurvivalBridge.R47a" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "SurvivalBridge.R47a" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "SurvivalBridge.R47a" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "SurvivalBridge.R47a"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.SurvivalBridge.R47a

/-! ## `SurvivalBridge.R48c` (blind)

Text: "For a PT law (κ(θ) constant), the value of κ determines the family: * κ < 1: Binomial(n, p)
with n = 1/(1-κ); this needs 1/(1-κ) ∈ ℕ, so κ ∈ [0, 1) is realised only for κ = (n-1)/n * κ = 1:
Poisson(λ) * κ > 1: NegBin(r, p) with r = 1/(κ-1)"

Read at the level of the families' moment records (`closureKappa`): S1, S2: binomial records have
κ < 1 and n = 1/(1−κ); S3: Poisson records have κ = 1; S4, S5: negative-binomial records have κ > 1
and r = 1/(κ−1); S6: a value κ ∈ [0, 1) of a binomial record is of the form (n−1)/n. -/
namespace Alignment.Shadows.SurvivalBridge.R48c

open Alignment.Shadows.SurvivalBridge.Shared2

@[sa_reference "SurvivalBridge.R48c"]
def T : Prop :=
  (∀ (n : ℕ) (p : ℚ) (hn : 1 ≤ n) (hp : 0 < p), p ≤ 1 → (binRec n p hn hp).closureKappa < 1) ∧
  (∀ (n : ℕ) (p : ℚ) (hn : 1 ≤ n) (hp : 0 < p), p ≤ 1 →
      (n : ℚ) = 1 / (1 - (binRec n p hn hp).closureKappa)) ∧
  (∀ (lam : ℚ) (h : 0 < lam), (PGFData.poisson lam h).closureKappa = 1) ∧
  (∀ (r c : ℚ) (hr : 0 < r) (hc0 : 0 < c) (hc1 : c < 1), 1 < (nbRec r c hr hc0 hc1).closureKappa) ∧
  (∀ (r c : ℚ) (hr : 0 < r) (hc0 : 0 < c) (hc1 : c < 1),
      r = 1 / ((nbRec r c hr hc0 hc1).closureKappa - 1)) ∧
  (∀ κ : ℚ, 0 ≤ κ → κ < 1 →
      (∃ (n : ℕ) (p : ℚ) (hn : 1 ≤ n) (hp : 0 < p), p ≤ 1 ∧ (binRec n p hn hp).closureKappa = κ) →
      ∃ n : ℕ, 1 ≤ n ∧ κ = ((n : ℚ) - 1) / n)

/-- S1: binomial records have κ < 1. -/
@[sa_shadow "SurvivalBridge.R48c" 1]
def S1 : Prop :=
  ∀ (n : ℕ) (p : ℚ) (hn : 1 ≤ n) (hp : 0 < p), p ≤ 1 → (binRec n p hn hp).closureKappa < 1
/-- S2: κ determines n = 1/(1−κ). -/
@[sa_shadow "SurvivalBridge.R48c" 2]
def S2 : Prop :=
  ∀ (n : ℕ) (p : ℚ) (hn : 1 ≤ n) (hp : 0 < p), p ≤ 1 →
    (n : ℚ) = 1 / (1 - (binRec n p hn hp).closureKappa)
/-- S3: Poisson records have κ = 1. -/
@[sa_shadow "SurvivalBridge.R48c" 3]
def S3 : Prop := ∀ (lam : ℚ) (h : 0 < lam), (PGFData.poisson lam h).closureKappa = 1
/-- S4: negative-binomial records have κ > 1. -/
@[sa_shadow "SurvivalBridge.R48c" 4]
def S4 : Prop :=
  ∀ (r c : ℚ) (hr : 0 < r) (hc0 : 0 < c) (hc1 : c < 1), 1 < (nbRec r c hr hc0 hc1).closureKappa
/-- S5: κ determines r = 1/(κ−1). -/
@[sa_shadow "SurvivalBridge.R48c" 5]
def S5 : Prop :=
  ∀ (r c : ℚ) (hr : 0 < r) (hc0 : 0 < c) (hc1 : c < 1),
    r = 1 / ((nbRec r c hr hc0 hc1).closureKappa - 1)
/-- S6: binomial values of κ ∈ [0, 1) are of the form (n−1)/n. -/
@[sa_shadow "SurvivalBridge.R48c" 6]
def S6 : Prop :=
  ∀ κ : ℚ, 0 ≤ κ → κ < 1 →
    (∃ (n : ℕ) (p : ℚ) (hn : 1 ≤ n) (hp : 0 < p), p ≤ 1 ∧ (binRec n p hn hp).closureKappa = κ) →
    ∃ n : ℕ, 1 ≤ n ∧ κ = ((n : ℚ) - 1) / n

@[sa_ref_forward "SurvivalBridge.R48c" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "SurvivalBridge.R48c" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "SurvivalBridge.R48c" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "SurvivalBridge.R48c" 4] theorem ref_fwd4 : T → S4 := fun t => t.2.2.2.1
@[sa_ref_forward "SurvivalBridge.R48c" 5] theorem ref_fwd5 : T → S5 := fun t => t.2.2.2.2.1
@[sa_ref_forward "SurvivalBridge.R48c" 6] theorem ref_fwd6 : T → S6 := fun t => t.2.2.2.2.2
@[sa_complete "SurvivalBridge.R48c"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) : T :=
  ⟨s1, s2, s3, s4, s5, s6⟩

end Alignment.Shadows.SurvivalBridge.R48c

/-! ## `SurvivalBridge.R49a` (re-authored blind)

Text: "**Result 49.** Some degree record has closure constant κ(1) ≠ 1 and dispersion index ≠ 1. A
two-moment record cannot show that a law is non-PT. For a non-PT law such as ψ(u) = (1 + u²)/2,
κ(θ) = (1 + θ²)/(2θ²) varies with θ, making the pairwise closure approximate rather than exact."

-- AMBIGUITY: "A two-moment record cannot show that a law is non-PT" is read through the example
the text gives: the non-PT law (1 + u²)/2 has the same record (ψ′(1), ψ″(1)) = (1, 1) as the PT
law Poisson(1) (S2). The exactness of the pairwise closure needs the closed model and is not
formalised. -/
namespace Alignment.Shadows.SurvivalBridge.R49a

open Alignment.Shadows.SurvivalBridge.Shared2

@[sa_reference "SurvivalBridge.R49a"]
def T : Prop :=
  (∃ ψ : PGFData, ψ.closureKappa ≠ 1 ∧ ψ.dispersionIndex ≠ 1) ∧
  (((PGFData.poisson 1 one_pos).mean : ℝ) = deriv psiMix 1 ∧
      ((PGFData.poisson 1 one_pos).secondFactorial : ℝ) = iteratedDeriv 2 psiMix 1) ∧
  (∀ θ : ℝ, 0 < θ → kappaFn psiMix θ = (1 + θ ^ 2) / (2 * θ ^ 2)) ∧
  (∃ θ₁ θ₂ : ℝ, 0 < θ₁ ∧ θ₁ ≤ 1 ∧ 0 < θ₂ ∧ θ₂ ≤ 1 ∧ kappaFn psiMix θ₁ ≠ kappaFn psiMix θ₂)

/-- S1: some record has κ(1) ≠ 1 and dispersion index ≠ 1. -/
@[sa_shadow "SurvivalBridge.R49a" 1]
def S1 : Prop := ∃ ψ : PGFData, ψ.closureKappa ≠ 1 ∧ ψ.dispersionIndex ≠ 1
/-- S2: the non-PT law (1 + u²)/2 has the record of the PT law Poisson(1). -/
@[sa_shadow "SurvivalBridge.R49a" 2]
def S2 : Prop :=
  ((PGFData.poisson 1 one_pos).mean : ℝ) = deriv psiMix 1 ∧
    ((PGFData.poisson 1 one_pos).secondFactorial : ℝ) = iteratedDeriv 2 psiMix 1
/-- S3: its closure ratio is κ(θ) = (1 + θ²)/(2θ²). -/
@[sa_shadow "SurvivalBridge.R49a" 3]
def S3 : Prop := ∀ θ : ℝ, 0 < θ → kappaFn psiMix θ = (1 + θ ^ 2) / (2 * θ ^ 2)
/-- S4: κ(θ) varies with θ on (0, 1]. -/
@[sa_shadow "SurvivalBridge.R49a" 4]
def S4 : Prop :=
  ∃ θ₁ θ₂ : ℝ, 0 < θ₁ ∧ θ₁ ≤ 1 ∧ 0 < θ₂ ∧ θ₂ ≤ 1 ∧ kappaFn psiMix θ₁ ≠ kappaFn psiMix θ₂

@[sa_ref_forward "SurvivalBridge.R49a" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "SurvivalBridge.R49a" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "SurvivalBridge.R49a" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "SurvivalBridge.R49a" 4] theorem ref_fwd4 : T → S4 := fun t => t.2.2.2
@[sa_complete "SurvivalBridge.R49a"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.SurvivalBridge.R49a

/-! ## `SurvivalBridge.R49b` (blind)

Text: "Witness: the record mean 10, ψ''(1) = 200 (κ(1) = 2, dispersion 11). It is the record of the
geometric law (NegBin with r = 1), which is PT; the bimodal law with 80% degree 4 and 20% degree 34
has mean 10 but ψ''(1) = 234."

The geometric law with mean 10 has PGF `ψ(u) = (1/11)/(1 − (10/11)u)`; the bimodal law has PGF
`ψ(u) = (4/5)u⁴ + (1/5)u³⁴`. "PT" = constant closure ratio on [0, 1]. -/
namespace Alignment.Shadows.SurvivalBridge.R49b

open Alignment.Shadows.SurvivalBridge.Shared2

/-- The witness record: mean 10, ψ''(1) = 200. -/
def wit : PGFData := ⟨10, 200, by norm_num, by norm_num⟩
/-- The geometric PGF with mean 10. -/
def psiGeo (u : ℝ) : ℝ := (1 / 11) / (1 - (10 / 11) * u)
/-- The bimodal PGF: 80% degree 4, 20% degree 34. -/
def psiBi (u : ℝ) : ℝ := (4 / 5) * u ^ 4 + (1 / 5) * u ^ 34

@[sa_reference "SurvivalBridge.R49b"]
def T : Prop :=
  wit.closureKappa = 2 ∧ wit.dispersionIndex = 11 ∧ deriv psiGeo 1 = 10 ∧
    iteratedDeriv 2 psiGeo 1 = 200 ∧ (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → kappaFn psiGeo θ = 2) ∧
    deriv psiBi 1 = 10 ∧ iteratedDeriv 2 psiBi 1 = 234

/-- S1: the witness has κ(1) = 2. -/
@[sa_shadow "SurvivalBridge.R49b" 1]
def S1 : Prop := wit.closureKappa = 2
/-- S2: the witness has dispersion index 11. -/
@[sa_shadow "SurvivalBridge.R49b" 2]
def S2 : Prop := wit.dispersionIndex = 11
/-- S3: the geometric law has mean 10. -/
@[sa_shadow "SurvivalBridge.R49b" 3]
def S3 : Prop := deriv psiGeo 1 = 10
/-- S4: the geometric law has ψ''(1) = 200. -/
@[sa_shadow "SurvivalBridge.R49b" 4]
def S4 : Prop := iteratedDeriv 2 psiGeo 1 = 200
/-- S5: the geometric law is PT (constant closure ratio 2). -/
@[sa_shadow "SurvivalBridge.R49b" 5]
def S5 : Prop := ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → kappaFn psiGeo θ = 2
/-- S6: the bimodal law has mean 10. -/
@[sa_shadow "SurvivalBridge.R49b" 6]
def S6 : Prop := deriv psiBi 1 = 10
/-- S7: the bimodal law has ψ''(1) = 234. -/
@[sa_shadow "SurvivalBridge.R49b" 7]
def S7 : Prop := iteratedDeriv 2 psiBi 1 = 234

@[sa_ref_forward "SurvivalBridge.R49b" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "SurvivalBridge.R49b" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "SurvivalBridge.R49b" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "SurvivalBridge.R49b" 4] theorem ref_fwd4 : T → S4 := fun t => t.2.2.2.1
@[sa_ref_forward "SurvivalBridge.R49b" 5] theorem ref_fwd5 : T → S5 := fun t => t.2.2.2.2.1
@[sa_ref_forward "SurvivalBridge.R49b" 6] theorem ref_fwd6 : T → S6 := fun t => t.2.2.2.2.2.1
@[sa_ref_forward "SurvivalBridge.R49b" 7] theorem ref_fwd7 : T → S7 := fun t => t.2.2.2.2.2.2
@[sa_complete "SurvivalBridge.R49b"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) (s7 : S7) : T :=
  ⟨s1, s2, s3, s4, s5, s6, s7⟩

end Alignment.Shadows.SurvivalBridge.R49b

/-! ## `SurvivalBridge.R50b` (re-authored blind)

Text: "The variable change x_{SI} = p_I · θ · ψ'(θ) is well-defined and invertible whenever
θ·ψ'(θ) > 0,"

The variable change is `volzToDSA` with the factor `θ·ψ′(θ)` (ψ′(θ) a value `d`): S1 its x_SI
component; S2, S3 the two round trips when `θ·ψ′(θ) > 0`. -/
namespace Alignment.Shadows.SurvivalBridge.R50b

@[sa_reference "SurvivalBridge.R50b"]
def T : Prop :=
  (∀ (v : VolzState) (d : ℚ), (volzToDSA v (v.θ * d)).x_SI = v.p_I * (v.θ * d)) ∧
  (∀ (v : VolzState) (d : ℚ) (h : 0 < v.θ * d),
      dsaToVolz (volzToDSA v (v.θ * d)) (v.θ * d) h.ne' = v) ∧
  (∀ (x : DSAState) (d : ℚ) (h : 0 < x.x_θ * d),
      volzToDSA (dsaToVolz x (x.x_θ * d) h.ne') (x.x_θ * d) = x)

/-- S1: `x_SI = p_I · θ · ψ′(θ)`. -/
@[sa_shadow "SurvivalBridge.R50b" 1]
def S1 : Prop := ∀ (v : VolzState) (d : ℚ), (volzToDSA v (v.θ * d)).x_SI = v.p_I * (v.θ * d)
/-- S2: Volz → DSA → Volz is the identity when `θψ′(θ) > 0`. -/
@[sa_shadow "SurvivalBridge.R50b" 2]
def S2 : Prop :=
  ∀ (v : VolzState) (d : ℚ) (h : 0 < v.θ * d), dsaToVolz (volzToDSA v (v.θ * d)) (v.θ * d) h.ne' = v
/-- S3: DSA → Volz → DSA is the identity when `x_θ ψ′(x_θ) > 0`. -/
@[sa_shadow "SurvivalBridge.R50b" 3]
def S3 : Prop :=
  ∀ (x : DSAState) (d : ℚ) (h : 0 < x.x_θ * d),
    volzToDSA (dsaToVolz x (x.x_θ * d) h.ne') (x.x_θ * d) = x

@[sa_ref_forward "SurvivalBridge.R50b" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "SurvivalBridge.R50b" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "SurvivalBridge.R50b" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "SurvivalBridge.R50b"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.SurvivalBridge.R50b

/-! ## `SurvivalBridge.R50e` (re-authored blind)

Text: "This is formalised here only as the round trip of Result 45 with the scalar factor
ψ'(1) = mean degree, so it needs only ψ'(1) ≠ 0 and no condition on κ. It is a statement about one
linear rescaling, not about the ODE systems."

The mathematical content: for every degree record (no condition on κ), the DSA → Volz → DSA round
trip with factor ψ'(1) = `mean` is the identity. The rest describes the formalisation. -/
namespace Alignment.Shadows.SurvivalBridge.R50e

@[sa_reference "SurvivalBridge.R50e"]
def T : Prop :=
  ∀ (ψ : PGFData) (x : DSAState), volzToDSA (dsaToVolz x ψ.mean ψ.mean_pos.ne') ψ.mean = x

/-- S1: the round trip with factor ψ'(1) is the identity for every record. -/
@[sa_shadow "SurvivalBridge.R50e" 1]
def S1 : Prop :=
  ∀ (ψ : PGFData) (x : DSAState), volzToDSA (dsaToVolz x ψ.mean ψ.mean_pos.ne') ψ.mean = x

@[sa_ref_forward "SurvivalBridge.R50e" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SurvivalBridge.R50e"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SurvivalBridge.R50e

/-! ## `SurvivalBridge.closureKappa-c` (blind)

Text: "The function κ(θ) = ψ''(θ)ψ(θ)/ψ'(θ)² is constant in θ iff the degree distribution is
Poisson-type; `closureKappa` records only its value κ(1), which does not determine the family:
ψ(u) = (1 + u²)/2 has κ(1) = 1 but is not Poisson."

"Poisson-type" is defined by the constancy of κ(θ), so the first clause is a definition. S1:
`closureKappa` is κ(1) = ψ''(1)·1/ψ'(1)²; S2: (1 + u²)/2 has κ(1) = 1; S3: it is not Poisson;
S4: the Poisson record also has κ(1) = 1. -/
namespace Alignment.Shadows.SurvivalBridge.closureKappa_c

open Alignment.Shadows.SurvivalBridge.Shared2

@[sa_reference "SurvivalBridge.closureKappa-c"]
def T : Prop :=
  (∀ ψ : PGFData, ψ.closureKappa = ψ.secondFactorial * 1 / ψ.mean ^ 2) ∧ kappaFn psiMix 1 = 1 ∧
    (∀ lam : ℝ, psiMix ≠ fun u => Real.exp (lam * (u - 1))) ∧
    (∀ (lam : ℚ) (h : 0 < lam), (PGFData.poisson lam h).closureKappa = 1)

/-- S1: `closureKappa` records κ(1). -/
@[sa_shadow "SurvivalBridge.closureKappa-c" 1]
def S1 : Prop := ∀ ψ : PGFData, ψ.closureKappa = ψ.secondFactorial * 1 / ψ.mean ^ 2
/-- S2: (1 + u²)/2 has κ(1) = 1. -/
@[sa_shadow "SurvivalBridge.closureKappa-c" 2]
def S2 : Prop := kappaFn psiMix 1 = 1
/-- S3: (1 + u²)/2 is not Poisson. -/
@[sa_shadow "SurvivalBridge.closureKappa-c" 3]
def S3 : Prop := ∀ lam : ℝ, psiMix ≠ fun u => Real.exp (lam * (u - 1))
/-- S4: Poisson records have κ(1) = 1. -/
@[sa_shadow "SurvivalBridge.closureKappa-c" 4]
def S4 : Prop := ∀ (lam : ℚ) (h : 0 < lam), (PGFData.poisson lam h).closureKappa = 1

@[sa_ref_forward "SurvivalBridge.closureKappa-c" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "SurvivalBridge.closureKappa-c" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "SurvivalBridge.closureKappa-c" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "SurvivalBridge.closureKappa-c" 4] theorem ref_fwd4 : T → S4 := fun t => t.2.2.2
@[sa_complete "SurvivalBridge.closureKappa-c"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.SurvivalBridge.closureKappa_c

/-! ## `SurvivalBridge.header.categorical.eta` (blind)

Text: "They are related by the change of variables x_θ = θ, x_{SI} = p_I · θ · ψ'(θ),
x_{SS} = p_S · θ · ψ'(θ) (Kiss, Kenah & Rempała 2023, App. B), which is invertible when
θ·ψ'(θ) > 0."

The change of variables is `volzToDSA` with the factor `θ·ψ′(θ)` (ψ′(θ) a value `d`). -/
namespace Alignment.Shadows.SurvivalBridge.header_categorical_eta

@[sa_reference "SurvivalBridge.header.categorical.eta"]
def T : Prop :=
  (∀ (v : VolzState) (d : ℚ), (volzToDSA v (v.θ * d)).x_θ = v.θ) ∧
  (∀ (v : VolzState) (d : ℚ), (volzToDSA v (v.θ * d)).x_SI = v.p_I * (v.θ * d)) ∧
  (∀ (v : VolzState) (d : ℚ), (volzToDSA v (v.θ * d)).x_SS = v.p_S * (v.θ * d)) ∧
  (∀ (v : VolzState) (d : ℚ) (h : 0 < v.θ * d),
      dsaToVolz (volzToDSA v (v.θ * d)) (v.θ * d) h.ne' = v)

/-- S1: `x_θ = θ`. -/
@[sa_shadow "SurvivalBridge.header.categorical.eta" 1]
def S1 : Prop := ∀ (v : VolzState) (d : ℚ), (volzToDSA v (v.θ * d)).x_θ = v.θ
/-- S2: `x_SI = p_I θ ψ′(θ)`. -/
@[sa_shadow "SurvivalBridge.header.categorical.eta" 2]
def S2 : Prop := ∀ (v : VolzState) (d : ℚ), (volzToDSA v (v.θ * d)).x_SI = v.p_I * (v.θ * d)
/-- S3: `x_SS = p_S θ ψ′(θ)`. -/
@[sa_shadow "SurvivalBridge.header.categorical.eta" 3]
def S3 : Prop := ∀ (v : VolzState) (d : ℚ), (volzToDSA v (v.θ * d)).x_SS = v.p_S * (v.θ * d)
/-- S4: invertible when `θψ′(θ) > 0`. -/
@[sa_shadow "SurvivalBridge.header.categorical.eta" 4]
def S4 : Prop :=
  ∀ (v : VolzState) (d : ℚ) (h : 0 < v.θ * d), dsaToVolz (volzToDSA v (v.θ * d)) (v.θ * d) h.ne' = v

@[sa_ref_forward "SurvivalBridge.header.categorical.eta" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t.1
@[sa_ref_forward "SurvivalBridge.header.categorical.eta" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2.1
@[sa_ref_forward "SurvivalBridge.header.categorical.eta" 3] theorem ref_fwd3 : T → S3 :=
  fun t => t.2.2.1
@[sa_ref_forward "SurvivalBridge.header.categorical.eta" 4] theorem ref_fwd4 : T → S4 :=
  fun t => t.2.2.2
@[sa_complete "SurvivalBridge.header.categorical.eta"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.SurvivalBridge.header_categorical_eta

/-! ## `SurvivalBridge.table.R42` (re-authored blind)

Text: "| 42 | Poisson ⇒ κ(1) = 1 (κ ≡ 1 on an interval iff Poisson) |"

S1: the Poisson record has κ(1) = 1. S2 (Poisson ⇒ κ ≡ 1): the Poisson PGF e^{λ(u−1)} (λ > 0) has
closure ratio 1 everywhere. S3 (κ ≡ 1 on an interval ⇒ Poisson): a PGF `ψ(u) = Σ pₖ uᵏ`
(pₖ ≥ 0, Σ pₖ = 1) whose closure ratio is 1 on an interval in (0, 1) has Poisson weights. -/
namespace Alignment.Shadows.SurvivalBridge.table_R42

open Alignment.Shadows.SurvivalBridge.Shared2

@[sa_reference "SurvivalBridge.table.R42"]
def T : Prop :=
  (∀ (lam : ℚ) (h : 0 < lam), (PGFData.poisson lam h).closureKappa = 1) ∧
  (∀ lam : ℝ, 0 < lam → ∀ u : ℝ, kappaFn (fun x => Real.exp (lam * (x - 1))) u = 1) ∧
  (∀ (p : ℕ → ℝ) (a b : ℝ), (∀ k, 0 ≤ p k) → HasSum p 1 → 0 < a → a < b → b < 1 →
      (∀ u ∈ Set.Ioo a b, kappaFn (fun x => ∑' k, p k * x ^ k) u = 1) →
      ∃ lam : NNReal, ∀ k, p k = ProbabilityTheory.poissonPMFReal lam k)

/-- S1: Poisson ⇒ κ(1) = 1. -/
@[sa_shadow "SurvivalBridge.table.R42" 1]
def S1 : Prop := ∀ (lam : ℚ) (h : 0 < lam), (PGFData.poisson lam h).closureKappa = 1
/-- S2: the Poisson PGF has κ ≡ 1. -/
@[sa_shadow "SurvivalBridge.table.R42" 2]
def S2 : Prop := ∀ lam : ℝ, 0 < lam → ∀ u : ℝ, kappaFn (fun x => Real.exp (lam * (x - 1))) u = 1
/-- S3: κ ≡ 1 on an interval forces Poisson weights. -/
@[sa_shadow "SurvivalBridge.table.R42" 3]
def S3 : Prop :=
  ∀ (p : ℕ → ℝ) (a b : ℝ), (∀ k, 0 ≤ p k) → HasSum p 1 → 0 < a → a < b → b < 1 →
    (∀ u ∈ Set.Ioo a b, kappaFn (fun x => ∑' k, p k * x ^ k) u = 1) →
    ∃ lam : NNReal, ∀ k, p k = ProbabilityTheory.poissonPMFReal lam k

@[sa_ref_forward "SurvivalBridge.table.R42" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "SurvivalBridge.table.R42" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "SurvivalBridge.table.R42" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "SurvivalBridge.table.R42"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.SurvivalBridge.table_R42

/-! ## `SurvivalBridge.table.R43` (re-authored blind)

Text: "| 43 | Some record has κ(1) < 1 (Binomial: κ ≡ (n-1)/n) |"

S1: some record has `closureKappa < 1`; S2: the binomial PGF has closure ratio (n−1)/n on (0, 1];
S3: its moment record has `closureKappa = (n−1)/n`. -/
namespace Alignment.Shadows.SurvivalBridge.table_R43

open Alignment.Shadows.SurvivalBridge.Shared2

@[sa_reference "SurvivalBridge.table.R43"]
def T : Prop :=
  (∃ ψ : PGFData, ψ.closureKappa < 1) ∧
  (∀ (n : ℕ) (p : ℝ), 1 ≤ n → 0 < p → p ≤ 1 → ∀ u : ℝ, 0 < u → u ≤ 1 →
      kappaFn (psiBin n p) u = ((n : ℝ) - 1) / n) ∧
  (∀ (n : ℕ) (p : ℚ) (hn : 1 ≤ n) (hp : 0 < p), (binRec n p hn hp).closureKappa = ((n : ℚ) - 1) / n)

/-- S1: some record has κ(1) < 1. -/
@[sa_shadow "SurvivalBridge.table.R43" 1]
def S1 : Prop := ∃ ψ : PGFData, ψ.closureKappa < 1
/-- S2: binomial κ ≡ (n−1)/n. -/
@[sa_shadow "SurvivalBridge.table.R43" 2]
def S2 : Prop :=
  ∀ (n : ℕ) (p : ℝ), 1 ≤ n → 0 < p → p ≤ 1 → ∀ u : ℝ, 0 < u → u ≤ 1 →
    kappaFn (psiBin n p) u = ((n : ℝ) - 1) / n
/-- S3: the binomial record has κ(1) = (n−1)/n. -/
@[sa_shadow "SurvivalBridge.table.R43" 3]
def S3 : Prop :=
  ∀ (n : ℕ) (p : ℚ) (hn : 1 ≤ n) (hp : 0 < p), (binRec n p hn hp).closureKappa = ((n : ℚ) - 1) / n

@[sa_ref_forward "SurvivalBridge.table.R43" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "SurvivalBridge.table.R43" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "SurvivalBridge.table.R43" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "SurvivalBridge.table.R43"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.SurvivalBridge.table_R43

/-! ## `SurvivalBridge.table.R44` (re-authored blind)

Text: "| 44 | Some record has κ(1) > 1 (NegBin: κ ≡ (r+1)/r) |"

S1: some record has `closureKappa > 1`; S2: the negative-binomial PGF has closure ratio (r+1)/r on
[0, 1]; S3: its moment record has `closureKappa = (r+1)/r`. -/
namespace Alignment.Shadows.SurvivalBridge.table_R44

open Alignment.Shadows.SurvivalBridge.Shared2

@[sa_reference "SurvivalBridge.table.R44"]
def T : Prop :=
  (∃ ψ : PGFData, 1 < ψ.closureKappa) ∧
  (∀ r c : ℝ, 0 < r → 0 < c → c < 1 → ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      kappaFn (psiNB r c) u = (r + 1) / r) ∧
  (∀ (r c : ℚ) (hr : 0 < r) (hc0 : 0 < c) (hc1 : c < 1),
      (nbRec r c hr hc0 hc1).closureKappa = (r + 1) / r)

/-- S1: some record has κ(1) > 1. -/
@[sa_shadow "SurvivalBridge.table.R44" 1]
def S1 : Prop := ∃ ψ : PGFData, 1 < ψ.closureKappa
/-- S2: negative-binomial κ ≡ (r+1)/r. -/
@[sa_shadow "SurvivalBridge.table.R44" 2]
def S2 : Prop :=
  ∀ r c : ℝ, 0 < r → 0 < c → c < 1 → ∀ u : ℝ, 0 ≤ u → u ≤ 1 → kappaFn (psiNB r c) u = (r + 1) / r
/-- S3: the negative-binomial record has κ(1) = (r+1)/r. -/
@[sa_shadow "SurvivalBridge.table.R44" 3]
def S3 : Prop :=
  ∀ (r c : ℚ) (hr : 0 < r) (hc0 : 0 < c) (hc1 : c < 1),
    (nbRec r c hr hc0 hc1).closureKappa = (r + 1) / r

@[sa_ref_forward "SurvivalBridge.table.R44" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "SurvivalBridge.table.R44" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "SurvivalBridge.table.R44" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "SurvivalBridge.table.R44"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.SurvivalBridge.table_R44

/-! ## `SurvivalBridge.table.R46` (re-authored blind)

Text: "| 46 | S = ψ(θ) gives dS/dt = −β x_SI (chain rule; informal) |" -/
namespace Alignment.Shadows.SurvivalBridge.table_R46

open Alignment.Shadows.SurvivalBridge.Shared2

@[sa_reference "SurvivalBridge.table.R46"]
def T : Prop := ChainRule46

/-- S1: the chain rule `d/dt ψ(θ) = −β x_SI`. -/
@[sa_shadow "SurvivalBridge.table.R46" 1]
def S1 : Prop := ChainRule46

@[sa_ref_forward "SurvivalBridge.table.R46" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SurvivalBridge.table.R46"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SurvivalBridge.table_R46

/-! ## `SurvivalBridge.table.R47` (re-authored blind)

Text: "| 47 | Poisson ⇒ κ(1) = 1 (DSA has mass-action form, rescaled) |" -/
namespace Alignment.Shadows.SurvivalBridge.table_R47

open Alignment.Shadows.SurvivalBridge.Shared2

@[sa_reference "SurvivalBridge.table.R47"]
def T : Prop :=
  (∀ (μ : ℚ) (hμ : 0 < μ), (PGFData.poisson μ hμ).closureKappa = 1) ∧ PoisDSASurvival

/-- S1: Poisson ⇒ κ(1) = 1. -/
@[sa_shadow "SurvivalBridge.table.R47" 1]
def S1 : Prop := ∀ (μ : ℚ) (hμ : 0 < μ), (PGFData.poisson μ hμ).closureKappa = 1
/-- S2: the Poisson DSA survival equation has the rescaled mass-action form. -/
@[sa_shadow "SurvivalBridge.table.R47" 2]
def S2 : Prop := PoisDSASurvival

@[sa_ref_forward "SurvivalBridge.table.R47" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "SurvivalBridge.table.R47" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "SurvivalBridge.table.R47"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.SurvivalBridge.table_R47

/-! ## `SurvivalBridge.volzState-a` (blind)

Text: "They are related by (Kiss, Kenah & Rempała 2023, App. B): x_{SI} = p_I · θ · ψ'(θ)
x_{SS} = p_S · θ · ψ'(θ) The maps `volzToDSA`/`dsaToVolz` below multiply and divide by an arbitrary
scalar factor `psi_prime`; this change of variables is the instance `psi_prime := θ·ψ'(θ)`."

S1, S2: `volzToDSA` multiplies p_I, p_S by the factor; S3, S4: `dsaToVolz` divides x_SI, x_SS by it.
The KKR relation is the instance factor = θψ′(θ) of S1, S2. -/
namespace Alignment.Shadows.SurvivalBridge.volzState_a

@[sa_reference "SurvivalBridge.volzState-a"]
def T : Prop :=
  (∀ (v : VolzState) (c : ℚ), (volzToDSA v c).x_SI = v.p_I * c) ∧
  (∀ (v : VolzState) (c : ℚ), (volzToDSA v c).x_SS = v.p_S * c) ∧
  (∀ (x : DSAState) (c : ℚ) (hc : c ≠ 0), (dsaToVolz x c hc).p_I = x.x_SI / c) ∧
  (∀ (x : DSAState) (c : ℚ) (hc : c ≠ 0), (dsaToVolz x c hc).p_S = x.x_SS / c)

/-- S1: `volzToDSA` multiplies p_I by the factor. -/
@[sa_shadow "SurvivalBridge.volzState-a" 1]
def S1 : Prop := ∀ (v : VolzState) (c : ℚ), (volzToDSA v c).x_SI = v.p_I * c
/-- S2: `volzToDSA` multiplies p_S by the factor. -/
@[sa_shadow "SurvivalBridge.volzState-a" 2]
def S2 : Prop := ∀ (v : VolzState) (c : ℚ), (volzToDSA v c).x_SS = v.p_S * c
/-- S3: `dsaToVolz` divides x_SI by the factor. -/
@[sa_shadow "SurvivalBridge.volzState-a" 3]
def S3 : Prop := ∀ (x : DSAState) (c : ℚ) (hc : c ≠ 0), (dsaToVolz x c hc).p_I = x.x_SI / c
/-- S4: `dsaToVolz` divides x_SS by the factor. -/
@[sa_shadow "SurvivalBridge.volzState-a" 4]
def S4 : Prop := ∀ (x : DSAState) (c : ℚ) (hc : c ≠ 0), (dsaToVolz x c hc).p_S = x.x_SS / c

@[sa_ref_forward "SurvivalBridge.volzState-a" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "SurvivalBridge.volzState-a" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "SurvivalBridge.volzState-a" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "SurvivalBridge.volzState-a" 4] theorem ref_fwd4 : T → S4 := fun t => t.2.2.2
@[sa_complete "SurvivalBridge.volzState-a"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.SurvivalBridge.volzState_a

/-! ## `SurvivalBridge.volzState-b` (re-authored blind)

Text: "This is invertible whenever θ·ψ'(θ) > 0."

"This" is the change of variables with factor θ·ψ′(θ) (ψ′(θ) a value `d`); both round trips. -/
namespace Alignment.Shadows.SurvivalBridge.volzState_b

@[sa_reference "SurvivalBridge.volzState-b"]
def T : Prop :=
  (∀ (v : VolzState) (d : ℚ) (h : 0 < v.θ * d),
      dsaToVolz (volzToDSA v (v.θ * d)) (v.θ * d) h.ne' = v) ∧
  (∀ (x : DSAState) (d : ℚ) (h : 0 < x.x_θ * d),
      volzToDSA (dsaToVolz x (x.x_θ * d) h.ne') (x.x_θ * d) = x)

/-- S1: Volz → DSA → Volz is the identity. -/
@[sa_shadow "SurvivalBridge.volzState-b" 1]
def S1 : Prop :=
  ∀ (v : VolzState) (d : ℚ) (h : 0 < v.θ * d), dsaToVolz (volzToDSA v (v.θ * d)) (v.θ * d) h.ne' = v
/-- S2: DSA → Volz → DSA is the identity. -/
@[sa_shadow "SurvivalBridge.volzState-b" 2]
def S2 : Prop :=
  ∀ (x : DSAState) (d : ℚ) (h : 0 < x.x_θ * d),
    volzToDSA (dsaToVolz x (x.x_θ * d) h.ne') (x.x_θ * d) = x

@[sa_ref_forward "SurvivalBridge.volzState-b" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "SurvivalBridge.volzState-b" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "SurvivalBridge.volzState-b"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.SurvivalBridge.volzState_b

/-! ## `SurvivalBridge.dsaVolzRoundtrip` (blind)

Text: "The round-trip DSA → Volz → DSA is the identity."

For every nonzero factor (the maps `dsaToVolz` / `volzToDSA` with the same factor). -/
namespace Alignment.Shadows.SurvivalBridge.dsaVolzRoundtrip

@[sa_reference "SurvivalBridge.dsaVolzRoundtrip"]
def T : Prop := ∀ (x : DSAState) (c : ℚ) (hc : c ≠ 0), volzToDSA (dsaToVolz x c hc) c = x

/-- S1: DSA → Volz → DSA is the identity. -/
@[sa_shadow "SurvivalBridge.dsaVolzRoundtrip" 1]
def S1 : Prop := ∀ (x : DSAState) (c : ℚ) (hc : c ≠ 0), volzToDSA (dsaToVolz x c hc) c = x

@[sa_ref_forward "SurvivalBridge.dsaVolzRoundtrip" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SurvivalBridge.dsaVolzRoundtrip"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SurvivalBridge.dsaVolzRoundtrip

end
