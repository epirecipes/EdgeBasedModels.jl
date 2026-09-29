import Alignment.Registry
import EBCMCategory.ConvergenceTheorems
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Blind shadow sets: group `ConvergenceTheorems`

Written blind: the author read only the claims' entries in `Alignment/claims_blind.yaml`,
`Alignment/DataTypes/ConvergenceTheorems.md`, `Alignment/README.md`,
`Alignment/Example/ExampleShadows.lean` and `SA-PASS_SKILL.md` (and used `#check` on the listed
data types and operations only).

Vocabulary (from `DataTypes/ConvergenceTheorems.md`):
* `PoissonEBCMData` (fields `kappa` = κ, `beta_tilde` = β̃, `gamma_tilde` = γ̃, all positive);
  `effective_beta d` (β = κβ̃), `effective_gamma d` (γ = γ̃ + β̃).
* `PGFMoments` (fields `mean` = ⟨k⟩ = ψ'(1), `secondFactorial` = ⟨k(k-1)⟩ = ψ''(1),
  `variance` = Var(k)); `m.excessDegree` (the excess degree ratio ψ''(1)/ψ'(1)),
  `m.secondMoment` (⟨k²⟩), `poissonMoments κ hκ` (Poisson(κ) moments),
  `R0_heterogeneous T m` (R₀ with transmissibility `T`), `R0_homogeneous T k` (R₀ of a regular
  network of degree `k`), `criticalTransmissibility m h` (T_c), `finalSizeMap T x`
  (f(θ) = 1 - T + T·g(θ) evaluated at the *value* x = g(θ)).

Conventions used throughout:
* The text's transmissibility `T` is written `τ` (to avoid a clash with the reference `T`).
* "Any degree distribution" is represented by its moment record `PGFMoments`
  (VOCAB-GAP: there is no degree distribution / PGF as a function in the vocabulary).
* For the final-size map (Results 110), the function g(θ) = ψ'(θ)/ψ'(1) is not in the
  vocabulary (VOCAB-GAP). It is modelled by an arbitrary `g : ℝ → ℝ` with the two properties
  the text relies on at θ = 1: `g 1 = 1` (normalisation, from the `finalSizeMap` docstring) and
  `HasDerivAt g (m.secondFactorial / m.mean) 1` (g'(1) = ψ''(1)/ψ'(1), written with the moment
  fields); the map itself is `fun θ => finalSizeMap τ (g θ)` and f'(1) is
  `deriv (fun θ => finalSizeMap τ (g θ)) 1`.

Re-authored blind (second pass, from the current claim texts, `DataTypes/*.md`, the README,
`SA-PASS_SKILL.md`, `Example/ExampleShadows.lean` and background papers only): the blocks marked
"(re-authored blind)" or "(blind)" near the end of this file (with any `Shared2` helper
namespace). Ids of that pass not formalised (remarks on proof status, on which notions the library
defines, or cited results needing models the vocabulary lacks): `R105e.2`, `R110b.3`, `R111a`,
`R111b`, `header.scope`.
-/

/-! ## `ConvergenceTheorems.effectiveBetaPos` — "Effective β is positive." -/
namespace Alignment.Shadows.ConvergenceTheorems.effectiveBetaPos

/-- Intended statement: for all Poisson-EBCM data, the effective transmission rate is positive. -/
@[sa_reference "ConvergenceTheorems.effectiveBetaPos"]
def T : Prop := ∀ d : PoissonEBCMData, 0 < effective_beta d

/-- S1: effective β > 0 for every data record. -/
@[sa_shadow "ConvergenceTheorems.effectiveBetaPos" 1]
def S1 : Prop := ∀ d : PoissonEBCMData, 0 < effective_beta d

@[sa_ref_forward "ConvergenceTheorems.effectiveBetaPos" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "ConvergenceTheorems.effectiveBetaPos"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.ConvergenceTheorems.effectiveBetaPos

/-! ## `ConvergenceTheorems.effectiveGammaPos` — "Effective γ is positive." -/
namespace Alignment.Shadows.ConvergenceTheorems.effectiveGammaPos

/-- Intended statement: for all Poisson-EBCM data, the effective recovery rate is positive. -/
@[sa_reference "ConvergenceTheorems.effectiveGammaPos"]
def T : Prop := ∀ d : PoissonEBCMData, 0 < effective_gamma d

/-- S1: effective γ > 0 for every data record. -/
@[sa_shadow "ConvergenceTheorems.effectiveGammaPos" 1]
def S1 : Prop := ∀ d : PoissonEBCMData, 0 < effective_gamma d

@[sa_ref_forward "ConvergenceTheorems.effectiveGammaPos" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "ConvergenceTheorems.effectiveGammaPos"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.ConvergenceTheorems.effectiveGammaPos

/-! ## `ConvergenceTheorems.R105c.4`

Text: "Here we verify the simpler identity: κ · β̃/(β̃ + γ̃) = κβ̃/(β̃ + γ̃)." -/
namespace Alignment.Shadows.ConvergenceTheorems.R105c_4

-- AMBIGUITY: "κ · β̃/(β̃ + γ̃)" read as κ · (β̃/(β̃ + γ̃)) (κ times the per-edge
-- transmissibility); the purely left-associative parse (κ·β̃)/(β̃ + γ̃) would make the two sides
-- syntactically identical (a tautology), so it is not the intended reading.
-- AMBIGUITY: κ, β̃, γ̃ read as the fields of `PoissonEBCMData` (the vocabulary's record for exactly
-- these parameters), not as arbitrary reals.
-- NOTE: the text asserts only an algebraic identity; the shadow is a true statement about reals
-- that does not involve any operation under test.

/-- Intended statement: κ · (β̃/(β̃+γ̃)) = (κβ̃)/(β̃+γ̃) for all Poisson-EBCM parameters. -/
@[sa_reference "ConvergenceTheorems.R105c.4"]
def T : Prop := ∀ d : PoissonEBCMData,
  d.kappa * (d.beta_tilde / (d.beta_tilde + d.gamma_tilde)) =
    d.kappa * d.beta_tilde / (d.beta_tilde + d.gamma_tilde)

/-- S1: the whole identity (a single atomic equation). -/
@[sa_shadow "ConvergenceTheorems.R105c.4" 1]
def S1 : Prop := ∀ d : PoissonEBCMData,
  d.kappa * (d.beta_tilde / (d.beta_tilde + d.gamma_tilde)) =
    d.kappa * d.beta_tilde / (d.beta_tilde + d.gamma_tilde)

@[sa_ref_forward "ConvergenceTheorems.R105c.4" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "ConvergenceTheorems.R105c.4"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.ConvergenceTheorems.R105c_4

/-! ## `ConvergenceTheorems.R105d.2`

Text: "Thus the excess degree ratio ψ''(1)/ψ'(1) = κ²/κ = κ." -/
namespace Alignment.Shadows.ConvergenceTheorems.R105d_2

-- The chain "ψ''(1)/ψ'(1) = κ²/κ = κ" is split into its two links that involve the operation
-- under test (the link κ²/κ = κ alone is plain arithmetic). "The excess degree ratio
-- ψ''(1)/ψ'(1)" of the Poisson(κ) distribution is `(poissonMoments κ hκ).excessDegree`.

/-- Intended statement: for every κ > 0 the Poisson excess degree ratio equals κ²/κ and κ. -/
@[sa_reference "ConvergenceTheorems.R105d.2"]
def T : Prop := ∀ (κ : ℝ) (hκ : 0 < κ),
  (poissonMoments κ hκ).excessDegree = κ ^ 2 / κ ∧ (poissonMoments κ hκ).excessDegree = κ

/-- S1: ψ''(1)/ψ'(1) = κ²/κ for Poisson(κ). -/
@[sa_shadow "ConvergenceTheorems.R105d.2" 1]
def S1 : Prop := ∀ (κ : ℝ) (hκ : 0 < κ), (poissonMoments κ hκ).excessDegree = κ ^ 2 / κ

/-- S2: ψ''(1)/ψ'(1) = κ for Poisson(κ). -/
@[sa_shadow "ConvergenceTheorems.R105d.2" 2]
def S2 : Prop := ∀ (κ : ℝ) (hκ : 0 < κ), (poissonMoments κ hκ).excessDegree = κ

@[sa_ref_forward "ConvergenceTheorems.R105d.2" 1]
theorem ref_fwd1 : T → S1 := fun t κ hκ => (t κ hκ).1

@[sa_ref_forward "ConvergenceTheorems.R105d.2" 2]
theorem ref_fwd2 : T → S2 := fun t κ hκ => (t κ hκ).2

@[sa_complete "ConvergenceTheorems.R105d.2"]
theorem complete (s1 : S1) (s2 : S2) : T := fun κ hκ => ⟨s1 κ hκ, s2 κ hκ⟩

end Alignment.Shadows.ConvergenceTheorems.R105d_2

/-! ## `ConvergenceTheorems.R107a`

Text: "**Result 107a.** ψ''(1)/ψ'(1) = (⟨k²⟩ - ⟨k⟩)/⟨k⟩." -/
namespace Alignment.Shadows.ConvergenceTheorems.R107a

-- AMBIGUITY: "ψ''(1)/ψ'(1)" read both as the operation `m.excessDegree` (documented as exactly
-- this ratio) and as the quotient of the moment fields `m.secondFactorial / m.mean`
-- (ψ''(1), ψ'(1)); both are required (S1, S2). ⟨k²⟩ is `m.secondMoment`, ⟨k⟩ is `m.mean`.

/-- Intended statement: for every degree distribution, ψ''(1)/ψ'(1) = (⟨k²⟩ - ⟨k⟩)/⟨k⟩. -/
@[sa_reference "ConvergenceTheorems.R107a"]
def T : Prop := ∀ m : PGFMoments,
  m.excessDegree = (m.secondMoment - m.mean) / m.mean ∧
    m.secondFactorial / m.mean = (m.secondMoment - m.mean) / m.mean

/-- S1: the excess degree ratio operation equals (⟨k²⟩ - ⟨k⟩)/⟨k⟩. -/
@[sa_shadow "ConvergenceTheorems.R107a" 1]
def S1 : Prop := ∀ m : PGFMoments, m.excessDegree = (m.secondMoment - m.mean) / m.mean

/-- S2: the field quotient ψ''(1)/ψ'(1) equals (⟨k²⟩ - ⟨k⟩)/⟨k⟩. -/
@[sa_shadow "ConvergenceTheorems.R107a" 2]
def S2 : Prop := ∀ m : PGFMoments,
  m.secondFactorial / m.mean = (m.secondMoment - m.mean) / m.mean

@[sa_ref_forward "ConvergenceTheorems.R107a" 1]
theorem ref_fwd1 : T → S1 := fun t m => (t m).1

@[sa_ref_forward "ConvergenceTheorems.R107a" 2]
theorem ref_fwd2 : T → S2 := fun t m => (t m).2

@[sa_complete "ConvergenceTheorems.R107a"]
theorem complete (s1 : S1) (s2 : S2) : T := fun m => ⟨s1 m, s2 m⟩

end Alignment.Shadows.ConvergenceTheorems.R107a

/-! ## `ConvergenceTheorems.R107b`

Text: "**Result 107b.** (⟨k²⟩ - ⟨k⟩)/⟨k⟩ = ⟨k⟩ + Var(k)/⟨k⟩ - 1." -/
namespace Alignment.Shadows.ConvergenceTheorems.R107b

/-- Intended statement: for every degree distribution, (⟨k²⟩ - ⟨k⟩)/⟨k⟩ = ⟨k⟩ + Var(k)/⟨k⟩ - 1. -/
@[sa_reference "ConvergenceTheorems.R107b"]
def T : Prop := ∀ m : PGFMoments,
  (m.secondMoment - m.mean) / m.mean = m.mean + m.variance / m.mean - 1

/-- S1: the whole identity (a single atomic equation). -/
@[sa_shadow "ConvergenceTheorems.R107b" 1]
def S1 : Prop := ∀ m : PGFMoments,
  (m.secondMoment - m.mean) / m.mean = m.mean + m.variance / m.mean - 1

@[sa_ref_forward "ConvergenceTheorems.R107b" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "ConvergenceTheorems.R107b"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.ConvergenceTheorems.R107b

/-! ## `ConvergenceTheorems.R107c`

Text: "**Result 107c.** The two forms are equal: (⟨k²⟩-⟨k⟩)/⟨k⟩ = ⟨k⟩+Var/⟨k⟩-1." -/
namespace Alignment.Shadows.ConvergenceTheorems.R107c

-- AMBIGUITY: "The two forms" is resolved by the displayed equation after the colon: the form
-- (⟨k²⟩-⟨k⟩)/⟨k⟩ equals the form ⟨k⟩+Var/⟨k⟩-1 (a reading "both forms equal ψ''(1)/ψ'(1)" is
-- not what the displayed equation says). "Var" is Var(k) = `m.variance`.

/-- Intended statement: for every degree distribution the two forms agree. -/
@[sa_reference "ConvergenceTheorems.R107c"]
def T : Prop := ∀ m : PGFMoments,
  (m.secondMoment - m.mean) / m.mean = m.mean + m.variance / m.mean - 1

/-- S1: the whole identity (a single atomic equation). -/
@[sa_shadow "ConvergenceTheorems.R107c" 1]
def S1 : Prop := ∀ m : PGFMoments,
  (m.secondMoment - m.mean) / m.mean = m.mean + m.variance / m.mean - 1

@[sa_ref_forward "ConvergenceTheorems.R107c" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "ConvergenceTheorems.R107c"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.ConvergenceTheorems.R107c

/-! ## `ConvergenceTheorems.R108a`

Text: "**Result 108a.** R₀ = T · (⟨k⟩ + Var(k)/⟨k⟩ - 1)." -/
namespace Alignment.Shadows.ConvergenceTheorems.R108a

-- The text states no restriction on T, so the identity is required for every real τ.

/-- Intended statement: for every transmissibility and degree distribution,
R₀ = T·(⟨k⟩ + Var(k)/⟨k⟩ - 1). -/
@[sa_reference "ConvergenceTheorems.R108a"]
def T : Prop := ∀ (τ : ℝ) (m : PGFMoments),
  R0_heterogeneous τ m = τ * (m.mean + m.variance / m.mean - 1)

/-- S1: the whole identity (a single atomic equation). -/
@[sa_shadow "ConvergenceTheorems.R108a" 1]
def S1 : Prop := ∀ (τ : ℝ) (m : PGFMoments),
  R0_heterogeneous τ m = τ * (m.mean + m.variance / m.mean - 1)

@[sa_ref_forward "ConvergenceTheorems.R108a" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "ConvergenceTheorems.R108a"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.ConvergenceTheorems.R108a

/-! ## `ConvergenceTheorems.R108b`

Text: "**Result 108b.** Heterogeneity amplifies R₀: for any degree distribution with mean ⟨k⟩ and
Var ≥ 0, R₀ ≥ T·(⟨k⟩ - 1) = R₀(homogeneous)." -/
namespace Alignment.Shadows.ConvergenceTheorems.R108b

-- AMBIGUITY: the range of T is not stated. T is a transmissibility (a probability), and the
-- inequality R₀ ≥ T·(⟨k⟩ - 1) needs T ≥ 0; read as "for every τ ≥ 0" (the upper bound τ ≤ 1 is
-- irrelevant and not imposed). The same context applies to the whole sentence.
-- "any degree distribution with mean ⟨k⟩ and Var ≥ 0": any `PGFMoments` (Var ≥ 0 is built in).
-- "R₀(homogeneous)": R₀ of the regular network with degree ⟨k⟩, `R0_homogeneous τ m.mean`.
-- The chain "R₀ ≥ A = B" is split into R₀ ≥ A (S1) and A = B (S2).

/-- Intended statement: for τ ≥ 0 and any degree distribution,
T·(⟨k⟩ - 1) ≤ R₀ and T·(⟨k⟩ - 1) = R₀(homogeneous). -/
@[sa_reference "ConvergenceTheorems.R108b"]
def T : Prop := ∀ τ : ℝ, 0 ≤ τ → ∀ m : PGFMoments,
  τ * (m.mean - 1) ≤ R0_heterogeneous τ m ∧ τ * (m.mean - 1) = R0_homogeneous τ m.mean

/-- S1: R₀ ≥ T·(⟨k⟩ - 1). -/
@[sa_shadow "ConvergenceTheorems.R108b" 1]
def S1 : Prop := ∀ τ : ℝ, 0 ≤ τ → ∀ m : PGFMoments, τ * (m.mean - 1) ≤ R0_heterogeneous τ m

/-- S2: T·(⟨k⟩ - 1) = R₀(homogeneous) for the regular network of degree ⟨k⟩. -/
@[sa_shadow "ConvergenceTheorems.R108b" 2]
def S2 : Prop := ∀ τ : ℝ, 0 ≤ τ → ∀ m : PGFMoments, τ * (m.mean - 1) = R0_homogeneous τ m.mean

@[sa_ref_forward "ConvergenceTheorems.R108b" 1]
theorem ref_fwd1 : T → S1 := fun t τ hτ m => (t τ hτ m).1

@[sa_ref_forward "ConvergenceTheorems.R108b" 2]
theorem ref_fwd2 : T → S2 := fun t τ hτ m => (t τ hτ m).2

@[sa_complete "ConvergenceTheorems.R108b"]
theorem complete (s1 : S1) (s2 : S2) : T := fun τ hτ m => ⟨s1 τ hτ m, s2 τ hτ m⟩

end Alignment.Shadows.ConvergenceTheorems.R108b

/-! ## `ConvergenceTheorems.R108c`

Text: "**Result 108c.** Equality iff Var(k) = 0 (regular network)." -/
namespace Alignment.Shadows.ConvergenceTheorems.R108c

-- AMBIGUITY: "Equality" refers to the inequality of Result 108b, R₀ ≥ T·(⟨k⟩ - 1) = R₀(homogeneous):
-- read both as R₀ = T·(⟨k⟩ - 1) (S1, S2) and as R₀ = R₀(homogeneous) = `R0_homogeneous τ m.mean`
-- (S3, S4). Both directions of the iff are required for each reading.
-- AMBIGUITY: the range of T is not stated; the "only if" direction fails for T = 0 (then R₀ and
-- T·(⟨k⟩ - 1) are both 0), so the iff is read for a positive transmissibility τ > 0, for both
-- directions (one common context for the iff).

/-- Intended statement: for τ > 0 and any degree distribution, equality holds iff Var(k) = 0. -/
@[sa_reference "ConvergenceTheorems.R108c"]
def T : Prop := ∀ τ : ℝ, 0 < τ → ∀ m : PGFMoments,
  (R0_heterogeneous τ m = τ * (m.mean - 1) ↔ m.variance = 0) ∧
    (R0_heterogeneous τ m = R0_homogeneous τ m.mean ↔ m.variance = 0)

/-- S1 (if, R₀ = T·(⟨k⟩ - 1) reading): Var(k) = 0 gives equality. -/
@[sa_shadow "ConvergenceTheorems.R108c" 1]
def S1 : Prop := ∀ τ : ℝ, 0 < τ → ∀ m : PGFMoments,
  m.variance = 0 → R0_heterogeneous τ m = τ * (m.mean - 1)

/-- S2 (only if, R₀ = T·(⟨k⟩ - 1) reading): equality forces Var(k) = 0. -/
@[sa_shadow "ConvergenceTheorems.R108c" 2]
def S2 : Prop := ∀ τ : ℝ, 0 < τ → ∀ m : PGFMoments,
  R0_heterogeneous τ m = τ * (m.mean - 1) → m.variance = 0

/-- S3 (if, R₀ = R₀(homogeneous) reading). -/
@[sa_shadow "ConvergenceTheorems.R108c" 3]
def S3 : Prop := ∀ τ : ℝ, 0 < τ → ∀ m : PGFMoments,
  m.variance = 0 → R0_heterogeneous τ m = R0_homogeneous τ m.mean

/-- S4 (only if, R₀ = R₀(homogeneous) reading). -/
@[sa_shadow "ConvergenceTheorems.R108c" 4]
def S4 : Prop := ∀ τ : ℝ, 0 < τ → ∀ m : PGFMoments,
  R0_heterogeneous τ m = R0_homogeneous τ m.mean → m.variance = 0

@[sa_ref_forward "ConvergenceTheorems.R108c" 1]
theorem ref_fwd1 : T → S1 := fun t τ hτ m => (t τ hτ m).1.mpr

@[sa_ref_forward "ConvergenceTheorems.R108c" 2]
theorem ref_fwd2 : T → S2 := fun t τ hτ m => (t τ hτ m).1.mp

@[sa_ref_forward "ConvergenceTheorems.R108c" 3]
theorem ref_fwd3 : T → S3 := fun t τ hτ m => (t τ hτ m).2.mpr

@[sa_ref_forward "ConvergenceTheorems.R108c" 4]
theorem ref_fwd4 : T → S4 := fun t τ hτ m => (t τ hτ m).2.mp

@[sa_complete "ConvergenceTheorems.R108c"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := fun τ hτ m =>
  ⟨⟨s2 τ hτ m, s1 τ hτ m⟩, ⟨s4 τ hτ m, s3 τ hτ m⟩⟩

end Alignment.Shadows.ConvergenceTheorems.R108c

/-! ## `ConvergenceTheorems.R109a`

Text: "**Result 109a.** Poisson excess degree equals the mean κ." -/
namespace Alignment.Shadows.ConvergenceTheorems.R109a

-- AMBIGUITY: "the mean κ" may be read as the Poisson parameter κ or as the mean ψ'(1) of the
-- Poisson moment record, `(poissonMoments κ hκ).mean`; both readings are required (S1, S2).

/-- Intended statement: for every κ > 0, the Poisson excess degree equals κ and equals the mean. -/
@[sa_reference "ConvergenceTheorems.R109a"]
def T : Prop := ∀ (κ : ℝ) (hκ : 0 < κ),
  (poissonMoments κ hκ).excessDegree = κ ∧
    (poissonMoments κ hκ).excessDegree = (poissonMoments κ hκ).mean

/-- S1: the Poisson excess degree equals the parameter κ. -/
@[sa_shadow "ConvergenceTheorems.R109a" 1]
def S1 : Prop := ∀ (κ : ℝ) (hκ : 0 < κ), (poissonMoments κ hκ).excessDegree = κ

/-- S2: the Poisson excess degree equals the mean ψ'(1) of the moment record. -/
@[sa_shadow "ConvergenceTheorems.R109a" 2]
def S2 : Prop := ∀ (κ : ℝ) (hκ : 0 < κ),
  (poissonMoments κ hκ).excessDegree = (poissonMoments κ hκ).mean

@[sa_ref_forward "ConvergenceTheorems.R109a" 1]
theorem ref_fwd1 : T → S1 := fun t κ hκ => (t κ hκ).1

@[sa_ref_forward "ConvergenceTheorems.R109a" 2]
theorem ref_fwd2 : T → S2 := fun t κ hκ => (t κ hκ).2

@[sa_complete "ConvergenceTheorems.R109a"]
theorem complete (s1 : S1) (s2 : S2) : T := fun κ hκ => ⟨s1 κ hκ, s2 κ hκ⟩

end Alignment.Shadows.ConvergenceTheorems.R109a

/-! ## `ConvergenceTheorems.R109b`

Text: "**Result 109b.** R₀ = T·κ for Poisson networks." -/
namespace Alignment.Shadows.ConvergenceTheorems.R109b

-- The text states no restriction on T, so the identity is required for every real τ; κ is the
-- Poisson parameter (κ > 0, as required by `poissonMoments`).

/-- Intended statement: for every τ and κ > 0, R₀ of the Poisson(κ) network is τ·κ. -/
@[sa_reference "ConvergenceTheorems.R109b"]
def T : Prop := ∀ (τ κ : ℝ) (hκ : 0 < κ), R0_heterogeneous τ (poissonMoments κ hκ) = τ * κ

/-- S1: the whole identity (a single atomic equation). -/
@[sa_shadow "ConvergenceTheorems.R109b" 1]
def S1 : Prop := ∀ (τ κ : ℝ) (hκ : 0 < κ), R0_heterogeneous τ (poissonMoments κ hκ) = τ * κ

@[sa_ref_forward "ConvergenceTheorems.R109b" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "ConvergenceTheorems.R109b"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.ConvergenceTheorems.R109b

/-! ## `ConvergenceTheorems.R110a`

Text: "**Result 110a.** θ = 1 is always a fixed point: f(1) = 1 when g(1) = 1." -/
namespace Alignment.Shadows.ConvergenceTheorems.R110a

-- Split along the colon: the value form "f(1) = 1 when g(1) = 1" (f(1) = `finalSizeMap τ (g 1)`,
-- i.e. `finalSizeMap τ 1` when g(1) = 1) and the fixed-point form "θ = 1 is a fixed point of
-- θ ↦ finalSizeMap τ (g θ)" for every g with g(1) = 1. "always": for every real τ.
-- VOCAB-GAP: the map as a function of θ needs a function g (the vocabulary takes only its value).

/-- Intended statement: for every τ, f(1) = 1 when g(1) = 1, and θ = 1 is a fixed point of the
final-size map for every normalised g. -/
@[sa_reference "ConvergenceTheorems.R110a"]
def T : Prop := (∀ τ : ℝ, finalSizeMap τ 1 = 1) ∧
  ∀ (τ : ℝ) (g : ℝ → ℝ), g 1 = 1 → Function.IsFixedPt (fun θ => finalSizeMap τ (g θ)) 1

/-- S1: f(1) = 1 when g(1) = 1, i.e. the map sends the value g(1) = 1 to 1, for every τ. -/
@[sa_shadow "ConvergenceTheorems.R110a" 1]
def S1 : Prop := ∀ τ : ℝ, finalSizeMap τ 1 = 1

/-- S2: θ = 1 is a fixed point of θ ↦ f(θ) for every τ and every g with g(1) = 1. -/
@[sa_shadow "ConvergenceTheorems.R110a" 2]
def S2 : Prop :=
  ∀ (τ : ℝ) (g : ℝ → ℝ), g 1 = 1 → Function.IsFixedPt (fun θ => finalSizeMap τ (g θ)) 1

@[sa_ref_forward "ConvergenceTheorems.R110a" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "ConvergenceTheorems.R110a" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "ConvergenceTheorems.R110a"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.ConvergenceTheorems.R110a

/-! ## `ConvergenceTheorems.R110c.2`

Text: "|f'(1)| ≤ 1 iff T · excessDeg ≤ 1 (since both T and excessDeg are nonneg)." -/
namespace Alignment.Shadows.ConvergenceTheorems.R110c_2

-- AMBIGUITY: "f'(1)" read (A) as the derivative at 1 of the final-size map θ ↦ finalSizeMap T (g θ)
-- (VOCAB-GAP: g modelled as in the module header), and (B) as the already computed value
-- f'(1) = T · excessDeg (Result 110b), so that the claim is |T·excessDeg| ≤ 1 ↔ T·excessDeg ≤ 1.
-- Both readings are required, each in both directions (S1–S4).
-- AMBIGUITY: "(since both T and excessDeg are nonneg)": T ≥ 0 is taken as a hypothesis (τ is a
-- real number); the nonnegativity of excessDeg is asserted by the text as a fact about degree
-- distributions, so it is not assumed. excessDeg is `m.excessDegree`.

/-- Intended statement: for τ ≥ 0 and any degree distribution, (A) for every normalised g with
g'(1) = ψ''(1)/ψ'(1), |f'(1)| ≤ 1 iff τ·excessDeg ≤ 1; and (B) |τ·excessDeg| ≤ 1 iff
τ·excessDeg ≤ 1. -/
@[sa_reference "ConvergenceTheorems.R110c.2"]
def T : Prop :=
  (∀ τ : ℝ, 0 ≤ τ → ∀ (m : PGFMoments) (g : ℝ → ℝ), g 1 = 1 →
    HasDerivAt g (m.secondFactorial / m.mean) 1 →
      (|deriv (fun θ => finalSizeMap τ (g θ)) 1| ≤ 1 ↔ τ * m.excessDegree ≤ 1)) ∧
  (∀ τ : ℝ, 0 ≤ τ → ∀ m : PGFMoments, (|τ * m.excessDegree| ≤ 1 ↔ τ * m.excessDegree ≤ 1))

/-- S1 (reading A, →): |f'(1)| ≤ 1 implies τ·excessDeg ≤ 1. -/
@[sa_shadow "ConvergenceTheorems.R110c.2" 1]
def S1 : Prop := ∀ τ : ℝ, 0 ≤ τ → ∀ (m : PGFMoments) (g : ℝ → ℝ), g 1 = 1 →
  HasDerivAt g (m.secondFactorial / m.mean) 1 →
    |deriv (fun θ => finalSizeMap τ (g θ)) 1| ≤ 1 → τ * m.excessDegree ≤ 1

/-- S2 (reading A, ←): τ·excessDeg ≤ 1 implies |f'(1)| ≤ 1. -/
@[sa_shadow "ConvergenceTheorems.R110c.2" 2]
def S2 : Prop := ∀ τ : ℝ, 0 ≤ τ → ∀ (m : PGFMoments) (g : ℝ → ℝ), g 1 = 1 →
  HasDerivAt g (m.secondFactorial / m.mean) 1 →
    τ * m.excessDegree ≤ 1 → |deriv (fun θ => finalSizeMap τ (g θ)) 1| ≤ 1

/-- S3 (reading B, →): |τ·excessDeg| ≤ 1 implies τ·excessDeg ≤ 1. -/
@[sa_shadow "ConvergenceTheorems.R110c.2" 3]
def S3 : Prop := ∀ τ : ℝ, 0 ≤ τ → ∀ m : PGFMoments,
  |τ * m.excessDegree| ≤ 1 → τ * m.excessDegree ≤ 1

/-- S4 (reading B, ←): τ·excessDeg ≤ 1 implies |τ·excessDeg| ≤ 1 (uses excessDeg ≥ 0). -/
@[sa_shadow "ConvergenceTheorems.R110c.2" 4]
def S4 : Prop := ∀ τ : ℝ, 0 ≤ τ → ∀ m : PGFMoments,
  τ * m.excessDegree ≤ 1 → |τ * m.excessDegree| ≤ 1

@[sa_ref_forward "ConvergenceTheorems.R110c.2" 1]
theorem ref_fwd1 : T → S1 := fun t τ hτ m g hg1 hg' => (t.1 τ hτ m g hg1 hg').mp

@[sa_ref_forward "ConvergenceTheorems.R110c.2" 2]
theorem ref_fwd2 : T → S2 := fun t τ hτ m g hg1 hg' => (t.1 τ hτ m g hg1 hg').mpr

@[sa_ref_forward "ConvergenceTheorems.R110c.2" 3]
theorem ref_fwd3 : T → S3 := fun t τ hτ m => (t.2 τ hτ m).mp

@[sa_ref_forward "ConvergenceTheorems.R110c.2" 4]
theorem ref_fwd4 : T → S4 := fun t τ hτ m => (t.2 τ hτ m).mpr

@[sa_complete "ConvergenceTheorems.R110c.2"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T :=
  ⟨fun τ hτ m g hg1 hg' => ⟨s1 τ hτ m g hg1 hg', s2 τ hτ m g hg1 hg'⟩,
   fun τ hτ m => ⟨s3 τ hτ m, s4 τ hτ m⟩⟩

end Alignment.Shadows.ConvergenceTheorems.R110c_2

/-! ## `ConvergenceTheorems.R110d`

Text: "**Result 110d.** When T = 0 (no transmission), the fixed point is trivially θ = 1." -/
namespace Alignment.Shadows.ConvergenceTheorems.R110d

-- AMBIGUITY: "the fixed point is θ = 1" (definite article) read as existence (θ = 1 is a fixed
-- point, S1) and uniqueness (every fixed point equals 1, S2) for the map θ ↦ finalSizeMap 0 (g θ).
-- VOCAB-GAP: the map as a function of θ needs a function g; g is any function with g(1) = 1
-- (the normalisation of g); θ ranges over all reals (the text does not restrict it).

/-- Intended statement: for T = 0 and every normalised g, θ = 1 is the unique fixed point of
θ ↦ finalSizeMap 0 (g θ). -/
@[sa_reference "ConvergenceTheorems.R110d"]
def T : Prop := ∀ g : ℝ → ℝ, g 1 = 1 →
  Function.IsFixedPt (fun θ => finalSizeMap 0 (g θ)) 1 ∧
    ∀ θ : ℝ, Function.IsFixedPt (fun θ => finalSizeMap 0 (g θ)) θ → θ = 1

/-- S1 (existence): θ = 1 is a fixed point when T = 0. -/
@[sa_shadow "ConvergenceTheorems.R110d" 1]
def S1 : Prop := ∀ g : ℝ → ℝ, g 1 = 1 → Function.IsFixedPt (fun θ => finalSizeMap 0 (g θ)) 1

/-- S2 (uniqueness): every fixed point equals 1 when T = 0. -/
@[sa_shadow "ConvergenceTheorems.R110d" 2]
def S2 : Prop := ∀ g : ℝ → ℝ, g 1 = 1 →
  ∀ θ : ℝ, Function.IsFixedPt (fun θ => finalSizeMap 0 (g θ)) θ → θ = 1

@[sa_ref_forward "ConvergenceTheorems.R110d" 1]
theorem ref_fwd1 : T → S1 := fun t g hg => (t g hg).1

@[sa_ref_forward "ConvergenceTheorems.R110d" 2]
theorem ref_fwd2 : T → S2 := fun t g hg => (t g hg).2

@[sa_complete "ConvergenceTheorems.R110d"]
theorem complete (s1 : S1) (s2 : S2) : T := fun g hg => ⟨s1 g hg, s2 g hg⟩

end Alignment.Shadows.ConvergenceTheorems.R110d

/-! ## `ConvergenceTheorems.R112a`

Text: "**Result 112a.** T_c = 1 / excessDegree." -/
namespace Alignment.Shadows.ConvergenceTheorems.R112a

-- T_c is `criticalTransmissibility m h`, which needs a proof `h : 0 < m.secondFactorial`; the
-- claim is required for every such m and h.

/-- Intended statement: for every degree distribution with ψ''(1) > 0, T_c = 1/excessDegree. -/
@[sa_reference "ConvergenceTheorems.R112a"]
def T : Prop := ∀ (m : PGFMoments) (h : 0 < m.secondFactorial),
  criticalTransmissibility m h = 1 / m.excessDegree

/-- S1: the whole identity (a single atomic equation). -/
@[sa_shadow "ConvergenceTheorems.R112a" 1]
def S1 : Prop := ∀ (m : PGFMoments) (h : 0 < m.secondFactorial),
  criticalTransmissibility m h = 1 / m.excessDegree

@[sa_ref_forward "ConvergenceTheorems.R112a" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "ConvergenceTheorems.R112a"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.ConvergenceTheorems.R112a

/-! ## `ConvergenceTheorems.R112b`

Text: "**Result 112b.** R₀ > 1 iff T > T_c: the epidemic threshold. R₀ = T · excessDeg > 1 ↔
T > 1/excessDeg (when excessDeg > 0)." -/
namespace Alignment.Shadows.ConvergenceTheorems.R112b

-- First sentence: R₀ > 1 ↔ T > T_c, both directions (S1, S2); T_c = `criticalTransmissibility m h`
-- needs h : 0 < m.secondFactorial. No restriction on T is stated: every real τ.
-- Second sentence, the chain "R₀ = T·excessDeg > 1 ↔ T > 1/excessDeg (when excessDeg > 0)":
-- the identity R₀ = T·excessDeg (S3) and R₀ > 1 ↔ T > 1/excessDeg under excessDeg > 0 (S4, S5);
-- together with S3 these give the displayed T·excessDeg > 1 ↔ T > 1/excessDeg (which on its own
-- is plain arithmetic about a positive real).
-- AMBIGUITY: "(when excessDeg > 0)" read as qualifying the equivalence, not the identity
-- R₀ = T·excessDeg (which is asserted unconditionally).
-- "the epidemic threshold" only names T_c and carries no further requirement.

/-- Intended statement: R₀ > 1 ↔ τ > T_c; R₀ = τ·excessDeg; and, when excessDeg > 0,
R₀ > 1 ↔ τ > 1/excessDeg. -/
@[sa_reference "ConvergenceTheorems.R112b"]
def T : Prop :=
  (∀ (τ : ℝ) (m : PGFMoments) (h : 0 < m.secondFactorial),
      1 < R0_heterogeneous τ m ↔ criticalTransmissibility m h < τ) ∧
    (∀ (τ : ℝ) (m : PGFMoments), R0_heterogeneous τ m = τ * m.excessDegree) ∧
      (∀ (τ : ℝ) (m : PGFMoments), 0 < m.excessDegree →
        (1 < R0_heterogeneous τ m ↔ 1 / m.excessDegree < τ))

/-- S1: R₀ > 1 implies τ > T_c. -/
@[sa_shadow "ConvergenceTheorems.R112b" 1]
def S1 : Prop := ∀ (τ : ℝ) (m : PGFMoments) (h : 0 < m.secondFactorial),
  1 < R0_heterogeneous τ m → criticalTransmissibility m h < τ

/-- S2: τ > T_c implies R₀ > 1. -/
@[sa_shadow "ConvergenceTheorems.R112b" 2]
def S2 : Prop := ∀ (τ : ℝ) (m : PGFMoments) (h : 0 < m.secondFactorial),
  criticalTransmissibility m h < τ → 1 < R0_heterogeneous τ m

/-- S3: R₀ = τ · excessDeg. -/
@[sa_shadow "ConvergenceTheorems.R112b" 3]
def S3 : Prop := ∀ (τ : ℝ) (m : PGFMoments), R0_heterogeneous τ m = τ * m.excessDegree

/-- S4: when excessDeg > 0, R₀ > 1 implies τ > 1/excessDeg. -/
@[sa_shadow "ConvergenceTheorems.R112b" 4]
def S4 : Prop := ∀ (τ : ℝ) (m : PGFMoments), 0 < m.excessDegree →
  1 < R0_heterogeneous τ m → 1 / m.excessDegree < τ

/-- S5: when excessDeg > 0, τ > 1/excessDeg implies R₀ > 1. -/
@[sa_shadow "ConvergenceTheorems.R112b" 5]
def S5 : Prop := ∀ (τ : ℝ) (m : PGFMoments), 0 < m.excessDegree →
  1 / m.excessDegree < τ → 1 < R0_heterogeneous τ m

@[sa_ref_forward "ConvergenceTheorems.R112b" 1]
theorem ref_fwd1 : T → S1 := fun t τ m h => (t.1 τ m h).mp

@[sa_ref_forward "ConvergenceTheorems.R112b" 2]
theorem ref_fwd2 : T → S2 := fun t τ m h => (t.1 τ m h).mpr

@[sa_ref_forward "ConvergenceTheorems.R112b" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.1

@[sa_ref_forward "ConvergenceTheorems.R112b" 4]
theorem ref_fwd4 : T → S4 := fun t τ m hm => (t.2.2 τ m hm).mp

@[sa_ref_forward "ConvergenceTheorems.R112b" 5]
theorem ref_fwd5 : T → S5 := fun t τ m hm => (t.2.2 τ m hm).mpr

@[sa_complete "ConvergenceTheorems.R112b"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T :=
  ⟨fun τ m h => ⟨s1 τ m h, s2 τ m h⟩, s3, fun τ m hm => ⟨s4 τ m hm, s5 τ m hm⟩⟩

end Alignment.Shadows.ConvergenceTheorems.R112b

/-! ## `ConvergenceTheorems.R112c`

Text: "**Result 112c.** The threshold depends only on first two moments. T_c = ⟨k⟩/⟨k(k-1)⟩ =
⟨k⟩/(⟨k²⟩ - ⟨k⟩)." -/
namespace Alignment.Shadows.ConvergenceTheorems.R112c

-- "depends only on first two moments": T_c is determined by ⟨k⟩ = `m.mean` and ⟨k²⟩ =
-- `m.secondMoment` (S1: two records with equal first two moments have equal T_c).
-- VOCAB-GAP: degree distributions exist only as `PGFMoments`, so "depends only on" is stated as a
-- functional dependence over moment records (it is also implied by the explicit formulas).
-- The chain "T_c = A = B" is split into T_c = ⟨k⟩/⟨k(k-1)⟩ (S2, ⟨k(k-1)⟩ = `m.secondFactorial`)
-- and T_c = ⟨k⟩/(⟨k²⟩ - ⟨k⟩) (S3).

/-- Intended statement: T_c depends only on (⟨k⟩, ⟨k²⟩), and T_c = ⟨k⟩/⟨k(k-1)⟩ = ⟨k⟩/(⟨k²⟩-⟨k⟩). -/
@[sa_reference "ConvergenceTheorems.R112c"]
def T : Prop :=
  (∀ (m₁ m₂ : PGFMoments) (h₁ : 0 < m₁.secondFactorial) (h₂ : 0 < m₂.secondFactorial),
      m₁.mean = m₂.mean → m₁.secondMoment = m₂.secondMoment →
        criticalTransmissibility m₁ h₁ = criticalTransmissibility m₂ h₂) ∧
    ∀ (m : PGFMoments) (h : 0 < m.secondFactorial),
      criticalTransmissibility m h = m.mean / m.secondFactorial ∧
        criticalTransmissibility m h = m.mean / (m.secondMoment - m.mean)

/-- S1: records with the same first two moments have the same threshold. -/
@[sa_shadow "ConvergenceTheorems.R112c" 1]
def S1 : Prop :=
  ∀ (m₁ m₂ : PGFMoments) (h₁ : 0 < m₁.secondFactorial) (h₂ : 0 < m₂.secondFactorial),
    m₁.mean = m₂.mean → m₁.secondMoment = m₂.secondMoment →
      criticalTransmissibility m₁ h₁ = criticalTransmissibility m₂ h₂

/-- S2: T_c = ⟨k⟩/⟨k(k-1)⟩. -/
@[sa_shadow "ConvergenceTheorems.R112c" 2]
def S2 : Prop := ∀ (m : PGFMoments) (h : 0 < m.secondFactorial),
  criticalTransmissibility m h = m.mean / m.secondFactorial

/-- S3: T_c = ⟨k⟩/(⟨k²⟩ - ⟨k⟩). -/
@[sa_shadow "ConvergenceTheorems.R112c" 3]
def S3 : Prop := ∀ (m : PGFMoments) (h : 0 < m.secondFactorial),
  criticalTransmissibility m h = m.mean / (m.secondMoment - m.mean)

@[sa_ref_forward "ConvergenceTheorems.R112c" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "ConvergenceTheorems.R112c" 2]
theorem ref_fwd2 : T → S2 := fun t m h => (t.2 m h).1

@[sa_ref_forward "ConvergenceTheorems.R112c" 3]
theorem ref_fwd3 : T → S3 := fun t m h => (t.2 m h).2

@[sa_complete "ConvergenceTheorems.R112c"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T :=
  ⟨s1, fun m h => ⟨s2 m h, s3 m h⟩⟩

end Alignment.Shadows.ConvergenceTheorems.R112c

/-! ## `ConvergenceTheorems.R112d`

Text: "**Result 112d.** For Poisson(κ), T_c = 1/κ." -/
namespace Alignment.Shadows.ConvergenceTheorems.R112d

-- T_c needs a proof that ψ''(1) > 0 for the Poisson record; the claim is required for every
-- κ > 0 and every such proof (proof irrelevance makes this the same as for a canonical one).

/-- Intended statement: for every κ > 0, the Poisson(κ) critical transmissibility is 1/κ. -/
@[sa_reference "ConvergenceTheorems.R112d"]
def T : Prop := ∀ (κ : ℝ) (hκ : 0 < κ) (h : 0 < (poissonMoments κ hκ).secondFactorial),
  criticalTransmissibility (poissonMoments κ hκ) h = 1 / κ

/-- S1: the whole identity (a single atomic equation). -/
@[sa_shadow "ConvergenceTheorems.R112d" 1]
def S1 : Prop := ∀ (κ : ℝ) (hκ : 0 < κ) (h : 0 < (poissonMoments κ hκ).secondFactorial),
  criticalTransmissibility (poissonMoments κ hκ) h = 1 / κ

@[sa_ref_forward "ConvergenceTheorems.R112d" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "ConvergenceTheorems.R112d"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.ConvergenceTheorems.R112d

/-! ## `ConvergenceTheorems.R112e`

Text: "**Result 112e.** Higher variance lowers the epidemic threshold. If m₁ and m₂ have the same
mean but Var(m₁) ≤ Var(m₂), then T_c(m₂) ≤ T_c(m₁): more heterogeneous networks have lower
thresholds." -/
namespace Alignment.Shadows.ConvergenceTheorems.R112e

-- AMBIGUITY: "lowers" / "lower thresholds" could suggest a strict decrease; the precise
-- "If ... then" sentence states the non-strict monotonicity T_c(m₂) ≤ T_c(m₁), which is adopted.
-- T_c needs proofs of ψ''(1) > 0 for both records; the claim is required for all such proofs.

/-- Intended statement: equal means and Var(m₁) ≤ Var(m₂) imply T_c(m₂) ≤ T_c(m₁). -/
@[sa_reference "ConvergenceTheorems.R112e"]
def T : Prop :=
  ∀ (m₁ m₂ : PGFMoments) (h₁ : 0 < m₁.secondFactorial) (h₂ : 0 < m₂.secondFactorial),
    m₁.mean = m₂.mean → m₁.variance ≤ m₂.variance →
      criticalTransmissibility m₂ h₂ ≤ criticalTransmissibility m₁ h₁

/-- S1: the whole monotonicity statement (a single atomic implication). -/
@[sa_shadow "ConvergenceTheorems.R112e" 1]
def S1 : Prop :=
  ∀ (m₁ m₂ : PGFMoments) (h₁ : 0 < m₁.secondFactorial) (h₂ : 0 < m₂.secondFactorial),
    m₁.mean = m₂.mean → m₁.variance ≤ m₂.variance →
      criticalTransmissibility m₂ h₂ ≤ criticalTransmissibility m₁ h₁

@[sa_ref_forward "ConvergenceTheorems.R112e" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "ConvergenceTheorems.R112e"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.ConvergenceTheorems.R112e

noncomputable section

/-! ## `ConvergenceTheorems.R105` (blind)

Text: "For a Poisson(κ) degree distribution with per-edge transmission rate β̃ and recovery γ̃, the
susceptible curve S(t) of the EBCM coincides with that of classical SIR with effective rates:
β = κ β̃ and γ = γ̃ + β̃; the infected curves differ (Rempała 2023)."

Poisson EBCM (Result 105 key identity): `θ̇ = −β̃θ + β̃e^{κ(θ−1)} + γ̃(1−θ)`, `S = e^{κ(θ−1)}`,
network recovery `Ṙ = γ̃·I_net` with network prevalence `I_net = 1 − S − R`. Classical SIR:
`Ṡ = −βSI`, `İ = βSI − γI`. The effective rates are the operations `effective_beta`,
`effective_gamma`. "Coincides" is read as: along every EBCM solution, `S(t)` together with some
infected curve `I` solves classical SIR (S1). "The infected curves differ": that SIR infected
curve is not the network prevalence of the EBCM, for some solution and time (S2). -/
namespace Alignment.Shadows.ConvergenceTheorems.R105

/-- Right-hand side of the Poisson EBCM ODE. -/
def ebcmRHS (d : PoissonEBCMData) (x : ℝ) : ℝ :=
  -d.beta_tilde * x + d.beta_tilde * Real.exp (d.kappa * (x - 1)) + d.gamma_tilde * (1 - x)
/-- Susceptible fraction `S = e^{κ(θ−1)}`. -/
def Sof (d : PoissonEBCMData) (x : ℝ) : ℝ := Real.exp (d.kappa * (x - 1))
/-- `(S, I)` solves classical SIR with rates `β`, `γ`. -/
def IsSIR (β γ : ℝ) (S I : ℝ → ℝ) : Prop :=
  (∀ t, HasDerivAt S (-β * S t * I t) t) ∧ (∀ t, HasDerivAt I (β * S t * I t - γ * I t) t)

@[sa_reference "ConvergenceTheorems.R105"]
def T : Prop :=
  (∀ (d : PoissonEBCMData) (θ : ℝ → ℝ), (∀ t, HasDerivAt θ (ebcmRHS d (θ t)) t) →
      ∃ I : ℝ → ℝ, IsSIR (effective_beta d) (effective_gamma d) (fun t => Sof d (θ t)) I) ∧
  (∃ (d : PoissonEBCMData) (θ R I : ℝ → ℝ) (t : ℝ), (∀ s, HasDerivAt θ (ebcmRHS d (θ s)) s) ∧
      (∀ s, HasDerivAt R (d.gamma_tilde * (1 - Sof d (θ s) - R s)) s) ∧
      IsSIR (effective_beta d) (effective_gamma d) (fun s => Sof d (θ s)) I ∧
      I t ≠ 1 - Sof d (θ t) - R t)

/-- S1: the EBCM susceptible curve is the susceptible curve of classical SIR with the effective
rates. -/
@[sa_shadow "ConvergenceTheorems.R105" 1]
def S1 : Prop :=
  ∀ (d : PoissonEBCMData) (θ : ℝ → ℝ), (∀ t, HasDerivAt θ (ebcmRHS d (θ t)) t) →
    ∃ I : ℝ → ℝ, IsSIR (effective_beta d) (effective_gamma d) (fun t => Sof d (θ t)) I
/-- S2: the SIR infected curve differs from the network prevalence. -/
@[sa_shadow "ConvergenceTheorems.R105" 2]
def S2 : Prop :=
  ∃ (d : PoissonEBCMData) (θ R I : ℝ → ℝ) (t : ℝ), (∀ s, HasDerivAt θ (ebcmRHS d (θ s)) s) ∧
    (∀ s, HasDerivAt R (d.gamma_tilde * (1 - Sof d (θ s) - R s)) s) ∧
    IsSIR (effective_beta d) (effective_gamma d) (fun s => Sof d (θ s)) I ∧
    I t ≠ 1 - Sof d (θ t) - R t

@[sa_ref_forward "ConvergenceTheorems.R105" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "ConvergenceTheorems.R105" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "ConvergenceTheorems.R105"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.ConvergenceTheorems.R105

/-! ## `ConvergenceTheorems.R105.keyIdentity` (blind)

Text: "Key algebraic identity: the Poisson EBCM ODE θ̇ = -β̃ θ + β̃ exp(κ(θ-1)) + γ̃(1-θ) reduces to
dS/dt = -β S I when S = exp(κ(θ-1)) and I := φ_I (the probability that a partner is infectious and
has not yet transmitted), not the network prevalence."

In the EBCM, `θ̇ = −β̃·φ_I`, so `φ_I = −θ̇/β̃` is read off the right-hand side. β is the effective
mass-action rate `effective_beta` (β = κβ̃, Result 105). "Not the network prevalence": for some
EBCM solution with network recovery `Ṙ = γ̃(1 − S − R)`, `φ_I ≠ 1 − S − R` at some time. -/
namespace Alignment.Shadows.ConvergenceTheorems.R105_keyIdentity

/-- Right-hand side of the Poisson EBCM ODE. -/
def ebcmRHS (d : PoissonEBCMData) (x : ℝ) : ℝ :=
  -d.beta_tilde * x + d.beta_tilde * Real.exp (d.kappa * (x - 1)) + d.gamma_tilde * (1 - x)
/-- Susceptible fraction `S = e^{κ(θ−1)}`. -/
def Sof (d : PoissonEBCMData) (x : ℝ) : ℝ := Real.exp (d.kappa * (x - 1))
/-- `φ_I` read off the EBCM: `θ̇ = −β̃ φ_I`. -/
def phiI (d : PoissonEBCMData) (x : ℝ) : ℝ := -(ebcmRHS d x) / d.beta_tilde

@[sa_reference "ConvergenceTheorems.R105.keyIdentity"]
def T : Prop :=
  (∀ (d : PoissonEBCMData) (θ : ℝ → ℝ) (t : ℝ), HasDerivAt θ (ebcmRHS d (θ t)) t →
      HasDerivAt (fun s => Sof d (θ s)) (-effective_beta d * Sof d (θ t) * phiI d (θ t)) t) ∧
  (∃ (d : PoissonEBCMData) (θ R : ℝ → ℝ) (t : ℝ), (∀ s, HasDerivAt θ (ebcmRHS d (θ s)) s) ∧
      (∀ s, HasDerivAt R (d.gamma_tilde * (1 - Sof d (θ s) - R s)) s) ∧
      phiI d (θ t) ≠ 1 - Sof d (θ t) - R t)

/-- S1: along the EBCM, `dS/dt = −β S φ_I`. -/
@[sa_shadow "ConvergenceTheorems.R105.keyIdentity" 1]
def S1 : Prop :=
  ∀ (d : PoissonEBCMData) (θ : ℝ → ℝ) (t : ℝ), HasDerivAt θ (ebcmRHS d (θ t)) t →
    HasDerivAt (fun s => Sof d (θ s)) (-effective_beta d * Sof d (θ t) * phiI d (θ t)) t
/-- S2: `φ_I` is not the network prevalence. -/
@[sa_shadow "ConvergenceTheorems.R105.keyIdentity" 2]
def S2 : Prop :=
  ∃ (d : PoissonEBCMData) (θ R : ℝ → ℝ) (t : ℝ), (∀ s, HasDerivAt θ (ebcmRHS d (θ s)) s) ∧
    (∀ s, HasDerivAt R (d.gamma_tilde * (1 - Sof d (θ s) - R s)) s) ∧
    phiI d (θ t) ≠ 1 - Sof d (θ t) - R t

@[sa_ref_forward "ConvergenceTheorems.R105.keyIdentity" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t.1
@[sa_ref_forward "ConvergenceTheorems.R105.keyIdentity" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2
@[sa_complete "ConvergenceTheorems.R105.keyIdentity"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.ConvergenceTheorems.R105_keyIdentity

/-! ## `ConvergenceTheorems.R105c.1` (blind)

Text: "**Result 105c.** Transmissibility consistency: with β = κβ̃ and γ = γ̃ + β̃, the mass-action
R₀ is β/γ = κβ̃/(β̃ + γ̃)."

β and γ are the effective rates `effective_beta`, `effective_gamma`. -/
namespace Alignment.Shadows.ConvergenceTheorems.R105c_1

@[sa_reference "ConvergenceTheorems.R105c.1"]
def T : Prop :=
  ∀ d : PoissonEBCMData,
    effective_beta d / effective_gamma d = d.kappa * d.beta_tilde / (d.beta_tilde + d.gamma_tilde)

/-- S1: `β/γ = κβ̃/(β̃+γ̃)` for the effective rates. -/
@[sa_shadow "ConvergenceTheorems.R105c.1" 1]
def S1 : Prop :=
  ∀ d : PoissonEBCMData,
    effective_beta d / effective_gamma d = d.kappa * d.beta_tilde / (d.beta_tilde + d.gamma_tilde)

@[sa_ref_forward "ConvergenceTheorems.R105c.1" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "ConvergenceTheorems.R105c.1"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.ConvergenceTheorems.R105c_1

/-! ## `ConvergenceTheorems.R105c.2` (blind)

Text: "With the edge-based transmissibility T_edge = β̃/(β̃ + γ̃), the mass-action R₀ is exactly
T_edge · κ, the Poisson EBCM R₀ (`R0_massAction_eq_edge`)."

The mass-action R₀ is `effective_beta d / effective_gamma d`; the Poisson EBCM R₀ is
`R0_heterogeneous T_edge (poissonMoments κ)`. -/
namespace Alignment.Shadows.ConvergenceTheorems.R105c_2

/-- `T_edge = β̃/(β̃ + γ̃)`. -/
def Tedge (d : PoissonEBCMData) : ℝ := d.beta_tilde / (d.beta_tilde + d.gamma_tilde)

@[sa_reference "ConvergenceTheorems.R105c.2"]
def T : Prop :=
  (∀ d : PoissonEBCMData, effective_beta d / effective_gamma d = Tedge d * d.kappa) ∧
  (∀ d : PoissonEBCMData,
      R0_heterogeneous (Tedge d) (poissonMoments d.kappa d.kappa_pos) = Tedge d * d.kappa)

/-- S1: the mass-action R₀ is `T_edge·κ`. -/
@[sa_shadow "ConvergenceTheorems.R105c.2" 1]
def S1 : Prop := ∀ d : PoissonEBCMData, effective_beta d / effective_gamma d = Tedge d * d.kappa
/-- S2: `T_edge·κ` is the Poisson EBCM R₀. -/
@[sa_shadow "ConvergenceTheorems.R105c.2" 2]
def S2 : Prop :=
  ∀ d : PoissonEBCMData,
    R0_heterogeneous (Tedge d) (poissonMoments d.kappa d.kappa_pos) = Tedge d * d.kappa

@[sa_ref_forward "ConvergenceTheorems.R105c.2" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "ConvergenceTheorems.R105c.2" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "ConvergenceTheorems.R105c.2"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.ConvergenceTheorems.R105c_2

/-! ## `ConvergenceTheorems.R105c.3` (blind)

Text: "There is no large-κ approximation: the two R₀ agree for every κ."

The two R₀ are the mass-action `β/γ` (effective rates) and the Poisson EBCM R₀
`R0_heterogeneous T_edge (poissonMoments κ)` with `T_edge = β̃/(β̃+γ̃)`. -/
namespace Alignment.Shadows.ConvergenceTheorems.R105c_3

/-- `T_edge = β̃/(β̃ + γ̃)`. -/
def Tedge (d : PoissonEBCMData) : ℝ := d.beta_tilde / (d.beta_tilde + d.gamma_tilde)

@[sa_reference "ConvergenceTheorems.R105c.3"]
def T : Prop :=
  ∀ d : PoissonEBCMData, effective_beta d / effective_gamma d =
    R0_heterogeneous (Tedge d) (poissonMoments d.kappa d.kappa_pos)

/-- S1: the two R₀ agree for every κ (and all rates). -/
@[sa_shadow "ConvergenceTheorems.R105c.3" 1]
def S1 : Prop :=
  ∀ d : PoissonEBCMData, effective_beta d / effective_gamma d =
    R0_heterogeneous (Tedge d) (poissonMoments d.kappa d.kappa_pos)

@[sa_ref_forward "ConvergenceTheorems.R105c.3" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "ConvergenceTheorems.R105c.3"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.ConvergenceTheorems.R105c_3

/-! ## `ConvergenceTheorems.R110.stability` (re-authored blind)

Text: "For strictly convex f (some degree ≥ 3 has positive probability) it is the only fixed point
in [0, 1] iff R₀ ≤ 1, where R₀ = f'(1) (not formalised here)."

"It" is θ = 1, the trivial fixed point of the final-size map `f(θ) = finalSizeMap T (g θ)`
(`= 1 − T + T·g(θ)`, `g(1) = 1`). Strict convexity is taken as a hypothesis on [0, 1] (the text's
parenthesis gives the reason it holds); R₀ = f'(1) is the derivative of f at 1 within [0, 1].
-- AMBIGUITY: the side conditions needed for a fixed point to exist below 1 when R₀ > 1 are read
as `0 < T ≤ 1` and `0 ≤ g ≤ 1` on [0, 1] (g(θ) = ψ'(θ)/ψ'(1) for a PGF ψ), with f continuous. -/
namespace Alignment.Shadows.ConvergenceTheorems.R110_stability

open Set

/-- The hypotheses of the text on `T`, `g` and `R₀ = f'(1)`. -/
def Hyp (T : ℝ) (g : ℝ → ℝ) (R0 : ℝ) : Prop :=
  0 < T ∧ T ≤ 1 ∧ g 1 = 1 ∧ (∀ θ ∈ Icc (0 : ℝ) 1, 0 ≤ g θ ∧ g θ ≤ 1) ∧
    ContinuousOn g (Icc 0 1) ∧ StrictConvexOn ℝ (Icc 0 1) (fun θ => finalSizeMap T (g θ)) ∧
    HasDerivWithinAt (fun θ => finalSizeMap T (g θ)) R0 (Icc 0 1) 1

/-- θ = 1 is the only fixed point of `f` in [0, 1]. -/
def OnlyFixedOne (T : ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ θ ∈ Icc (0 : ℝ) 1, finalSizeMap T (g θ) = θ → θ = 1

@[sa_reference "ConvergenceTheorems.R110.stability"]
def T : Prop :=
  ∀ (T : ℝ) (g : ℝ → ℝ) (R0 : ℝ), Hyp T g R0 → (OnlyFixedOne T g ↔ R0 ≤ 1)

/-- S1 (→): if θ = 1 is the only fixed point, then R₀ ≤ 1. -/
@[sa_shadow "ConvergenceTheorems.R110.stability" 1]
def S1 : Prop := ∀ (T : ℝ) (g : ℝ → ℝ) (R0 : ℝ), Hyp T g R0 → OnlyFixedOne T g → R0 ≤ 1
/-- S2 (←): if R₀ ≤ 1, then θ = 1 is the only fixed point. -/
@[sa_shadow "ConvergenceTheorems.R110.stability" 2]
def S2 : Prop := ∀ (T : ℝ) (g : ℝ → ℝ) (R0 : ℝ), Hyp T g R0 → R0 ≤ 1 → OnlyFixedOne T g

@[sa_ref_forward "ConvergenceTheorems.R110.stability" 1] theorem ref_fwd1 : T → S1 :=
  fun t T g R0 h => (t T g R0 h).1
@[sa_ref_forward "ConvergenceTheorems.R110.stability" 2] theorem ref_fwd2 : T → S2 :=
  fun t T g R0 h => (t T g R0 h).2
@[sa_complete "ConvergenceTheorems.R110.stability"]
theorem complete (s1 : S1) (s2 : S2) : T := fun T g R0 h => ⟨s1 T g R0 h, s2 T g R0 h⟩

end Alignment.Shadows.ConvergenceTheorems.R110_stability

/-! ## `ConvergenceTheorems.R110b.2` (blind)

Text: "Linear stability of θ = 1 needs |f'(1)| < 1, i.e. R₀ < 1; at R₀ = 1 the linearisation is
inconclusive, and θ = 1 is still attracting from below when f is strictly convex."

`f(θ) = finalSizeMap T (g θ)`; `R₀ = T·g'(1)` (g'(1) = ψ''(1)/ψ'(1) ≥ 0). S1 formalises "|f'(1)| < 1,
i.e. R₀ < 1": whenever f has derivative f' at 1, `|f'| < 1 ↔ T·g'(1) < 1` (T ≥ 0). S2 formalises
"attracting from below": at R₀ = f'(1) = 1, for strictly convex, monotone, continuous f on [0, 1]
with f(1) = 1 and f(0) ≥ 0, the iterates from every θ₀ ∈ [0, 1) converge to 1. "The linearisation
is inconclusive" is a remark about the method and is not formalised. -/
namespace Alignment.Shadows.ConvergenceTheorems.R110b_2

open Set Filter Topology

@[sa_reference "ConvergenceTheorems.R110b.2"]
def T : Prop :=
  (∀ (T : ℝ) (g : ℝ → ℝ) (g' f' : ℝ), 0 ≤ T → 0 ≤ g' → HasDerivAt g g' 1 →
      HasDerivAt (fun θ => finalSizeMap T (g θ)) f' 1 → (|f'| < 1 ↔ T * g' < 1)) ∧
  (∀ (T : ℝ) (g : ℝ → ℝ), 0 < T → T ≤ 1 →
      StrictConvexOn ℝ (Icc 0 1) (fun θ => finalSizeMap T (g θ)) →
      MonotoneOn (fun θ => finalSizeMap T (g θ)) (Icc 0 1) →
      ContinuousOn (fun θ => finalSizeMap T (g θ)) (Icc 0 1) →
      finalSizeMap T (g 1) = 1 → 0 ≤ finalSizeMap T (g 0) →
      HasDerivWithinAt (fun θ => finalSizeMap T (g θ)) 1 (Icc 0 1) 1 →
      ∀ θ₀ ∈ Ico (0 : ℝ) 1,
        Tendsto (fun k : ℕ => (fun θ => finalSizeMap T (g θ))^[k] θ₀) atTop (𝓝 1))

/-- S1: `|f'(1)| < 1` iff `R₀ = T·g'(1) < 1`. -/
@[sa_shadow "ConvergenceTheorems.R110b.2" 1]
def S1 : Prop :=
  ∀ (T : ℝ) (g : ℝ → ℝ) (g' f' : ℝ), 0 ≤ T → 0 ≤ g' → HasDerivAt g g' 1 →
    HasDerivAt (fun θ => finalSizeMap T (g θ)) f' 1 → (|f'| < 1 ↔ T * g' < 1)
/-- S2: at R₀ = 1, θ = 1 attracts the iteration from below when f is strictly convex. -/
@[sa_shadow "ConvergenceTheorems.R110b.2" 2]
def S2 : Prop :=
  ∀ (T : ℝ) (g : ℝ → ℝ), 0 < T → T ≤ 1 →
    StrictConvexOn ℝ (Icc 0 1) (fun θ => finalSizeMap T (g θ)) →
    MonotoneOn (fun θ => finalSizeMap T (g θ)) (Icc 0 1) →
    ContinuousOn (fun θ => finalSizeMap T (g θ)) (Icc 0 1) →
    finalSizeMap T (g 1) = 1 → 0 ≤ finalSizeMap T (g 0) →
    HasDerivWithinAt (fun θ => finalSizeMap T (g θ)) 1 (Icc 0 1) 1 →
    ∀ θ₀ ∈ Ico (0 : ℝ) 1,
      Tendsto (fun k : ℕ => (fun θ => finalSizeMap T (g θ))^[k] θ₀) atTop (𝓝 1)

@[sa_ref_forward "ConvergenceTheorems.R110b.2" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "ConvergenceTheorems.R110b.2" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "ConvergenceTheorems.R110b.2"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.ConvergenceTheorems.R110b_2

/-! ## `ConvergenceTheorems.r0MassActionEqEdge` (blind)

Text: "The mass-action R₀ β/γ with β = κβ̃ and γ = γ̃ + β̃ equals the Poisson EBCM R₀
κ · T_edge = κ · β̃/(β̃ + γ̃), exactly."

β, γ are `effective_beta`, `effective_gamma`; the Poisson EBCM R₀ is
`R0_heterogeneous T_edge (poissonMoments κ)`. -/
namespace Alignment.Shadows.ConvergenceTheorems.r0MassActionEqEdge

/-- `T_edge = β̃/(β̃ + γ̃)`. -/
def Tedge (d : PoissonEBCMData) : ℝ := d.beta_tilde / (d.beta_tilde + d.gamma_tilde)

@[sa_reference "ConvergenceTheorems.r0MassActionEqEdge"]
def T : Prop :=
  (∀ d : PoissonEBCMData, effective_beta d / effective_gamma d = d.kappa * Tedge d) ∧
  (∀ d : PoissonEBCMData, effective_beta d / effective_gamma d =
      R0_heterogeneous (Tedge d) (poissonMoments d.kappa d.kappa_pos))

/-- S1: `β/γ = κ·T_edge`. -/
@[sa_shadow "ConvergenceTheorems.r0MassActionEqEdge" 1]
def S1 : Prop := ∀ d : PoissonEBCMData, effective_beta d / effective_gamma d = d.kappa * Tedge d
/-- S2: `β/γ` is the Poisson EBCM R₀. -/
@[sa_shadow "ConvergenceTheorems.r0MassActionEqEdge" 2]
def S2 : Prop :=
  ∀ d : PoissonEBCMData, effective_beta d / effective_gamma d =
    R0_heterogeneous (Tedge d) (poissonMoments d.kappa d.kappa_pos)

@[sa_ref_forward "ConvergenceTheorems.r0MassActionEqEdge" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t.1
@[sa_ref_forward "ConvergenceTheorems.r0MassActionEqEdge" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2
@[sa_complete "ConvergenceTheorems.r0MassActionEqEdge"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.ConvergenceTheorems.r0MassActionEqEdge

/-! ## `ConvergenceTheorems.sThetaChainRule` (blind)

Text: "The chain rule behind Result 105e: if `θ` has derivative `θ'` at `t`, then
`S = exp(κ(θ − 1))` has derivative `κ · S · θ'` at `t`."

κ is the Poisson mean degree of the Result 105 data. -/
namespace Alignment.Shadows.ConvergenceTheorems.sThetaChainRule

@[sa_reference "ConvergenceTheorems.sThetaChainRule"]
def T : Prop :=
  ∀ (d : PoissonEBCMData) (θ : ℝ → ℝ) (θ' t : ℝ), HasDerivAt θ θ' t →
    HasDerivAt (fun s => Real.exp (d.kappa * (θ s - 1)))
      (d.kappa * Real.exp (d.kappa * (θ t - 1)) * θ') t

/-- S1: the chain rule for `S = exp(κ(θ − 1))`. -/
@[sa_shadow "ConvergenceTheorems.sThetaChainRule" 1]
def S1 : Prop :=
  ∀ (d : PoissonEBCMData) (θ : ℝ → ℝ) (θ' t : ℝ), HasDerivAt θ θ' t →
    HasDerivAt (fun s => Real.exp (d.kappa * (θ s - 1)))
      (d.kappa * Real.exp (d.kappa * (θ t - 1)) * θ') t

@[sa_ref_forward "ConvergenceTheorems.sThetaChainRule" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "ConvergenceTheorems.sThetaChainRule"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.ConvergenceTheorems.sThetaChainRule

/-! ## `ConvergenceTheorems.finalSizeMapHasDerivAt` (blind)

Text: "The derivative of the final-size map: if `g` has derivative `g'` at `x`, then
`θ ↦ f(θ) = 1 − T + T·g(θ)` has derivative `T·g'` at `x`."

The final-size map is the operation `finalSizeMap T (g θ)`. -/
namespace Alignment.Shadows.ConvergenceTheorems.finalSizeMapHasDerivAt

@[sa_reference "ConvergenceTheorems.finalSizeMapHasDerivAt"]
def T : Prop :=
  ∀ (T : ℝ) (g : ℝ → ℝ) (g' x : ℝ), HasDerivAt g g' x →
    HasDerivAt (fun θ => finalSizeMap T (g θ)) (T * g') x

/-- S1: the derivative of the final-size map is `T·g'`. -/
@[sa_shadow "ConvergenceTheorems.finalSizeMapHasDerivAt" 1]
def S1 : Prop :=
  ∀ (T : ℝ) (g : ℝ → ℝ) (g' x : ℝ), HasDerivAt g g' x →
    HasDerivAt (fun θ => finalSizeMap T (g θ)) (T * g') x

@[sa_ref_forward "ConvergenceTheorems.finalSizeMapHasDerivAt" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t
@[sa_complete "ConvergenceTheorems.finalSizeMapHasDerivAt"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.ConvergenceTheorems.finalSizeMapHasDerivAt

/-! ## `ConvergenceTheorems.dfeDerivativeAbsLeOneIff` (blind)

Text: "For `T ≥ 0` and `excessDeg ≥ 0`, `|f'(1)| ≤ 1 ↔ R₀ ≤ 1`, where `f'(1) = R₀ = T · excessDeg`."

The final clause defines the notation: `f'(1)` and `R₀` both denote `T · excessDeg`, for real
`T` and `excessDeg`. The statement is therefore a statement about reals only. -/
namespace Alignment.Shadows.ConvergenceTheorems.dfeDerivativeAbsLeOneIff

@[sa_reference "ConvergenceTheorems.dfeDerivativeAbsLeOneIff"]
def T : Prop :=
  ∀ T e : ℝ, 0 ≤ T → 0 ≤ e → (|T * e| ≤ 1 ↔ T * e ≤ 1)

/-- S1 (→): `|f'(1)| ≤ 1 → R₀ ≤ 1`. -/
@[sa_shadow "ConvergenceTheorems.dfeDerivativeAbsLeOneIff" 1]
def S1 : Prop := ∀ T e : ℝ, 0 ≤ T → 0 ≤ e → |T * e| ≤ 1 → T * e ≤ 1
/-- S2 (←): `R₀ ≤ 1 → |f'(1)| ≤ 1`. -/
@[sa_shadow "ConvergenceTheorems.dfeDerivativeAbsLeOneIff" 2]
def S2 : Prop := ∀ T e : ℝ, 0 ≤ T → 0 ≤ e → T * e ≤ 1 → |T * e| ≤ 1

@[sa_ref_forward "ConvergenceTheorems.dfeDerivativeAbsLeOneIff" 1] theorem ref_fwd1 : T → S1 :=
  fun t T e h1 h2 => (t T e h1 h2).1
@[sa_ref_forward "ConvergenceTheorems.dfeDerivativeAbsLeOneIff" 2] theorem ref_fwd2 : T → S2 :=
  fun t T e h1 h2 => (t T e h1 h2).2
@[sa_complete "ConvergenceTheorems.dfeDerivativeAbsLeOneIff"]
theorem complete (s1 : S1) (s2 : S2) : T := fun T e h1 h2 => ⟨s1 T e h1 h2, s2 T e h1 h2⟩

end Alignment.Shadows.ConvergenceTheorems.dfeDerivativeAbsLeOneIff

/-! ## `ConvergenceTheorems.R105e.2` — not formalised (re-authored blind)

Text: "The Lean statement `kappa * S = kappa * S` is tautological: it holds by reflexivity. The
chain rule itself is `S_theta_chain_rule`." The text describes a Lean statement (and points to
another theorem); it asserts no proposition about the model, and the only formula it quotes is a
reflexivity instance. The earlier shadow set for this id was removed. -/
namespace Alignment.Shadows.ConvergenceTheorems.R105e_2
end Alignment.Shadows.ConvergenceTheorems.R105e_2

/-! ## `ConvergenceTheorems.R110b.3` — not formalised (re-authored blind)

Text: "**Tautological Lean statement:** `T * excessDeg = T * excessDeg`; the derivative is computed
in `finalSizeMap_hasDerivAt`." A remark about a Lean statement (a reflexivity instance) and a
pointer to another theorem; no proposition to shadow. The earlier shadow set for this id was
removed. -/
namespace Alignment.Shadows.ConvergenceTheorems.R110b_3
end Alignment.Shadows.ConvergenceTheorems.R110b_3

end
