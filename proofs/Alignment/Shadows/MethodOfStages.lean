import Alignment.Registry
import EBCMCategory.MethodOfStages
import Mathlib

/-!
# Blind shadow sets: group `MethodOfStages`

Written blind: the author read only the claims' entries in `Alignment/claims_blind.yaml`,
`Alignment/DataTypes/MethodOfStages.md`, `Alignment/README.md`, `Alignment/Example/ExampleShadows.lean`,
Mathlib sources, and (for the meaning of "transmissibility") passages of `papers/*.md`.

Data types used: `ErlangParams` (fields `n : ℕ`, `gamma : ℝ`, invariants `0 < n`, `0 < gamma`),
the parameters of the Erlang(n, nγ) distribution, i.e. n sequential sub-stages each with rate nγ
(module header text).

VOCAB-GAP (group-wide): the DataTypes file lists **no** operations. There is no Erlang/exponential
distribution object, no mean/variance/CV operation, no transmissibility operation and no ODE-model
object in the vocabulary. Following DataTypes §(d), the text's distributional notions are stated with
Mathlib: Erlang(n, λ) is `ProbabilityTheory.gammaMeasure n λ` (Gamma with shape n and rate λ), the
mean is `∫ x, x ∂μ`, the variance is `ProbabilityTheory.variance (fun x => x) μ`. Where the text
writes a chain `A = B = C` whose first member is a distributional quantity, the shadows split it
into the distributional equation `A = B` and the arithmetic identity `B = C`, so that both the
distributional reading and the purely arithmetic reading are required.

Re-authored blind (second pass, from the current claim texts, `DataTypes/*.md`, the README,
`SA-PASS_SKILL.md`, `Example/ExampleShadows.lean` and background papers only): the blocks marked
"(re-authored blind)" or "(blind)" near the end of this file (with any `Shared2` helper
namespace).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology

namespace Alignment.Shadows.MethodOfStages

/-- The Erlang(n, nγ) distribution (n sub-stages, each of rate nγ): Gamma with shape `n` and
rate `n * γ`. -/
def erlangMeasure (n : ℕ) (γ : ℝ) : Measure ℝ := gammaMeasure (n : ℝ) ((n : ℝ) * γ)

/-- Mean E[Erlang(n, nγ)] = ∫ x dErlang(n, nγ)(x). -/
def erlangMean (n : ℕ) (γ : ℝ) : ℝ := ∫ x, x ∂(erlangMeasure n γ)

/-- Variance Var[Erlang(n, nγ)] of the identity random variable under Erlang(n, nγ). -/
def erlangVar (n : ℕ) (γ : ℝ) : ℝ := variance (fun x => x) (erlangMeasure n γ)

end Alignment.Shadows.MethodOfStages

/-! ### `MethodOfStages.R87`

Blind text: "Result 87: Erlang(1,γ) is Exponential(γ) When n=1, the sub-stage rate is 1·γ = γ,
recovering the exponential." -/

namespace Alignment.Shadows.MethodOfStages.R87

/-- Density of Exponential(γ), in primitive terms: `γ e^{-γx}` for `x ≥ 0`, `0` otherwise.
VOCAB-GAP: Mathlib's `exponentialPDFReal r` is *defined* as `gammaPDFReal 1 r` and `expMeasure r`
as `gammaMeasure 1 r`; using them would make "Erlang(1,γ) is Exponential(γ)" hold by `rfl`, so the
exponential law is written out explicitly here. -/
def expDensity (γ x : ℝ) : ℝ := if 0 ≤ x then γ * Real.exp (-(γ * x)) else 0

-- AMBIGUITY: "Erlang(1,γ) is Exponential(γ)" read both as equality of densities (S2) and as
-- equality of distributions, i.e. of measures on ℝ (S3). "When n=1, the sub-stage rate is
-- 1·γ = γ" is the arithmetic statement about the sub-stage rate n·γ of `ErlangParams` (S1).
-- γ is read as a rate, γ > 0.

/-- Intended statement: (S1) for Erlang parameters with n = 1 the sub-stage rate n·γ equals γ;
(S2) the Erlang(1, γ) density is the Exponential(γ) density; (S3) the Erlang(1, γ) distribution is
the Exponential(γ) distribution. -/
@[sa_reference "MethodOfStages.R87"]
def T : Prop :=
  (∀ p : ErlangParams, p.n = 1 → (p.n : ℝ) * p.gamma = p.gamma) ∧
  (∀ γ : ℝ, 0 < γ → ∀ x : ℝ, gammaPDFReal 1 γ x = expDensity γ x) ∧
  (∀ γ : ℝ, 0 < γ →
    gammaMeasure 1 γ = volume.withDensity (fun x => ENNReal.ofReal (expDensity γ x)))

/-- S1: when n = 1 the sub-stage rate n·γ is γ. -/
@[sa_shadow "MethodOfStages.R87" 1]
def S1 : Prop := ∀ p : ErlangParams, p.n = 1 → (p.n : ℝ) * p.gamma = p.gamma

/-- S2: the Erlang(1, γ) (= Gamma(1, γ)) density equals the Exponential(γ) density pointwise. -/
@[sa_shadow "MethodOfStages.R87" 2]
def S2 : Prop := ∀ γ : ℝ, 0 < γ → ∀ x : ℝ, gammaPDFReal 1 γ x = expDensity γ x

/-- S3: the Erlang(1, γ) distribution equals the Exponential(γ) distribution (as measures). -/
@[sa_shadow "MethodOfStages.R87" 3]
def S3 : Prop := ∀ γ : ℝ, 0 < γ →
  gammaMeasure 1 γ = volume.withDensity (fun x => ENNReal.ofReal (expDensity γ x))

@[sa_ref_forward "MethodOfStages.R87" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "MethodOfStages.R87" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1

@[sa_ref_forward "MethodOfStages.R87" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2

@[sa_complete "MethodOfStages.R87"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.MethodOfStages.R87

/-! ### `MethodOfStages.R88`

Blind text: "Result 88: Mean sojourn time preserved E[Erlang(n,nγ)] = n/(nγ) = 1/γ for all n ≥ 1." -/

namespace Alignment.Shadows.MethodOfStages.R88

open Alignment.Shadows.MethodOfStages

-- "for all n ≥ 1": quantified over all `ErlangParams` (whose invariant is 0 < n, i.e. n ≥ 1,
-- and 0 < γ).
-- AMBIGUITY: "E[Erlang(n,nγ)] = n/(nγ) = 1/γ" read as the chain E[Erlang(n,nγ)] = n/(nγ) (the
-- mean of the distribution, S1) and n/(nγ) = 1/γ (arithmetic, S2); together they give the
-- headline E[Erlang(n,nγ)] = 1/γ.
-- VOCAB-GAP: E[·] is not in the DataTypes; stated as `∫ x, x ∂(gammaMeasure n (n γ))`.

/-- Intended statement: for all Erlang parameters (n ≥ 1, γ > 0),
E[Erlang(n,nγ)] = n/(nγ) and n/(nγ) = 1/γ. -/
@[sa_reference "MethodOfStages.R88"]
def T : Prop := ∀ p : ErlangParams,
  erlangMean p.n p.gamma = (p.n : ℝ) / ((p.n : ℝ) * p.gamma) ∧
    (p.n : ℝ) / ((p.n : ℝ) * p.gamma) = 1 / p.gamma

/-- S1: the mean of Erlang(n, nγ) is n/(nγ). -/
@[sa_shadow "MethodOfStages.R88" 1]
def S1 : Prop := ∀ p : ErlangParams,
  erlangMean p.n p.gamma = (p.n : ℝ) / ((p.n : ℝ) * p.gamma)

/-- S2: n/(nγ) = 1/γ for all n ≥ 1. -/
@[sa_shadow "MethodOfStages.R88" 2]
def S2 : Prop := ∀ p : ErlangParams, (p.n : ℝ) / ((p.n : ℝ) * p.gamma) = 1 / p.gamma

@[sa_ref_forward "MethodOfStages.R88" 1]
theorem ref_fwd1 : T → S1 := fun t p => (t p).1

@[sa_ref_forward "MethodOfStages.R88" 2]
theorem ref_fwd2 : T → S2 := fun t p => (t p).2

@[sa_complete "MethodOfStages.R88"]
theorem complete (s1 : S1) (s2 : S2) : T := fun p => ⟨s1 p, s2 p⟩

end Alignment.Shadows.MethodOfStages.R88

/-! ### `MethodOfStages.R89a`

Blind text: "Var[Erlang(n,nγ)] = n/(nγ)² = 1/(nγ²)." -/

namespace Alignment.Shadows.MethodOfStages.R89a

open Alignment.Shadows.MethodOfStages

-- The text gives no quantifier; read over all Erlang parameters (n ≥ 1, γ > 0), as in R88.
-- AMBIGUITY: chain read as Var[Erlang(n,nγ)] = n/(nγ)² (distributional variance, S1) and
-- n/(nγ)² = 1/(nγ²) (arithmetic, S2); "nγ²" read as n·(γ²).
-- VOCAB-GAP: Var[·] is not in the DataTypes; stated with `ProbabilityTheory.variance`.

/-- Intended statement: for all Erlang parameters, Var[Erlang(n,nγ)] = n/(nγ)² and
n/(nγ)² = 1/(nγ²). -/
@[sa_reference "MethodOfStages.R89a"]
def T : Prop := ∀ p : ErlangParams,
  erlangVar p.n p.gamma = (p.n : ℝ) / ((p.n : ℝ) * p.gamma) ^ 2 ∧
    (p.n : ℝ) / ((p.n : ℝ) * p.gamma) ^ 2 = 1 / ((p.n : ℝ) * p.gamma ^ 2)

/-- S1: the variance of Erlang(n, nγ) is n/(nγ)². -/
@[sa_shadow "MethodOfStages.R89a" 1]
def S1 : Prop := ∀ p : ErlangParams,
  erlangVar p.n p.gamma = (p.n : ℝ) / ((p.n : ℝ) * p.gamma) ^ 2

/-- S2: n/(nγ)² = 1/(nγ²). -/
@[sa_shadow "MethodOfStages.R89a" 2]
def S2 : Prop := ∀ p : ErlangParams,
  (p.n : ℝ) / ((p.n : ℝ) * p.gamma) ^ 2 = 1 / ((p.n : ℝ) * p.gamma ^ 2)

@[sa_ref_forward "MethodOfStages.R89a" 1]
theorem ref_fwd1 : T → S1 := fun t p => (t p).1

@[sa_ref_forward "MethodOfStages.R89a" 2]
theorem ref_fwd2 : T → S2 := fun t p => (t p).2

@[sa_complete "MethodOfStages.R89a"]
theorem complete (s1 : S1) (s2 : S2) : T := fun p => ⟨s1 p, s2 p⟩

end Alignment.Shadows.MethodOfStages.R89a

/-! ### `MethodOfStages.R90a`

Blind text: "CV² = Var/Mean² = (1/(nγ²))/(1/γ)² = 1/n," -/

namespace Alignment.Shadows.MethodOfStages.R90a

open Alignment.Shadows.MethodOfStages

/-- The squared coefficient of variation of Erlang(n, nγ), by the text's definition
CV² = Var/Mean² (Var and Mean of the distribution). -/
def cvSq (n : ℕ) (γ : ℝ) : ℝ := erlangVar n γ / erlangMean n γ ^ 2

-- The text gives no quantifier; read over all Erlang parameters (n ≥ 1, γ > 0).
-- AMBIGUITY: "CV² = Var/Mean²" is read as the definition of CV² (`cvSq`), not as a separate
-- requirement. The rest of the chain is read as Var/Mean² = (1/(nγ²))/(1/γ)² for the
-- distribution's variance and mean (S1) and the arithmetic identity (1/(nγ²))/(1/γ)² = 1/n (S2).
-- VOCAB-GAP: CV, Var and Mean are not in the DataTypes; stated with Mathlib (see header).

/-- Intended statement: for all Erlang parameters, CV²[Erlang(n,nγ)] = (1/(nγ²))/(1/γ)² and
(1/(nγ²))/(1/γ)² = 1/n. -/
@[sa_reference "MethodOfStages.R90a"]
def T : Prop := ∀ p : ErlangParams,
  cvSq p.n p.gamma = (1 / ((p.n : ℝ) * p.gamma ^ 2)) / (1 / p.gamma) ^ 2 ∧
    (1 / ((p.n : ℝ) * p.gamma ^ 2)) / (1 / p.gamma) ^ 2 = 1 / (p.n : ℝ)

/-- S1: Var/Mean² of Erlang(n, nγ) equals (1/(nγ²))/(1/γ)². -/
@[sa_shadow "MethodOfStages.R90a" 1]
def S1 : Prop := ∀ p : ErlangParams,
  cvSq p.n p.gamma = (1 / ((p.n : ℝ) * p.gamma ^ 2)) / (1 / p.gamma) ^ 2

/-- S2: (1/(nγ²))/(1/γ)² = 1/n. -/
@[sa_shadow "MethodOfStages.R90a" 2]
def S2 : Prop := ∀ p : ErlangParams,
  (1 / ((p.n : ℝ) * p.gamma ^ 2)) / (1 / p.gamma) ^ 2 = 1 / (p.n : ℝ)

@[sa_ref_forward "MethodOfStages.R90a" 1]
theorem ref_fwd1 : T → S1 := fun t p => (t p).1

@[sa_ref_forward "MethodOfStages.R90a" 2]
theorem ref_fwd2 : T → S2 := fun t p => (t p).2

@[sa_complete "MethodOfStages.R90a"]
theorem complete (s1 : S1) (s2 : S2) : T := fun p => ⟨s1 p, s2 p⟩

end Alignment.Shadows.MethodOfStages.R90a

/-! ### `MethodOfStages.R91a`

Blind text: "Result 91: Variance vanishes as n → ∞ The variance 1/(nγ²) → 0 as n → ∞," -/

namespace Alignment.Shadows.MethodOfStages.R91a

open Alignment.Shadows.MethodOfStages

-- For every fixed rate γ > 0, as the number of sub-stages n → ∞ along ℕ.
-- AMBIGUITY: "Variance vanishes" / "The variance 1/(nγ²) → 0" read both as the limit of the
-- explicit expression 1/(nγ²) (S1) and as the limit of the variance of the Erlang(n, nγ)
-- distribution itself (S2).
-- VOCAB-GAP: the variance of Erlang(n, nγ) is not in the DataTypes; stated with
-- `ProbabilityTheory.variance` of `gammaMeasure n (n γ)`.

/-- Intended statement: for every γ > 0, 1/(nγ²) → 0 and Var[Erlang(n, nγ)] → 0 as n → ∞. -/
@[sa_reference "MethodOfStages.R91a"]
def T : Prop := ∀ γ : ℝ, 0 < γ →
  Tendsto (fun n : ℕ => 1 / ((n : ℝ) * γ ^ 2)) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => erlangVar n γ) atTop (𝓝 0)

/-- S1: the expression 1/(nγ²) tends to 0 as n → ∞. -/
@[sa_shadow "MethodOfStages.R91a" 1]
def S1 : Prop := ∀ γ : ℝ, 0 < γ → Tendsto (fun n : ℕ => 1 / ((n : ℝ) * γ ^ 2)) atTop (𝓝 0)

/-- S2: the variance of the Erlang(n, nγ) distribution tends to 0 as n → ∞. -/
@[sa_shadow "MethodOfStages.R91a" 2]
def S2 : Prop := ∀ γ : ℝ, 0 < γ → Tendsto (fun n : ℕ => erlangVar n γ) atTop (𝓝 0)

@[sa_ref_forward "MethodOfStages.R91a" 1]
theorem ref_fwd1 : T → S1 := fun t γ hγ => (t γ hγ).1

@[sa_ref_forward "MethodOfStages.R91a" 2]
theorem ref_fwd2 : T → S2 := fun t γ hγ => (t γ hγ).2

@[sa_complete "MethodOfStages.R91a"]
theorem complete (s1 : S1) (s2 : S2) : T := fun γ hγ => ⟨s1 γ hγ, s2 γ hγ⟩

end Alignment.Shadows.MethodOfStages.R91a

/-! ### `MethodOfStages.R92`

Blind text: "Result 92: ODE dimension counting For a model with k stages where stage i has nᵢ
sub-stages, total dimension = Σᵢ nᵢ + 2 (the +2 is for θ and R)." -/

namespace Alignment.Shadows.MethodOfStages.R92

/-- State variables of the staged ODE model whose stage sub-stage counts are the list `ns`
(k = `ns.length` stages; stage `i` has `ns.get i` sub-stages): one variable for each sub-stage
`j` of each stage `i`, plus the two variables θ and R (`Unit ⊕ Unit`). -/
abbrev StateVar (ns : List ℕ) : Type := (Σ i : Fin ns.length, Fin (ns.get i)) ⊕ (Unit ⊕ Unit)

/-- Total dimension of the ODE system: the dimension of its state space `StateVar ns → ℝ`. -/
def odeDim (ns : List ℕ) : ℕ := Module.finrank ℝ (StateVar ns → ℝ)

-- VOCAB-GAP: the DataTypes have no ODE model / state-space object and no dimension operation;
-- "total dimension" is formalised as the real dimension of the state space with one coordinate
-- per sub-stage of each stage plus θ and R (the parenthetical "the +2 is for θ and R").
-- Stage counts are a `List ℕ` (DataTypes §(d): `List.sum` for stage counts); Σᵢ nᵢ = `ns.sum`.
-- AMBIGUITY: "stage i has nᵢ sub-stages": the text imposes no nᵢ ≥ 1, so every list of natural
-- numbers is allowed (keeping the text's generality).

/-- Intended statement: for every model with stage counts `ns`, the ODE dimension is
Σᵢ nᵢ + 2. -/
@[sa_reference "MethodOfStages.R92"]
def T : Prop := ∀ ns : List ℕ, odeDim ns = ns.sum + 2

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "MethodOfStages.R92" 1]
def S1 : Prop := ∀ ns : List ℕ, odeDim ns = ns.sum + 2

@[sa_ref_forward "MethodOfStages.R92" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MethodOfStages.R92"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MethodOfStages.R92

/-! ### `MethodOfStages.R93c`

Blind text: "For n=1: T₁ = 1 - γ/(β+γ) = β/(β+γ) — standard Markovian result." -/

namespace Alignment.Shadows.MethodOfStages.R93c

open Alignment.Shadows.MethodOfStages

/-- Transmissibility across an edge with per-edge transmission rate `β` when the infectious
period is Erlang(n, nγ): the probability that transmission occurs before recovery,
∫ (1 − e^{−βτ}) dErlang(n, nγ)(τ) (papers: "If ego is infectious for a duration T, the probability
of transmitting to a given alter is 1 − e^{−rT}", integrated over the infectious-period law). -/
def transmissibility (β : ℝ) (n : ℕ) (γ : ℝ) : ℝ :=
  ∫ τ, (1 - Real.exp (-(β * τ))) ∂(erlangMeasure n γ)

-- VOCAB-GAP: the DataTypes have no transmissibility operation (T_n "appears only as an explicit
-- real expression"); T₁ is formalised probabilistically as `transmissibility β 1 γ`.
-- AMBIGUITY: the chain "T₁ = 1 - γ/(β+γ) = β/(β+γ)" read as T₁ = 1 - γ/(β+γ) for the
-- transmissibility with Erlang(1, γ) infectious period (S1) and the arithmetic identity
-- 1 - γ/(β+γ) = β/(β+γ) (S2). β and γ read as rates, β > 0, γ > 0.

/-- Intended statement: for all rates β, γ > 0, the transmissibility with n = 1 sub-stage is
1 − γ/(β+γ), and 1 − γ/(β+γ) = β/(β+γ). -/
@[sa_reference "MethodOfStages.R93c"]
def T : Prop := ∀ β γ : ℝ, 0 < β → 0 < γ →
  transmissibility β 1 γ = 1 - γ / (β + γ) ∧ 1 - γ / (β + γ) = β / (β + γ)

/-- S1: T₁ (transmissibility with Erlang(1, γ) infectious period) equals 1 − γ/(β+γ). -/
@[sa_shadow "MethodOfStages.R93c" 1]
def S1 : Prop := ∀ β γ : ℝ, 0 < β → 0 < γ → transmissibility β 1 γ = 1 - γ / (β + γ)

/-- S2: 1 − γ/(β+γ) = β/(β+γ). -/
@[sa_shadow "MethodOfStages.R93c" 2]
def S2 : Prop := ∀ β γ : ℝ, 0 < β → 0 < γ → 1 - γ / (β + γ) = β / (β + γ)

@[sa_ref_forward "MethodOfStages.R93c" 1]
theorem ref_fwd1 : T → S1 := fun t β γ hβ hγ => (t β γ hβ hγ).1

@[sa_ref_forward "MethodOfStages.R93c" 2]
theorem ref_fwd2 : T → S2 := fun t β γ hβ hγ => (t β γ hβ hγ).2

@[sa_complete "MethodOfStages.R93c"]
theorem complete (s1 : S1) (s2 : S2) : T :=
  fun β γ hβ hγ => ⟨s1 β γ hβ hγ, s2 β γ hβ hγ⟩

end Alignment.Shadows.MethodOfStages.R93c

/-! ### `MethodOfStages.R94b`

Blind text: "We verify the intermediate identity: nγ/(β+nγ) = 1/(1+β/(nγ))." -/

namespace Alignment.Shadows.MethodOfStages.R94b

-- Read over all Erlang parameters (n ≥ 1, γ > 0) and every transmission rate β > 0.
-- AMBIGUITY: the text puts no constraint on β; it is read as a transmission rate, β > 0.

/-- Intended statement: for all Erlang parameters and β > 0, nγ/(β+nγ) = 1/(1+β/(nγ)). -/
@[sa_reference "MethodOfStages.R94b"]
def T : Prop := ∀ (p : ErlangParams) (β : ℝ), 0 < β →
  (p.n : ℝ) * p.gamma / (β + (p.n : ℝ) * p.gamma) = 1 / (1 + β / ((p.n : ℝ) * p.gamma))

/-- S1: the whole identity (a single atomic requirement). -/
@[sa_shadow "MethodOfStages.R94b" 1]
def S1 : Prop := ∀ (p : ErlangParams) (β : ℝ), 0 < β →
  (p.n : ℝ) * p.gamma / (β + (p.n : ℝ) * p.gamma) = 1 / (1 + β / ((p.n : ℝ) * p.gamma))

@[sa_ref_forward "MethodOfStages.R94b" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MethodOfStages.R94b"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MethodOfStages.R94b

/-! ## Shared notions for the re-authored MethodOfStages blocks (blind)

Not registered; inlined by the audit. The module defines no operations. The transmissibility of
the n-stage model with per-edge transmission rate β and Erlang(n, nγ) infectious period is
`T_n = 1 − (nγ/(β + nγ))ⁿ` (each of the n sub-stages of rate nγ ends before a transmission with
probability nγ/(β + nγ)). -/
namespace Alignment.Shadows.MethodOfStages.Shared2

/-- `T_n = 1 − (nγ/(β + nγ))ⁿ` for the Erlang parameters `e`. -/
def Tn (β : ℝ) (e : ErlangParams) : ℝ :=
  1 - ((e.n : ℝ) * e.gamma / (β + (e.n : ℝ) * e.gamma)) ^ e.n
/-- Erlang parameters with 1 stage and rate γ. -/
def erl1 (γ : ℝ) (hγ : 0 < γ) : ErlangParams := ⟨1, γ, Nat.one_pos, hγ⟩
/-- Erlang parameters with 2 stages and rate γ. -/
def erl2 (γ : ℝ) (hγ : 0 < γ) : ErlangParams := ⟨2, γ, Nat.two_pos, hγ⟩

end Alignment.Shadows.MethodOfStages.Shared2

/-! ## `MethodOfStages.R93a` (blind)

Text: "Result 93: Transmissibility changes with the number of stages"

-- AMBIGUITY: "changes" read as: for every β, γ > 0 the transmissibility is not the same for all
numbers of stages. -/
namespace Alignment.Shadows.MethodOfStages.R93a

open Alignment.Shadows.MethodOfStages.Shared2

@[sa_reference "MethodOfStages.R93a"]
def T : Prop :=
  ∀ β γ : ℝ, 0 < β → 0 < γ →
    ∃ e₁ e₂ : ErlangParams, e₁.gamma = γ ∧ e₂.gamma = γ ∧ Tn β e₁ ≠ Tn β e₂

/-- S1: two stage counts give different transmissibilities. -/
@[sa_shadow "MethodOfStages.R93a" 1]
def S1 : Prop :=
  ∀ β γ : ℝ, 0 < β → 0 < γ →
    ∃ e₁ e₂ : ErlangParams, e₁.gamma = γ ∧ e₂.gamma = γ ∧ Tn β e₁ ≠ Tn β e₂

@[sa_ref_forward "MethodOfStages.R93a" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "MethodOfStages.R93a"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MethodOfStages.R93a

/-! ## `MethodOfStages.erlangTransmissibilityOneLtTwo` (blind)

Text: "**Result 93 (corrected).** Staging changes the transmissibility: T₁ < T₂ for all β, γ > 0,
since T₂ − T₁ = β²γ/((β+γ)(β+2γ)²)." -/
namespace Alignment.Shadows.MethodOfStages.erlangTransmissibilityOneLtTwo

open Alignment.Shadows.MethodOfStages.Shared2

@[sa_reference "MethodOfStages.erlangTransmissibilityOneLtTwo"]
def T : Prop :=
  (∀ (β γ : ℝ) (hγ : 0 < γ), 0 < β → Tn β (erl1 γ hγ) < Tn β (erl2 γ hγ)) ∧
  (∀ (β γ : ℝ) (hγ : 0 < γ), 0 < β →
      Tn β (erl2 γ hγ) - Tn β (erl1 γ hγ) = β ^ 2 * γ / ((β + γ) * (β + 2 * γ) ^ 2))

/-- S1: `T₁ < T₂` for all β, γ > 0. -/
@[sa_shadow "MethodOfStages.erlangTransmissibilityOneLtTwo" 1]
def S1 : Prop := ∀ (β γ : ℝ) (hγ : 0 < γ), 0 < β → Tn β (erl1 γ hγ) < Tn β (erl2 γ hγ)
/-- S2: `T₂ − T₁ = β²γ/((β+γ)(β+2γ)²)`. -/
@[sa_shadow "MethodOfStages.erlangTransmissibilityOneLtTwo" 2]
def S2 : Prop :=
  ∀ (β γ : ℝ) (hγ : 0 < γ), 0 < β →
    Tn β (erl2 γ hγ) - Tn β (erl1 γ hγ) = β ^ 2 * γ / ((β + γ) * (β + 2 * γ) ^ 2)

@[sa_ref_forward "MethodOfStages.erlangTransmissibilityOneLtTwo" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t.1
@[sa_ref_forward "MethodOfStages.erlangTransmissibilityOneLtTwo" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2
@[sa_complete "MethodOfStages.erlangTransmissibilityOneLtTwo"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.MethodOfStages.erlangTransmissibilityOneLtTwo

/-! ## `MethodOfStages.erlangTransmissibilityValues` (blind)

Text: "At β = γ = 1: T₁ = 1/2 and T₂ = 5/9." -/
namespace Alignment.Shadows.MethodOfStages.erlangTransmissibilityValues

open Alignment.Shadows.MethodOfStages.Shared2

@[sa_reference "MethodOfStages.erlangTransmissibilityValues"]
def T : Prop := Tn 1 (erl1 1 one_pos) = 1 / 2 ∧ Tn 1 (erl2 1 one_pos) = 5 / 9

/-- S1: `T₁ = 1/2` at β = γ = 1. -/
@[sa_shadow "MethodOfStages.erlangTransmissibilityValues" 1]
def S1 : Prop := Tn 1 (erl1 1 one_pos) = 1 / 2
/-- S2: `T₂ = 5/9` at β = γ = 1. -/
@[sa_shadow "MethodOfStages.erlangTransmissibilityValues" 2]
def S2 : Prop := Tn 1 (erl2 1 one_pos) = 5 / 9

@[sa_ref_forward "MethodOfStages.erlangTransmissibilityValues" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t.1
@[sa_ref_forward "MethodOfStages.erlangTransmissibilityValues" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2
@[sa_complete "MethodOfStages.erlangTransmissibilityValues"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.MethodOfStages.erlangTransmissibilityValues

end
