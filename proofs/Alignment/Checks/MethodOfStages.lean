import Alignment.Registry
import Alignment.Shadows.MethodOfStages

/-!
# Checkers: group `MethodOfStages`

Registrations, checkers and failure records for the implemented claims of
`EBCMCategory/MethodOfStages.lean` (shadows: `Alignment/Shadows/MethodOfStages.lean`, written blind).

**No bridges.** The trusted module defines no operations (only the structure `ErlangParams`), so
there is no trusted definition to identify with the text's notions. Every implementation theorem
is a statement about free real (or natural) scalars:

* `erlang_one_is_exponential : ∀ γ, 0 < γ → ↑(1 : ℕ) * γ = γ`,
* `erlang_mean_preserved : ∀ n γ, 0 < n → 0 < γ → n/(nγ) = 1/γ`,
* `erlang_variance : ∀ n γ, 0 < n → 0 < γ → n/(nγ)² = 1/(nγ²)`,
* `erlang_cv_squared : ∀ n γ, 0 < n → 0 < γ → (1/(nγ²))/(1/γ)² = 1/n`,
* `erlang_variance_limit : ∀ γ, 0 < γ → Tendsto (n ↦ 1/(nγ²)) atTop (𝓝 0)`,
* `ode_dimension : ∀ l : List ℕ, l.sum + 2 = (l.map id).sum + 2` (a tautology),
* `transmissibility_n_one : ∀ β γ, 0 < β → 0 < γ → 1 − γ/(β+γ) = β/(β+γ)`,
* `transmissibility_ratio : ∀ n β γ, 0 < n → 0 < β → 0 < γ → nγ/(β+nγ) = 1/(1+β/(nγ))`.

Policy for the recorded failures (the same as the other groups):
* No implementation mentions a probability distribution (`gammaMeasure`, `gammaPDFReal`), an
  integral, a variance, a transmissibility integral or a state-space dimension. Shadows that
  state such distributional or structural readings are recorded as `sa_fail_forward`.
* The blind shadows quantify over `ErlangParams` records `p`. Instantiating a free-scalar impl at
  `p.n`, `p.gamma` needs its positivity hypotheses `0 < p.n` / `0 < p.gamma`, which are available
  only as the structure fields `p.n_pos` / `p.gamma_pos` (data invariants, not structural). These
  are recorded as `sa_fail_forward`. The backward direction builds a record from the impl's own
  hypotheses (proofs inside data terms are skipped by the audit), so it holds.
-/

/-! ## `MethodOfStages.R87` -/
namespace Alignment.Shadows.MethodOfStages.R87

sa_claim "MethodOfStages.R87" group "MethodOfStages" required
  text "Result 87: Erlang(1,γ) is Exponential(γ) When n=1, the sub-stage rate is 1·γ = γ, recovering the exponential."
  impl erlang_one_is_exponential

sa_fail_forward "MethodOfStages.R87" 1 "free-scalar abstraction with an extra hypothesis: impl erlang_one_is_exponential is ∀ γ : ℝ, 0 < γ → ↑(1:ℕ)·γ = γ, with the hypothesis 0 < γ (_hg, unused in its ring proof). S1 is stated over ErlangParams p with p.n = 1; after rewriting p.n = 1, instantiating the impl at p.gamma needs a proof of 0 < p.gamma, available only as the structure field p.gamma_pos (a data invariant, not structural). A faithful impl would drop the unused hypothesis or be stated over ErlangParams."

sa_fail_forward "MethodOfStages.R87" 2 "different notion: impl is the real-arithmetic identity ↑(1:ℕ)·γ = γ and mentions no density. S2 requires the Gamma(1, γ) density gammaPDFReal 1 γ x to equal the Exponential(γ) density γe^{-γx} (x ≥ 0, else 0) pointwise; this needs unfolding gammaPDFReal (γ^1/Γ(1)·x^0·e^{-γx}), Real.Gamma_one and rpow lemmas, none of which the impl states. The heading 'Erlang(1,γ) is Exponential(γ)' is not formalised by the impl."

sa_fail_forward "MethodOfStages.R87" 3 "different notion: impl is the real-arithmetic identity ↑(1:ℕ)·γ = γ and mentions no measure. S3 requires gammaMeasure 1 γ = volume.withDensity (ofReal ∘ Exponential(γ) density), an equality of distributions on ℝ; the impl states nothing about gammaMeasure, so 'Erlang(1,γ) is Exponential(γ)' as distributions is not proved."

/-- The impl's hypothesis `0 < γ` builds an `ErlangParams` record with `n = 1` (its proof fields
are data arguments); `S1` at that record is `↑1 * γ = γ` by projection reduction. -/
@[sa_backward "MethodOfStages.R87"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) : sa_impl% "MethodOfStages.R87" :=
  fun γ hγ => s1 ⟨1, γ, Nat.one_pos, hγ⟩ rfl

end Alignment.Shadows.MethodOfStages.R87

/-! ## `MethodOfStages.R88` -/
namespace Alignment.Shadows.MethodOfStages.R88

sa_claim "MethodOfStages.R88" group "MethodOfStages" required
  text "Result 88: Mean sojourn time preserved E[Erlang(n,nγ)] = n/(nγ) = 1/γ for all n ≥ 1."
  impl erlang_mean_preserved

sa_fail_forward "MethodOfStages.R88" 1 "different notion: impl erlang_mean_preserved is the arithmetic identity n/(nγ) = 1/γ for free reals (n > 0, γ > 0) and mentions no distribution. S1 requires the mean of the Erlang(n, nγ) law, ∫ x d(gammaMeasure n (nγ)), to equal n/(nγ); the impl never computes an expectation, so 'E[Erlang(n,nγ)] = n/(nγ)' is not stated."

sa_fail_forward "MethodOfStages.R88" 2 "free-scalar abstraction: impl is ∀ n γ, 0 < n → 0 < γ → n/(nγ) = 1/γ. S2 is stated over ErlangParams p; instantiating the impl at p.n, p.gamma needs proofs of 0 < p.n and 0 < p.gamma, available only as the structure fields p.n_pos / p.gamma_pos (data invariants, not structural). A faithful impl would be stated over ErlangParams."

/-- The impl's hypotheses build the `ErlangParams` record `⟨n, γ, hn, hγ⟩`. -/
@[sa_backward "MethodOfStages.R88"]
theorem bwd (_s1 : S1) (s2 : S2) : sa_impl% "MethodOfStages.R88" :=
  fun n γ hn hγ => s2 ⟨n, γ, hn, hγ⟩

end Alignment.Shadows.MethodOfStages.R88

/-! ## `MethodOfStages.R89a` -/
namespace Alignment.Shadows.MethodOfStages.R89a

sa_claim "MethodOfStages.R89a" group "MethodOfStages" required
  text "Var[Erlang(n,nγ)] = n/(nγ)² = 1/(nγ²)."
  impl erlang_variance

sa_fail_forward "MethodOfStages.R89a" 1 "different notion: impl erlang_variance is the arithmetic identity n/(nγ)² = 1/(nγ²) for free reals (n > 0, γ > 0) and mentions no distribution. S1 requires the variance of the Erlang(n, nγ) law, ProbabilityTheory.variance id (gammaMeasure n (nγ)), to equal n/(nγ)²; the impl never computes a variance, so 'Var[Erlang(n,nγ)] = n/(nγ)²' is not stated."

sa_fail_forward "MethodOfStages.R89a" 2 "free-scalar abstraction: impl is ∀ n γ, 0 < n → 0 < γ → n/(nγ)² = 1/(nγ²). S2 is stated over ErlangParams p; instantiating the impl at p.n, p.gamma needs proofs of 0 < p.n and 0 < p.gamma, available only as the structure fields p.n_pos / p.gamma_pos (data invariants, not structural). A faithful impl would be stated over ErlangParams."

/-- The impl's hypotheses build the `ErlangParams` record `⟨n, γ, hn, hγ⟩`. -/
@[sa_backward "MethodOfStages.R89a"]
theorem bwd (_s1 : S1) (s2 : S2) : sa_impl% "MethodOfStages.R89a" :=
  fun n γ hn hγ => s2 ⟨n, γ, hn, hγ⟩

end Alignment.Shadows.MethodOfStages.R89a

/-! ## `MethodOfStages.R90a` -/
namespace Alignment.Shadows.MethodOfStages.R90a

sa_claim "MethodOfStages.R90a" group "MethodOfStages" required
  text "CV² = Var/Mean² = (1/(nγ²))/(1/γ)² = 1/n,"
  impl erlang_cv_squared

sa_fail_forward "MethodOfStages.R90a" 1 "different notion: impl erlang_cv_squared is the arithmetic identity (1/(nγ²))/(1/γ)² = 1/n for free reals (n > 0, γ > 0) and mentions no distribution. S1 requires Var/Mean² of the Erlang(n, nγ) law (variance and mean of gammaMeasure n (nγ)) to equal (1/(nγ²))/(1/γ)²; the impl computes neither the variance nor the mean, so 'CV² = Var/Mean² = (1/(nγ²))/(1/γ)²' is not stated."

sa_fail_forward "MethodOfStages.R90a" 2 "free-scalar abstraction: impl is ∀ n γ, 0 < n → 0 < γ → (1/(nγ²))/(1/γ)² = 1/n. S2 is stated over ErlangParams p; instantiating the impl at p.n, p.gamma needs proofs of 0 < p.n and 0 < p.gamma, available only as the structure fields p.n_pos / p.gamma_pos (data invariants, not structural). A faithful impl would be stated over ErlangParams."

/-- The impl's hypotheses build the `ErlangParams` record `⟨n, γ, hn, hγ⟩`. -/
@[sa_backward "MethodOfStages.R90a"]
theorem bwd (_s1 : S1) (s2 : S2) : sa_impl% "MethodOfStages.R90a" :=
  fun n γ hn hγ => s2 ⟨n, γ, hn, hγ⟩

end Alignment.Shadows.MethodOfStages.R90a

/-! ## `MethodOfStages.R91a` -/
namespace Alignment.Shadows.MethodOfStages.R91a

sa_claim "MethodOfStages.R91a" group "MethodOfStages" required
  text "Result 91: Variance vanishes as n → ∞ The variance 1/(nγ²) → 0 as n → ∞,"
  impl erlang_variance_limit

/-- `S1` is the impl's statement verbatim (`𝓝` is `nhds`). -/
@[sa_forward "MethodOfStages.R91a" 1]
theorem fwd1 (h : sa_impl% "MethodOfStages.R91a") : S1 :=
  fun γ hγ => h γ hγ

sa_fail_forward "MethodOfStages.R91a" 2 "different notion: impl erlang_variance_limit is the limit of the explicit real expression 1/(nγ²) → 0 and mentions no distribution. S2 requires the variance of the Erlang(n, nγ) law, ProbabilityTheory.variance id (gammaMeasure n (nγ)), to tend to 0; linking it to 1/(nγ²) needs the Gamma variance formula, which no impl states (erlang_variance is also only the arithmetic n/(nγ)² = 1/(nγ²)). So 'Variance vanishes' for the distribution is not proved."

@[sa_backward "MethodOfStages.R91a"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "MethodOfStages.R91a" :=
  fun γ hγ => s1 γ hγ

end Alignment.Shadows.MethodOfStages.R91a

/-! ## `MethodOfStages.R92` -/
namespace Alignment.Shadows.MethodOfStages.R92

sa_claim "MethodOfStages.R92" group "MethodOfStages" required
  text "Result 92: ODE dimension counting For a model with k stages where stage i has nᵢ sub-stages, total dimension = Σᵢ nᵢ + 2 (the +2 is for θ and R)."
  impl ode_dimension

sa_fail_forward "MethodOfStages.R92" 1 "tautological impl: ode_dimension is ∀ l : List ℕ, l.sum + 2 = (l.map id).sum + 2, which holds because List.map id = id and mentions no model, state space or dimension. S1 requires the dimension of the staged ODE state space (Module.finrank ℝ of the functions on one coordinate per sub-stage plus θ and R) to be Σᵢ nᵢ + 2; that needs Module.finrank_fintype_fun_eq_card and a cardinality count of Σ i, Fin nᵢ ⊕ (Unit ⊕ Unit), none of which the impl states. The count Σᵢ nᵢ + 2 is never tied to any system."

/-- `List.map id l = l`, by structural induction on the list (plain data) with `congrArg`. -/
theorem map_id_eq (l : List ℕ) : List.map id l = l := by
  induction l with
  | nil => rfl
  | cons a t ih => exact congrArg (List.cons a) ih

/-- The impl is a tautology: `(l.map id).sum + 2` is `l.sum + 2` after `List.map id l = l`, proved
by list induction. `S1` is not needed. -/
@[sa_backward "MethodOfStages.R92"]
theorem bwd (_s1 : S1) : sa_impl% "MethodOfStages.R92" :=
  fun l => congrArg (fun m : List ℕ => m.sum + 2) (map_id_eq l).symm

end Alignment.Shadows.MethodOfStages.R92

/-! ## `MethodOfStages.R93c` -/
namespace Alignment.Shadows.MethodOfStages.R93c

sa_claim "MethodOfStages.R93c" group "MethodOfStages" required
  text "For n=1: T₁ = 1 - γ/(β+γ) = β/(β+γ) — standard Markovian result."
  impl transmissibility_n_one

sa_fail_forward "MethodOfStages.R93c" 1 "different notion: impl transmissibility_n_one is the arithmetic identity 1 − γ/(β+γ) = β/(β+γ) for β, γ > 0 and defines no transmissibility. S1 requires T₁, the transmission probability ∫ (1 − e^{−βτ}) dErlang(1, γ)(τ), to equal 1 − γ/(β+γ); that needs the exponential integral ∫ e^{−βτ} γe^{−γτ} dτ = γ/(β+γ), which the impl does not state. 'T₁ = 1 − γ/(β+γ)' is not proved."

/-- `S2` is the impl's statement verbatim. -/
@[sa_forward "MethodOfStages.R93c" 2]
theorem fwd2 (h : sa_impl% "MethodOfStages.R93c") : S2 :=
  fun β γ hβ hγ => h β γ hβ hγ

@[sa_backward "MethodOfStages.R93c"]
theorem bwd (_s1 : S1) (s2 : S2) : sa_impl% "MethodOfStages.R93c" :=
  fun β γ hβ hγ => s2 β γ hβ hγ

end Alignment.Shadows.MethodOfStages.R93c

/-! ## `MethodOfStages.R94b` -/
namespace Alignment.Shadows.MethodOfStages.R94b

sa_claim "MethodOfStages.R94b" group "MethodOfStages" required
  text "We verify the intermediate identity: nγ/(β+nγ) = 1/(1+β/(nγ))."
  impl transmissibility_ratio

sa_fail_forward "MethodOfStages.R94b" 1 "free-scalar abstraction: impl transmissibility_ratio is ∀ n β γ, 0 < n → 0 < β → 0 < γ → nγ/(β+nγ) = 1/(1+β/(nγ)). S1 is stated over ErlangParams p and β > 0; instantiating the impl at p.n, β, p.gamma needs proofs of 0 < p.n and 0 < p.gamma, available only as the structure fields p.n_pos / p.gamma_pos (data invariants, not structural). A faithful impl would be stated over ErlangParams."

/-- The impl's hypotheses build the `ErlangParams` record `⟨n, γ, hn, hγ⟩`. -/
@[sa_backward "MethodOfStages.R94b"]
theorem bwd (s1 : S1) : sa_impl% "MethodOfStages.R94b" :=
  fun n β γ hn hβ hγ => s1 ⟨n, γ, hn, hγ⟩ β hβ

end Alignment.Shadows.MethodOfStages.R94b

/-! ## erlangTransmissibilityOneLtTwo (`Tn β (erlN γ hγ)` unfolds to
`erlangTransmissibility β γ N`) -/
namespace Alignment.Shadows.MethodOfStages.erlangTransmissibilityOneLtTwo

sa_claim "MethodOfStages.erlangTransmissibilityOneLtTwo" group "MethodOfStages" required
  text "**Result 93 (corrected).** Staging changes the transmissibility: T₁ < T₂ for all β, γ > 0, since T₂ − T₁ = β²γ/((β+γ)(β+2γ)²)."
  impl erlangTransmissibility_one_lt_two

@[sa_forward "MethodOfStages.erlangTransmissibilityOneLtTwo" 1]
theorem fwd1 (h : sa_impl% "MethodOfStages.erlangTransmissibilityOneLtTwo") : S1 :=
  fun β γ hγ hβ => h β γ hβ hγ

sa_fail_forward "MethodOfStages.erlangTransmissibilityOneLtTwo" 2 "impl erlangTransmissibility_one_lt_two states only T₁ < T₂. S2 is the closed form of the difference, T₂ − T₁ = β²γ/((β+γ)(β+2γ)²); it appears only in impl's docstring (as the reason), not in its statement, so impl is weaker than S2."

@[sa_backward "MethodOfStages.erlangTransmissibilityOneLtTwo"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "MethodOfStages.erlangTransmissibilityOneLtTwo" :=
  fun β γ hβ hγ => s1 β γ hγ hβ

end Alignment.Shadows.MethodOfStages.erlangTransmissibilityOneLtTwo

/-! ## erlangTransmissibilityValues -/
namespace Alignment.Shadows.MethodOfStages.erlangTransmissibilityValues

sa_claim "MethodOfStages.erlangTransmissibilityValues" group "MethodOfStages" required
  text "At β = γ = 1: T₁ = 1/2 and T₂ = 5/9."
  impl erlangTransmissibility_values

@[sa_forward "MethodOfStages.erlangTransmissibilityValues" 1]
theorem fwd1 (h : sa_impl% "MethodOfStages.erlangTransmissibilityValues") : S1 := h.1

@[sa_forward "MethodOfStages.erlangTransmissibilityValues" 2]
theorem fwd2 (h : sa_impl% "MethodOfStages.erlangTransmissibilityValues") : S2 := h.2

@[sa_backward "MethodOfStages.erlangTransmissibilityValues"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "MethodOfStages.erlangTransmissibilityValues" :=
  ⟨s1, s2⟩

end Alignment.Shadows.MethodOfStages.erlangTransmissibilityValues

/-! ## `MethodOfStages.R93a` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.MethodOfStages.R93a

sa_claim "MethodOfStages.R93a" group "MethodOfStages"
  text "Result 93: Transmissibility changes with the number of stages"
  impl

end Alignment.Shadows.MethodOfStages.R93a
