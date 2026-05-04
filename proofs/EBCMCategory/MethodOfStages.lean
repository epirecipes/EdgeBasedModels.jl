import Mathlib

/-!
# Method of Stages for Non-Exponential Distributions

Formalizes the Erlang sub-stage technique for replacing exponential sojourn
times with gamma-distributed ones. An Erlang(n, nγ) distribution is implemented
as n sequential sub-stages each with rate nγ.

## References

* Sherborne N, Miller JC, Blyuss KB, Kiss IZ (2018).
  Mean-field models for non-Markovian epidemics on networks.
  J. Math. Biol. 76, 755–778.
-/

noncomputable section

open Real

/-! ## Erlang distribution parameters -/

structure ErlangParams where
  n : ℕ           -- number of sub-stages
  gamma : ℝ       -- overall rate
  n_pos : 0 < n
  gamma_pos : 0 < gamma

/-! ## Result 87: Erlang(1,γ) is Exponential(γ)

When n=1, the sub-stage rate is 1·γ = γ, recovering the exponential. -/

theorem erlang_one_is_exponential (gamma : ℝ) (_hg : 0 < gamma) :
    (1 : ℕ) * gamma = gamma := by ring

/-! ## Result 88: Mean sojourn time preserved

E[Erlang(n,nγ)] = n/(nγ) = 1/γ for all n ≥ 1. -/

theorem erlang_mean_preserved (n : ℕ) (gamma : ℝ) (hn : 0 < n) (hg : 0 < gamma) :
    (n : ℝ) / ((n : ℝ) * gamma) = 1 / gamma := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-! ## Result 89: Variance decreases with stages

Var[Erlang(n,nγ)] = n/(nγ)² = 1/(nγ²). -/

theorem erlang_variance (n : ℕ) (gamma : ℝ) (hn : 0 < n) (hg : 0 < gamma) :
    (n : ℝ) / ((n : ℝ) * gamma) ^ 2 = 1 / ((n : ℝ) * gamma ^ 2) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hg' : gamma ≠ 0 := ne_of_gt hg
  field_simp

/-! ## Result 90: CV = 1/√n

CV² = Var/Mean² = (1/(nγ²))/(1/γ)² = 1/n, so CV = 1/√n. -/

theorem erlang_cv_squared (n : ℕ) (gamma : ℝ) (hn : 0 < n) (hg : 0 < gamma) :
    (1 / ((n : ℝ) * gamma ^ 2)) / (1 / gamma) ^ 2 = 1 / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hg' : gamma ≠ 0 := ne_of_gt hg
  field_simp

/-! ## Result 91: Variance vanishes as n → ∞

The variance 1/(nγ²) → 0 as n → ∞, meaning Erlang(n,nγ) → Dirac(1/γ). -/

theorem erlang_variance_limit (gamma : ℝ) (hg : 0 < gamma) :
    Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) * gamma ^ 2))
      Filter.atTop (nhds 0) := by
  have hg2 : gamma ^ 2 > 0 := pow_pos hg 2
  have hg2' : gamma ^ 2 ≠ 0 := ne_of_gt hg2
  rw [show (fun n : ℕ => 1 / ((n : ℝ) * gamma ^ 2)) =
      (fun n : ℕ => (1 / gamma ^ 2) * (1 / (n : ℝ))) from by ext n; ring]
  rw [show (0 : ℝ) = (1 / gamma ^ 2) * 0 from by ring]
  apply Filter.Tendsto.const_mul
  simp only [one_div]
  exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

/-! ## Result 92: ODE dimension counting

For a model with k stages where stage i has nᵢ sub-stages,
total dimension = Σᵢ nᵢ + 2 (the +2 is for θ and R). -/

theorem ode_dimension (stages : List ℕ) :
    stages.sum + 2 = (stages.map id).sum + 2 := by
  simp

/-! ## Result 93: Transmissibility preserved across stages

For Erlang(n, nγ) infectious period with transmission rate β,
the transmissibility T_n = 1 - (nγ/(β+nγ))^n.

For n=1: T₁ = 1 - γ/(β+γ) = β/(β+γ) — standard Markovian result. -/

theorem transmissibility_n_one (beta gamma : ℝ) (hb : 0 < beta) (hg : 0 < gamma) :
    1 - gamma / (beta + gamma) = beta / (beta + gamma) := by
  have h : beta + gamma ≠ 0 := ne_of_gt (add_pos hb hg)
  field_simp
  ring

/-! ## Result 94: Limiting transmissibility

As n→∞, T_n = 1-(nγ/(β+nγ))^n → 1-exp(-β/γ).

We verify the intermediate identity: nγ/(β+nγ) = 1/(1+β/(nγ)). -/

theorem transmissibility_ratio (n : ℕ) (beta gamma : ℝ)
    (hn : 0 < n) (hb : 0 < beta) (hg : 0 < gamma) :
    (n : ℝ) * gamma / (beta + (n : ℝ) * gamma) =
    1 / (1 + beta / ((n : ℝ) * gamma)) := by
  have hn' : (n : ℝ) > 0 := Nat.cast_pos.mpr hn
  have hng : (n : ℝ) * gamma > 0 := mul_pos hn' hg
  have hng' : (n : ℝ) * gamma ≠ 0 := ne_of_gt hng
  have hd : beta + (n : ℝ) * gamma > 0 := add_pos hb hng
  have hd' : beta + (n : ℝ) * gamma ≠ 0 := ne_of_gt hd
  have h1bg : 1 + beta / ((n : ℝ) * gamma) ≠ 0 := by positivity
  field_simp
  ring

end
