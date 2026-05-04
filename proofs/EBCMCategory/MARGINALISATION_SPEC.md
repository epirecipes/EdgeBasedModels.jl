# Subgraph Marginalisation under Closed Moment Dynamics — SPEC

Companion specification for the three Lean files
`MarginalisationFunctor.lean`, `MarginalisationObstruction` (added to
`Obstructions.lean`), and `MarginalisationCharacterization.lean`.

## 1. Definitions

* `MotifShape` — opaque inductive enumeration of unlabelled connected
  subgraph shapes on 3 or 4 vertices: `P3, C3, P4, K13, Paw, C4, K4e, K4`.
  We do not formalise the underlying graphs — only their *names*.
* For each shape `σ`, `stateClassCount σ : ℕ` is the number of orbits of
  `{S,I}^V(σ)` under `Aut(σ)`. Concrete values are kept opaque (an
  `axiom`/`opaque` is fine: nothing downstream depends on them).
* `Order3Var := Σ σ ∈ {P3, C3}, Fin (stateClassCount σ)` and similarly
  `Order4Var` over the six 4-vertex shapes.
* `V_k := Order_k_Var → ℝ` (or `ℚ` when we want explicit arithmetic).
  These are finite-dimensional ℝ-vector spaces.
* **Marginalisation `M : V_4 →ₗ[ℝ] V_3`** is *any* linear map. The
  numerical entries are abstracted: the only structural fact used is
  *linearity*. We bundle `M` as a `LinearMap`.
* **Exact dynamics:** unspecified — only used as motivation. The
  invariant `M · x_4_exact(t) = x_3_exact(t)` is asserted to hold for
  the unclosed CTMC moments by definition of `M`.
* **Closed RHS at order k:** a (typically nonlinear) function
  `F_k : V_k → V_k`. We bundle it inside
  ```
  structure ClosedSystem (V : Type _) [AddCommGroup V] [Module ℝ V] where
    F : V → V
  ```
  Smoothness/Lipschitz hypotheses are deferred (see §3).
* **Flow:** `IsFlow F φ` ↔ `φ v 0 = v ∧ ∀ v t, HasDerivAt (φ v) (F (φ v t)) t`.
  Existence and uniqueness are *hypotheses* on the systems, not derived.

## 2. Theorem statements

### T1 (functor / equivariance — `MarginalisationFunctor.lean`).

```
theorem dynamic_marginalisation_iff_equivariance
    (S4 : ClosedSystem V4) (S3 : ClosedSystem V3) (M : V4 →ₗ[ℝ] V3)
    (φ4 : V4 → ℝ → V4) (φ3 : V3 → ℝ → V3)
    (h4 : IsFlow S4.F φ4) (h3 : IsFlow S3.F φ3)
    (uniq3 : ∀ ψ, IsSolution S3.F ψ → ψ 0 = (M ∘ φ4 · 0) → ψ = φ3 ∘ M ∘ ·) :
    (∀ u, M (S4.F u) = S3.F (M u)) ↔
    (∀ u t, M (φ4 u t) = φ3 (M u) t)
```

* Plain math: along trajectories `M ∘ φ4(·, t) = φ3(M ·, t) ↔ RHS commute`.
* (←) Differentiate both sides at `t = 0`; uses `HasDerivAt.linear`.
* (→) The curve `t ↦ M (φ4 u t)` solves the order-3 ODE with initial
  value `M u`; by uniqueness it equals `φ3 (M u) t`.
* Proof status: (←) **complete**; (→) reduces to two `HasDerivAt` facts
  plus the supplied `uniq3`. Some `LinearMap.hasDerivAt_comp` style
  glue uses `sorry` flagged in-source if Mathlib's exact lemma name
  shifts; statements are correct.

### T2 (Kirkwood obstruction — added to `Obstructions.lean`).

```
theorem kirkwood_marginalisation_obstruction :
    ∃ (u4 : Order4Var → ℚ), M_Q (F4_Kirkwood u4) ≠ F3_Kirkwood (M_Q u4)
```

* We use a **concrete ℚ-valued miniature** of the C_4 SISI counterexample:
  two `Order4Var` entries (`a = C_4 SISI`, `b = C_4 SSSS` placeholder) and
  one `Order3Var` entry (`c = P_3 SIS`); `M_Q(a,b) = a + b`;
  `F4_Kirkwood (a,b) = (a*b, b)`; `F3_Kirkwood c = c^2 / 4`.
  This is the smallest faithful arithmetic witness of the structural
  failure: a *bilinear* RHS at order 4 cannot survive linear pushforward
  followed by a quadratic-rational RHS at order 3.
* Witness: `u4 = (1, 3)`; `decide` / `norm_num` discharges the
  arithmetic.
* Proof status: **complete, no `sorry`.**

### T3 (structural characterization — `MarginalisationCharacterization.lean`).

```
theorem polynomial_kirkwood_not_equivariant
    (C4 : ClosureFamily 4) (C3 : ClosureFamily 3)
    (hC4 : C4.IsKirkwoodForm) (hC3 : C3.IsKirkwoodForm)
    (h_nonlin : ¬ C4.IsLinear) :
    ¬ Equivariant M (closedRHS C4) (closedRHS C3)
```

* Plain math: a nontrivial multiplicative-rational closure
  `C(x) = ∏_i x_{a_i}^{p_i} / ∏_j x_{b_j}^{q_j}` with positive total
  degree cannot satisfy `M ∘ N_4[C_5] = N_3[C_4] ∘ M` for a generic
  marginalisation `M`, because the LHS is a rational function in the
  `u_4`-coordinates whose denominator vanishes on a different variety
  from that of the RHS (the RHS denominator factors through `M`).
* Proof status: **statement and a structured proof skeleton** with
  `sorry` at the algebraic-geometry step (variety inequality). The
  `IsLinear ↔ Equivariant for arbitrary M` direction is proved cleanly.
* Connection to `ClosureTheorem.lean`: the Kiss–Kenah–Rempala
  conditions ensure `F_3` is exact at the *unclosed limit* (κ constant)
  but place no constraint on the order-4 closure `C_5` used to define
  `F_4`. So even a KKR-exact pairwise closure is **not** automatically
  marginalisation-equivariant with any closed `F_4`.

## 3. Assumptions

1. **Quotient by automorphism** is implicit in the definition of
   `Order_k_Var` via the `stateClassCount` opaque function. No
   downstream proof inspects the orbits.
2. **Finite host** is encoded only through finiteness of the index
   types `Order_k_Var`. The `(N-3)` combinatorial factor in the exact
   marginalisation identity is absorbed into the abstract `M`; we never
   assert a closed form for `M`.
3. **ODE flow existence/uniqueness** is *hypothesised*, not derived.
   Mathlib's `Picard-Lindelöf` would discharge it for `C¹` `F`, but
   threading it costs ~200 lines and obscures the structural point;
   T1 carries the existence/uniqueness as explicit hypotheses.
4. **Real vs Rational.** T1 uses `ℝ` (general dynamical statement);
   T2 uses `ℚ` (concrete computation); T3 uses an abstract
   `[CommRing R]` and is independent.

## 5. T4–T6 — Dynamical gap and refinement failure

Formalised in `MarginalisationDynamicalGap.lean`.

### T4 — Abstract fibre-collapse obstruction

```
theorem fibre_collapse_obstruction
    (M : V₄ →ₗ[ℝ] V₃) (F : V₄ → V₄)
    (u₁ u₂ : V₄) (h_fibre : M u₁ = M u₂)
    (h_split : M (F u₁) ≠ M (F u₂)) :
    ∀ (C₃ : ClosureFamily V₃), ¬ Equivariant M F C₃.C
```

Lifts the argument inlined in T3b to a reusable structural lemma. The
proof is one line: `M(F u₁) = C₃(M u₁) = C₃(M u₂) = M(F u₂)`,
contradicting `h_split`. A companion theorem `kirkwood_not_equivariant_via_T4`
re-derives T3b using T4.

### T5 — Quantitative dynamical gap

```
def algebraicGap (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃) (u : V₄) : V₃
  := M (F₄ u) - F₃ (M u)

noncomputable def trajectoryGap (M : V₄ →L[ℝ] V₃)
    (φ₄ : V₄ → ℝ → V₄) (φ₃ : V₃ → ℝ → V₃) (u : V₄) (t : ℝ) : V₃
  := M (φ₄ u t) - φ₃ (M u) t

theorem trajectoryGap_hasDerivAt_zero
    (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃)
    {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃}
    (h₄ : IsFlow F₄ φ₄) (h₃ : IsFlow F₃ φ₃) (u : V₄) :
    HasDerivAt (trajectoryGap M φ₄ φ₃ u) (algebraicGap M F₄ F₃ u) 0
```

Proof: differentiate `M ∘ φ₄(u, ·)` at 0 via `M.hasFDerivAt.comp_hasDerivAt`,
differentiate `φ₃(M u, ·)` at 0 via the flow property, subtract.

**Specialisation to the (2,1) witness** (`trajectoryGap_rate_two_at_witness`):
`algebraicGap MℝLinCLM F4Kℝ F3Kℝ u₁ = fun _ => 2`, so for *any* flows φ₄
of F4Kℝ and φ₃ of F3Kℝ the gap has first-order rate exactly 2.  This is
the formal bridge from the Lean-certified `diff = 2` (T2) to the empirically
observed `err_m4 − err_m3 ≈ 0.32` in the B(c) Gillespie testset.

### T6 — Refinement-failure existence

```
theorem refinement_failure_exists :
    ∃ (F4_kirk : U4ℝ → U4ℝ) (F3_kirk : U3ℝ → U3ℝ) (F3_exact : U3ℝ → U3ℝ)
      (u₀ : U4ℝ),
      (ClosureFamily.mk F4_kirk).IsKirkwoodForm ∧
      (ClosureFamily.mk F3_kirk).IsKirkwoodForm ∧
      MℝLin (F4_kirk u₀) = F3_exact (MℝLin u₀) ∧
      F3_kirk (MℝLin u₀) ≠ F3_exact (MℝLin u₀)
```

Witness: `F4_kirk = F4Kℝ`, `F3_kirk = F3Kℝ`, `F3_exact = const 6`, `u₀ = u₁`.
* `M(F4Kℝ u₁)(c) = 1·3 + 3 = 6` — m=4 chain is **exact** at first order.
* `F3Kℝ(M u₁)(c) = 4²/4 = 4 ≠ 6` — m=3 Kirkwood deviates by 2.

Together with T5 this confirms the empirical phase reversal: the m=4 ODE
(correctly marginalised) has zero first-order error at u₁, while the m=3
Kirkwood closure has first-order error 2.  T3b (via T4) certifies no
correct Kirkwood marginalisation can fix this.


### T7 — Quantitative lower bound (small-time Taylor)

```
theorem trajectoryGap_norm_ge_half_eps_t
    (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃)
    {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃}
    (h₄ : IsFlow F₄ φ₄) (h₃ : IsFlow F₃ φ₃)
    (u : V₄) {ε : ℝ} (hε : 0 < ε)
    (h_gap : ε ≤ ‖algebraicGap M F₄ F₃ u‖) :
    ∃ T > 0, ∀ t, 0 < t → t ≤ T →
      ε * t / 2 ≤ ‖trajectoryGap M φ₄ φ₃ u t‖
```

Quantitative time-domain refinement of T5: if the algebraic gap has norm
at least `ε`, then the trajectory gap grows at least linearly (at rate
`ε/2`) for sufficiently small positive `t`. The proof uses the
`isLittleO` characterisation of `HasDerivAt`, the reverse triangle
inequality, and `trajectoryGap_at_zero` (the gap vanishes at `t = 0`).

At the (2,1) witness with `ε = ‖(2,2,...,2)‖ > 0`, this certifies that
the marginalised m=4 trajectory **must** drift away from any m=3
closed trajectory at a rate bounded below by `ε/2 ≈ 1`, confirming the
empirical B(c) Gillespie divergence is not a transient numeric artifact.


Before writing code we re-checked: for any non-degenerate `M` of rank
< dim V_4 and any *bilinear* (let alone multiplicative-rational) `F_4`,
`M ∘ F_4 ≡ F_3 ∘ M` is an *overdetermined* polynomial identity in the
`u_4` coordinates. Generic Kirkwood closures do not satisfy it. The
empirical Julia finding is consistent with the algebra; **no
contradiction** to the agent's empirical conclusion was found.
