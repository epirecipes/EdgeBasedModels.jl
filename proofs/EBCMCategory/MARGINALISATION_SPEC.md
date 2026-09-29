# Subgraph Marginalisation under Closed Moment Dynamics — SPEC

Companion specification for the Lean files
`MarginalisationFunctor.lean`, `MarginalisationObstruction` (added to
`Obstructions.lean`), `MarginalisationCharacterization.lean` and
`MarginalisationDynamicalGap.lean`. No `sorry` remains in any of them.

## 1. Definitions

* `MotifShape` — opaque inductive enumeration of unlabelled connected
  subgraph shapes on 3 or 4 vertices: `P3, C3, P4, K13, Paw, C4, K4e, K4`.
  We do not formalise the underlying graphs — only their *names*.
* For each shape `σ`, `stateClassCount σ : ℕ` is the number of orbits of
  `{S,I}^V(σ)` under `Aut(σ)`. Concrete values are kept opaque (an
  `opaque` constant: nothing downstream depends on them).
* `Order3Var` is a structure of a shape in `{P3, C3}` and a
  `Fin (stateClassCount σ)`, and similarly `Order4Var` over the six
  4-vertex shapes. These types, `V_3`, `V_4` and `ClosedSystem` are
  declared for documentation only; no theorem uses them.
* `V_k := Order_k_Var → ℝ` (or `ℚ` when we want explicit arithmetic).
  These are finite-dimensional ℝ-vector spaces.
* **Marginalisation `M`** is *any* linear map. The numerical entries are
  abstracted: the only structural fact used is *linearity*. T1, T5 and T7
  use a continuous linear map `M : V₄ →L[ℝ] V₃` between normed spaces; T3
  and T4 use a linear map `M : V₄ →ₗ[ℝ] V₃` between ℝ-modules.
* **Exact dynamics:** unspecified — only used as motivation. The
  invariant `M · x_4_exact(t) = x_3_exact(t)` is asserted to hold for
  the unclosed CTMC moments by definition of `M`.
* **Closed RHS at order k:** a (typically nonlinear) function
  `F_k : V_k → V_k`. We bundle it inside
  ```
  structure ClosedSystem (V : Type _) where
    F       : V → V
    F_exact : V → V
  ```
  The theorems take the field `F : V → V` directly. Smoothness/Lipschitz
  hypotheses are deferred (see §3).
* **Flow:** `IsFlow F φ` ↔ `(∀ v, φ v 0 = v) ∧ ∀ v t, HasDerivAt (φ v) (F (φ v t)) t`.
  Existence and uniqueness are *hypotheses* on the systems, not derived.
  `IsFlow` asks for solutions on all of `ℝ`, so a field whose solutions
  blow up in finite time has no flow: `F3Kℝ` (`c ↦ c²/4`) has none
  (`no_flow_F3Kℝ`).
* **Local solution:** `IsLocalSolution F v₀ δ ψ` ↔
  `0 < δ ∧ ψ 0 = v₀ ∧ ∀ t, |t| < δ → HasDerivAt ψ (F (ψ t)) t`. The local
  forms of M3, T5 and T7 use only this.

## 2. Theorem statements

### T1 (functor / equivariance — `MarginalisationFunctor.lean`).

```
theorem dynamic_marginalisation_iff_equivariance
    (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃)
    {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃}
    (h₄ : IsFlow F₄ φ₄) (h₃ : IsFlow F₃ φ₃)
    (uniq₃ : UniqueFlow F₃) :
    (∀ u, M (F₄ u) = F₃ (M u)) ↔ (∀ u t, M (φ₄ u t) = φ₃ (M u) t)
```

* Plain math: for global flows, and unique solutions of `F₃`, along
  trajectories `M ∘ φ₄(·, t) = φ₃(M ·, t) ↔ RHS commute`.
* (←) Differentiate both sides at `t = 0`; uses `HasFDerivAt.comp_hasDerivAt`.
* (→) The curve `t ↦ M (φ₄ u t)` solves the order-3 ODE with initial
  value `M u`; by uniqueness it equals `φ₃ (M u) t`.
* Proof status: both directions are proved; there is no `sorry`.
* Local form of (←): `rhs_commute_of_local_traj_commute` needs only local
  solutions through `u` and `M u` that agree on `(-δ, δ)`, and no uniqueness.

### T2 (Kirkwood obstruction — added to `Obstructions.lean`).

```
theorem kirkwood_marginalisation_obstruction :
    ∃ (u4 : Order4Var → ℚ), M_Q (F4_Kirkwood u4) ≠ F3_Kirkwood (M_Q u4)
```

* We use a **concrete ℚ-valued surrogate** with mnemonic labels:
  two order-4 entries (`a = C_4 SISI`, `b = C_4 SSSS` placeholder) and
  one order-3 entry (`c = P_3 SIS`); `M_Q(a,b) = a + b`;
  `F4_Kirkwood (a,b) = (a*b, b)`; `F3_Kirkwood c = c^2 / 4`. In Lean the
  index types are `Idx4 = {a, b}` and `Idx3 = {c}`, not `Order4Var`/`Order3Var`.
  `M_Q` is not the subgraph marginalisation of these classes, and the two
  fields are chosen, not derived from a closure.
  It is one arithmetic witness for one pair of fields, not a general law:
  with `M = id` a quadratic field commutes with itself, and at `u4 = (1, 3)`
  the quadratic field `c ↦ 3c²/8` agrees with `M ∘ F4_Kirkwood`.
* Witness: `u4 = (1, 3)`; `decide` / `norm_num` discharges the
  arithmetic.
* Proof status: **complete, no `sorry`.**

### T3 (structural characterization — `MarginalisationCharacterization.lean`).

```
theorem kirkwood_form_not_equivariant :
    ∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : AddCommGroup V₃)
      (_ : Module ℝ V₄) (_ : Module ℝ V₃)
      (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
      C₄.IsKirkwoodForm ∧
      ∀ (C₃ : ClosureFamily V₃), ¬ Equivariant M C₄.C C₃.C
```

* Plain math: T3 is the existential statement T3b. There is a linear `M`
  and a non-additive order-4 field `C₄` such that no order-3 field `C₃`
  satisfies `M ∘ C₄ = C₃ ∘ M` (the witness of T2, over ℝ).
* `IsKirkwoodForm C` means only that `C` is not additive. The universal
  statement "no non-additive closure is ever equivariant" is false for
  this predicate: with `M = id`, `x ↦ x²` is non-additive and equivariant
  (`exists_kirkwoodForm_equivariant`). The universal statement for genuine
  multiplicative-rational closures is not formalised.
* Fibre criterion: some `C₃` makes the diagram commute iff `C₄` maps each
  fibre of `M` into a single fibre (`exists_equivariant_iff_fibrewise`).
  For a linear `L₄` this reads `L₄(ker M) ⊆ ker M`
  (`linear_admits_equivariant_iff`), so linear closures are not
  equivariant for every `M`.
* Proof status: every statement above is proved; there is no `sorry`.
  `linear_closure_equivariant` is tautological (its hypothesis is its
  conclusion) and `isLinear_admits_equivariant` is vacuous (`∨ True`).
* Connection to `ClosureTheorem.lean`: the Kiss–Kenah–Rempala
  conditions ensure `F_3` is exact at the *unclosed limit* (κ constant)
  but place no constraint on the order-4 closure used to define `F_4`.
  T3c records only that a degree record with `closureKappa = 1` can be
  paired with the non-equivariant surrogate of T3b; the two are unrelated
  data.

## 3. Assumptions

1. **Quotient by automorphism** is implicit in the definition of
   `Order_k_Var` via the `stateClassCount` opaque function. No
   downstream proof inspects the orbits.
2. **Finite host** is encoded only through finiteness of the index
   types `Order_k_Var`. The `(N-3)` combinatorial factor in the exact
   marginalisation identity is absorbed into the abstract `M`; we never
   assert a closed form for `M`.
3. **ODE flow existence/uniqueness** is *hypothesised*, not derived.
   Picard–Lindelöf gives only local existence for `C¹` `F`; global flows
   (`IsFlow`) need not exist, and for `F3Kℝ` they do not (`no_flow_F3Kℝ`).
   T1 carries global existence and uniqueness as explicit hypotheses; the
   local forms of M3, T5 and T7 assume only local solutions.
4. **Real vs Rational.** T1 uses `ℝ` (general dynamical statement);
   T2 uses `ℚ` (concrete computation); T3 is stated over ℝ-modules.

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

**Specialisation to the (2,1) witness** (`algebraicGap_at_witness`):
`algebraicGap MℝLinCLM F4Kℝ F3Kℝ u₁ = fun _ => 2`.
The global-flow corollary `trajectoryGap_rate_two_at_witness` is vacuous,
because F3Kℝ has no global flow (`no_flow_F3Kℝ`).
For *any* local solutions ψ₄ of F4Kℝ from u₁ and ψ₃ of F3Kℝ from M u₁, the
gap `t ↦ M(ψ₄ t) − ψ₃ t` has first-order rate exactly 2
(`witness_localGap_hasDerivAt`), and such local solutions exist
(`witness_local_solutions_exist`).
For another order-3 field C₃ the rate is 6 − C₃(4) (`algebraicGap_witness`).
None of this is a formal bridge to the empirically observed
`err_m4 − err_m3 ≈ 0.32` in the B(c) Gillespie testset.

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

Here "exact" means only agreement with the fitted constant `F3_exact = 6`.
T6 is one surrogate witness and says nothing about the empirical phase
reversal. T3b (via T4) shows that no order-3 field commutes with F4Kℝ
under MℝLin at every state; at the single state u₁ the non-additive field
`c ↦ 3c²/8` does match (`kirkwoodForm_matches_at_witness`).


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

At the (2,1) witness the global-flow form is vacuous (F3Kℝ has no global
flow). The local form `localGap_norm_ge_half_eps_t` assumes only local
solutions, and at the witness (`witness_localGap_ge`, ε = 2) it gives
`‖M(ψ₄ t) − ψ₃ t‖ ≥ t` for all small `t > 0`, for any local solutions ψ₄ of
F4Kℝ from u₁ and ψ₃ of F3Kℝ from M u₁. This concerns the surrogate fields
only and says nothing about the B(c) Gillespie comparison.


Before writing code we re-checked: for any non-degenerate `M` of rank
< dim V_4 and any *bilinear* (let alone multiplicative-rational) `F_4`,
`M ∘ F_4 ≡ F_3 ∘ M` is an *overdetermined* polynomial identity in the
`u_4` coordinates. Generic Kirkwood closures do not satisfy it. The
empirical Julia finding is consistent with the algebra; **no
contradiction** to the agent's empirical conclusion was found.
