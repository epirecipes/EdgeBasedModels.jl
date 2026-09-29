import Mathlib.Tactic

/-!
# Obstructions — When EBCM changes form (and what truly breaks it)

The **standard** EBCM (4 ODE variables, single θ) rests on three assumptions:
1. The network is a **configuration model** (tree-like local structure)
2. Disease transitions are **Markovian** (exponential waiting times)
3. Initial infections are **uniform** (i.i.d. across nodes)

Violations of these assumptions do NOT necessarily break the EBCM *framework*
— they change its mathematical character:

### Network structure (assumption 1)
For the specific network classes below an EBCM variant is known, at a
dimension cost; this is a literature summary, not a statement about network
structure in general:
* **Clustering** (triangles): the triangle EBCM of Volz, Miller, Galvani &
  Meyers (2011) tracks line states φ_X and triangle states φ_{XY} on
  configuration-model networks with triangles; their system has 7 ODEs.
* **Degree correlations**: Multi-type EBCM of Miller & Volz (2013)
  with mixing matrix. Still an ODE system.
* **Population structure**: Multi-type EBCM with biased mixing.

### Non-Markovian dynamics (assumption 2)
Changes the *type* of system, not an absolute obstruction:
* Sherborne, Miller, Blyuss & Kiss (2018, J. Math. Biol. 76, 755–778)
  proved the non-Markovian EBCM is equivalent to message passing for
  general τ(a), q(a).
* The system becomes a **PDE** (von Foerster age-structured equation)
  rather than an ODE, with infinite-dimensional state space.
* For Markovian dynamics, the PDE collapses back to the standard ODE.
* The ODE approximation via n-stage Erlang needs 2n + 2 variables in the
  counting convention of `extensionDim` (θ, n edge stages φ_{I_j}, n node
  stages I_j, and R): 4 for n = 1 and 6 for n = 2.

### Localised initial conditions (assumption 3)
Among the three standard assumptions, only localised seeding has no EBCM
variant. When initial infections are spatially correlated, edge states are
correlated through shared proximity to the seed, breaking the factorisation
that all EBCM variants (ODE and PDE) require. In Lean this holds by
definition: `ebcmExists` is `init = .uniform`.

## Key results

| Result | Statement                                              |
|--------|--------------------------------------------------------|
| 17     | Standard ODE EBCM valid under all three assumptions     |
| 18     | Triangle clustering: standard fails, triangle EBCM (ODE) |
| 19     | Non-Markovian: ODE fails, PDE EBCM works (exact)        |
| 20     | Localised initials: genuine obstruction (all variants)   |
| 21     | Degree correlations: multi-type EBCM works (ODE)        |
| 22     | Hard-coded counts: clustered (13) > 3·standard (4) − 1   |
| 23     | `systemRequired` is ODE, PDE or impossible as tabulated  |
| 24     | Erlang staging needs more variables than Markovian       |

## References

* Sherborne, Miller, Blyuss, Kiss (2018). Mean-field models for
  non-Markovian epidemics on networks. J. Math. Biol. 76, 755–778.
  DOI: 10.1007/s00285-017-1155-0
* Volz, Miller, Galvani, Meyers (2011). Effects of heterogeneous and
  clustered contact patterns on infectious disease dynamics.
  PLoS Comput. Biol. 7(6): e1002042.
* Miller, Volz (2013). Incorporating disease and population structure
  into models of SIR disease in contact networks. PLoS ONE 8(8): e69162.
* Miller (2009). Spread of infectious disease through clustered
  populations. J. R. Soc. Interface 6, 1121–1134.
-/

/-! ## Classifications -/

/-- Classification of network structure. -/
inductive NetworkType where
  | configurationModel   -- tree-like (standard EBCM is exact)
  | clusteredTriangles   -- clustering via triangles (triangle EBCM is exact)
  | degreeCorrelated     -- degree-degree correlations (multi-type EBCM works)
  | multiplexStaticDyn   -- static+dynamic layers (multiplex EBCM works)
  deriving DecidableEq, Repr

/-- Classification of disease dynamics.
    Non-Markovian dynamics are NOT an absolute obstruction — they change
    the EBCM from an ODE to a PDE (age-structured von Foerster equation).
    The Erlang approximation recovers an ODE system with more variables. -/
inductive TransitionType where
  | markovian       -- exponential waiting times → ODE EBCM
  | erlangStaged    -- n-stage Erlang approximation → ODE EBCM (more vars)
  | generalNonMarkov -- general τ(a), q(a) → PDE EBCM (exact, infinite-dim)
  deriving DecidableEq, Repr

/-- Classification of initial conditions. -/
inductive InitCondType where
  | uniform    -- i.i.d. infection with probability ε
  | localised  -- spatially correlated initial outbreak
  deriving DecidableEq, Repr

/-- The type of mathematical system required. -/
inductive SystemType where
  | ode        -- finite-dimensional ODE system
  | pde        -- age-structured PDE (von Foerster + integral equations)
  | impossible -- no EBCM variant works
  deriving DecidableEq, Repr

/-! ## Validity predicates -/

/-- The **standard** EBCM (4 ODE variables) is valid iff:
    configuration model + Markovian + uniform initials. -/
def standardEbcmValid (net : NetworkType) (trans : TransitionType)
    (init : InitCondType) : Prop :=
  net = .configurationModel ∧ trans = .markovian ∧ init = .uniform

/-- An EBCM variant exists (as ODE or PDE) for any network type and
    any transition type, provided initials are uniform. -/
def ebcmExists (_net : NetworkType) (_trans : TransitionType)
    (init : InitCondType) : Prop :=
  init = .uniform

/-- What type of system is needed? -/
def systemRequired (trans : TransitionType) (init : InitCondType) : SystemType :=
  match init with
  | .localised => .impossible
  | .uniform =>
    match trans with
    | .markovian => .ode
    | .erlangStaged => .ode
    | .generalNonMarkov => .pde

/-- **Result 17.** The standard EBCM is valid under all correct assumptions. -/
theorem standard_ebcm_valid :
    standardEbcmValid .configurationModel .markovian .uniform :=
  ⟨rfl, rfl, rfl⟩

/-! ## Network structure: dimension cost, not obstruction -/

/-- **Result 18.** Clustering breaks the *standard* EBCM, but NOT the
    EBCM framework. The triangle EBCM handles it with more variables. -/
theorem clustering_breaks_standard :
    ¬ standardEbcmValid .clusteredTriangles .markovian .uniform := by
  intro ⟨h, _, _⟩
  exact NetworkType.noConfusion h

/-- But an EBCM variant exists for clustered networks. -/
theorem clustering_ebcm_exists :
    ebcmExists .clusteredTriangles .markovian .uniform :=
  rfl

/-- **Result 21.** Degree correlations break the standard EBCM,
    but multi-type EBCM handles them. -/
theorem degreeCorr_breaks_standard :
    ¬ standardEbcmValid .degreeCorrelated .markovian .uniform := by
  intro ⟨h, _, _⟩
  exact NetworkType.noConfusion h

theorem degreeCorr_ebcm_exists :
    ebcmExists .degreeCorrelated .markovian .uniform :=
  rfl

theorem multiplex_ebcm_exists :
    ebcmExists .multiplexStaticDyn .markovian .uniform :=
  rfl

/-! ## Non-Markovian dynamics: PDE, not obstruction -/

/-- **Result 19.** Non-Markovian dynamics change the system type from ODE
    to PDE, but the EBCM framework still works exactly.

    Sherborne, Miller, Blyuss & Kiss (2018) proved the non-Markovian EBCM
    is equivalent to message passing for general τ(a), q(a).
    The von Foerster equation (∂/∂t + ∂/∂a)φ_I = -[ζ(a)+ρ(a)]φ_I tracks
    the infection-age distribution, giving an infinite-dimensional state. -/
theorem nonmarkov_requires_pde :
    systemRequired .generalNonMarkov .uniform = .pde :=
  rfl

/-- Non-Markovian + uniform: an EBCM exists (as a PDE system). -/
theorem nonmarkov_ebcm_exists (net : NetworkType) :
    ebcmExists net .generalNonMarkov .uniform :=
  rfl

/-- The Erlang-staged approximation recovers an ODE system. -/
theorem erlang_is_ode :
    systemRequired .erlangStaged .uniform = .ode :=
  rfl

/-- Markovian dynamics with uniform initial infection give an ODE system. -/
theorem markov_is_ode :
    systemRequired .markovian .uniform = .ode :=
  rfl

/-! ## Localised initials: the genuine obstruction -/

/-- **Result 20.** Among the three standard assumptions, only localised
    seeding has no EBCM variant. They break ALL EBCM variants (ODE and PDE alike)
    because edge states become correlated through shared proximity
    to the seed, breaking the factorisation that underpins all EBCMs.
    The Lean statement holds by definition of `ebcmExists`; it records the
    classification, it does not derive it. -/
theorem localised_genuine_obstruction (net : NetworkType) (trans : TransitionType) :
    ¬ ebcmExists net trans .localised := by
  intro h
  exact InitCondType.noConfusion h

theorem localised_impossible (trans : TransitionType) :
    systemRequired trans .localised = .impossible := by
  cases trans <;> rfl

/-! ## Dimension cost of extensions -/

/-- The ODE state-space dimension for each network × transition combination.
    Returns 0 for PDE systems (infinite-dimensional). -/
def extensionDim (net : NetworkType) (trans : TransitionType) : ℕ :=
  match trans with
  | .generalNonMarkov => 0  -- infinite-dimensional PDE
  | .markovian =>
    match net with
    | .configurationModel => 4
    | .clusteredTriangles => 13
    | .degreeCorrelated   => 8   -- 2-type example
    | .multiplexStaticDyn => 18
  | .erlangStaged =>
    match net with
    | .configurationModel => 6   -- 2-stage Erlang example
    | .clusteredTriangles => 15
    | .degreeCorrelated   => 12
    | .multiplexStaticDyn => 22

/-- **Result 22.** In the hard-coded table `extensionDim`, the
    triangle-clustered EBCM has 13 variables, more than 3·4 − 1 for the
    standard EBCM. This is the price of tracking joint triangle states.
    The counts are labels, not derived here; Volz et al. (2011) give a
    7-ODE system for triangle-clustered networks. -/
theorem clustering_dimension_cost :
    extensionDim .clusteredTriangles .markovian >
    3 * extensionDim .configurationModel .markovian - 1 := by
  simp [extensionDim]

/-- The standard EBCM is the most compact ODE variant. -/
theorem standard_most_compact (net : NetworkType) :
    extensionDim .configurationModel .markovian ≤ extensionDim net .markovian := by
  cases net <;> simp [extensionDim]

/-! ## Result 24: Erlang approximation -/

/-- **Result 24.** The Erlang approximation turns the PDE into an ODE
    at the cost of extra variables. For an n-stage Erlang infectious period
    on a configuration model, the standard 4 variables become 2n + 2
    (θ, n edge stages φ_{I_j}, n node stages I_j, and R).

    Here we show the Erlang variant always needs more variables than
    the Markovian variant on the same network. -/
theorem erlang_costs_more (net : NetworkType) :
    extensionDim net .markovian ≤ extensionDim net .erlangStaged := by
  cases net <;> simp [extensionDim]

/-! ## System type classification -/

/-- **Result 23.** Complete classification of what system type is needed.
    * Uniform + Markovian/Erlang → ODE (always works)
    * Uniform + general non-Markov → PDE (always works, infinite-dim)
    * Localised → impossible (by definition of `systemRequired`) -/
theorem system_classification (trans : TransitionType) (init : InitCondType) :
    (init = .uniform ∧ (trans = .markovian ∨ trans = .erlangStaged) →
      systemRequired trans init = .ode) ∧
    (init = .uniform ∧ trans = .generalNonMarkov →
      systemRequired trans init = .pde) ∧
    (init = .localised →
      systemRequired trans init = .impossible) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨rfl, h⟩; cases h with | inl h => subst h; rfl | inr h => subst h; rfl
  · rintro ⟨rfl, rfl⟩; rfl
  · intro h; subst h; cases trans <;> rfl

/-! ## Marginalisation obstruction (Theorem T2)

For a two-variable surrogate of a closed order-4 moment system and a
one-variable surrogate of a closed order-3 system (defined below), the closed
dynamics do **not** project consistently under the surrogate
marginalisation `M(a,b) = a + b`.

Concretely, with `Mat_3from4 : ℝ^{n_4} → ℝ^{n_3}` the linear marginalisation
map and `F_k_Kirkwood` the Kirkwood-closed RHS at order `k`, the diagram

       F_4_Kirkwood
   V₄ ─────────────► V₄
   │                  │
 M │                  │ M
   ▼                  ▼
   V₃ ─────────────► V₃
       F_3_Kirkwood

does **not** commute at the witness state. Theorem T1
(`dynamic_marginalisation_iff_equivariance` in `MarginalisationFunctor.lean`)
needs global flows of both systems, and the order-3 surrogate `c ↦ c²/4` has
none (`no_flow_F3Kℝ`), so T1 does not apply to this witness. The local
statement does hold: for any local solutions of the two surrogate systems
from `u` and `M u`, `M · u₄(t) ≠ u₃(t)` for all small `t > 0`
(`MarginalisationDynamicalGap.witness_localGap_ge`).

The proof uses a **concrete ℚ-valued surrogate**. We use a 2-dim order-4
surrogate (with mnemonic labels `a = (C₄, SISI)` and `b = (C₄, SSSS)`) and
a 1-dim order-3 surrogate (`c = (P₃, SIS)`), with `M(a,b) = a + b`.
The labels are mnemonic only: `M` is not the subgraph marginalisation of
these classes (deleting a vertex of C₄ SISI gives P₃ SIS or P₃ ISI, and
deleting a vertex of C₄ SSSS gives P₃ SSS).
The surrogate right-hand sides are chosen, not derived from a closure:
`F₄(a,b) = (a·b, b)` is bilinear, as a pair-Kirkwood closure is, and
`F₃(c) = c²/4` is quadratic.

This is one arithmetic witness for one pair of surrogate fields, not a
general law: with `M = id` a quadratic field commutes with itself, and at
the witness state the quadratic field `c ↦ 3c²/8` agrees with `M ∘ F₄`
(both give 6; `MarginalisationDynamicalGap.kirkwoodForm_matches_at_witness`). -/

namespace MarginalisationObstruction

/-- Index type for the order-4 surrogate (a = C₄ SISI, b = C₄ SSSS). -/
inductive Idx4 | a | b
  deriving DecidableEq, Repr

/-- Index type for the order-3 surrogate (c = P₃ SIS). -/
inductive Idx3 | c
  deriving DecidableEq, Repr

/-- Order-4 state vector. -/
abbrev U4 := Idx4 → ℚ
/-- Order-3 state vector. -/
abbrev U3 := Idx3 → ℚ

/-- The marginalisation `M : U4 → U3`, here `M(u)(c) = u(a) + u(b)`. -/
def M_witness (u : U4) : U3 := fun _ => u .a + u .b

/-- The Kirkwood-closed order-4 RHS at the witness configuration. The
    bilinear `(a·b, b)` form is the characteristic shape of a pair-Kirkwood
    closure applied to a 5-vertex moment that decomposes as a product of
    a "pair" entry (`a`) and a "single" entry (`b`). -/
def F4_Kirkwood (u : U4) : U4 := fun
  | .a => u .a * u .b
  | .b => u .b

/-- The Kirkwood-closed order-3 RHS at the witness configuration. The
    quadratic-rational `c²/4` form is the analogous order-3 Kirkwood
    closure applied to the collapsed variable. -/
def F3_Kirkwood (v : U3) : U3 := fun _ => (v .c) ^ 2 / 4

/-- **Result 25 — Theorem T2 (Marginalisation obstruction).**
    There exists a state at which `M ∘ F₄_Kirkwood ≠ F₃_Kirkwood ∘ M`.

    Witness: `u = (a ↦ 1, b ↦ 3)`.
    * `M (F₄_Kirkwood u) (c) = 1·3 + 3 = 6`.
    * `F₃_Kirkwood (M u) (c) = (1+3)² / 4 = 4`.
    The diagram fails by `6 ≠ 4`. T1 does not apply here (the order-3
    field has no global flow); the local consequence, `M · u₄(t) ≠ u₃(t)`
    for small `t > 0`, is `MarginalisationDynamicalGap.witness_localGap_ge`. -/
theorem kirkwood_marginalisation_obstruction :
    ∃ (u : U4), M_witness (F4_Kirkwood u) ≠ F3_Kirkwood (M_witness u) := by
  refine ⟨fun i => (match i with | .a => 1 | .b => 3 : ℚ), ?_⟩
  intro h
  have h_c := congrArg (fun f => f Idx3.c) h
  simp [M_witness, F4_Kirkwood, F3_Kirkwood] at h_c
  norm_num at h_c

/-- The witness explicitly evaluated: the LHS minus the RHS is a fixed
    nonzero rational. The value 2 is a property of the two surrogate
    fields only. Nothing links it to the order-3 and order-4 moment
    equations of the Julia implementation, so it is not a test oracle for
    them. -/
theorem kirkwood_obstruction_witness_value :
    let u : U4 := fun i => match i with | .a => 1 | .b => 3
    M_witness (F4_Kirkwood u) Idx3.c - F3_Kirkwood (M_witness u) Idx3.c = 2 := by
  simp [M_witness, F4_Kirkwood, F3_Kirkwood]
  norm_num

end MarginalisationObstruction
