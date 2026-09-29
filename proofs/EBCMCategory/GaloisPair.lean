import EBCMCategory.CoarseGrain

/-!
# GaloisPair — The (F, G) pair between Edge and Node

The coarse-graining map F: Edge → Node and the Poisson lift
G: Node → Edge satisfy the following properties:

* F ∘ G ∘ F = F and G ∘ F ∘ G = G (idempotency)
* F ∘ G preserves R₀ exactly
* G ∘ F ≠ id (G ∘ F sets every dimension to 4)

F and G are not a Galois connection for the dimension preorder: for
E = ⟨10, r⟩ and N = ⟨3, r⟩, F(E) ≤ N holds but E ≤ G(N) fails
(`not_galoisConnection_coarseGrain_poissonLift`). The idempotency laws are
proved directly, and F ∘ G is the identity on records of dimension 3
(`FG_eq_self_of_dim_three`). Every statement here is about `EpiModel`
records, which store only a dimension and an R₀: F sets the dimension to
3, G sets it to 4, and both keep R₀.

## Key results

| Result | Statement                                      |
|--------|-------------------------------------------------|
| 9      | G is monotone                                   |
| 10     | Counit: F(G(N)).dim = 3                         |
| 11     | G(F(E)).dim = 4 for all E                       |
| 12     | Idempotency: F ∘ G ∘ F = F                      |
| 13     | Idempotency: G ∘ F ∘ G = G                      |
| 14     | G ∘ F ≠ id (G ∘ F forgets the dimension)        |
| 15     | Round-trip preserves R₀                          |
-/

/-! ## The Poisson lift -/

/-- The Poisson lift G: Node → Edge.
    Embeds a node model into the canonical 4D edge model with
    Poisson degree distribution.
    In Lean, `poissonLift` sets the dimension to 4 and keeps R₀; no degree
    distribution is stored. -/
def poissonLift (n : EpiModel) : EpiModel where
  dim := 4
  R0 := n.R0

/-- **Result 9.** G is (trivially) monotone. -/
theorem poissonLift_mono : Monotone poissonLift := by
  intro _ _ _
  show 4 ≤ 4
  omega

/-! ## Core properties -/

/-- **Result 10.** Counit: F(G(N)).dim = 3. -/
theorem counit_dim (n : EpiModel) :
    (coarseGrain (poissonLift n)).dim = 3 := by
  rfl

/-- **Result 11.** G(F(E)).dim = 4 for all E. -/
theorem unit_dim (e : EpiModel) :
    (poissonLift (coarseGrain e)).dim = 4 := by
  rfl

/-- **Result 12.** F ∘ G ∘ F = F (left idempotency). -/
theorem F_G_F_eq_F (e : EpiModel) :
    coarseGrain (poissonLift (coarseGrain e)) = coarseGrain e := by
  rfl

/-- **Result 13.** G ∘ F ∘ G = G (right idempotency). -/
theorem G_F_G_eq_G (n : EpiModel) :
    poissonLift (coarseGrain (poissonLift n)) = poissonLift n := by
  rfl

/-- **Result 14.** G ∘ F ≠ id: G ∘ F sets the dimension of every record to 4.
    Witness: a record of dimension 10 maps to dimension 3 via F and back to
    dimension 4 via G.
    `EpiModel` stores only a dimension and an R₀, so this says nothing about
    what the lost state variables describe. -/
theorem GF_ne_id : ∃ (e : EpiModel), poissonLift (coarseGrain e) ≠ e := by
  use ⟨10, 1⟩
  intro h
  have : (4 : ℕ) = 10 := congrArg EpiModel.dim h
  omega

/-! ## R₀ preservation -/

/-- F preserves R₀. -/
theorem coarseGrain_R0 (e : EpiModel) : (coarseGrain e).R0 = e.R0 :=
  rfl

/-- G preserves R₀. -/
theorem poissonLift_R0 (n : EpiModel) : (poissonLift n).R0 = n.R0 :=
  rfl

/-- **Result 15.** The round-trip F ∘ G preserves R₀ exactly. -/
theorem FG_preserves_R0 (n : EpiModel) :
    (coarseGrain (poissonLift n)).R0 = n.R0 :=
  rfl

/-! ## F and G are not a Galois connection -/

/-- F ∘ G is the identity on records of dimension 3. -/
theorem FG_eq_self_of_dim_three (n : EpiModel) (h : n.dim = 3) :
    coarseGrain (poissonLift n) = n := by
  cases n
  simp_all [coarseGrain, poissonLift]

/-- F and G are not a Galois connection for the dimension preorder on
    `EpiModel`: for E = ⟨10, 1⟩ and N = ⟨3, 1⟩, F(E) ≤ N holds but
    E ≤ G(N) fails. -/
theorem not_galoisConnection_coarseGrain_poissonLift :
    ¬ GaloisConnection coarseGrain poissonLift := by
  intro h
  have h' : (⟨10, 1⟩ : EpiModel) ≤ poissonLift ⟨3, 1⟩ :=
    (h ⟨10, 1⟩ ⟨3, 1⟩).mp (show (3 : ℕ) ≤ 3 from le_refl 3)
  exact absurd (show (10 : ℕ) ≤ 4 from h') (by decide)

/-- G and F are not a Galois connection in the other order either: for
    E = N = ⟨3, 1⟩, E ≤ F(N) holds but G(E) ≤ N fails. -/
theorem not_galoisConnection_poissonLift_coarseGrain :
    ¬ GaloisConnection poissonLift coarseGrain := by
  intro h
  have h' : poissonLift ⟨3, 1⟩ ≤ (⟨3, 1⟩ : EpiModel) :=
    (h ⟨3, 1⟩ ⟨3, 1⟩).mpr (show (3 : ℕ) ≤ 3 from le_refl 3)
  exact absurd (show (4 : ℕ) ≤ 3 from h') (by decide)
