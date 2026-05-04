import EBCMCategory.CoarseGrain

/-!
# GaloisPair — The (F, G) pair between Edge and Node

The coarse-graining map F: Edge → Node and the Poisson lift
G: Node → Edge satisfy key adjunction-like properties:

* F ∘ G ∘ F = F and G ∘ F ∘ G = G (idempotency)
* F ∘ G preserves R₀ exactly
* G ∘ F ≠ id (the connection is lossy)

The mathematical Galois connection F(E) ≤ N ↔ E ≤ G(N) holds on the
distribution-space preorder (where ≤ is "can be recovered from").
Here we prove the combinatorial/dimensional shadow of these properties.

## Key results

| Result | Statement                                      |
|--------|-------------------------------------------------|
| 9      | G is monotone                                   |
| 10     | Counit: F(G(N)).dim = 3                         |
| 11     | G(F(E)).dim = 4 for all E                       |
| 12     | Idempotency: F ∘ G ∘ F = F                      |
| 13     | Idempotency: G ∘ F ∘ G = G                      |
| 14     | G ∘ F ≠ id (lossy)                              |
| 15     | Round-trip preserves R₀                          |
-/

/-! ## The Poisson lift -/

/-- The Poisson lift G: Node → Edge.
    Embeds a node model into the canonical 4D edge model with
    Poisson degree distribution. -/
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

/-- **Result 14.** G ∘ F ≠ id: the connection is **lossy**.
    A 10D multi-type model maps to dim 3 via F, then lifts to dim 4.
    The 6 lost dimensions encode multi-type edge correlations. -/
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
