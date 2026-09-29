import Alignment.Registry
import Alignment.Shadows.Obstructions

/-!
# Checkers: group `Obstructions`

Registrations, forward / backward checkers and failure records for the claims of
`EBCMCategory/Obstructions.lean`. The shadows are in `Alignment/Shadows/Obstructions.lean`
(written blind). No bridges are needed: every shadow is stated directly over the operations under
test (`standardEbcmValid`, `ebcmExists`, `systemRequired`, `extensionDim`,
`MarginalisationObstruction.{M_witness, F4_Kirkwood, F3_Kirkwood}`).

Policy used for this group. Every operation under test is a lookup table, and every
implementation theorem is proved by `rfl`, constructor disequality or case analysis. So almost
every shadow could be re-proved *from scratch* from the definitions. A check counts as proved
only when the shadow is an instance, projection or logical consequence of the implementation's
statement, and `h` supplies the content. Logical consequences may read the operations by their
documented meanings (`standardEbcmValid n t i` = `n = cm ∧ t = markovian ∧ i = uniform`;
`ebcmExists n t i` = `i = uniform`). A check is recorded as failed when the shadow mentions an
operation, an instance or a property that the implementation's statement does not cover. In that
case the only proofs would re-prove it from the definitions, or re-use a proof of the
definitionally trivial `.uniform = .uniform` at a different instance. Ordered arithmetic on ℕ
(`Nat.le` constructors, `Nat.le_of_lt`, …) is not structural, and no bridge on a trusted
definition can carry an order lemma. Failures that come only from this are marked in their
reasons as audit limitations.
-/

/-! ## header.networkNotObstruction

`ebcmExists n t i` is by definition `i = .uniform`, so for the configuration model (not one of the
text's "network classes below") the case holds by `rfl`; the three listed classes come from the
implementation. -/
namespace Alignment.Shadows.Obstructions.header_networkNotObstruction

sa_claim "Obstructions.header.networkNotObstruction" group "Obstructions" required
  text "Network structure (assumption 1) For the specific network classes below an EBCM variant is known, at a dimension cost; this is a literature summary, not a statement about network structure in general:"
  impl clustering_ebcm_exists degreeCorr_ebcm_exists multiplex_ebcm_exists

@[sa_forward "Obstructions.header.networkNotObstruction" 1]
theorem fwd1 (h : sa_impl% "Obstructions.header.networkNotObstruction") : S1 := fun n =>
  match n with
  | .configurationModel => rfl
  | .clusteredTriangles => h.1
  | .degreeCorrelated => h.2.1
  | .multiplexStaticDyn => h.2.2

sa_fail_forward "Obstructions.header.networkNotObstruction" 2 "impl (clustering_ebcm_exists ∧ degreeCorr_ebcm_exists ∧ multiplex_ebcm_exists) states only existence, via ebcmExists, which is definitionally 'uniform seeding'. It says nothing about the dimension cost (S2: every non-standard class needs more variables than the standard EBCM in extensionDim). That is a closed ℕ comparison of table entries, which impl does not state and which is not structurally provable (Nat.le constructors are core-library proofs)."

@[sa_backward "Obstructions.header.networkNotObstruction"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "Obstructions.header.networkNotObstruction" :=
  ⟨s1 .clusteredTriangles, s1 .degreeCorrelated, s1 .multiplexStaticDyn⟩

end Alignment.Shadows.Obstructions.header_networkNotObstruction

/-! ## `Obstructions.table.R17` -/
namespace Alignment.Shadows.Obstructions.table_R17

sa_claim "Obstructions.table.R17" group "Obstructions" required
  text "| 17 | Standard ODE EBCM valid under all three assumptions |"
  impl standard_ebcm_valid

@[sa_forward "Obstructions.table.R17" 1]
theorem fwd1 (h : sa_impl% "Obstructions.table.R17") : S1 := h

@[sa_backward "Obstructions.table.R17"]
theorem bwd (s1 : S1) : sa_impl% "Obstructions.table.R17" := s1

end Alignment.Shadows.Obstructions.table_R17

/-! ## table.R18 (a standard-valid triple forces `markovian` and `uniform`, where the
implementation's first conjunct applies) -/
namespace Alignment.Shadows.Obstructions.table_R18

sa_claim "Obstructions.table.R18" group "Obstructions" required
  text "| 18 | Triangle clustering: standard fails, triangle EBCM (ODE) |"
  impl clustering_breaks_standard clustering_ebcm_exists

@[sa_forward "Obstructions.table.R18" 1]
theorem fwd1 (h : sa_impl% "Obstructions.table.R18") : S1 := by
  intro t i hv
  obtain ⟨hn, ht, hi⟩ := hv
  subst ht
  subst hi
  exact h.1 ⟨hn, rfl, rfl⟩

@[sa_forward "Obstructions.table.R18" 2]
theorem fwd2 (h : sa_impl% "Obstructions.table.R18") : S2 := h.2

sa_fail_forward "Obstructions.table.R18" 3 "S3 (the triangle EBCM is an ODE system: extensionDim .clusteredTriangles .markovian ≠ 0) is a closed fact about the table (13 ≠ 0). impl (clustering_breaks_standard ∧ clustering_ebcm_exists) does not state it, so a checker could only prove S3 without h (vacuous)."

@[sa_backward "Obstructions.table.R18"]
theorem bwd (s1 : S1) (s2 : S2) (_s3 : S3) : sa_impl% "Obstructions.table.R18" :=
  ⟨s1 .markovian .uniform, s2⟩

end Alignment.Shadows.Obstructions.table_R18

/-! ## `Obstructions.table.R19` -/
namespace Alignment.Shadows.Obstructions.table_R19

sa_claim "Obstructions.table.R19" group "Obstructions" required
  text "| 19 | Non-Markovian: ODE fails, PDE EBCM works (exact) |"
  impl nonmarkov_requires_pde nonmarkov_ebcm_exists

/-- `h.1` says the required system is `pde`, and `pde ≠ ode` (constructor distinctness). -/
@[sa_forward "Obstructions.table.R19" 1]
theorem fwd1 (h : sa_impl% "Obstructions.table.R19") : S1 :=
  fun he => SystemType.noConfusion (h.1.symm.trans he)

sa_fail_forward "Obstructions.table.R19" 2 "impl (nonmarkov_requires_pde ∧ nonmarkov_ebcm_exists) never mentions standardEbcmValid. ¬ standardEbcmValid .configurationModel .generalNonMarkov .uniform holds only by the definition of standardEbcmValid (generalNonMarkov ≠ markovian), independently of the impl. systemRequired and standardEbcmValid are separate lookup tables with no definitional link, so 'the standard ODE EBCM fails' is not stated."
sa_fail_forward "Obstructions.table.R19" 3 "impl never mentions standardEbcmValid. ∀ n i, ¬ standardEbcmValid n .generalNonMarkov i holds only by the definition of standardEbcmValid (generalNonMarkov ≠ markovian), independently of the impl, and is not stated."

@[sa_forward "Obstructions.table.R19" 4]
theorem fwd4 (h : sa_impl% "Obstructions.table.R19") : S4 := h.1

@[sa_forward "Obstructions.table.R19" 5]
theorem fwd5 (h : sa_impl% "Obstructions.table.R19") : S5 := h.2 .configurationModel

sa_fail_backward "Obstructions.table.R19" "SHADOW?: the impl's second conjunct is ∀ net, ebcmExists net .generalNonMarkov .uniform (every network), but the shadow set requires existence only on the configuration model (S5). The row text 'Non-Markovian: ODE fails, PDE EBCM works (exact)' does not fix the network. The blind author's own reading of the same passage for R19b ('Non-Markovian + uniform: an EBCM exists', network left free) requires every network. The ∀-conjunct cannot be derived from S5 except by re-using the configuration-model proof at other networks, which works only because ebcmExists ignores its network argument."

end Alignment.Shadows.Obstructions.table_R19

/-! ## `Obstructions.table.R20` -/
namespace Alignment.Shadows.Obstructions.table_R20

sa_claim "Obstructions.table.R20" group "Obstructions" required
  text "| 20 | Localised initials: genuine obstruction (all variants) |"
  impl localised_genuine_obstruction localised_impossible

@[sa_forward "Obstructions.table.R20" 1]
theorem fwd1 (h : sa_impl% "Obstructions.table.R20") : S1 := h.1

@[sa_forward "Obstructions.table.R20" 2]
theorem fwd2 (h : sa_impl% "Obstructions.table.R20") : S2 := h.2

/-- Standard validity includes `init = .uniform`, which is `ebcmExists n t .localised` by
definition; `h.1` refutes it. -/
@[sa_forward "Obstructions.table.R20" 3]
theorem fwd3 (h : sa_impl% "Obstructions.table.R20") : S3 :=
  fun n t hv => h.1 n t hv.2.2

@[sa_backward "Obstructions.table.R20"]
theorem bwd (s1 : S1) (s2 : S2) (_s3 : S3) : sa_impl% "Obstructions.table.R20" :=
  ⟨s1, s2⟩

end Alignment.Shadows.Obstructions.table_R20

/-! ## `Obstructions.table.R21` -/
namespace Alignment.Shadows.Obstructions.table_R21

sa_claim "Obstructions.table.R21" group "Obstructions" required
  text "| 21 | Degree correlations: multi-type EBCM works (ODE) |"
  impl degreeCorr_ebcm_exists

@[sa_forward "Obstructions.table.R21" 1]
theorem fwd1 (h : sa_impl% "Obstructions.table.R21") : S1 := h

sa_fail_forward "Obstructions.table.R21" 2 "impl degreeCorr_ebcm_exists says only ebcmExists .degreeCorrelated .markovian .uniform. It says nothing about extensionDim, so '(ODE)' as a finite positive dimension (0 < extensionDim .degreeCorrelated .markovian) is not stated."
sa_fail_forward "Obstructions.table.R21" 3 "impl says nothing about systemRequired. systemRequired .markovian .uniform = .ode is the supporting theorem markov_is_ode, which is not in the impl list."

@[sa_backward "Obstructions.table.R21"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) : sa_impl% "Obstructions.table.R21" := s1

end Alignment.Shadows.Obstructions.table_R21

/-! ## table.R22 (`a > b` unfolds to `b < a`) -/
namespace Alignment.Shadows.Obstructions.table_R22

sa_claim "Obstructions.table.R22" group "Obstructions" required
  text "| 22 | Hard-coded counts: clustered (13) > 3·standard (4) − 1 |"
  impl clustering_dimension_cost standard_most_compact

sa_fail_forward "Obstructions.table.R22" 1 "S1 (extensionDim .clusteredTriangles .markovian = 13) is a clause of the table extensionDim (rfl). impl (clustering_dimension_cost ∧ standard_most_compact) states only inequalities, so a checker could only prove S1 without h (vacuous)."

sa_fail_forward "Obstructions.table.R22" 2 "S2 (extensionDim .configurationModel .markovian = 4) is a clause of the table (rfl). impl states only inequalities, so a checker could only prove S2 without h (vacuous)."

@[sa_forward "Obstructions.table.R22" 3]
theorem fwd3 (h : sa_impl% "Obstructions.table.R22") : S3 := h.1

sa_fail_backward "Obstructions.table.R22" "impl's second conjunct standard_most_compact (∀ net, extensionDim .configurationModel .markovian ≤ extensionDim net .markovian: the standard EBCM has the fewest variables of all classes) is not in the row and not in any shadow. The shadows give only the two counts and the comparison clustered > 3·standard − 1, so impl is stronger than the row."

end Alignment.Shadows.Obstructions.table_R22

/-! ## table.R23 (the three conjuncts of `system_classification` are instantiated at each tabulated
case; the backward checker substitutes the case equations and uses the shadow for each case) -/
namespace Alignment.Shadows.Obstructions.table_R23

sa_claim "Obstructions.table.R23" group "Obstructions" required
  text "| 23 | `systemRequired` is ODE, PDE or impossible as tabulated |"
  impl system_classification

@[sa_forward "Obstructions.table.R23" 1]
theorem fwd1 (h : sa_impl% "Obstructions.table.R23") : S1 :=
  (h .markovian .uniform).1 ⟨rfl, Or.inl rfl⟩

@[sa_forward "Obstructions.table.R23" 2]
theorem fwd2 (h : sa_impl% "Obstructions.table.R23") : S2 :=
  (h .erlangStaged .uniform).1 ⟨rfl, Or.inr rfl⟩

@[sa_forward "Obstructions.table.R23" 3]
theorem fwd3 (h : sa_impl% "Obstructions.table.R23") : S3 :=
  (h .generalNonMarkov .uniform).2.1 ⟨rfl, rfl⟩

@[sa_forward "Obstructions.table.R23" 4]
theorem fwd4 (h : sa_impl% "Obstructions.table.R23") : S4 := fun t => (h t .localised).2.2 rfl

@[sa_backward "Obstructions.table.R23"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : sa_impl% "Obstructions.table.R23" := by
  intro trans init
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨rfl, rfl | rfl⟩
    · exact s1
    · exact s2
  · rintro ⟨rfl, rfl⟩
    exact s3
  · rintro rfl
    exact s4 trans

end Alignment.Shadows.Obstructions.table_R23

/-! ## `Obstructions.R17` -/
namespace Alignment.Shadows.Obstructions.R17

sa_claim "Obstructions.R17" group "Obstructions" required
  text "**Result 17.** The standard EBCM is valid under all correct assumptions."
  impl standard_ebcm_valid

@[sa_forward "Obstructions.R17" 1]
theorem fwd1 (h : sa_impl% "Obstructions.R17") : S1 := h

@[sa_backward "Obstructions.R17"]
theorem bwd (s1 : S1) : sa_impl% "Obstructions.R17" := s1

end Alignment.Shadows.Obstructions.R17

/-! ## `Obstructions.R18a` -/
namespace Alignment.Shadows.Obstructions.R18a

sa_claim "Obstructions.R18a" group "Obstructions" required
  text "**Result 18.** Clustering breaks the *standard* EBCM,"
  impl clustering_breaks_standard

@[sa_forward "Obstructions.R18a" 1]
theorem fwd1 (h : sa_impl% "Obstructions.R18a") : S1 := h

/-- Validity at any `(t, i)` gives `clusteredTriangles = configurationModel`, hence validity at
`(markovian, uniform)`, which `h` refutes. -/
@[sa_forward "Obstructions.R18a" 2]
theorem fwd2 (h : sa_impl% "Obstructions.R18a") : S2 := by
  intro t i hv
  exact h ⟨hv.1, rfl, rfl⟩

@[sa_backward "Obstructions.R18a"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "Obstructions.R18a" := s1

end Alignment.Shadows.Obstructions.R18a

/-! ## `Obstructions.R18b` -/
namespace Alignment.Shadows.Obstructions.R18b

sa_claim "Obstructions.R18b" group "Obstructions" required
  text "but NOT the EBCM framework. [...] But an EBCM variant exists for clustered networks."
  impl clustering_ebcm_exists

@[sa_forward "Obstructions.R18b" 1]
theorem fwd1 (h : sa_impl% "Obstructions.R18b") : S1 := h

@[sa_backward "Obstructions.R18b"]
theorem bwd (s1 : S1) : sa_impl% "Obstructions.R18b" := s1

end Alignment.Shadows.Obstructions.R18b

/-! ## `Obstructions.R18c` -/
namespace Alignment.Shadows.Obstructions.R18c

sa_claim "Obstructions.R18c" group "Obstructions" required
  text "The triangle EBCM handles it with more variables."
  impl clustering_dimension_cost

sa_fail_forward "Obstructions.R18c" 1 "impl clustering_dimension_cost only compares extensionDim values. 'handles it' (ebcmExists .clusteredTriangles .markovian .uniform) is not stated, because clustering_ebcm_exists is not in the impl list."
sa_fail_forward "Obstructions.R18c" 2 "impl states extensionDim .clusteredTriangles .markovian > 3·extensionDim .configurationModel .markovian − 1 (truncated ℕ subtraction). That is a different inequality from S2, extensionDim .configurationModel .markovian < extensionDim .clusteredTriangles .markovian. S2 follows only by ℕ arithmetic (d ≤ 3d − 1, then transitivity: Nat.lt_of_le_of_lt / Nat.le constructors), which structural proofs cannot use, and no bridge on a trusted definition can carry an order lemma. Logically the impl is stronger here, so this failure is an audit limitation for this shadow."
sa_fail_backward "Obstructions.R18c" "impl's ~3× bound (extensionDim .clusteredTriangles .markovian > 3·extensionDim .configurationModel .markovian − 1) is stronger than 'more variables'. S1 ∧ S2 hold with dimensions 4 < 5, which violate 5 > 11. The impl states Result 22's ~3× cost, not this sentence's 'more variables'."

end Alignment.Shadows.Obstructions.R18c

/-! ## `Obstructions.R21a` -/
namespace Alignment.Shadows.Obstructions.R21a

sa_claim "Obstructions.R21a" group "Obstructions" required
  text "**Result 21.** Degree correlations break the standard EBCM,"
  impl degreeCorr_breaks_standard

@[sa_forward "Obstructions.R21a" 1]
theorem fwd1 (h : sa_impl% "Obstructions.R21a") : S1 := h

/-- Validity at any `(t, i)` gives `degreeCorrelated = configurationModel`, hence validity at
`(markovian, uniform)`, which `h` refutes. -/
@[sa_forward "Obstructions.R21a" 2]
theorem fwd2 (h : sa_impl% "Obstructions.R21a") : S2 := by
  intro t i hv
  exact h ⟨hv.1, rfl, rfl⟩

@[sa_backward "Obstructions.R21a"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "Obstructions.R21a" := s1

end Alignment.Shadows.Obstructions.R21a

/-! ## `Obstructions.R21b` -/
namespace Alignment.Shadows.Obstructions.R21b

sa_claim "Obstructions.R21b" group "Obstructions" required
  text "**Degree correlations**: Multi-type EBCM of Miller & Volz (2013) with mixing matrix. Still an ODE system. [...] but multi-type EBCM handles them."
  impl degreeCorr_ebcm_exists

@[sa_forward "Obstructions.R21b" 1]
theorem fwd1 (h : sa_impl% "Obstructions.R21b") : S1 := h

sa_fail_forward "Obstructions.R21b" 2 "impl degreeCorr_ebcm_exists states only ebcmExists .degreeCorrelated .markovian .uniform. 'Still an ODE system', read as 0 < extensionDim .degreeCorrelated .markovian, is not stated (the impl says nothing about extensionDim)."
sa_fail_forward "Obstructions.R21b" 3 "impl says nothing about systemRequired. 'Still an ODE system', read as systemRequired .markovian .uniform = .ode, is the supporting theorem markov_is_ode, which is not in the impl list (registry: 'multi-type', 'mixing matrix' and 'ODE' are not formalised for this network type)."

@[sa_backward "Obstructions.R21b"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) : sa_impl% "Obstructions.R21b" := s1

end Alignment.Shadows.Obstructions.R21b

/-! ## `Obstructions.R19a` -/
namespace Alignment.Shadows.Obstructions.R19a

sa_claim "Obstructions.R19a" group "Obstructions" required
  text "The system becomes a **PDE** (von Foerster age-structured equation) rather than an ODE, with infinite-dimensional state space. [...] **Result 19.** Non-Markovian dynamics change the system type from ODE to PDE,"
  impl nonmarkov_requires_pde

@[sa_forward "Obstructions.R19a" 1]
theorem fwd1 (h : sa_impl% "Obstructions.R19a") : S1 := h

sa_fail_forward "Obstructions.R19a" 2 "impl nonmarkov_requires_pde states only systemRequired .generalNonMarkov .uniform = .pde. The 'from ODE' baseline, systemRequired .markovian .uniform = .ode, is markov_is_ode, which is not in the impl list (registry: 'Change from ODE' is not stated)."
sa_fail_forward "Obstructions.R19a" 3 "impl says nothing about extensionDim. 'infinite-dimensional state space', read as the PDE sentinel extensionDim n .generalNonMarkov = 0 on every network, is not stated (registry: 'infinite-dimensional' is not stated)."

@[sa_backward "Obstructions.R19a"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) : sa_impl% "Obstructions.R19a" := s1

end Alignment.Shadows.Obstructions.R19a

/-! ## `Obstructions.R19b` -/
namespace Alignment.Shadows.Obstructions.R19b

sa_claim "Obstructions.R19b" group "Obstructions" required
  text "Changes the *type* of system, not an absolute obstruction: [...] but the EBCM framework still works exactly. [...] Non-Markovian + uniform: an EBCM exists (as a PDE system)."
  impl nonmarkov_ebcm_exists

@[sa_forward "Obstructions.R19b" 1]
theorem fwd1 (h : sa_impl% "Obstructions.R19b") : S1 := h .configurationModel

@[sa_forward "Obstructions.R19b" 2]
theorem fwd2 (h : sa_impl% "Obstructions.R19b") : S2 := h

sa_fail_forward "Obstructions.R19b" 3 "impl nonmarkov_ebcm_exists states only ebcmExists net .generalNonMarkov .uniform. 'as a PDE system' (systemRequired .generalNonMarkov .uniform = .pde) is the supporting theorem nonmarkov_requires_pde, which is not in the impl list."
sa_fail_forward "Obstructions.R19b" 4 "impl says nothing about systemRequired. 'Changes the type of system' (systemRequired .generalNonMarkov .uniform ≠ systemRequired .markovian .uniform) is not stated."

@[sa_backward "Obstructions.R19b"]
theorem bwd (_s1 : S1) (s2 : S2) (_s3 : S3) (_s4 : S4) : sa_impl% "Obstructions.R19b" := s2

end Alignment.Shadows.Obstructions.R19b

/-! ## `Obstructions.erlangIsOde` -/
namespace Alignment.Shadows.Obstructions.erlangIsOde

sa_claim "Obstructions.erlangIsOde" group "Obstructions" required
  text "The Erlang-staged approximation recovers an ODE system."
  impl erlang_is_ode

@[sa_forward "Obstructions.erlangIsOde" 1]
theorem fwd1 (h : sa_impl% "Obstructions.erlangIsOde") : S1 := h

sa_fail_forward "Obstructions.erlangIsOde" 2 "impl erlang_is_ode states only systemRequired .erlangStaged .uniform = .ode. It says nothing about extensionDim, so 0 < extensionDim n .erlangStaged on every network (a hard-coded table fact) is not stated."

@[sa_backward "Obstructions.erlangIsOde"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "Obstructions.erlangIsOde" := s1

end Alignment.Shadows.Obstructions.erlangIsOde

/-! ## markovIsOde -/
namespace Alignment.Shadows.Obstructions.markovIsOde

sa_claim "Obstructions.markovIsOde" group "Obstructions" required
  text "Markovian dynamics with uniform initial infection give an ODE system."
  impl markov_is_ode

@[sa_forward "Obstructions.markovIsOde" 1]
theorem fwd1 (h : sa_impl% "Obstructions.markovIsOde") : S1 := h

@[sa_backward "Obstructions.markovIsOde"]
theorem bwd (s1 : S1) : sa_impl% "Obstructions.markovIsOde" := s1

end Alignment.Shadows.Obstructions.markovIsOde

/-! ## R20a -/
namespace Alignment.Shadows.Obstructions.R20a

sa_claim "Obstructions.R20a" group "Obstructions" required
  text "Localised initial conditions (assumption 3) Among the three standard assumptions, only localised seeding has no EBCM variant. [...] **Result 20.** Among the three standard assumptions, only localised seeding has no EBCM variant."
  impl localised_genuine_obstruction

@[sa_forward "Obstructions.R20a" 1]
theorem fwd1 (h : sa_impl% "Obstructions.R20a") : S1 := fun n t => h n t

sa_fail_forward "Obstructions.R20a" 2 "S2 (every network and transition type has an EBCM variant under uniform seeding) holds by the definition of ebcmExists (it is .uniform = .uniform, rfl). impl localised_genuine_obstruction states only the localised case, so a checker could only prove S2 without h (vacuous)."

@[sa_backward "Obstructions.R20a"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "Obstructions.R20a" := fun n t => s1 n t

end Alignment.Shadows.Obstructions.R20a

/-! ## `Obstructions.R20b` -/
namespace Alignment.Shadows.Obstructions.R20b

sa_claim "Obstructions.R20b" group "Obstructions" required
  text "They break ALL EBCM variants (ODE and PDE alike)"
  impl localised_genuine_obstruction localised_impossible

@[sa_forward "Obstructions.R20b" 1]
theorem fwd1 (h : sa_impl% "Obstructions.R20b") : S1 := h.1

@[sa_forward "Obstructions.R20b" 2]
theorem fwd2 (h : sa_impl% "Obstructions.R20b") : S2 :=
  fun n t hv => h.1 n t hv.2.2

/-- `h.2 t` says the system type is `impossible`, and `impossible ≠ ode`. -/
@[sa_forward "Obstructions.R20b" 3]
theorem fwd3 (h : sa_impl% "Obstructions.R20b") : S3 :=
  fun t he => SystemType.noConfusion ((h.2 t).symm.trans he)

/-- `h.2 t` says the system type is `impossible`, and `impossible ≠ pde`. -/
@[sa_forward "Obstructions.R20b" 4]
theorem fwd4 (h : sa_impl% "Obstructions.R20b") : S4 :=
  fun t he => SystemType.noConfusion ((h.2 t).symm.trans he)

/-- The second conjunct follows from S3 and S4 by exhaustiveness of `SystemType`. -/
@[sa_backward "Obstructions.R20b"]
theorem bwd (s1 : S1) (_s2 : S2) (s3 : S3) (s4 : S4) : sa_impl% "Obstructions.R20b" :=
  ⟨s1, fun t => match hs : systemRequired t .localised with
    | .ode => absurd hs (s3 t)
    | .pde => absurd hs (s4 t)
    | .impossible => rfl⟩

end Alignment.Shadows.Obstructions.R20b

/-! ## R22a -/
namespace Alignment.Shadows.Obstructions.R22a

sa_claim "Obstructions.R22a" group "Obstructions" required
  text "**Result 22.** In the hard-coded table `extensionDim`, the triangle-clustered EBCM has 13 variables, more than 3·4 − 1 for the standard EBCM."
  impl clustering_dimension_cost

sa_fail_forward "Obstructions.R22a" 1 "S1 (the table gives 13 variables for the triangle-clustered EBCM) is a clause of extensionDim (rfl). impl clustering_dimension_cost states only the inequality, so a checker could only prove S1 without h (vacuous)."

sa_fail_forward "Obstructions.R22a" 2 "S2 (the table gives 4 variables for the standard EBCM) is a clause of extensionDim (rfl). impl states only the inequality, so a checker could only prove S2 without h (vacuous)."

@[sa_forward "Obstructions.R22a" 3]
theorem fwd3 (h : sa_impl% "Obstructions.R22a") : S3 := h

@[sa_backward "Obstructions.R22a"]
theorem bwd (_s1 : S1) (_s2 : S2) (s3 : S3) : sa_impl% "Obstructions.R22a" := s3

end Alignment.Shadows.Obstructions.R22a

/-! ## `Obstructions.standardMostCompact` -/
namespace Alignment.Shadows.Obstructions.standardMostCompact

sa_claim "Obstructions.standardMostCompact" group "Obstructions" required
  text "The standard EBCM is the most compact ODE variant."
  impl standard_most_compact

sa_fail_forward "Obstructions.standardMostCompact" 1 "impl standard_most_compact states only extensionDim .configurationModel .markovian ≤ extensionDim net .markovian. It does not state that the standard EBCM is an ODE variant (0 < extensionDim .configurationModel .markovian)."
sa_fail_forward "Obstructions.standardMostCompact" 2 "impl compares only Markovian variants (∀ net, … ≤ extensionDim net .markovian). S2 quantifies over every ODE variant (n, t), including the erlangStaged ones, which the impl does not cover. They are larger in the table (6/15/12/22 ≥ 4), but this is not stated (registry: Erlang-staged ODE variants are not quantified over)."
sa_fail_forward "Obstructions.standardMostCompact" 3 "impl states only ≤, not strictly fewer, and only over Markovian variants. S3 (the unique minimum: every other ODE variant, including erlangStaged, is strictly larger) is not stated."
sa_fail_backward "Obstructions.standardMostCompact" "impl is unconditional over Markovian networks (extensionDim .configurationModel .markovian ≤ extensionDim net .markovian for every net), whereas the shadows compare only ODE variants (hypothesis 0 < extensionDim n t). Deriving the impl from S2 needs 0 < extensionDim net .markovian for every net, which the shadow set does not state (S1 covers only the configuration model). For example, a table with extensionDim .degreeCorrelated .markovian = 0 satisfies S1–S3 but not the impl."

end Alignment.Shadows.Obstructions.standardMostCompact

/-! ## `Obstructions.R24a` -/
namespace Alignment.Shadows.Obstructions.R24a

sa_claim "Obstructions.R24a" group "Obstructions" required
  text "**Result 24.** The Erlang approximation turns the PDE into an ODE at the cost of extra variables."
  impl erlang_costs_more erlang_is_ode

@[sa_forward "Obstructions.R24a" 1]
theorem fwd1 (h : sa_impl% "Obstructions.R24a") : S1 := h.2

sa_fail_forward "Obstructions.R24a" 2 "impl (erlang_costs_more ∧ erlang_is_ode) does not state the presupposition 'the PDE' (systemRequired .generalNonMarkov .uniform = .pde). That is nonmarkov_requires_pde, which is not in the impl list (registry: no PDE → ODE approximation is formalised)."
sa_fail_forward "Obstructions.R24a" 3 "impl erlang_costs_more states only ≤ (extensionDim net .markovian ≤ extensionDim net .erlangStaged). 'at the cost of extra variables' requires strict < on every network."
sa_fail_backward "Obstructions.R24a" "Not structurally derivable, although logically implied. S3 gives extensionDim n .markovian < extensionDim n .erlangStaged, and the impl's first conjunct needs ≤. The step < ⇒ ≤ on ℕ is Nat.le_of_lt (or Nat.le.step), which the structural rule forbids, and no bridge on a trusted definition can carry an order lemma. S1 gives the second conjunct. The impl is weaker than the shadows here, so this backward failure is an audit limitation, not an over-strong impl."

end Alignment.Shadows.Obstructions.R24a

/-! ## `Obstructions.R24c` -/
namespace Alignment.Shadows.Obstructions.R24c

sa_claim "Obstructions.R24c" group "Obstructions" required
  text "Here we show the Erlang variant always needs more variables than the Markovian variant on the same network."
  impl erlang_costs_more

sa_fail_forward "Obstructions.R24c" 1 "impl erlang_costs_more states ≤ (extensionDim net .markovian ≤ extensionDim net .erlangStaged), but the text 'always needs more variables' requires strict <. The registry notes the same."
sa_fail_backward "Obstructions.R24c" "Not structurally derivable, although logically implied. S1 (<) implies the impl (≤) only through Nat.le_of_lt (or Nat.le.step), which the structural rule forbids, and no bridge on a trusted definition can carry an order lemma. The impl is weaker than the shadow, so this backward failure is an audit limitation, not an over-strong impl."

end Alignment.Shadows.Obstructions.R24c

/-! ## `Obstructions.R23a` -/
namespace Alignment.Shadows.Obstructions.R23a

sa_claim "Obstructions.R23a" group "Obstructions" required
  text "**Result 23.** Complete classification of what system type is needed."
  impl system_classification

@[sa_forward "Obstructions.R23a" 1]
theorem fwd1 (h : sa_impl% "Obstructions.R23a") : S1 :=
  (h .markovian .uniform).1 ⟨rfl, Or.inl rfl⟩

@[sa_forward "Obstructions.R23a" 2]
theorem fwd2 (h : sa_impl% "Obstructions.R23a") : S2 :=
  (h .erlangStaged .uniform).1 ⟨rfl, Or.inr rfl⟩

@[sa_forward "Obstructions.R23a" 3]
theorem fwd3 (h : sa_impl% "Obstructions.R23a") : S3 :=
  (h .generalNonMarkov .uniform).2.1 ⟨rfl, rfl⟩

@[sa_forward "Obstructions.R23a" 4]
theorem fwd4 (h : sa_impl% "Obstructions.R23a") : S4 :=
  fun t => (h t .localised).2.2 rfl

@[sa_backward "Obstructions.R23a"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : sa_impl% "Obstructions.R23a" := by
  intro trans init
  refine ⟨?_, ?_, ?_⟩
  · intro hx
    obtain ⟨hi, ht⟩ := hx
    subst hi
    cases ht with
    | inl ht => subst ht; exact s1
    | inr ht => subst ht; exact s2
  · intro hx
    obtain ⟨hi, ht⟩ := hx
    subst hi
    subst ht
    exact s3
  · intro hi
    subst hi
    exact s4 trans

end Alignment.Shadows.Obstructions.R23a

/-! ## `Obstructions.R23b` -/
namespace Alignment.Shadows.Obstructions.R23b

sa_claim "Obstructions.R23b" group "Obstructions" required
  text "Uniform + Markovian/Erlang → ODE (always works)"
  impl system_classification

@[sa_forward "Obstructions.R23b" 1]
theorem fwd1 (h : sa_impl% "Obstructions.R23b") : S1 :=
  (h .markovian .uniform).1 ⟨rfl, Or.inl rfl⟩

@[sa_forward "Obstructions.R23b" 2]
theorem fwd2 (h : sa_impl% "Obstructions.R23b") : S2 :=
  (h .erlangStaged .uniform).1 ⟨rfl, Or.inr rfl⟩

sa_fail_forward "Obstructions.R23b" 3 "impl system_classification is only about systemRequired. 'always works' (∀ n, ebcmExists n .markovian .uniform) is not stated, because ebcmExists does not occur in the impl (registry: '(always works)' is not formalised)."
sa_fail_forward "Obstructions.R23b" 4 "impl system_classification is only about systemRequired. 'always works' (∀ n, ebcmExists n .erlangStaged .uniform) is not stated, because ebcmExists does not occur in the impl."
sa_fail_backward "Obstructions.R23b" "impl system_classification also states the other two rows of the table for every trans: uniform ∧ generalNonMarkov → pde, and localised → impossible. The R23b shadow set (the Markovian/Erlang row only) does not imply them. The single impl covers the whole Result 23 table, so it is stronger than this row."

end Alignment.Shadows.Obstructions.R23b

/-! ## `Obstructions.R23c` -/
namespace Alignment.Shadows.Obstructions.R23c

sa_claim "Obstructions.R23c" group "Obstructions" required
  text "Uniform + general non-Markov → PDE (always works, infinite-dim)"
  impl system_classification

@[sa_forward "Obstructions.R23c" 1]
theorem fwd1 (h : sa_impl% "Obstructions.R23c") : S1 :=
  (h .generalNonMarkov .uniform).2.1 ⟨rfl, rfl⟩

sa_fail_forward "Obstructions.R23c" 2 "impl system_classification is only about systemRequired. 'always works' (∀ n, ebcmExists n .generalNonMarkov .uniform) is not stated, because ebcmExists does not occur in the impl."
sa_fail_forward "Obstructions.R23c" 3 "impl says nothing about extensionDim. 'infinite-dim' (the PDE sentinel extensionDim n .generalNonMarkov = 0) is not stated (registry: 'infinite-dim' is not formalised)."
sa_fail_backward "Obstructions.R23c" "impl system_classification also states the rows uniform ∧ (markovian ∨ erlangStaged) → ode and localised → impossible, which the R23c shadow set does not imply. The single impl covers the whole Result 23 table, so it is stronger than this row."

end Alignment.Shadows.Obstructions.R23c

/-! ## R23d

The backward checker uses S1 for the localised conjunct of `system_classification`. The two
uniform conjuncts, which this fragment of the text does not mention, hold by computation of
`systemRequired` (a match on plain data) after substituting the case equations, so the backward
pass is weak evidence for them. -/
namespace Alignment.Shadows.Obstructions.R23d

sa_claim "Obstructions.R23d" group "Obstructions" required
  text "Localised → impossible (by definition of `systemRequired`)"
  impl system_classification

@[sa_forward "Obstructions.R23d" 1]
theorem fwd1 (h : sa_impl% "Obstructions.R23d") : S1 := fun t => (h t .localised).2.2 rfl

@[sa_backward "Obstructions.R23d"]
theorem bwd (s1 : S1) : sa_impl% "Obstructions.R23d" := by
  intro trans init
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨rfl, rfl | rfl⟩
    · rfl
    · rfl
  · rintro ⟨rfl, rfl⟩
    rfl
  · rintro rfl
    exact s1 trans

end Alignment.Shadows.Obstructions.R23d

/-! ## header.kirkwoodHierarchyInconsistent -/
namespace Alignment.Shadows.Obstructions.header_kirkwoodHierarchyInconsistent

sa_claim "Obstructions.header.kirkwoodHierarchyInconsistent" group "Obstructions" required
  text "For a two-variable surrogate of a closed order-4 moment system and a one-variable surrogate of a closed order-3 system (defined below), the closed dynamics do **not** project consistently under the surrogate marginalisation `M(a,b) = a + b`. [...] does **not** commute at the witness state."
  impl MarginalisationObstruction.kirkwood_marginalisation_obstruction

sa_fail_forward "Obstructions.header.kirkwoodHierarchyInconsistent" 1 "S1 (the surrogate marginalisation is M(a, b) = a + b) is the definition of M_witness (rfl). impl kirkwood_marginalisation_obstruction states only the existence of a non-commuting state, so a checker could only prove S1 without h (vacuous)."

@[sa_forward "Obstructions.header.kirkwoodHierarchyInconsistent" 2]
theorem fwd2 (h : sa_impl% "Obstructions.header.kirkwoodHierarchyInconsistent") : S2 := h

sa_fail_forward "Obstructions.header.kirkwoodHierarchyInconsistent" 3 "impl is existential (∃ u, M(F₄ u) ≠ F₃(M u)); the witness state (1, 3) appears only in its proof. S3 (the diagram does not commute at the named state (1, 3)) does not follow from the existential."

@[sa_backward "Obstructions.header.kirkwoodHierarchyInconsistent"]
theorem bwd (_s1 : S1) (s2 : S2) (_s3 : S3) :
    sa_impl% "Obstructions.header.kirkwoodHierarchyInconsistent" := s2

end Alignment.Shadows.Obstructions.header_kirkwoodHierarchyInconsistent

/-! ## `Obstructions.R25a` -/
namespace Alignment.Shadows.Obstructions.R25a

open MarginalisationObstruction

sa_claim "Obstructions.R25a" group "Obstructions" required
  text "**Result 25 — Theorem T2 (Marginalisation obstruction).** There exists a state at which `M ∘ F₄_Kirkwood ≠ F₃_Kirkwood ∘ M`."
  impl MarginalisationObstruction.kirkwood_marginalisation_obstruction

@[sa_forward "Obstructions.R25a" 1]
theorem fwd1 (h : sa_impl% "Obstructions.R25a") : S1 := h

@[sa_backward "Obstructions.R25a"]
theorem bwd (s1 : S1) : sa_impl% "Obstructions.R25a" := s1

end Alignment.Shadows.Obstructions.R25a

/-! ## `Obstructions.R25b` -/
namespace Alignment.Shadows.Obstructions.R25b

open MarginalisationObstruction

sa_claim "Obstructions.R25b" group "Obstructions" required
  text "Witness: `u = (a ↦ 1, b ↦ 3)`. * `M (F₄_Kirkwood u) (c) = 1·3 + 3 = 6`. * `F₃_Kirkwood (M u) (c) = (1+3)² / 4 = 4`. The diagram fails by `6 ≠ 4`."
  impl MarginalisationObstruction.kirkwood_obstruction_witness_value

sa_fail_forward "Obstructions.R25b" 1 "impl kirkwood_obstruction_witness_value states only the difference M_witness (F4_Kirkwood u) c − F3_Kirkwood (M_witness u) c = 2 at the witness. The individual value M (F₄ u)(c) = 6 is not stated, since a difference does not determine its terms. The registry notes the same."
sa_fail_forward "Obstructions.R25b" 2 "impl kirkwood_obstruction_witness_value states only the difference LHS − RHS = 2 at the witness. The individual value F₃ (M u)(c) = 4 is not stated, since a difference does not determine its terms. The registry notes the same."

/-- If the two composites agreed at the witness, the impl's difference would be `X − X = 0`
(closed ℚ computation), contradicting the impl's value `2` (compared through `Rat.num`). -/
@[sa_forward "Obstructions.R25b" 3]
theorem fwd3 (h : sa_impl% "Obstructions.R25b") : S3 := by
  intro u ha hb heq
  have hc := congrArg (fun f => f Idx3.c) heq
  change u .a * u .b + u .b = (u .a + u .b) ^ 2 / 4 at hc
  rw [ha, hb] at hc
  change (1 : ℚ) * 3 + 3 - (1 + 3) ^ 2 / 4 = 2 at h
  rw [hc] at h
  have h0 : Int.ofNat 0 = Int.ofNat 2 := by with_unfolding_all exact congrArg Rat.num h
  exact Int.noConfusion h0 (fun hn => Nat.noConfusion hn)

/-- The impl's difference is `6 − 4` by S1 and S2 (closed ℚ arithmetic). -/
@[sa_backward "Obstructions.R25b"]
theorem bwd (s1 : S1) (s2 : S2) (_s3 : S3) : sa_impl% "Obstructions.R25b" := by
  intro u
  rw [s1 u rfl rfl, s2 u rfl rfl]
  with_unfolding_all rfl

end Alignment.Shadows.Obstructions.R25b

/-! ## `Obstructions.kirkwoodObstructionWitnessValue-a` -/
namespace Alignment.Shadows.Obstructions.kirkwoodObstructionWitnessValue_a

open MarginalisationObstruction

sa_claim "Obstructions.kirkwoodObstructionWitnessValue-a" group "Obstructions" required
  text "The witness explicitly evaluated: the LHS minus the RHS is a fixed nonzero rational."
  impl MarginalisationObstruction.kirkwood_obstruction_witness_value

/-- A zero difference at the witness would contradict the impl's value `2`
(compared through `Rat.num`). -/
@[sa_forward "Obstructions.kirkwoodObstructionWitnessValue-a" 1]
theorem fwd1 (h : sa_impl% "Obstructions.kirkwoodObstructionWitnessValue-a") : S1 := by
  intro u ha hb h0
  change u .a * u .b + u .b - (u .a + u .b) ^ 2 / 4 = 0 at h0
  rw [ha, hb] at h0
  change (1 : ℚ) * 3 + 3 - (1 + 3) ^ 2 / 4 = 2 at h
  have e : (0 : ℚ) = 2 := h0.symm.trans h
  have e0 : Int.ofNat 0 = Int.ofNat 2 := by with_unfolding_all exact congrArg Rat.num e
  exact Int.noConfusion e0 (fun hn => Nat.noConfusion hn)

/-- Any state with the witness values has the impl's difference `2`. -/
@[sa_forward "Obstructions.kirkwoodObstructionWitnessValue-a" 2]
theorem fwd2 (h : sa_impl% "Obstructions.kirkwoodObstructionWitnessValue-a") : S2 := by
  intro u ha hb
  show u .a * u .b + u .b - (u .a + u .b) ^ 2 / 4 = 2
  rw [ha, hb]
  exact h

@[sa_backward "Obstructions.kirkwoodObstructionWitnessValue-a"]
theorem bwd (_s1 : S1) (s2 : S2) : sa_impl% "Obstructions.kirkwoodObstructionWitnessValue-a" := by
  intro u
  exact s2 u rfl rfl

end Alignment.Shadows.Obstructions.kirkwoodObstructionWitnessValue_a

/-! ## `Obstructions.R24b` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.Obstructions.R24b

sa_claim "Obstructions.R24b" group "Obstructions"
  text "The ODE approximation via n-stage Erlang needs 2n + 2 variables in the counting convention of `extensionDim` (θ, n edge stages φ_{I_j}, n node stages I_j, and R): 4 for n = 1 and 6 for n = 2. [...] For an n-stage Erlang infectious period on a configuration model, the standard 4 variables become 2n + 2 (θ, n edge stages φ_{I_j}, n node stages I_j, and R)."
  impl

end Alignment.Shadows.Obstructions.R24b

/-! ## `Obstructions.header.T1ImpliesTrajectoryFailure` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.Obstructions.header_T1ImpliesTrajectoryFailure

sa_claim "Obstructions.header.T1ImpliesTrajectoryFailure" group "Obstructions"
  text "Theorem T1 (`dynamic_marginalisation_iff_equivariance` in `MarginalisationFunctor.lean`) needs global flows of both systems, and the order-3 surrogate `c ↦ c²/4` has none (`no_flow_F3Kℝ`), so T1 does not apply to this witness. The local statement does hold: for any local solutions of the two surrogate systems from `u` and `M u`, `M · u₄(t) ≠ u₃(t)` for all small `t > 0` (`MarginalisationDynamicalGap.witness_localGap_ge`). [...] T1 does not apply here (the order-3 field has no global flow); the local consequence, `M · u₄(t) ≠ u₃(t)` for small `t > 0`, is `MarginalisationDynamicalGap.witness_localGap_ge`."
  impl

end Alignment.Shadows.Obstructions.header_T1ImpliesTrajectoryFailure

/-! ## `Obstructions.header.smallestFaithfulWitness` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.Obstructions.header_smallestFaithfulWitness

sa_claim "Obstructions.header.smallestFaithfulWitness" group "Obstructions"
  text "This is one arithmetic witness for one pair of surrogate fields, not a general law: with `M = id` a quadratic field commutes with itself, and at the witness state the quadratic field `c ↦ 3c²/8` agrees with `M ∘ F₄` (both give 6; `MarginalisationDynamicalGap.kirkwoodForm_matches_at_witness`)."
  impl

end Alignment.Shadows.Obstructions.header_smallestFaithfulWitness

/-! ## `Obstructions.header.surrogateForms` (registry status `informal`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.Obstructions.header_surrogateForms

sa_claim "Obstructions.header.surrogateForms" group "Obstructions"
  text "The surrogate right-hand sides are chosen, not derived from a closure: `F₄(a,b) = (a·b, b)` is bilinear, as a pair-Kirkwood closure is, and `F₃(c) = c²/4` is quadratic."
  impl

end Alignment.Shadows.Obstructions.header_surrogateForms

/-! ## `Obstructions.table.R24` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.Obstructions.table_R24

sa_claim "Obstructions.table.R24" group "Obstructions"
  text "| 24 | Erlang staging needs more variables than Markovian |"
  impl

end Alignment.Shadows.Obstructions.table_R24
