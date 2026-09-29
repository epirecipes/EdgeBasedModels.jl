# SA-PASS triage of non-passing claims

Legend. **status**: F p/n = forward checks passed / shadows, B ok/x/- = backward pass/fail/missing; miss/inf/axiom = unregistered registry status. **symptom**: FWD forward fail (impl weaker), BWD backward fail (impl stronger or different), F+B both, SHQ SHADOW? only, INC no shadows, VAC vacuous shadow, GAP no theorem, INF informal, AX axiom; digits = failing shadows, ?n = SHADOW? on shadow n. **cause**: CAT no category/functor defined; NOTH no theorem; DEF/META definition/commentary text; FS free-scalar impl (raw ℚ/ℝ, more general than the text); FP free-scalar PGF (ψ,ψ′,ψ″ unrelated numbers); NT no ODE solutions, pointwise signs only; TAU tautological/vacuous impl; DV impl omits facts true by rfl; FIAT lookup-table predicate; LEN List.length comparison; ND no probability distribution; AUD audit limitation only; EX ∃-witness vs ∀ text; HYP extra/unused hypothesis; PART impl covers part of the text; DIFF different notion; SHQ shadow may misread text; VS shadow restates a definition; NOSH no shadows; WD Lean definition differs from the text's notion (a bridge would be rejected); AXF inconsistent axiom; AXT tautological axiom; OTH see report fail record. **fix**: TL add trusted theorem; TLdef change/add trusted definition; DOC docstring in EBCMCategory/&lt;Group&gt;.lean; MD categorical_foundations.md / MARGINALISATION_SPEC.md; RM README/vignettes; AL alignment library; REG claims/&lt;G&gt;.yaml impl list; JL Julia src; AX- delete axiom; SPEC owner question; CITE citation. **text true?**: yes-def (true by definition), yes-alg (elementary algebra), yes-lit (established result, cited paper), yes-math (standard analysis/probability); NO / partly / ill-posed / unverified / depends + reason (full reasons and wording for NO/partly rows are in the plan item). **action**: P1.x/P2.x/P3.x/P4 = remediation plan item (P2.x has the proposed wording); keep, reword, delete, cite, prove TL (effort), SPEC.

**CategoricalComposition** (51)
|id|status|symptom|cause|fix|text true?|action|
|-|-|-|-|-|-|-|
|header.scope|miss|GAP|CAT NOTH|DOC|NO: as a description of..|P2.2|
|R95.functor|miss|GAP|CAT NOTH|DOC|ill-posed: no cat.|P3.1|
|R95a.1|miss|GAP|NOTH|TLdef|yes-lit|P3.1|
|R95b|axiom|AX|AXT|AX-+DOC|ill-posed: no cat.|P1.2 reword|
|R95c|axiom|AX|AXT|AX-+RM+DOC|ill-posed: no cat.|P1.2 reword|
|R96.product|miss|GAP|NOTH|TLdef|yes-alg|P3.6|
|R96b|inf|INF|DEF|DOC|partly: compact system has n+1 ODEs|reword|
|R96c|miss|GAP|NOTH|JL+TL+DOC|NO: non-Poisson layers: ρ(K)≠sum|P2.5|
|R97.coproduct|miss|GAP|CAT NOTH|DOC|NO: coupling is not a coproduct|P2.10|
|R97a.1|inf|INF|DEF|DOC|yes-alg|keep|
|R97a.2|miss|GAP|CAT NOTH|DOC|NO: convex combination≠injection|P2.10|
|R97d.1|F0/1 Bok|FWD 1|TAU|TLdef+DOC|yes-alg|P4|
|R97d.2|miss|GAP|CAT NOTH|DOC|NO: with mixing, not invariant|P2.10|
|R98.natTrans|miss|GAP|CAT NOTH|DOC|ill-posed: no cat.|reword|
|R98.keyProperty|miss|GAP|NOTH|RM+DOC|NO: T_n rises with n|P2.7|
|R98a|F0/2 Bx|F+B 1,2|FS DV AUD|TL|yes-alg|P4|
|R98b.1|F0/1 Bx|F+B 1|OTH|DOC+REG|partly: 'R₀ preservation' false|P2.7|
|R98b.2|miss|GAP|NOTH|DOC|yes-alg|prove TL|
|R98b.3|miss|GAP|CAT NOTH|DOC|ill-posed: no cat.|reword|
|R98c.1|F0/1 Bx|F+B 1|OTH|TL|yes-math|prove TL (low)|
|R98c.2|inf|INF|CAT META PART|DOC|ill-posed: no cat.|delete|
|R98d.1|F0/0 B-|INC|NOSH|TL+AL|yes-lit|P3.3|
|R98d.2|inf|INF|META|DOC|yes-alg|keep|
|R99.natTrans|miss|GAP|CAT NOTH|DOC|ill-posed: no cat.|reword|
|R99a.1|miss|GAP|NOTH|TLdef|yes-alg|prove TL (med)|
|R99a.2|miss|GAP|CAT NOTH|DOC|ill-posed: no cat.|reword|
|R99a.3|F0/1 Bok|SHQ ?1|HYP SHQ|DOC+AL|partly: formula is stub fraction|P2.8|
|R99b.1|F0/1 Bx|F+B 1|OTH|TL|yes-alg|prove TL|
|R99b.2|miss|GAP|NOTH|DOC|NO: triangle term bounded by 2T|P2.8|
|R99c|axiom|AX|AXT|AX-+DOC|ill-posed: no cat.|P1.2 reword|
|R100.monoidal|miss|GAP|CAT NOTH|DOC|ill-posed: no cat.|reword|
|R100.unitObject|miss|GAP|NOTH|DOC|yes-alg|prove TL|
|R100f.1|F0/4 Bok|FWD 1,2 ?3,4|PART SHQ|DOC+AL|ill-posed: undefined category|P4 SHADOW?|
|R100f.2|inf|INF|META|-|yes-alg|keep|
|R101.natTrans|miss|GAP|CAT NOTH|DOC|ill-posed: no cat.|reword|
|R101a|F0/1 Bx|F+B 1|FS HYP PART|TL|yes-alg|P4|
|R101b|F1/1 Bx|BWD|FS|TL|yes-alg|P4|
|R101c|F1/1 Bx|BWD|FS|TL|yes-alg|P4|
|R101d|F1/1 Bx|BWD|FS|TL|yes-alg|P4|
|R101e|F0/1 Bx|F+B 1|FS|DOC|partly: 'naturality' meaningless|reword|
|R102.pullback|miss|GAP|CAT NOTH|DOC|ill-posed: no cat.|reword|
|R102.terminal|miss|GAP|CAT NOTH|DOC|ill-posed: no cat.|reword|
|R102a.1|miss|GAP|NOTH|TL|yes-alg|prove TL|
|R102a.2|miss|GAP|CAT NOTH|DOC|ill-posed: no cat.|delete|
|R102a.3|F0/1 Bx|F+B 1|FS|TL|yes-def|P4|
|R102c.1|miss|GAP|CAT NOTH|DOC|ill-posed: no cat.|delete|
|R102c.2|F4/4 Bx|BWD|FS|TL|yes-alg|P4|
|R102d.1|miss|GAP|CAT NOTH|DOC|partly: rank one true|keep|
|R102d.2|F0/1 Bx|F+B 1|FS HYP|REG|yes-alg|P4|
|R102e.1|F0/2 Bx|F+B 1,2|OTH|TL|yes-alg (with (k−1)Q)|P3.5|
|R102e.2|miss|GAP|NOTH|DOC|NO: off by one (k vs k−1)|P2.6|

**ClosureTheorem** (24)
|id|status|symptom|cause|fix|text true?|action|
|-|-|-|-|-|-|-|
|header.closureExact|miss|GAP|NOTH|TLdef|yes-lit|P3.7|
|header.verificationStrategy|F3/4 Bx|F+B 3|FP DIFF|TL|yes-alg|P3.7|
|header.paperProofCorrect|miss|GAP|NOTH|DOC|unverified: not checked in Lean|P2.2|
|header.sorryFree|inf|INF|META|-|yes-alg|keep|
|table.R52|F0/2 Bx|F+B 1,2|FP DIFF|TL|yes-alg|P3.7|
|table.R53|F0/2 Bx|F+B 1,2|FP DIFF|TL|yes-alg|P3.7|
|table.R54|F0/2 Bx|F+B 1,2|FP DIFF|TL|yes-alg|P3.7|
|table.R55|F0/2 Bx|F+B 1,2|FP DIFF|TL|yes-alg|P3.7|
|table.R56|F0/1 Bx|F+B 1|FP PART DIFF|TL|yes-alg|P3.7|
|table.R57|F1/1 Bx|BWD|OTH|TL|yes-alg|P3.7|
|R52|F1/2 Bx|F+B 2|FP DIFF|TL|yes-alg|P3.7|
|poissonClosureRatio|F1/2 Bx|F+B 2|FP AUD DIFF|TL|yes-alg|P3.7|
|R53|F1/2 Bx|F+B 2|FP DIFF|TL|yes-alg|P3.7|
|binomialClosureRatio|F0/2 Bx|F+B 1,2|FP AUD DIFF|TL|yes-alg|P3.7|
|R54|F0/2 Bx|F+B 1,2|FP DIFF|TL|yes-alg|P3.7|
|negbin2ClosureRatio|F0/2 Bx|F+B 1,2|FP DIFF|TL|yes-alg|P3.7|
|R55|F0/2 Bx|F+B 1,2|FP DIFF|TL|yes-alg|P3.7|
|negbin3ClosureRatio|F0/2 Bx|F+B 1,2|FP DIFF|TL|yes-alg|P3.7|
|R56|F0/2 Bx|F+B 1,2|FP PART DIFF|TL|yes-alg|P3.7|
|R57|F1/3 Bx|F+B 2,3|PART|TL|yes-alg|P3.7|
|R59|F0/1 Bok|FWD 1|HYP|TL|yes-alg|P4|
|binomialKappaDeterminesN|F0/2 Bx|F+B 1,2|PART|TL|yes-alg|prove TL (low)|
|binomialRecoverN|F0/1 Bx|F+B 1|AUD|TL|yes-alg|P4|
|negbinKappaDeterminesR|F1/2 Bok|FWD 2|PART|TL|yes-alg|prove TL (low)|

**ClusteringExtension** (14)
|id|status|symptom|cause|fix|text true?|action|
|-|-|-|-|-|-|-|
|R69|inf|INF|DEF WD|TLdef+DOC|NO: stub fraction, C=2⟨t⟩/⟨k(k−1)⟩|P2.8|
|R70-sec|miss|GAP|NOTH|TLdef|yes-alg|prove TL (med)|
|R71-sec-a|F1/1 Bx|BWD|FS|TL|yes-lit (indep. edges)|P4|
|R71-sec-b|F0/2 Bx|F+B 1,2|DIFF|DOC|NO: T(2−T)≠T+T²−T³|P2.8|
|R71a|F1/1 Bx|BWD|FS|TL|yes-alg|P4|
|R71b|F0/2 Bx|F+B 1,2|DIFF|DOC|NO: not a per-partner T|P2.8|
|R72|miss|GAP|NOTH|TLdef+DOC|NO: triangle term doesn't scale|P2.8|
|R73-sec-a|miss|GAP|NOTH|DOC|partly: reasoning contradictory|P2.8|
|R73-sec-b|F1/5 Bok|FWD 2,3,4,5|AUD PART|TL+DOC|partly: chain true, T(1+T)/2 unsourced|prove TL|
|R74|inf|INF|DEF|DOC|yes-alg|reword|
|R75-sec|F1/5 Bok|FWD 2,3,4,5|DV WD|TLdef+DOC|NO: literature C differs|P2.8|
|R75|F1/2 Bok|FWD 2|DV WD|DOC|NO: see R75-sec|P2.8|
|R76-sec|F1/1 Bx|BWD|FS|TL|yes-alg|P4|
|R76|F1/1 Bx|BWD|FS|TL|yes-alg|P4|

**CoarseGrain** (3)
|id|status|symptom|cause|fix|text true?|action|
|-|-|-|-|-|-|-|
|header.coarseGrainMap|miss|GAP|NOTH|TLdef+DOC|yes-alg|P3.4|
|table.R6|F1/1 Bx|BWD|AUD EX|TL|yes-alg|prove TL|
|R6|F1/1 Bx|BWD|AUD EX|TL|yes-alg|prove TL|

**ConvergenceTheorems** (30)
|id|status|symptom|cause|fix|text true?|action|
|-|-|-|-|-|-|-|
|header.scope|inf|INF|META|DOC|NO: nothing convergent proved|P2.2|
|R105|miss|GAP|NOTH|TL|partly: S-curve only (Rempała)|P3.4|
|R105.keyIdentity|miss|GAP|NOTH|TL+SPEC|depends: true iff I := φ_I|P3.4|
|R105a|inf|INF|DEF|DOC|yes-lit|reword|
|R105b|inf|INF|DEF|DOC|yes-lit|reword|
|R105c.1|miss|GAP|NOTH|TL|yes-alg|P4|
|R105c.2|miss|GAP|NOTH|DOC|NO: R₀_MA = T_edge·κ exactly|P2.9|
|R105c.3|miss|GAP|NOTH|DOC|NO: ratio → (β̃+γ̃)/β̃ ≠ 1|P2.9|
|R105c.4|F0/1 Bx|F+B 1|FS HYP|REG|yes-alg|prove TL|
|R105d.1|miss|GAP|NOTH|TL|yes-alg|P3.1|
|R105d.2|F1/2 Bok|FWD 1|DV|TL|yes-alg|P4|
|R105e.1|miss|GAP|NOTH|TL|yes-math|P3.4|
|R105e.2|F0/1 Bok|FWD 1|TAU|TL|yes-alg|prove TL|
|R106.header|axiom|AX|AXF|AX-|yes-lit (Lean axiom proves False)|P1.1 P2.11|
|R106|axiom|AX|AXF|AX-|yes-lit (Lean axiom proves False)|P1.1 P2.11|
|R107b|F0/1 Bx|F+B 1|AUD|TL+REG|yes-alg|P4|
|R108b|F1/2 Bok|FWD 2|DV|TL|yes-math|P4|
|R110.header|miss|GAP|NOTH|TL|yes-lit|P3.3|
|R110.stability|F0/2 Bok|FWD 1,2|TAU|TL+SPEC|depends: on 'stable'; ≤ vs <|SPEC|
|R110b.1|miss|GAP|NOTH|TL|yes-alg|P3.3|
|R110b.2|miss|GAP|NOTH|DOC|partly: R₀ = 1 also attracting|reword|
|R110b.3|F0/2 Bok|FWD 1,2|TAU|TL|yes-alg|prove TL|
|R110c.1|miss|GAP|NOTH|TL|yes-alg|P3.3|
|R110c.2|F0/4 Bok|FWD 1,2,3,4|TAU|TL|yes-alg|prove TL|
|R110d|F2/2 Bx|BWD|OTH|-|yes-alg|P4|
|R111a|axiom|AX|AXT|AX-+DOC|NO: needs major-outbreak conditioning|P1.2 P2.11|
|R111b|axiom|AX|AXT|AX-+DOC|partly: true under Ball 2021 conditions|P1.2 reword|
|R112b|F0/5 Bok|FWD 1,2,3,4,5|DV HYP|TL|yes-alg|P4|
|R112c|F2/3 Bok|FWD 2|DV|TL|yes-alg|P4|
|R112d|F1/1 Bx|BWD|AUD|TL|yes-alg|P4|

**DegreeCorrelation** (18)
|id|status|symptom|cause|fix|text true?|action|
|-|-|-|-|-|-|-|
|R79-sec|F0/5 Bx|F+B 1,2,3,4,5|OTH|TL|yes-alg|P3.5|
|R79a|inf|INF|DEF|-|yes-alg|keep|
|R79b|F0/2 Bx|F+B 1,2|FS HYP|REG|yes-alg|P4|
|R80-sec|F0/2 Bx|F+B 1,2|DV AUD|TL|yes-alg|P3.5|
|R80|inf|INF|DEF|-|yes-alg|keep|
|R81-sec|axiom|AX|AXT|AX-+DOC|NO: k·Q gives ⟨k²⟩/⟨k⟩|P1.2 P2.6|
|R81|axiom|AX|AXT|AX-+DOC|NO: off by one|P1.2 P2.6|
|R82|inf|INF|DEF WD|DOC|yes-def (but not the R₀ matrix)|prove TL|
|R83e|F1/3 Bok|FWD 2,3|PART|REG|yes-alg|P4|
|R83f|F1/2 Bx|F+B 2|AUD|REG|yes-alg|P4|
|R84-sec|F2/3 Bok|FWD 1|OTH|TL|yes-alg|prove TL (low)|
|R86-sec|inf|INF|META|-|yes-alg|keep|
|R86a|F0/1 Bx|F+B 1|AUD|TL|yes-alg|P4|
|R86c|F1/1 Bx|BWD|OTH|REG|yes-alg|P4|
|R86f-2|miss|GAP|NOTH|TL|yes-alg|prove TL (low)|
|R86g-2|inf|INF|META|-|yes-alg|keep|
|R86h-1|F2/7 Bx|F+B 1,2,5,6,7|HYP|TL|yes-alg|P3.5|
|R86h-2|F0/3 Bx|F+B 1,2,3|OTH|TL|yes-alg|prove TL (low)|

**Docs** (53)
|id|status|symptom|cause|fix|text true?|action|
|-|-|-|-|-|-|-|
|cf.nodeCategory|miss|GAP|NOTH|TLdef|yes-def|P3.4|
|cf.edgeCategory|miss|GAP|NOTH|MD|ill-posed: morphisms unspecified|SPEC|
|cf.ambientODE|miss|GAP|NOTH|MD|yes-def|keep|
|cf.coarseGrainDef|miss|GAP|NOTH|MD+TLdef|partly: morphism map undefined|P3.4|
|cf.prop3_1|miss|GAP|NOTH|TL|yes-math (standard IC)|P3.4|
|cf.thm3_2|F1/3 Bok|FWD 2,3|WD|MD|unverified: 'faithful' misused|reword|
|cf.thm3_3|miss|GAP|NOTH|MD|partly: omits θ-ODE constraint|prove TL|
|cf.thm3_3-lostInformation|miss|GAP|NOTH|MD|NO: node curve keeps ψ″/ψ′ and more|P2.9|
|cf.liftDef|miss|GAP|NOTH|MD|partly: βκ/(β+γ) is network R₀|prove TL|
|cf.poissonUniqueSection|miss|GAP|NOTH|MD+TL|partly: needs reparametrisation|P3.4|
|cf.thm4_1|miss|GAP|NOTH|MD|NO: false in dim-preorder|P2.10|
|cf.cor4_2-GF|F0/2 Bok|FWD 1,2|WD|MD+TLdef|yes-alg (not expressible in Lean)|reword|
|cf.thm4_3|F2/6 Bx|F+B 1,4,5,6|OTH|MD+TL|NO: 3⇒2, 4⇒2 fail|P2.9|
|cf.thm4_3-massAction|miss|GAP|NOTH|MD+TL|partly: I = φ_I, reparametrised|P3.4|
|cf.pgfClosureTreeLike|miss|GAP|NOTH|MD|partly: 'iff' informal|reword|
|cf.edgeTreeFunctor|miss|GAP|NOTH|MD|ill-posed: no cat.|reword|
|cf.nonMarkovObstruction|F1/4 Bok|FWD 1,3,4|OTH|MD|partly: not an obstruction|reword|
|cf.subcategoryInclusions|miss|GAP|NOTH|MD|ill-posed: no cat.|reword|
|cf.validityDomain|F1/3 Bok|FWD 1,2|DV|MD|partly: 'precisely' false|P2.14|
|cf.poissonEquivMassAction|miss|GAP|NOTH|MD+TL|partly: S-curve only|P3.4|
|cf.conj6_1|inf|INF|META|-|unverified (open conjecture)|keep|
|cf.thm7_1|miss|GAP|NOTH|MD|NO: 2 rates can't match a curve|P2.9|
|cf.liftNotUnique|miss|GAP|NOTH|MD|partly: 'minimal info' unsupported|delete|
|cf.thetaNonincreasing|F0/1 Bx|F+B 1|NT|TL|yes-math|P3.2|
|cf.thm8_1|F0/2 Bx|F+B 1,2|AUD|TL|yes-alg|P4|
|cf.thm8_1-factor|miss|GAP|NOTH|MD|NO: algebra wrong by (κ−1)/κ|P2.9|
|cf.thm8_1-poisson|F0/3 Bx|F+B 1,2,3|PART|MD+TL|partly: 'exact equivalence' Poisson only|reword|
|cf.thm8_1-overdispersed|miss|GAP|NOTH|TL|yes-alg|P4|
|cf.thm8_1-underdispersed|miss|GAP|NOTH|TL|yes-alg|P4|
|cf.dispersionSingleScalar|inf|INF|META|MD|NO: correction depends on κ too|P2.9|
|ms.marginalisationLinearMap|inf|INF|META|MD|partly: stale (→L vs →ₗ)|reword|
|ms.flowDef|inf|INF|META|MD|yes-def (global flows may not exist)|prove TL|
|ms.T1|F0/2 Bx|F+B 1,2|OTH|MD+TL|yes-math|prove TL|
|ms.T1-proofStatus|inf|INF|META|MD|NO: stale, no sorry|P2.13|
|ms.T2-smallestWitness|miss|GAP|NOTH|MD|NO: false as universal|P2.13|
|ms.T2-proofStatus|inf|INF|META|-|yes-alg|keep|
|ms.T3|F0/2 Bx|F+B 1,2|EX WD|MD|unverified (false for Lean predicate)|prove TL|
|ms.T3-proofStatus|inf|INF|META|MD|NO: stale|P2.13|
|ms.T3-linearEquivariant|F0/1 Bok|FWD 1|TAU HYP|MD+TL|NO: needs L₄(ker M)⊆ker M|P2.13|
|ms.T3-kkr|F0/2 Bx|F+B 1,2|DIFF|MD+TL|unverified: witness decoupled|prove TL|
|ms.flowHypothesised|miss|GAP|NOTH|MD|NO: Picard–Lindelöf is local|P2.13|
|ms.realVsRational|inf|INF|META|MD|NO: stale|P2.13|
|ms.T5-empiricalBridge|inf|INF|META|RM+MD|NO: vacuous hypothesis|P2.13|
|ms.T6|F1/5 Bok|FWD 2,3,4,5|EX|REG|yes-alg|P4|
|ms.T6-values|F1/4 Bx|F+B 1,2,3|PART|TL|yes-alg|P4|
|ms.T6-phaseReversal|inf|INF|META|MD|NO: one surrogate witness|P2.13|
|ms.T7-witness|miss|GAP|NOTH|MD|NO: no global flow of F3Kℝ|P2.13|
|ms.overdetermined|inf|INF|META|-|unverified (heuristic)|keep|
|ms.exactInvariant|inf|INF|META|-|yes-alg|keep|
|readme.conservationLaws|F2/2 Bx|BWD|OTH|RM+MD|partly: algebraic identities only|P2.1|
|readme.pgfIdentities|F0/2 Bx|F+B 1,2|PART VS|RM+MD|partly: two-moment records|P2.1|
|readme.vmInvariants|F2/3 Bx|F+B 2|OTH|RM+MD|partly: few facts; VM7/VM8 false|P2.1|
|vignettes.leanMarginalisation|inf|INF|META|RM|partly: T1,T4,T5,T7 only|P2.1|

**DynamicLimits** (25)
|id|status|symptom|cause|fix|text true?|action|
|-|-|-|-|-|-|-|
|header.staticLimitCollapse|miss|GAP|NOTH|TLdef|yes-lit|keep|
|header.fastRewiringCollapse|miss|GAP|NOTH|DOC|NO: limit is MFSH, keeps heterogeneity|P2.3|
|header.interpolation|F2/4 Bx|F+B 2,3|DV AUD|TL+DOC|partly: 'mean-field' mislabel|P4|
|table.R31|F1/3 Bok|FWD 1,2|DV|TL|yes-def|P4|
|table.R32|F1/3 Bok|FWD 1,2|DV|TL+DOC|partly: target is MFSH|prove TL|
|table.R35|F1/2 Bok|FWD 1|PART|DOC|NO: models differ in R₀|P2.3|
|table.R37|F0/1 Bok|FWD 1|EX|TLdef+DOC|NO: equidispersed counterexample|P2.3|
|table.R40|F0/2 Bx|F+B 1,2|AUD|TL|yes-def|P4|
|R29|F2/5 Bok|FWD 3,4,5|DV|TL|yes-def|P4|
|R30|F2/4 Bok|FWD 3,4|DV|TL|yes-alg|P4|
|R31a|F1/5 Bok|FWD 1,2,4,5|DV|TL|yes-def|P4|
|R31b|miss|GAP|NOTH|TLdef|yes-lit|prove TL (med)|
|R32a|F1/3 Bok|FWD 2,3|PART|TL|yes-def|P4|
|R32b|miss|GAP|NOTH|DOC|partly: MFSH keeps degrees|P2.3|
|R33c|inf|INF|META|RM+DOC|NO: R₀ depends on η (MSV 2012)|P2.3|
|fastRewiringR0MeanDegree|inf|INF|DEF|TLdef+DOC|NO: fast limit (β/γ)⟨K²⟩/⟨K⟩|P2.3|
|R34|F2/4 Bok|FWD 3,4|DV|TL|yes-def|P4|
|R35a|F1/3 Bok|FWD 2,3|DV|TL|yes-def|P4|
|R35b|F1/2 Bok|FWD 1|PART|DOC|NO: see table.R35|P2.3|
|R37a|F0/1 Bok|FWD 1|EX|TLdef+DOC|NO: see table.R37|P2.3|
|R37b|miss|GAP|NOTH|DOC|yes-alg (uses wrong R₀)|keep|
|R38|F1/6 Bok|FWD 2,3,4,5,6|DV|TL+REG|yes-def|P4|
|R39|F1/3 Bok|FWD 2,3|DV|TL|yes-def|P4|
|R40a|F0/2 Bx|F+B 1,2|AUD|TL|yes-def|P4|
|R40b|miss|GAP|NOTH|DOC|NO: 12N<3^N fails N≤3|P2.14|

**EpiCategory** (3)
|id|status|symptom|cause|fix|text true?|action|
|-|-|-|-|-|-|-|
|header.twoCategories|miss|GAP|NOTH|DOC|ill-posed: no cat.|reword|
|header.refinementPreorder|inf|INF|DEF|DOC|partly: order is by dimension|reword|
|dispersionIndexOneIffPoisson|miss|GAP|NOTH|DOC|NO: equidispersed non-Poisson|P2.9|

**GaloisPair** (7)
|id|status|symptom|cause|fix|text true?|action|
|-|-|-|-|-|-|-|
|header.GFLossy|F1/2 Bok|SHQ ?2|SHQ|DOC+AL|partly: only via dim mismatch|P4 SHADOW?|
|header.galoisConnection|miss|GAP|NOTH|MD+DOC|NO: false in dim-preorder|P2.10|
|table.R14|F1/2 Bok|SHQ ?2|SHQ|DOC+AL|partly: only via dim mismatch|P4 SHADOW?|
|poissonLiftPoisson|miss|GAP|NOTH|TL|yes-alg|P4|
|R14a|F1/2 Bok|SHQ ?2|SHQ|DOC+AL|partly: only via dim mismatch|P4 SHADOW?|
|R14b|miss|GAP|NOTH|TL+DOC|yes-def|reword|
|R14c|inf|INF|META|DOC|ill-posed: dims have no semantics|delete|

**Hierarchy** (7)
|id|status|symptom|cause|fix|text true?|action|
|-|-|-|-|-|-|-|
|header.fullGtPair|miss|GAP|NOTH|DOC|partly: 3^N>12N only N≥4|P2.14|
|header.stepsAreCoarseGrainings|miss|GAP|NOTH|DOC|ill-posed: nothing defined|reword|
|table.R27|F0/3 Bx|F+B 1,2,3|OTH|TL+DOC|NO: equidispersed non-Poisson|P2.9|
|table.R28|F0/1 Bok|FWD 1|DV|TL+DOC|partly: fibre is excess=κ|reword|
|R25|F1/3 Bok|FWD 2,3|PART|TL+SPEC|depends: dynamic 'exact' true|P3.4|
|R27|F0/3 Bx|F+B 1,2,3|OTH|TL+DOC|NO: equidispersed non-Poisson|P2.9|
|R28|F0/1 Bok|FWD 1|DV|TL+DOC|partly: fibre is excess=κ|reword|

**InvariantRegion** (43)
|id|status|symptom|cause|fix|text true?|action|
|-|-|-|-|-|-|-|
|header.invariance.theta|miss|GAP|NOTH NT|TL|yes-math|P3.2|
|header.invariance.phi|miss|GAP|NOTH NT|TL|yes-math|P3.2|
|header.invariance.S|miss|GAP|NOTH|TL|yes-math|P3.2|
|header.invariance.R|miss|GAP|NOTH NT|TL|yes-math|P3.2|
|header.invariance.I|miss|GAP|NOTH NT|TL|yes-math|P3.2|
|header.model|inf|INF|DEF|TLdef+DOC|NO: φ_I′ uses ψ″(θ), not ψ′(θ)/θ|P2.4|
|header.faceConditions|F0/7 Bx|F+B 1,2,3,4,5,6,7|WD|TLdef+DOC|partly: needs φ_I≤θ in region|P2.4|
|header.nagumoConditional|miss|GAP|NOTH HYP|TL+DOC|NO: no such theorem exists|P2.2|
|pgfEvalOne|F1/2 Bok|FWD 2|AUD|TL|yes-alg|P4|
|R113|F1/1 Bx|BWD|OTH|-|yes-alg|P4|
|R116a|F0/1 Bx|F+B 1|DV AUD|TLdef|yes-alg|P4|
|R116b|miss|GAP|NOTH NT|TL|yes-math|P3.2|
|R116c|miss|GAP|NOTH NT|TL|yes-math|P3.2|
|R117a|F2/2 Bx|BWD|FS|TLdef+DOC|partly: displayed field wrong|P2.4|
|R117b|miss|GAP|NOTH|TL|yes-math|P3.2|
|phiIDotFactors.a|F0/1 Bx|F+B 1|OTH|TLdef|yes-alg|prove TL|
|phiIDotFactors.b|miss|GAP|NOTH|DOC|NO: sign also depends on f(θ)|P2.4|
|R118b|miss|GAP|NOTH NT|TL|yes-math|P3.2|
|R119a|F1/1 Bx|BWD|FS|-|yes-alg|P4|
|R119b|miss|GAP|NOTH NT|TL|yes-math|P3.2|
|R120|F1/1 Bx|SHQ ?bwd|SHQ|AL|yes-def|P4 SHADOW?|
|R120b|F0/3 Bok|FWD 1,2,3|OTH|TL|yes-alg|prove TL|
|R120b.guard|F0/1 Bx|F+B 1|OTH|TL+DOC|partly: 'guards' overclaims|prove TL|
|missingSeedFactorOvercounts|F0/2 Bok|FWD 1,2|PART|TL|yes-alg|P4|
|R121|F2/2 Bx|BWD|FS|-|yes-alg|P4|
|R122a|F0/2 Bx|F+B 1,2|OTH|TL|yes-math|P3.2|
|R122b|inf|INF|META|-|yes-math|keep|
|R122c|miss|GAP|NOTH|TL|yes-math (with φ_I≤θ)|P3.2|
|R122d|miss|GAP|NOTH|TL|partly: drops seed factor|P3.2|
|iDotGeneral.a|F0/1 Bok|FWD 1|TAU|TL|yes-math|prove TL|
|iDotGeneral.b|F0/2 Bx|BWD ?1,2|FS SHQ|TL+AL|yes-alg|P4 SHADOW?|
|iDotAtZero|F0/2 Bx|F+B 1,2|PART|TL|yes-alg|P4|
|R123a|F1/5 Bx|F+B 1,2,3,5|PART WD|TLdef|partly: region lacks φ_I≤θ, S+R≤1|prove TL|
|R123b|F0/3 Bx|F+B 1,2,3|NT|TL|yes-math|P3.2|
|R123c|miss|GAP|NOTH HYP|DOC|NO: hypothesis not stated|P2.2|
|R123d|F1/1 Bx|BWD|FS|TL|yes-alg|P4|
|R123e|F0/1 Bok|FWD 1|AUD|TL|yes-alg|P4|
|R123f|F0/4 Bx|F+B 1,2,3,4|FS PART|TL|yes-math|P3.2|
|R123g|miss|GAP|NOTH|TL|partly: needs θ=0 face fix|P3.2|
|header.thetaFace.a|F0/2 Bx|F+B 1,2|DV AUD|TL|yes-alg|P4|
|header.thetaFace.b|miss|GAP|NOTH|DOC|NO: follows from conservation|P2.4|
|header.thetaFace.c|miss|GAP|NOTH|DOC|NO: 1/θ is an artefact|P2.4|
|thetaLowerBoundaryAbsorbing|F0/1 Bx|F+B 1|DV AUD|TL|yes-alg|P4|

**MarginalisationCharacterization** (21)
|id|status|symptom|cause|fix|text true?|action|
|-|-|-|-|-|-|-|
|header.T2witness|F1/1 Bx|BWD|AUD EX|-|yes-alg|P4|
|header.T1forces|F1/1 Bx|BWD|AUD|DOC|partly: vacuous at witness|prove TL|
|header.T3|F0/1 Bx|F+B 1|EX PART WD|MD+DOC|unverified; false for Lean predicate|P2.13|
|header.onlyTrivial|miss|GAP|NOTH WD|DOC|NO: C₄=s∘G∘M counterexample|P2.13|
|header.kkrCharacterization|inf|INF|META|DOC|partly: Lean has sufficiency only|reword|
|header.interLevel|F2/2 Bx|BWD|OTH|TL+DOC|partly: witness decoupled|reword|
|header.kkrNecessary|miss|GAP|NOTH|DOC|unverified: no argument|delete|
|header.kkrNotSufficient|F2/2 Bx|BWD|OTH|TL+DOC|partly: weakly supported|reword|
|table.T3a|F0/2 Bok|FWD 1,2|TAU HYP|DOC|NO: needs L₄(ker M)⊆ker M|P2.13|
|table.T3b|F0/1 Bx|F+B 1|EX PART WD|DOC|unverified as universal|P2.13|
|table.T3c.a|inf|INF|META|-|yes-lit|keep|
|table.T3c.b|F2/2 Bx|BWD|OTH|TL+DOC|partly: weakly supported|reword|
|closureFamilies.linear|inf|INF|META|DOC|NO: exact closures nonlinear|P2.13|
|closureFamilies.kirkwood|inf|INF|DEF EX PART|TLdef+DOC|yes-def (Lean predicate weaker)|prove TL|
|linearClosureEquivariant.b|miss|GAP|NOTH WD|DOC|NO: under Lean predicate|P2.13|
|isLinearAdmitsEquivariant|F0/1 Bok|FWD 1|TAU|TL|yes-def|prove TL|
|c4RealIsKirkwoodForm|F2/7 Bok|FWD 3,4,5,6,7|PART|TL|yes-alg|P4|
|kirkwoodFormNotEquivariant|F0/1 Bok|FWD 1|OTH|TL|yes-alg|prove TL (low)|
|kkrNecessaryNotSufficient.necessary|miss|GAP|NOTH|DOC|unverified: no argument|delete|
|kkrNecessaryNotSufficient.notSufficient|F1/3 Bx|F+B 2,3|DIFF|TL+DOC|partly: weakly supported|prove TL|
|kkrNecessaryNotSufficient.concretely|miss|GAP|NOTH WD|DOC|NO: M=id, C₄=u² equivariant|P2.13|

**MarginalisationDynamicalGap** (12)
|id|status|symptom|cause|fix|text true?|action|
|-|-|-|-|-|-|-|
|header.bridge|inf|INF|META|DOC|NO: no formal link; vacuous|P2.13|
|header.overview|F0/2 Bx|F+B 1,2|PART|MD+DOC|NO: rate is 6−C₃(4)|P2.13|
|header.T6.a|F1/1 Bx|BWD|OTH|DOC|partly: 'exact' is fitted|reword|
|header.T6.b|miss|GAP|NOTH|DOC|NO: C₃=3v²/8 matches|P2.13|
|header.T6.c|inf|INF|META|DOC|NO: T6 says the opposite|P2.13|
|kirkwoodNotEquivariantViaT4|F1/2 Bok|FWD 2|PART|TL|yes-alg|P4|
|trajectoryGapNormGeHalfEpsT|F0/1 Bx|F+B 1|AUD EX|TL|yes-math|P4|
|algebraicGapAtWitness.b|inf|INF|META|-|yes-alg|keep|
|trajectoryGapRateTwoAtWitness.b|inf|INF|META HYP|RM+DOC|NO: vacuous at F3Kℝ|P2.13|
|f3RealIsKirkwoodForm|F2/4 Bok|FWD 3,4|PART|TL|yes-alg|P4|
|refinementFailureExists.b|F0/1 Bx|F+B 1|PART|DOC|partly: zero error by construction|reword|
|refinementFailureExists.c|inf|INF|META|DOC|NO: T3b/T4 say nothing of it|P2.13|

**MarginalisationFunctor** (8)
|id|status|symptom|cause|fix|text true?|action|
|-|-|-|-|-|-|-|
|header.exactMarginalises|miss|GAP|NOTH|TLdef|yes-def|keep|
|header.closedNeedNotCommute|F1/3 Bx|F+B 1,2|AUD EX|REG|yes-alg|P4|
|header.T1|F2/4 Bok|FWD 1,2|PART|DOC|partly: ⇐ needs uniqueness|prove TL|
|header.scaffolding|inf|INF|META|DOC|partly: parts unused|reword|
|table.M1|inf|INF|META|DOC|NO: labels inconsistent|P2.2|
|uniqueFlow.c1|miss|GAP|NOTH|TL|yes-math|prove TL (med)|
|RM1|F1/2 Bx|F+B 2|HYP|DOC|partly: 'the flow' needs uniqueness|reword|
|RM4b|F2/3 Bx|F+B 3|AUD|DOC|partly: unusable at witness|prove TL|

**MessagePassingBridge** (36)
|id|status|symptom|cause|fix|text true?|action|
|-|-|-|-|-|-|-|
|header.sherborneThm1|miss|GAP|NOTH|TLdef|yes-lit|keep|
|header.kkrThm2|miss|GAP|NOTH|CITE|yes-lit|keep|
|header.hierarchy|miss|GAP|NOTH|DOC|partly: pairwise→MA needs reparam.|reword|
|table.R62|F0/1 Bx|F+B 1|FS|TL|yes-lit|P3.4|
|table.R63|F0/5 Bok|FWD 1,2,3,4,5|TAU|TL|yes-lit|prove TL (low)|
|table.R64|F1/5 Bx|F+B 1,2,3,4|LEN|DOC|ill-posed: no morphisms|reword|
|table.R65|F1/4 Bx|F+B 1,3,4|LEN|TLdef+DOC|partly: table inconsistent|prove TL|
|table.R66|F0/1 Bx|F+B 1|LEN|TL|yes-lit|prove TL|
|table.R67|F0/4 Bx|F+B 1,2,3,4|LEN|TL|yes-lit|prove TL (low)|
|table.R68|F0/6 Bok|FWD 1,2,3,4,5,6|TAU|TL+DOC|partly: MA only S, reparametrised|P2.9|
|R64|F1/5 Bx|F+B 1,2,3,4|LEN PART|DOC|partly: lists not nested|reword|
|R60|F2/3 Bok|FWD 2|OTH|-|yes-def|P4|
|R60b|inf|INF|META|-|yes-def|keep|
|ebcmState|miss|GAP|NOTH|CITE|yes-lit|keep|
|R62a|miss|GAP|NOTH|TLdef|yes-lit|keep|
|R62b|miss|GAP|NOTH|TLdef|yes-lit|keep|
|R62c|miss|GAP|NOTH|-|yes-lit|keep|
|R62d|F0/2 Bok|FWD 1,2|FS HYP|TL|yes-math|prove TL|
|R63a|miss|GAP|NOTH|TLdef|yes-lit|keep|
|R63b|miss|GAP|NOTH|TL|yes-math|prove TL (low)|
|R63c|miss|GAP|NOTH|-|yes-lit|keep|
|R63d|F1/2 Bok|FWD 2|TAU|TL|yes-math|prove TL|
|markovEbcmDim|F0/1 Bok|FWD 1|TAU|DOC+REG|yes-def|P4|
|pdeToOdeReduction|F0/1 Bx|F+B 1|TAU|TL|yes-lit|P4|
|R65|F1/3 Bx|F+B 1,3|LEN PART|DOC|partly: lookup table|P4|
|R66a|F0/1 Bx|F+B 1|LEN|TL|yes-lit|prove TL|
|R66b|miss|GAP|NOTH|CITE|yes-lit|keep|
|R66c|miss|GAP|NOTH|CITE|yes-lit|keep|
|R66d|miss|GAP|NOTH|CITE|yes-lit|keep|
|R66e|F0/4 Bx|F+B 1,2,3,4|LEN|DOC|ill-posed: 'only path'|delete|
|R67|F1/5 Bok|FWD 1,2,3,4|LEN|TL|yes-lit|prove TL (low)|
|R68a|F0/0 B-|INC|NOSH TAU|DOC+AL|NO: MA matches S only|P2.9|
|R68b|miss|GAP|NOTH|DOC|partly: last link needs caveat|prove TL|
|R68c|miss|GAP|NOTH|DOC|partly: not representable|reword|
|summary.ptDecouples|miss|GAP|NOTH|CITE|yes-lit|keep|
|summary.nonPT|miss|GAP|NOTH|DOC|yes-lit (cite KKR, not R57)|cite|

**MethodOfStages** (14)
|id|status|symptom|cause|fix|text true?|action|
|-|-|-|-|-|-|-|
|R87|F0/3 Bok|FWD 1,2,3|ND HYP|TL|yes-math|prove TL (low)|
|R88|F0/2 Bok|FWD 1,2|ND|TL|yes-math|prove TL (low)|
|R89a|F0/2 Bok|FWD 1,2|ND|TL|yes-math|prove TL (low)|
|R89b|miss|GAP|NOTH|TL|yes-alg|P4|
|R90a|F0/2 Bok|FWD 1,2|ND|TL|yes-math|prove TL (low)|
|R90b|miss|GAP|NOTH|TL|yes-alg|P4|
|R91a|F1/2 Bok|FWD 2|OTH|TL|yes-math|prove TL (low)|
|R91b|miss|GAP|NOTH|TL|yes-math|prove TL (med)|
|R92|F0/1 Bok|FWD 1|TAU|TLdef+DOC|unverified: formulation-dependent|prove TL|
|R93a|miss|GAP|NOTH|DOC|NO: T₁=1/2, T₂=5/9 (β=γ=1)|P2.7|
|R93b|miss|GAP|NOTH|TL|yes-math|prove TL (med)|
|R93c|F1/2 Bok|FWD 1|OTH|TL|yes-math|prove TL (low)|
|R94a|miss|GAP|NOTH|TL|yes-math|prove TL (med)|
|R94b|F0/1 Bok|FWD 1|FS|TL|yes-alg|P4|

**Obstructions** (36)
|id|status|symptom|cause|fix|text true?|action|
|-|-|-|-|-|-|-|
|header.standardAssumptions|inf|INF|DEF|-|yes-lit|keep|
|header.networkNotObstruction|F0/4 Bok|FWD 1,2,3,4|FIAT PART WD|DOC|partly: only specific graph classes|reword|
|header.clusteringAddsVariables|miss|GAP|NOTH|DOC+CITE|unverified: citation, count 9|cite|
|header.pdeCollapsesToOde|miss|GAP|NOTH|CITE|yes-lit|keep|
|table.R18|F3/5 Bok|FWD 4,5|FIAT WD|DOC|partly: triangle-clustered CM only|reword|
|table.R19|F3/5 Bx|FWD 2,3 ?bwd|FIAT SHQ WD|DOC+AL|yes-lit|P4 SHADOW?|
|table.R21|F1/3 Bok|FWD 2,3|FIAT WD|DOC|yes-lit|keep|
|table.R22|F0/2 Bx|F+B 1,2|OTH|DOC|ill-posed: a topic|delete|
|table.R23|F3/3 Bx|BWD|OTH|DOC|ill-posed: a title|delete|
|table.R24|miss|GAP|NOTH|TLdef+DOC|NO: 2+n inconsistent with table|P2.7|
|R18c|F0/2 Bx|F+B 1,2|OTH|REG|yes-alg|P4|
|R21b|F1/3 Bok|FWD 2,3|FIAT WD|DOC|yes-lit|keep|
|R19a|F1/3 Bok|FWD 2,3|FIAT PART WD|REG|yes-lit|P4|
|R19b|F2/4 Bok|FWD 3,4|FIAT WD|REG|yes-lit|P4|
|R19c|inf|INF|META|DOC|yes-lit (reference garbled)|reword|
|R19d|miss|GAP|NOTH|CITE|yes-lit|keep|
|erlangIsOde|F1/2 Bok|FWD 2|FIAT PART WD|-|yes-def|P4|
|markovIsOde|F1/3 Bok|FWD 2,3|PART|DOC|NO: localised is impossible|P2.14|
|R20a|F2/3 Bok|FWD 2|FIAT PART WD|DOC|NO: holds by fiat only|P2.14|
|R20c|inf|INF|META|-|yes-lit|keep|
|R22a|F0/2 Bx|F+B 1,2|OTH|DOC|unverified: hard-coded 13 vs 4|cite|
|R22b|inf|INF|META|-|yes-alg|keep|
|standardMostCompact|F0/3 Bx|F+B 1,2,3|PART|TL|yes-def|P4|
|R24a|F1/3 Bx|F+B 2,3|AUD PART|TL|yes-def|P4|
|R24b|miss|GAP|NOTH|DOC|NO: see table.R24|P2.7|
|R24c|F0/1 Bx|F+B 1|AUD|TL|yes-def|P4|
|R23b|F2/4 Bx|F+B 3,4|FIAT WD|REG|yes-def|P4|
|R23c|F1/3 Bx|F+B 2,3|FIAT WD|REG|yes-def|P4|
|R23d|F1/3 Bx|F+B 2,3|FIAT WD|DOC|partly: 'impossible' by fiat|reword|
|header.kirkwoodHierarchyInconsistent|F1/1 Bx|BWD|AUD EX PART|DOC|partly: 2→1 surrogate only|reword|
|header.T1ImpliesTrajectoryFailure|miss|GAP|NOTH|DOC|partly: formal chain vacuous|P2.13|
|header.witnessCollapse|miss|GAP|NOTH|DOC|NO: marginalisation combinatorics|P2.13|
|header.surrogateForms|inf|INF|META|DOC|unverified: asserted, not derived|reword|
|header.smallestFaithfulWitness|miss|GAP|NOTH|DOC|NO: false as universal|P2.13|
|R25b|F1/3 Bok|FWD 1,2|PART|TL|yes-alg|P4|
|kirkwoodObstructionWitnessValue-b|inf|INF|META|DOC|unverified: not linked to Julia|reword|

**PairwiseClosureConditions** (10)
|id|status|symptom|cause|fix|text true?|action|
|-|-|-|-|-|-|-|
|header.nonnegNeedsPointwise|F1/2 Bx|F+B 2|OTH|TL|yes-alg|prove TL (low)|
|header.conservationNotPositivity|F0/2 Bx|F+B 1,2|OTH|TL|yes-alg (p=(2,−1))|prove TL (low)|
|negativeWeightGivesNegativeTriple.b|F0/2 Bx|F+B 1,2|OTH|TL|yes-alg|prove TL (low)|
|barnardWeightsNormalized.a|F1/1 Bx|BWD|OTH|-|yes-alg|P4|
|barnardWeightsNormalized.b|inf|INF|META|DOC+CITE|unverified: form only asserted|cite|
|keelingFactorNonneg|F1/2 Bok|SHQ ?2|SHQ|AL|yes-alg (φ∈[0,1])|P4 SHADOW?|
|keelingWeightsNonneg|F1/2 Bok|SHQ ?2|SHQ|AL|yes-alg (φ∈[0,1])|P4 SHADOW?|
|keelingStyleClosureSafe.a|F2/5 Bok|FWD 5 ?3,4|PART SHQ|TL+AL|yes-alg|P4 SHADOW?|
|keelingStyleClosureSafe.b|F1/2 Bx|BWD ?2|SHQ|AL+REG|yes-alg|P4|
|keelingStyleClosureSafe.c|miss|GAP|NOTH|TL|yes-alg (corr≡2, φ=1)|prove TL (low)|

**SEIREquations** (15)
|id|status|symptom|cause|fix|text true?|action|
|-|-|-|-|-|-|-|
|table.SEIR1|F0/2 Bok|FWD 1,2|PART|TL|yes-def|P4|
|table.SEIR2|F1/1 Bx|BWD|PART|-|yes-def|P4|
|table.SEIR3|F0/1 Bx|F+B 1|WD|TLdef|yes-math|prove TL (med)|
|table.SEIR4|F0/2 Bx|FWD 1,2 ?bwd|PART SHQ|TL+AL|yes-def|P4 SHADOW?|
|table.SEIR5|miss|GAP|NOTH|TL+DOC|yes-alg (with equality)|P2.14|
|table.SEIR6|miss|GAP|NOTH NT|DOC|unverified: no general proof|reword|
|edgeHazard|F2/3 Bok|FWD 3|OTH|TL|yes-def|P4|
|dTheta|F0/2 Bx|F+B 1,2|PART|TL|yes-def|P4|
|iPop|inf|INF|DEF|-|yes-def|keep|
|iPopZeroAtSeed-a|F0/1 Bok|FWD 1|PART|TL|yes-def|P4|
|iPopZeroAtSeed-b|F0/2 Bx|F+B 1,2|PART|TL|yes-def|P4|
|iPopWrongNonzeroAtSeed|F1/2 Bok|FWD 1|OTH|TL|yes-def|P4|
|edgeHazardIndependentOfE|F1/1 Bx|BWD|OTH|-|yes-def|P4|
|seirIGrowthBounded-a|F0/2 Bx|F+B 1,2|HYP|DOC|NO: σE can exceed incidence|P2.14|
|seirIGrowthBounded-b|miss|GAP|NOTH|DOC|NO: no peak bound follows|P2.14|

**SurvivalBridge** (42)
|id|status|symptom|cause|fix|text true?|action|
|-|-|-|-|-|-|-|
|header.ptCharacterisation|miss|GAP|NOTH|TL|yes-lit|P3.7|
|header.threeModelEquivalence|miss|GAP|NOTH|TLdef+CITE|yes-lit|keep|
|header.survivalEquation|miss|GAP|NOTH|TL|yes-lit|P3.4|
|header.kappaInvariant-a|miss|GAP|NOTH|TL|yes-lit|P3.7|
|header.kappaInvariant-b|F0/6 Bx|F+B 1,2,3,4,5,6|FP PART|TL|yes-alg|P3.7|
|header.categorical.naturalIso|miss|GAP|NOTH|DOC|ill-posed: categorically|reword|
|header.categorical.eta|miss|GAP|NOTH WD|TLdef+DOC|NO: x_SI = p_I·θ·ψ′(θ)|P2.12|
|header.categorical.pairwiseIso|miss|GAP|NOTH|DOC|ill-posed: categorically|reword|
|header.categorical.colimit|miss|GAP|NOTH|DOC|NO: a reduction, not a colimit|P2.12|
|table.R41|miss|GAP|NOTH|TL|yes-lit|P3.7|
|table.R42|F1/4 Bok|FWD 1,2,4|PART WD|TL+SPEC|depends: κ(θ)≡1 yes, κ(1)=1 no|SPEC|
|table.R43|F0/5 Bok|FWD 1,2,3,4,5|EX WD|TL+SPEC|depends: constant κ(θ) only|SPEC|
|table.R44|F0/5 Bok|FWD 1,2,3,4,5|EX WD|TL+SPEC|depends: constant κ(θ) only|SPEC|
|table.R45|F2/4 Bok|FWD 2,4|PART|TL|yes-alg|prove TL|
|table.R46|miss|GAP|NOTH|DOC|ill-posed: no cat.|reword|
|table.R47|F0/3 Bx|F+B 1,2,3|OTH|TL+DOC|partly: form only, rescaled|P3.4|
|table.R48|F0/2 Bok|FWD 1,2|AUD|TL|yes-alg|P4|
|table.R49|F0/2 Bok|FWD 1,2|EX|TL|yes-lit (Lean witness is PT)|P3.7|
|table.R50|F1/5 Bx|F+B 2,3,4,5|OTH|TL|yes-lit|prove TL (med)|
|closureKappa-b|miss|GAP|NOTH|TL|yes-alg|P4|
|closureKappa-c|miss|GAP|NOTH WD|DOC|ill-posed: closureKappa has no θ|reword|
|volzState-a|inf|INF|DEF WD|TLdef+DOC|NO: missing factor θ|P2.12|
|volzState-b|F2/4 Bx|F+B 2,4|PART|TL|yes-alg|prove TL (low)|
|R42|F1/3 Bok|VAC ?2,3|SHQ VS|AL|yes-alg|P4 SHADOW?|
|R43a|F0/2 Bok|FWD 1,2|EX|TL|yes-alg|prove TL|
|R43b|inf|INF|META|-|yes-alg|keep|
|R44a|F0/2 Bok|FWD 1,2|EX|TL|yes-alg|prove TL|
|R44b|inf|INF|META|-|yes-alg|keep|
|R45b|F2/4 Bok|FWD 2,4|PART|TL|yes-alg|prove TL (low)|
|R46a|miss|GAP|NOTH|TL+DOC|ill-posed: no cat.|P3.4|
|R46b|miss|GAP|NOTH|TL+DOC|partly: needs KKR's x_SI|P2.12|
|R47a|F0/2 Bx|F+B 1,2|OTH|TL+DOC|partly: form only, rescaled|P3.4|
|R47b|F0/1 Bx|F+B 1|OTH|TL|yes-math|P3.7|
|R48b|miss|GAP|NOTH|TL|yes-lit|P3.7|
|R48c|miss|GAP|NOTH|DOC|partly: 1/(1−κ) must be integer|P2.12|
|R49a|F0/4 Bok|FWD 1,2,3,4|OTH|TL+DOC|partly: first sentence vague|delete|
|R49b|inf|INF|META|DOC|NO: ψ″(1)=234; ⟨10,200⟩ is PT|P2.12|
|R50a|F1/5 Bx|F+B 2,3,4,5|OTH|TL|yes-lit|prove TL (med)|
|R50b|F2/5 Bx|F+B 3,5 ?1|PART SHQ WD|TL+AL|partly: not KKR's map|P4 SHADOW?|
|R50c|miss|GAP|NOTH|TL|yes-alg|prove TL (low)|
|R50d|miss|GAP|NOTH|CITE|yes-lit|keep|
|R50e|F1/2 Bok|FWD 2|OTH|DOC|partly: left inverse only|reword|

**VolzMeyersEquations** (22)
|id|status|symptom|cause|fix|text true?|action|
|-|-|-|-|-|-|-|
|header.equationLevel|miss|GAP|NOTH|DOC|NO: most of system absent|P2.2|
|header.table4System|miss|GAP|NOTH|TLdef|yes-lit|prove TL (med)|
|header.popIEquation|miss|GAP|NOTH WD|TLdef+DOC|partly: def drops ψ(θ)|P2.4|
|table.VM1|F1/2 Bok|FWD 2|NT|TL|yes-math|prove TL (low)|
|table.VM4|F0/2 Bx|F+B 1,2|OTH|TL|yes-math|prove TL (low)|
|table.VM5|F0/1 Bx|F+B 1|AUD|TL|yes-lit|P4|
|table.VM6|F0/2 Bx|F+B 1,2|OTH|TL+DOC|yes-lit|reword|
|table.VM7|miss|GAP|NOTH|JL+DOC|NO: total is 1+sf (also Julia)|P1.3 P2.14|
|table.VM8|F0/3 Bx|F+B 1,2,3|OTH|DOC|NO: ρ=0 gives isolated pairs|P2.14|
|thetaNonincreasing|F1/2 Bok|FWD 2|NT|TL|yes-math|prove TL (low)|
|populationInflux-b|miss|GAP|NOTH WD|TLdef+DOC|partly: def drops ψ(θ)|P2.4|
|sNonincreasing-a|F0/2 Bx|F+B 1,2|OTH|TL|yes-math|prove TL (low)|
|sNonincreasing-b|F0/2 Bx|F+B 1,2|PART|TL+DOC|partly: 'formalised as' false|P2.2|
|staticThetaEq-a|F0/2 Bx|F+B 1,2|PART|TL|yes-def|P4|
|staticThetaEq-b|miss|GAP|NOTH|TLdef|yes-lit|prove TL|
|staticThetaEq-c|miss|GAP|NOTH|TL|yes-lit|prove TL (low)|
|fastMixingP1Equilibrium-a|F0/1 Bx|F+B 1|OTH|DOC|yes-lit|reword|
|fastMixingP1Equilibrium-b|miss|GAP|NOTH|TLdef+DOC|yes-lit|keep|
|fastMixingP1Equilibrium-c|miss|GAP|NOTH|TL|yes-alg|prove TL (low)|
|fastMixingP1Equilibrium-d|F0/3 Bx|F+B 1,2,3|OTH|DOC|partly: 'formalised as' false|P2.2|
|massActionIncidence-a|F0/3 Bx|F+B 1,2,3|OTH|DOC|NO: see table.VM8|P2.14|
|massActionIncidence-b|F0/1 Bx|F+B 1|OTH|TL|yes-alg|P4|

# Remediation plan (from triage of the 494 non-passing claims)

Rules (SA-PASS_SKILL.md §6): never adapt a shadow to an implementation; never weaken a trusted theorem. Add corrected theorems, move the old ones to `supporting`, and update `claims/<G>.yaml` and `sa_claim`. A false text gets a corrected docstring or spec, not a theorem. New bridges go back to independent review.

## P1 Soundness emergencies
- **P1.1 Delete `axiom tree_pair_exactness`** (`EBCMCategory/ConvergenceTheorems.lean:116`). It is inconsistent: `TreeNetwork` and `PairClosureError` are unconstrained classes, so the instances ⟨True⟩ and ⟨1⟩ on `Unit` give (1:ℝ) = 0. `EBCMCategory.lean` imports it, so any downstream file can prove False. Keep the result (Sharkey, Kiss, Wilkinson, Simon 2015, Bull Math Biol 77) as cited prose or as a `def … : Prop` hypothesis, and fix the citation. Add a CI gate: no `axiom` in `EBCMCategory/`, and every declaration's `#print axioms` ⊆ {propext, Quot.sound, Classical.choice}. (ConvergenceTheorems.R106, R106.header)
- **P1.2 Delete the five content-free axioms:** `ebcm_functor_identity` (l.R0 = l.R0), `ebcm_functor_composition` (≤-transitivity), `clustering_naturality` (True), `correlated_R0_spectral` (T·ρ = T·ρ) and `final_size_CLT` (True). They are consistent, but their docstrings present them as functoriality, naturality, a spectral R₀ and a CLT. Re-register the 7 claims as missing or informal.
- **P1.3 Provably wrong outputs of the Julia package:**
  - `src/multiplex.jl` `multiplex_R0` returns Σ Tᵢeᵢ. For independent layers R₀ = ρ(K), with K = [[T₁e₁, T₁⟨k₁⟩],[T₂⟨k₂⟩, T₂e₂]]. Two 3-regular layers give 5T, not 4T. The sum underestimates R₀ when e₁e₂ < ⟨k₁⟩⟨k₂⟩ and overestimates it when e₁e₂ > ⟨k₁⟩⟨k₂⟩.
  - The VM builder (`src/builders.jl` ≈ 746–771) uses `S_pop ~ ψ(θ)` with θ(0) = 1 and `pop_I(0) = sf`, so S+I+R = 1+sf at t = 0. This is the overcount already fixed in the static builder. Use (1−sf)ψ(θ), or seed with θ(0) = 1−ε.
  - The Lean definition `VMState.incidence := β·P₁·θ·κ` drops ψ(θ). Julia's β·P₁·θ·ψ′(θ) is correct, so it is the Lean definition that must change.
- **P1.4 Put the vacuity on record.** `IsFlow F3Kℝ` is unsatisfiable: v′ = v²/4 from 4 gives 4/(1−t), which blows up. Prove `¬ ∃ φ, IsFlow F3Kℝ φ`, and restate the T1/T5/T7 witness applications with local solutions.
  - Replace or relabel the vacuous theorems `isLinear_admits_equivariant` (∨ True) and `linear_closure_equivariant` (hypothesis = conclusion).
  - Replace or relabel the tautological implementations `dfe_stable_iff_R0_le_one`, `fixed_point_derivative`, `S_theta_chain_rule_coeff`, `I_dot_general`, `full_equivalence_poisson`, `pde_to_ode_reduction`, `markov_ebcm_dim`, `ode_dimension` and `stratified_dim`.

## P2 False or misleading text: proposed wording
- **P2.1 README and vignettes.** Replace the README "Lean proofs" section with: "`proofs/` contains Lean 4 statements about the model algebra: moment identities, sign conditions of the EBCM right-hand side, R₀ and threshold algebra, pairwise-closure weight lemmas, and general lemmas on marginalisation of flows (T1, T4, T5, T7). They are not yet theorems about solutions of the ODEs the package integrates; see proofs/Alignment/SUMMARY.md."
  - Drop "R₀ independence of rewiring" and "conservation laws" from the README.
  - Vignette 12, line 18: drop "the functor preserves composition".
  - index.qmd, line 42: "Lean lemmas on marginalisation of flows (T1, T4, T5, T7); the categorical composition is informal."
  - Remove the "Lean-certified" m = 4 claims from the NBM vignettes.
- **P2.2 Headers and "formalised as" sentences.**
  - CategoricalComposition, EpiCategory, ConvergenceTheorems and VolzMeyersEquations headers: "scalar identities motivated by …; no categorical structure, convergence result or full ODE system is formalised."
  - InvariantRegion: delete the "conditional Nagumo" sentence unless P3.2 lands. In R123c, either add the φ_I ≤ θ hypothesis or drop "stated here".
  - ClosureTheorem: "We check the sufficiency identities for PT families; the necessity direction of KKR Theorem 1 is not formalised."
  - VM4b and VM6d: change "Formalised as" to "Motivated by".
  - MarginalisationFunctor: fix the M1–M3 table labels.
- **P2.3 R₀ depends on rewiring** (Miller, Slim and Volz 2012, §3.2.1). R₀(η) = β/(β+η+γ)·((η+γ)/γ·⟨K²−K⟩/⟨K⟩ + η/γ). The limit η → 0 gives T⟨K²−K⟩/⟨K⟩. The limit η → ∞ gives the MFSH value (β/γ)⟨K²⟩/⟨K⟩, so degree heterogeneity is kept.
  - R33: "DynamicEBCM stores only the static-limit R₀; in the edge-swapping EBCM, R₀ depends on η."
  - Set the R₀ of `fastRewiringLimit` to the MFSH value.
  - R36: "For Poisson degrees the fast-rewiring R₀ is (β/γ)(κ+1), which differs from βκ/(β+γ)."
  - R35: "has the same dimension as a coarse-graining".
  - R37: "The fast-rewiring R₀ exceeds the static R₀ for every degree law."
  - This also corrects five claims that currently pass: DynamicLimits.R33a, table.R33, R36a, table.R36 and Docs.readme.r0RewiringIndependence.
- **P2.4 EBCM vector field.**
  - The correct equation is dφ_I/dt = βφ_I·ψ″(θ)/ψ′(1) − (β+γ)φ_I (Miller 2011; this is what the Julia builders use), not (βφ_I/θ)ψ′(θ)/ψ′(1) − (β+γ)φ_I. With it, the θ = 0 singularity disappears.
  - Replace "the sign of dφ_I/dt is the sign of φ_I" with "φ_I keeps its sign, and {φ_I = 0} is invariant".
  - φ_I ≤ θ follows from θ = φ_S+φ_I+φ_R. Add φ_I ≤ θ and S+R ≤ 1 to `EBCMRegion`.
  - VM incidence: β·P₁·θ·ψ′(θ).
- **P2.5 Multiplex R₀.** "For independent layers R₀ = ρ(K), eᵢ = ψᵢ″(1)/ψᵢ′(1). The sum T₁e₁+T₂e₂ equals R₀ iff e₁e₂ = ⟨k₁⟩⟨k₂⟩, for example for two Poisson layers." The passing claim R96f is false: two 3-regular layers with T = 0.24 give sum 0.96 but ρ = 1.2.
- **P2.6 Degree correlation.** "R₀ = T·ρ(K) with K_kl = (k−1)·Q(l|k), as in Julia src/pgf.jl:311. At r = 0, K has rank one and ρ = ⟨k(k−1)⟩/⟨k⟩." The matrix k·Q gives ⟨k²⟩/⟨k⟩, which is off by one.
- **P2.7 Method of stages.** "η_n preserves the PGF and the mean infectious period. T_n = 1 − (nγ/(β+nγ))^n increases with n towards 1 − e^{−β/γ}, so R₀ and the final size change." Make the Erlang variable count (Obstructions R24) agree with `extensionDim` and with the Julia builder.
- **P2.8 Clustering.**
  - Rename `clustering_coefficient` to `triangleStubFraction`. The clustering coefficient is C = 2⟨t⟩/⟨k(k−1)⟩ with k = s+2t (Volz 2011); for Poisson single and triangle degrees it is 2κ_t/((κ_s+2κ_t)²+2κ_t).
  - Delete "T(2−T) per partner".
  - Replace the clustered R₀ formulas (R72, R99b.2) with the spectral radius of Miller's (2009) edge-type matrix, or delete them.
- **P2.9 Poisson and mass action.**
  - "R₀_MA = β/γ = κβ̃/(β̃+γ̃) = T_edge·κ exactly."
  - "The Poisson EBCM is semiconjugate to mass-action SIR via S = e^{κ(θ−1)} and I = φ_I, with β = κβ̃ and γ = β̃+γ̃ (Rempała 2023). S(t) coincides; the infected curves differ."
  - Replace Theorem 4.3 with: "(a) ψ″(1)/ψ′(1) = ψ′(1) ⇔ Var = mean; (b) Poisson ⇒ (a); (c) the dynamics have mass-action form ⇔ ψ′ = κψ ⇔ Poisson. (a) does not imply Poisson."
  - Delete Theorem 7.1 and the claim that the lost information is exactly what lies beyond the first moment.
  - Correct the Theorem 8.1 factor to (κ²−κ+σ²)/κ².
  - Replace "dispersion index 1 iff Poisson" with "Poisson ⇒ dispersion index 1".
  - Hierarchy R27: restate as a statement about two-moment records.
  - MessagePassingBridge R68a: "MP, EBCM, DSA and pairwise agree. Mass action matches only S(t), and only after reparametrisation."
- **P2.10 Categorical claims that are false in the model.**
  - "F and G are not a Galois connection for the dimension preorder (take E = ⟨10,r⟩, N = ⟨3,r⟩). F∘G = id and the idempotency laws are proved directly."
  - A coupled multi-type system is not a coproduct.
  - For the other categorical rows marked ill-posed, use descriptive wording, or build real categories after P3.4.
- **P2.11 CLT and tree exactness.** "Conditional on a major outbreak (or with a positive initial infected fraction), for bounded degrees, Z_n/n → z in probability and √n(Z_n/n − z) ⇒ N(0,σ²) (Ball 2021)." Keep tree exactness as a citation.
- **P2.12 Volz ↔ DSA.**
  - Use x_SI = p_I·θ·ψ′(θ) and x_SS = p_S·θ·ψ′(θ) (KKR 2023, App. B), and change `volzToDSA` to match.
  - Replace "colimit" with "reduction".
  - R48c: κ ∈ (0,1) is realised only when 1/(1−κ) ∈ ℕ.
  - R49b: the witness ⟨10,200⟩ is geometric, hence PT, and the 80/20 law has ψ″(1) = 234. Use ψ = ½+u²/2 as the non-PT witness.
  - R42–R44: say "κ(θ) is constant on an interval". The value κ(1) alone does not determine the family: ψ = ½+u²/2 has κ(1) = 1.
- **P2.13 Marginalisation.**
  - Replace T3 with the existential statement T3b, and rename `IsKirkwoodForm` to `IsNonAdditive`. Under that predicate the universal claims are false (M = id, C₄ = C₃ = u²).
  - "Linear closures are equivariant for any M" becomes "… iff L₄(ker M) ⊆ ker M".
  - "The rate is 2 for any m = 3 closure" becomes "for F3Kℝ; in general the rate is 6 − C₃(4)".
  - "No Kirkwood m = 3 closure matches" is false: C₃ = 3v²/8 matches.
  - Delete "certifies", "formal bridge to 0.32" and "confirms err_m4 > err_m3".
  - Update the spec: no sorry remains, T3 is stated over ℝ-modules, and Picard–Lindelöf gives only local existence.
  - Fix the C₄ SISI combinatorics.
- **P2.14 Miscellaneous.**
  - VM7: state it as an equality once P1.3 is fixed.
  - VM8: "in the fast-mixing limit".
  - SEIR5: "SEIR final size = SIR final size".
  - Delete seirIGrowthBounded.
  - "Markovian dynamics with uniform initial infection give an ODE system."
  - R20a: "Among the three standard assumptions, only localised seeding has no EBCM variant."
  - Validity domain: include the non-Markovian PDE form and uniform seeding.
  - Hierarchy header and DynamicLimits R40b: 3^N > 12N holds only for N ≥ 4.
  - ClosureTheorem.table.R59 (passing) is false without the condition 1/(1−κ) ∈ ℕ.

## P3 Theorems worth proving genuinely (in order)
- **P3.1 Genuine PGF and EBCM field.** Define PGFs as power series with nonnegative coefficients summing to 1, generalising `PolyPGF` to include Poisson and NegBin, with ψ′ and ψ″ given by HasDerivAt. Define `ebcmField ψ β γ ρ` on (θ, φ_I, R), including the seed. This replaces the free-scalar `PGFData` and `PGFEval`.
- **P3.2 Conservation and invariant region along solutions.** θ is non-increasing and stays in [0,1]. φ_I ≥ 0, by an integrating factor, with no Nagumo theorem needed. S = (1−ρ)ψ(θ) ∈ [0,1], I ≥ 0, R is non-decreasing, and S+I+R = 1.
- **P3.3 Final size and threshold.** θ(t) → θ∞ with θ∞ = 1 − T + Tψ′(θ∞)/ψ′(1). f′(1) = T·ψ″(1)/ψ′(1) = R₀. θ = 1 is the only fixed point in [0,1] iff R₀ ≤ 1.
- **P3.4 Rempała conjugacy.** h(θ,φ_I) = (e^{κ(θ−1)}, φ_I) intertwines the Poisson EBCM with mass-action SIR, with β = κβ̃ and γ = β̃+γ̃ (the sympy residual is 0). Corollaries:
  - R₀_MA = R₀_EBCM.
  - For general ψ, S′ = −β̃φ_Iψ′(ψ⁻¹(S)); the dynamics have mass-action form ⇔ ψ′ = κψ ⇔ Poisson.
  - The scalar reduction S′ = G(S) (Proposition 3.1).
  - This is the first genuine morphism between the node and edge representations.
- **P3.5 Degree-correlated R₀ as a spectral radius,** using Mathlib `Matrix`. K = T(k−1)Q(l|k); at r = 0 it has rank one, and there is a closed form for 2×2. Check it against Julia `correlated_R0`.
- **P3.6 Multiplex R₀ = ρ(K)** for independent layers, with S = ψ₁(θ₁)ψ₂(θ₂) from the factorised PGF, and ρ(K) = sum ⇔ det K = 0. This underpins the Julia fix in P1.3.
- **P3.7 KKR characterisation and the EBCM → pairwise semiconjugacy.** ψ″ψ = κψ′² on an interval with ψ(1) = 1 ⇔ ψ is Poisson, Binomial (with 1/(1−κ) ∈ ℕ) or NegBin. For PT ψ, the corrected map to (x_S, x_SI, x_SS) intertwines the EBCM with the κ-closed pairwise system.
- **Lower priority:**
  - Erlang properties via Mathlib `gammaMeasure`: T_n, its limit, the mean and the variance.
  - R₀(η) for dynamic networks.
  - The Volz ↔ DSA dynamic conjugacy, and right inverses for `volzToDSA`.
  - The clustered EBCM of Volz (2011).

## P4 Cosmetic
- About 110 rows fail only because the implementation omits facts true by rfl, is stated over free scalars, carries an unused hypothesis, or needs one audit-limited step. Fixes:
  - Add corollaries in the text's form.
  - Drop unused hypotheses: 0 < T in `epidemic_threshold`, 0 < κ in `pt_classification_exhaustive`, and n ≥ 2 where n ≥ 1 suffices.
  - Register existing lemmas: q_sum_one, row1/row2_sum_eq_degree, R107a, static_lt_dynamic and the witness-value lemmas.
  - Define thetaDot and phiIDot once, so bridges can replace the neg_mul gaps.
- Resolve the 19 SHADOW? records from the text alone. SurvivalBridge R42 S2/S3 and R50b S1 are vacuous shadows that need reformulating.
- Author shadows for CategoricalComposition.R98d.1 and MessagePassingBridge.R68a.
- Hygiene:
  - Duplicate Result numbers R23–R25.
  - Stale build.log and EBCMCategory.md/html/pdf.
  - Makefile MD_FILES and the CI workflow location.
  - Citations: Sherborne et al. 2018 DOI, Sharkey et al. 2015, Koch & Britton.