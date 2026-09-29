import Alignment.Registry

/-!
# SA-PASS audit (alignment library, NOT trusted code)

Collects every registration made with `Alignment.Registry`, runs the SA-PASS checks and emits
a JSON document. The Python scorer `scripts/sa_pass_score.py` adds the registry-consistency
checks against `Alignment/claims.yaml`, computes the scores and renders the report.

Entry points:

* `#sa_pass_report "path.json"` writes the audit of every registered claim to `path.json`.
* `#sa_audit "claim-id"` logs the audit of one claim (for authors; review records made in
  `Alignment.ReviewedBridges` are only visible when that module is imported).

Check statuses: `pass | fail | vacuous | audit_violation | sorry | missing`.
Bridge statuses: `reviewed | unreviewed | stale | rejected | invalid`.
Lean-side claim flags: `invalid_id, duplicate, gap, impl_untrusted, impl_unsound,
shadow_mismatch, incomplete, module_mismatch, audit_error, shadow_trusted_free,
shadow_tautology, hypothesis_refuted, witness_invalid`.
Hints (reported, not scored): `witness_missing, backward_unused_shadows`.

The rules are documented in `Alignment/README.md`; the ones that matter for soundness of the
audit are stated next to the code that implements them.
-/

namespace Alignment.Audit

open Lean Meta Elab Command

/-! ## Configuration -/

/-- Pure-logic glue that a structural checker may use. Everything else a checker proof mentions
must be a hypothesis, a data constant (see `classifyConst`), an auto-generated equation lemma,
one of the claim's own shadows, or a reviewed bridge registered for the claim. -/
def coreLogicWhitelist : Array Name := #[
  -- conjunction
  ``And.intro, ``And.left, ``And.right, ``And.elim, ``And.imp, ``And.symm, ``And.rec,
  ``And.casesOn,
  -- bi-implication
  ``Iff.intro, ``Iff.mp, ``Iff.mpr, ``Iff.refl, ``Iff.rfl, ``Iff.symm, ``Iff.trans, ``Iff.of_eq,
  ``Iff.rec, ``Iff.casesOn,
  -- disjunction
  ``Or.inl, ``Or.inr, ``Or.elim, ``Or.imp, ``Or.symm, ``Or.resolve_left, ``Or.resolve_right,
  ``Or.rec, ``Or.casesOn,
  -- existential quantifier
  ``Exists.intro, ``Exists.elim, ``Exists.imp, ``Exists.rec, ``Exists.casesOn,
  -- equality
  ``Eq.refl, ``rfl, ``Eq.symm, ``Eq.trans, ``Eq.mp, ``Eq.mpr, ``Eq.rec, ``Eq.ndrec,
  ``Eq.casesOn, ``Eq.subst, ``Eq.substr, ``congrArg, ``congrFun, ``congr, ``cast,
  ``HEq.refl, ``HEq.rec, ``HEq.casesOn, ``HEq.ndrec, ``eq_of_heq, ``heq_of_eq,
  -- extensionality (standard axioms, no mathematical content)
  ``funext, ``propext,
  -- negation, truth, falsity
  ``Not, ``Not.intro, ``Not.elim, ``mt, ``absurd, ``False.elim, ``False.rec, ``False.casesOn,
  ``True.intro, ``trivial, ``True.rec, ``True.casesOn,
  -- combinators
  ``id, ``Function.comp, ``Function.const
]

/-- The axioms a sound trusted theorem may depend on. -/
def standardAxioms : Array Name := #[``propext, ``Quot.sound, ``Classical.choice]

/-- Constants that are never allowed in a checker proof, whatever their type. -/
def forbiddenConsts : Array Name := #[``sorryAx, ``Lean.ofReduceBool, ``Lean.ofReduceNat,
  ``Lean.reduceBool, ``Lean.reduceNat, ``Lean.trustCompiler]

/-- Namespaces whose constants are never allowed in a checker proof (classical reasoning and
decision procedures, including `Decidable.decide`, `Decidable.casesOn`, `Decidable.byCases`). -/
def forbiddenNamespaces : Array Name := #[`Classical, `Decidable]

/-- Structures that can carry a proof inside data: their projections and eliminators are never
allowed in a checker proof. -/
def proofCarriers : Array Name := #[``PLift, ``PProd, ``PSigma]

/-- Data combinators that the vacuity guard's normaliser unfolds. -/
def transparentCombinators : Array Name :=
  #[``id, ``Function.const, ``Function.comp, ``flip, ``inferInstance, ``inferInstanceAs]

/-- Root module of the trusted library. -/
def trustedRoot : Name := `EBCMCategory

/-- Root of the alignment library. -/
def alignmentRoot : Name := `Alignment

/-- The only module whose `sa_bridge_reviewed` / `sa_bridge_rejected` records count. -/
def reviewModule : Name := `Alignment.ReviewedBridges

/-- Fuel for the vacuity guard's normaliser. -/
def normFuel : Nat := 200000

/-- Claim ids used by the worked example and the self-test (excluded from normal reports). -/
def isExampleId (id : String) : Bool :=
  id.startsWith "SELFTEST." || id.startsWith "EXAMPLE."

/-- Claim ids must match `[A-Za-z0-9._-]+`. -/
def validId (id : String) : Bool :=
  !id.isEmpty && id.all fun c => c.isAlphanum || c == '.' || c == '_' || c == '-'

/-! ## Environment helpers -/

/-- The module that declares `n` (the main module for local constants). -/
def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => env.mainModule

/-- Modules of the alignment library (and the module currently being elaborated). -/
def isAlignmentModule (env : Environment) (m : Name) : Bool :=
  m == env.mainModule || alignmentRoot.isPrefixOf m

/-- Module names imported by the trusted root file `EBCMCategory.lean` (read from disk; the
root module itself is not built by the `EBCMCategory` library). -/
def rootImports (rootFile : System.FilePath := "EBCMCategory.lean") : IO (Option (Array Name)) := do
  unless ← rootFile.pathExists do return none
  let src ← IO.FS.readFile rootFile
  let mut out := #[]
  for line in src.splitOn "\n" do
    let l := line.trimAscii.toString
    if l.startsWith "import " then
      for tok in (l.drop 7).toString.splitOn " " do
        let t := tok.trimAscii.toString
        unless t.isEmpty do out := out.push t.toName
  return some out

/-- The trusted modules: the modules imported by the root file `EBCMCategory.lean` and every
`EBCMCategory.*` module they import (transitively), as far as they are loaded. Trust is by
module, never by declaration name. The flag is `false` when the root file cannot be read, in
which case every loaded `EBCMCategory.*` module is trusted. -/
def trustedModules (env : Environment) (roots? : Option (Array Name)) : NameSet × Bool := Id.run do
  match roots? with
  | none =>
    let s := env.header.moduleNames.foldl (init := ({} : NameSet)) fun s m =>
      if trustedRoot.isPrefixOf m then s.insert m else s
    return (s, false)
  | some roots =>
    let mut seen : NameSet := {}
    let mut stack : Array Nat := #[]
    for r in roots do
      if trustedRoot.isPrefixOf r then
        if let some j := env.getModuleIdx? r then
          seen := seen.insert r
          stack := stack.push j.toNat
    while !stack.isEmpty do
      let i := stack.back!
      stack := stack.pop
      let data := env.header.moduleData[i]!
      for imp in data.imports do
        if trustedRoot.isPrefixOf imp.module && !seen.contains imp.module then
          seen := seen.insert imp.module
          if let some j := env.getModuleIdx? imp.module then
            stack := stack.push j.toNat
    return (seen, true)

/-- Is `n` an auto-generated equation / unfolding lemma (`f.eq_1`, `f.eq_def`, `f.eq_unfold`) of
a definition? Such names are reserved: users cannot declare them. -/
def isEqLemma (env : Environment) (n : Name) : Bool :=
  (Meta.declFromEqLikeName env n).isSome && isReservedName env n

/-- Axioms that `c` depends on (memoised across one audit run). -/
abbrev AxCache := Std.HashMap Name (Array Name)

private def mergeNames (a b : Array Name) : Array Name :=
  b.foldl (fun acc x => if acc.contains x then acc else acc.push x) a

/-- Iterative post-order computation of the axioms reachable from `root` (like
`Lean.collectAxioms`, but memoised and without deep recursion). -/
def axiomsOf (env : Environment) (root : Name) : StateM AxCache (Array Name) := do
  if let some r := (← get)[root]? then return r
  let deps (c : Name) : Array Name :=
    match env.find? c with
    | some (.axiomInfo v) => v.type.getUsedConstants
    | some (.defnInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.thmInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.opaqueInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.ctorInfo v) => v.type.getUsedConstants
    | some (.recInfo v) => v.type.getUsedConstants
    | some (.inductInfo v) => v.type.getUsedConstants
    | _ => #[]
  let mut stack : Array (Name × Bool) := #[(root, false)]
  let mut inProgress : NameSet := {}
  let mut depMap : NameMap (Array Name) := {}
  while !stack.isEmpty do
    let (c, expanded) := stack.back!
    stack := stack.pop
    if (← get).contains c then continue
    if !expanded then
      if inProgress.contains c then continue
      inProgress := inProgress.insert c
      let ds := deps c
      depMap := depMap.insert c ds
      stack := stack.push (c, true)
      for d in ds do
        unless (← get).contains d || inProgress.contains d do
          stack := stack.push (d, false)
    else
      let ds := (depMap.find? c).getD #[]
      let mut r : Array Name := #[]
      if let some (.axiomInfo _) := env.find? c then r := #[c]
      for d in ds do
        if let some rd := (← get)[d]? then r := mergeNames r rd
      modify (·.insert c r)
  return (← get)[root]?.getD #[]

/-- Non-standard axioms (including `sorryAx`) that `c` depends on. -/
def nonStandardAxioms (env : Environment) (c : Name) : StateM AxCache (Array Name) := do
  return (← axiomsOf env c).filter (!standardAxioms.contains ·)

/-- Does the kernel accept `val : ty` (both closed) as a theorem with the universe parameters
occurring in them? Uses a synchronous, discarded `addDeclCore`. -/
def kernelAccepts (ty val : Expr) : MetaM Bool := do
  let env ← getEnv
  let lps := (collectLevelParams (collectLevelParams {} ty) val).params.toList
  let name := `_sa_pass_probe ++ (← mkFreshUserName `p)
  let decl := Declaration.thmDecl { name, levelParams := lps, type := ty, value := val }
  if ty.hasFVar || val.hasFVar || ty.hasMVar || val.hasMVar then return false
  match env.addDeclCore (400000 * 1000) decl none with
  | .ok _ => return true
  | .error _ => return false

/-- Re-check a theorem's proof with the kernel (defence against `debug.skipKernelTC`). -/
def kernelRecheck (ci : ConstantInfo) : MetaM Bool := do
  match ci.value? with
  | some v => kernelAccepts ci.type v
  | none => return false

/-! ## Stable statement hash -/

/-- FNV-1a (64 bit) of a string. -/
def fnv1a64 (s : String) : UInt64 :=
  s.toUTF8.foldl (fun h b => (h ^^^ b.toUInt64) * 1099511628211) 14695981039346656037

private partial def canonLevel : Level → String
  | .zero => "0"
  | .succ l => "s(" ++ canonLevel l ++ ")"
  | .max a b => "max(" ++ canonLevel a ++ "," ++ canonLevel b ++ ")"
  | .imax a b => "imax(" ++ canonLevel a ++ "," ++ canonLevel b ++ ")"
  | .param n => "p:" ++ n.toString
  | .mvar _ => "?"

/-- Canonical serialisation of an expression: de Bruijn indices, constants with levels,
literals; binder names, binder info and metadata are ignored. -/
partial def canonExpr : Expr → String
  | .bvar i => "#" ++ toString i
  | .fvar _ => "F"
  | .mvar _ => "?"
  | .sort l => "S(" ++ canonLevel l ++ ")"
  | .const n ls => "C(" ++ n.toString ++ ";" ++ ",".intercalate (ls.map canonLevel) ++ ")"
  | .app f a => "A(" ++ canonExpr f ++ "," ++ canonExpr a ++ ")"
  | .lam _ t b _ => "L(" ++ canonExpr t ++ "," ++ canonExpr b ++ ")"
  | .forallE _ t b _ => "P(" ++ canonExpr t ++ "," ++ canonExpr b ++ ")"
  | .letE _ t v b _ => "E(" ++ canonExpr t ++ "," ++ canonExpr v ++ "," ++ canonExpr b ++ ")"
  | .lit (.natVal n) => "N" ++ toString n
  | .lit (.strVal s) => "T" ++ s.quote
  | .mdata _ e => canonExpr e
  | .proj s i e => "J(" ++ s.toString ++ "," ++ toString i ++ "," ++ canonExpr e ++ ")"

/-- Stable hash of a declaration's statement (decimal string). It changes whenever the
statement changes (up to binder names), and is stable across rebuilds. -/
def statementHash (ci : ConstantInfo) : String :=
  toString (fnv1a64 (",".intercalate (ci.levelParams.map Name.toString) ++ "|" ++
    canonExpr ci.type))

/-! ## Registry index -/

structure Index where
  claims : Array ClaimEntry
  regs : Array RegEntry
  fails : Array FailEntry
  reviews : Array ReviewEntry

def buildIndex (env : Environment) : Index := Id.run do
  let mut claims := #[]
  let mut regs := #[]
  let mut fails := #[]
  let mut reviews := #[]
  for e in getEntries env do
    match e with
    | .claim c => claims := claims.push c
    | .reg r => regs := regs.push r
    | .fail f => fails := fails.push f
    | .review r => reviews := reviews.push r
  return { claims, regs, fails, reviews }

def Index.regsOf (ix : Index) (claim : String) (kind : RegKind) : Array RegEntry :=
  ix.regs.filter fun r => r.claim == claim && r.kind == kind

/-! ## Results -/

structure CheckResult where
  kind : String
  idx : Nat
  status : String
  decl : Option Name := none
  reason : String := ""
  offenders : Array String := #[]
  bridgesUsed : Array Name := #[]
  shadowQuestion : Bool := false
  /-- backward checks: indices of shadows that the normalised proof does not use relevantly -/
  unusedShadows : Array Nat := #[]
  deriving Inhabited

structure BridgeResult where
  decl : Name
  claims : Array String
  module : Name
  hash : String
  statement : String
  status : String
  reasons : Array String := #[]
  reviewReason : String := ""
  deriving Inhabited

structure ClaimResult where
  entry : ClaimEntry
  flags : Array (String × String) := #[]
  complete : Bool := false
  incompleteReasons : Array String := #[]
  reference : Option Name := none
  shadows : Array (Nat × Name) := #[]
  forward : Array CheckResult := #[]
  backward : CheckResult := { kind := "backward", idx := 0, status := "missing" }
  implInfo : Array (Name × Name × Array Name) := #[]
  /-- shadow indices (0 = reference) whose statement is syntactically the implementation type -/
  identicalToImpl : Array Nat := #[]
  /-- reported, unscored observations `(hint, detail)` -/
  hints : Array (String × String) := #[]
  /-- shadows without trusted constants: (index, shadow, content hash, review status) -/
  trustedFree : Array (Nat × Name × String × String) := #[]
  /-- shadows that hold by reflexivity or assumption: (index, shadow, content hash, review) -/
  tautological : Array (Nat × Name × String × String) := #[]
  /-- refuted implementation hypotheses (details) -/
  refutations : Array String := #[]
  /-- satisfiability witnesses: (impl index, declaration, status) -/
  witnesses : Array (Nat × Name × String) := #[]
  deriving Inhabited

/-! ## Audit state -/

structure Ctx where
  env : Environment
  trusted : NameSet
  trustedByImport : Bool
  ix : Index
  /-- every reference and shadow of every claim -/
  registeredProps : NameSet
  /-- every registered bridge -/
  bridgeDecls : NameSet
  /-- implementation theorems of every claim (for labelling offenders) -/
  implNames : NameSet
  /-- implementation theorems of non-example claims -/
  realImplNames : NameSet

/-- A refuter: a sound theorem `∀ ys, P₁ ys → … → Pₘ ys → False`, where the conclusion may also
be `¬ P ys` or `a ≠ b` (which adds `P ys` resp. `a = b` as the last refuted premise). -/
structure RefuterInfo where
  decl : Name
  module : Name
  /-- `"trusted"` (a theorem of the trusted library) or `"alignment"` (`@[sa_refutation]`) -/
  origin : String
  /-- head constants of the refuted premises (prefilter against implementation hypotheses) -/
  heads : Array Name
  deriving Inhabited

structure St where
  axCache : AxCache := {}
  propInd : NameMap Bool := {}
  proofFieldInd : NameMap Bool := {}
  bridges : NameMap BridgeResult := {}
  refuters : Array RefuterInfo := #[]
  /-- per shadow: constants after inlining alignment helpers, and the content hash -/
  shadowContent : NameMap (NameSet × String) := {}

abbrev AuditM := ReaderT Ctx (StateRefT St MetaM)

def liftAx {α} (x : StateM AxCache α) : AuditM α := do
  let s ← get
  let (a, c) := x.run s.axCache
  modify fun s => { s with axCache := c }
  return a

/-- Is the inductive type `I` a proposition-valued inductive (`And`, `Iff`, user predicates)? -/
def isPropInductive (I : Name) : AuditM Bool := do
  if let some b := (← get).propInd.find? I then return b
  let env := (← read).env
  let b ← match env.find? I with
    | some (.inductInfo v) =>
      forallTelescopeReducing v.type fun _ body => pure body.isProp
    | _ => pure false
  modify fun s => { s with propInd := s.propInd.insert I b }
  return b

/-- Does some constructor of the data inductive `I` have a proof field? -/
def hasProofField (I : Name) : AuditM Bool := do
  if let some b := (← get).proofFieldInd.find? I then return b
  let env := (← read).env
  let mut b := false
  if let some (.inductInfo v) := env.find? I then
    for ctor in v.ctors do
      if let some (.ctorInfo cv) := env.find? ctor then
        let r ← forallTelescopeReducing cv.type fun xs _ => do
          let mut r := false
          for x in xs.extract cv.numParams xs.size do
            if ← isProp (← inferType x) then r := true
          return r
        if r then b := true
  modify fun s => { s with proofFieldInd := s.proofFieldInd.insert I b }
  return b

/-- The inductive type eliminated by a recursor-like constant, if `c` is one. -/
def eliminatedInductive? (env : Environment) (c : Name) : Option Name :=
  match env.find? c with
  | some (.recInfo v) => some v.getMajorInduct
  | _ =>
    if isAuxRecursor env c || isNoConfusion env c then some c.getPrefix
    else match c with
      | .str p s => if s == "below" || s == "ibelow" then some p else none
      | _ => none

/-! ## Bridges -/

private partial def splitAnd (e : Expr) : Array Expr :=
  match e.consumeMData.and? with
  | some (a, b) => splitAnd a ++ splitAnd b
  | none => #[e]

/-- Statement-shape problems of a bridge: `∀ xs, f xs ↔ Q xs` or `∀ xs, f xs = g xs` with `f` a
trusted definition applied to distinct bound variables, and no closed component on the
right-hand side. -/
def bridgeShapeProblems (ci : ConstantInfo) : AuditM (Array String) := do
  let ctx ← read
  forallTelescope ci.type fun xs body => do
    let body := body.consumeMData
    let (lhs, rhs, isIff) ← match body.iff? with
      | some (l, r) => pure (l, r, true)
      | none => match body.eq? with
        | some (_, l, r) => pure (l, r, false)
        | none => return #["statement is neither `∀ xs, f xs ↔ Q xs` nor `∀ xs, f xs = g xs`"]
    let mut probs := #[]
    -- `f xs = true` is accepted as the Boolean form of `f xs`
    let lhs := lhs.consumeMData
    let lhs := match lhs.eq? with
      | some (_, a, b) => if isIff && b.isConstOf ``Bool.true then a else lhs
      | none => lhs
    match lhs.getAppFn with
    | .const f _ =>
      let isDef := match ctx.env.find? f with
        | some (.defnInfo _) => true
        | _ => false
      unless isDef && ctx.trusted.contains (moduleOf ctx.env f) do
        probs := probs.push s!"left-hand side head {f} is not a definition of the trusted library"
    | _ => probs := probs.push "left-hand side is not an application of a constant"
    let args := lhs.getAppArgs
    let mut seen : Array FVarId := #[]
    for a in args do
      match a with
      | .fvar id =>
        if !xs.any (·.fvarId! == id) then
          probs := probs.push "left-hand side argument is not a bound variable"
        else if seen.contains id then
          probs := probs.push "left-hand side arguments are not distinct bound variables"
        else seen := seen.push id
      | _ => probs := probs.push "left-hand side argument is not a bound variable"
    let mentions (e : Expr) : Bool := xs.any fun x => e.containsFVar x.fvarId!
    if !mentions rhs then
      probs := probs.push "closed right-hand side (mentions no bound variable)"
    else if isIff then
      for part in splitAnd rhs do
        unless mentions part do
          probs := probs.push "closed conjunct on the right-hand side"
    return probs

/-- Search the dependencies of `c` (through trusted and alignment constants only: nothing else
can depend on them) for an implementation theorem. Returns the offending path. -/
partial def launderingPath (implSet : NameSet) (start : Name) : AuditM (Option (List Name)) := do
  let ctx ← read
  let rec go (visited : NameSet) (path : List Name) (c : Name) :
      StateT NameSet AuditM (Option (List Name)) := do
    if implSet.contains c then return some (c :: path).reverse
    if (← getThe NameSet).contains c then return none
    modifyThe NameSet (·.insert c)
    let m := moduleOf ctx.env c
    unless ctx.trusted.contains m || isAlignmentModule ctx.env m do return none
    let some ci := ctx.env.find? c | return none
    let some v := ci.value? (allowOpaque := true) | return none
    for d in v.getUsedConstants do
      if let some p ← go visited (c :: path) d then return some p
    return none
  let some ci := ctx.env.find? start | return none
  let some v := ci.value? (allowOpaque := true) | return none
  let (r, _) ← (do
      for d in v.getUsedConstants do
        if let some p ← go {} [start] d then return some p
      return none : StateT NameSet AuditM (Option (List Name))).run {}
  return r

/-- Evaluate one registered bridge. -/
def evalBridge (d : Name) : AuditM Unit := do
  let ctx ← read
  let env := ctx.env
  let bridgeRegs := ctx.ix.regs.filter (·.kind == .bridge)
  do
    let regs := bridgeRegs.filter (·.decl == d)
    let claims := regs.map (·.claim)
    let some ci := env.find? d | do
      let b : BridgeResult :=
        { decl := d, claims, module := .anonymous, hash := "", statement := "",
          status := "invalid", reasons := #["unknown constant"] }
      modify fun s => { s with bridges := s.bridges.insert d b }
    let hash := statementHash ci
    let stmt := toString (← ppExpr ci.type)
    let mut reasons : Array String := #[]
    let m := moduleOf env d
    unless isAlignmentModule env m do
      reasons := reasons.push s!"bridge declared outside the alignment library ({m})"
    for r in regs do
      unless r.module == m do
        reasons := reasons.push s!"sa_bridge applied outside the declaring module ({r.module})"
    unless ci matches .thmInfo _ do
      reasons := reasons.push "bridge is not a theorem"
    unless ← kernelRecheck ci do
      reasons := reasons.push "kernel re-check of the proof failed"
    reasons := reasons ++ (← bridgeShapeProblems ci)
    -- laundering: the bridge must not be, or depend on, an implementation theorem
    let exampleOnly := claims.all isExampleId
    let implSet := if exampleOnly then ctx.implNames else ctx.realImplNames
    if implSet.contains d then
      reasons := reasons.push "bridge is itself an implementation theorem"
    else if let some p ← launderingPath implSet d then
      reasons := reasons.push s!"depends on implementation theorem {p.getLast!} (via {" → ".intercalate (p.map toString)})"
    let bad ← liftAx (nonStandardAxioms env d)
    unless bad.isEmpty do
      reasons := reasons.push s!"uses non-standard axioms or sorry: {bad.toList}"
    -- review records
    let recs := ctx.ix.reviews.filter fun r => r.decl == d && r.kind == .bridge
    let counted := recs.filter (·.module == reviewModule)
    let rejections := counted.filter (·.rejected)
    let accepts := counted.filter (!·.rejected)
    let (status, reviewReason) :=
      if !reasons.isEmpty then ("invalid", "")
      else if let some r := rejections[0]? then ("rejected", r.reason)
      else if let some r := accepts.find? (·.hash == hash) then ("reviewed", r.reason)
      else if let some r := accepts[0]? then ("stale", s!"review hash {r.hash} does not match {hash}")
      else ("unreviewed", "")
    let ignored := recs.filter (·.module != reviewModule)
    unless ignored.isEmpty do
      reasons := reasons.push s!"note: {ignored.size} review record(s) outside {reviewModule} ignored"
    let br : BridgeResult :=
      { decl := d, claims, module := m, hash, statement := stmt, status, reasons, reviewReason }
    modify fun s => { s with bridges := s.bridges.insert d br }

/-- Evaluate every registered bridge (each with a fresh heartbeat budget). -/
def evalBridges : AuditM Unit := do
  let ctx ← read
  let bridgeRegs := ctx.ix.regs.filter (·.kind == .bridge)
  let decls := bridgeRegs.foldl (fun (a : Array Name) r => if a.contains r.decl then a else a.push r.decl) #[]
  for d in decls do
    tryCatchRuntimeEx (withCurrHeartbeats (evalBridge d)) fun e => do
      let msg ← e.toMessageData.toString
      let claims := (bridgeRegs.filter (·.decl == d)).map (·.claim)
      let b : BridgeResult :=
        { decl := d, claims, module := moduleOf ctx.env d, hash := "", statement := "",
          status := "invalid", reasons := #[s!"audit error: {msg.take 300}"] }
      modify fun s => { s with bridges := s.bridges.insert d b }

/-! ## Structural rule -/

/-- Constants to inline (walk through) instead of judging: every constant with a value declared
in the alignment library that is not a registered reference, shadow or bridge and not an
equation lemma. This covers helper lemmas and definitions, auxiliary `_proof_`/`match_`/
`_auxLemma`/`_private` declarations generated for checkers, other checkers and completeness
certificates. -/
def shouldInline (ctx : Ctx) (c : Name) : Bool :=
  isAlignmentModule ctx.env (moduleOf ctx.env c) && !ctx.registeredProps.contains c &&
    !ctx.bridgeDecls.contains c && !isEqLemma ctx.env c &&
    (match ctx.env.find? c with
     | some (.defnInfo _) | some (.thmInfo _) => true
     | _ => false)

/-- Position of a subterm of a checker proof. Types and propositions are statements and are not
judged. Proofs are judged. Data is judged, except for proofs occurring as arguments of data
terms (e.g. the positivity argument of a structure constructor): by proof irrelevance they
carry no content unless extracted, and the extraction routes (projections of proof fields,
data projections in proof positions, eliminators of data with proof fields, proof carriers) are
judged where they occur. -/
inductive Pos where
  | proof | data
  deriving BEq, Inhabited

structure Collected where
  /-- judged constants with the strongest position they occur in -/
  consts : NameMap Pos := {}
  /-- primitive projections in proof positions -/
  projs : Array (Name × Nat) := #[]
  /-- projection functions heading a proof position -/
  projHeads : NameSet := {}
  inlined : NameSet := {}
  fuel : Nat := 200000
  exhausted : Bool := false

abbrev ColM := StateRefT Collected MetaM

/-- `none` for types and propositions (statements), otherwise proof or data. -/
def posOf (e : Expr) : MetaM (Option Pos) := do
  try
    let ty ← whnfD (← inferType e)
    if ty.isSort then return none
    if ← isProp ty then return some .proof
    return some .data
  catch _ => return some .proof

private def record (c : Name) (p : Pos) : ColM Unit :=
  modify fun s =>
    let p' := match s.consts.find? c with
      | some .proof => Pos.proof
      | _ => p
    { s with consts := s.consts.insert c p' }

mutual
/-- Visit a subterm, classifying its position from its type. -/
partial def visit (ctx : Ctx) (e : Expr) : ColM Unit := do
  let s ← get
  if s.fuel == 0 then
    set { s with exhausted := true }
    return
  set { s with fuel := s.fuel - 1 }
  let some p ← posOf e | return
  visitAt ctx e p

/-- Visit a subterm known to be in position `p`. -/
partial def visitAt (ctx : Ctx) (e : Expr) (p : Pos) : ColM Unit := do
  match e with
  | .mdata _ b => visitAt ctx b p
  | .lam .. => lambdaTelescope e fun _ body => visit ctx body
  | .letE _ _ v b _ => visit ctx v; visit ctx (b.instantiate1 v)
  | .proj S i b =>
    if p == .proof then
      modify fun s =>
        let ps := if s.projs.contains (S, i) then s.projs else s.projs.push (S, i)
        { s with projs := ps }
    visit ctx b
  | .const c _ => visitHead ctx c p
  | .app .. =>
    let f := e.getAppFn
    match f with
    | .const c _ => visitHead ctx c p
    | .fvar _ => pure ()
    | _ => visit ctx f
    for a in e.getAppArgs do
      match ← posOf a with
      | none => pure ()
      | some .proof => if p == .proof then visitAt ctx a .proof
      | some .data => visitAt ctx a .data
  | _ => pure ()

/-- A constant in head position: inline it or record it. -/
partial def visitHead (ctx : Ctx) (c : Name) (p : Pos) : ColM Unit := do
  if shouldInline ctx c then
    unless (← get).inlined.contains c do
      modify fun s => { s with inlined := s.inlined.insert c }
      if let some ci := ctx.env.find? c then
        if let some v := ci.value? then visit ctx v
  else
    record c p
    if p == .proof && (ctx.env.getProjectionFnInfo? c).isSome then
      modify fun s => { s with projHeads := s.projHeads.insert c }
end

/-- Per-claim context for judging constants. -/
structure ClaimScope where
  claim : String
  own : NameSet
  usableBridges : NameSet

/-- The structure a projection function projects from. -/
def projStructure? (env : Environment) (c : Name) : Option Name := do
  let info ← env.getProjectionFnInfo? c
  let .ctorInfo cv ← env.find? info.ctorName | none
  return cv.induct

/-- `none` if the constant is allowed in a checker of the claim, otherwise the reason. -/
def classifyConst (sc : ClaimScope) (c : Name) (p : Pos) (projHead : Bool) :
    AuditM (Option String) := do
  let ctx ← read
  let env := ctx.env
  if coreLogicWhitelist.contains c then return none
  if forbiddenConsts.contains c then return some "forbidden constant"
  if forbiddenNamespaces.any (·.isPrefixOf c) then
    return some "classical reasoning / decision procedure"
  if sc.own.contains c then return none
  if ctx.bridgeDecls.contains c then
    if sc.usableBridges.contains c then return none
    let st := (← get).bridges.find? c
    let status := st.map (·.status) |>.getD "unknown"
    let inScope := st.map (·.claims.contains sc.claim) |>.getD false
    if !inScope then return some s!"bridge registered for another claim ({status})"
    return some s!"{status} bridge"
  if ctx.registeredProps.contains c then return none
  if ctx.implNames.contains c then return some "implementation theorem used outside the hypothesis"
  if isEqLemma env c then return none
  let some ci := env.find? c | return some "unknown constant"
  if let some I := eliminatedInductive? env c then
    if proofCarriers.contains I then return some "eliminator of a proof-carrying structure"
  let localDecl := ctx.trusted.contains (moduleOf env c) || isAlignmentModule env (moduleOf env c)
  if let some S := projStructure? env c then
    if proofCarriers.contains S then return some "projection of a proof-carrying structure"
    let propStruct ← isPropInductive S
    if !propStruct && projHead && p == .proof then
      return some s!"proof extracted from data (projection of {S})"
    if propStruct && localDecl then return none
  let isProof ← isProp ci.type
  if isProof then
    -- introduction and elimination rules of trusted/alignment predicates
    if localDecl then
      if let .ctorInfo cv := ci then
        if ← isPropInductive cv.induct then return none
      if let some I := eliminatedInductive? env c then
        if ← isPropInductive I then return none
    if (← Meta.isInstance c) then return none
    if ci matches .axiomInfo _ then return some "axiom"
    if ctx.trusted.contains (moduleOf env c) then return some "trusted-library theorem"
    if isAlignmentModule env (moduleOf env c) then return some "alignment-library proof"
    return some s!"library theorem ({moduleOf env c})"
  else
    if let some I := eliminatedInductive? env c then
      if !(← isPropInductive I) && (← hasProofField I) then
        return some "eliminator of data with proof fields"
    return none

/-- `none` if the primitive projection `S.i` in a proof position is allowed. -/
def classifyProj (S : Name) (_i : Nat) : AuditM (Option String) := do
  if proofCarriers.contains S then return some "projection of a proof-carrying structure"
  if ← isPropInductive S then return none
  return some s!"proof extracted from data (primitive projection of {S})"

/-- Structural audit of a checker proof: returns (uses sorry, offenders, bridges used). -/
def structuralAudit (sc : ClaimScope) (value : Expr) :
    AuditM (Bool × Array String × Array Name) := do
  let ctx ← read
  let ((), col) ← (visit ctx value).run {}
  let mut offenders := #[]
  let mut usesSorry := false
  let mut bridges := #[]
  if col.exhausted then offenders := offenders.push "<structural audit budget exhausted>"
  for (c, p) in col.consts.toList do
    if c == ``sorryAx then usesSorry := true
    if ctx.bridgeDecls.contains c then bridges := bridges.push c
    if let some why ← classifyConst sc c p (col.projHeads.contains c) then
      offenders := offenders.push s!"{c} [{why}]"
  for (S, i) in col.projs do
    if let some why ← classifyProj S i then
      offenders := offenders.push s!"proj {S}.{i} [{why}]"
  for c in col.inlined.toList do
    if let some ci := ctx.env.find? c then
      unless ci.value?.isSome do
        offenders := offenders.push s!"{c} [declaration without value in the alignment library]"
  return (usesSorry, offenders.qsort (· < ·), bridges)

/-! ## Vacuity guard -/

/-- State of the vacuity guard's normaliser: the remaining fuel and a memo table of full
normalisations (`e ↦ normAll e`, and `r ↦ r` for every result `r`). Without the table, a case
split on a proof normalises each minor premise twice (once to test whether its branch ignores the
constructor fields, once as an argument of the stuck elimination), which is exponential in the
nesting depth of `obtain ⟨…⟩ := s`. The table is sound because free variables are unique within
one normalisation run, so equal keys denote equal terms in every local context they occur in. -/
structure NormSt where
  fuel : Nat
  cache : Std.HashMap Expr Expr := {}

abbrev NormM := StateRefT NormSt MetaM

private def tick : NormM Unit := do
  let s ← get
  if s.fuel == 0 then throwError "normalisation budget exhausted"
  set { s with fuel := s.fuel - 1 }

private def ctorArg? (env : Environment) (s : Expr) (i : Nat) (ctorName? : Option Name) :
    Option Expr := Id.run do
  let .const c _ := s.getAppFn | return none
  let some (.ctorInfo cv) := env.find? c | return none
  if let some n := ctorName? then
    unless n == c do return none
  let args := s.getAppArgs
  unless args.size == cv.numParams + cv.numFields do return none
  return args[cv.numParams + i]?

/-- Logical eliminators unfolded by the normaliser (their values are small `match`es). -/
def transparentEliminators : Array Name := #[``Or.elim, ``Exists.elim, ``And.elim]

/-- Is `I` an inductive proposition (so that its eliminations are proof-irrelevant)? -/
def isPropInductiveM (I : Name) : MetaM Bool := do
  match (← getEnv).find? I with
  | some (.inductInfo v) => forallTelescopeReducing v.type fun _ b => pure b.isProp
  | _ => pure false

mutual
/-- Head normalisation: β, ζ, metadata, inlining of alignment-library helpers, unfolding of
`transparentCombinators`, `transparentEliminators` and matchers, projections (functions and
primitive) of constructors, `Eq.mpr`/`Eq.mp`/`cast` between definitionally equal types,
ι-reduction (recursors, `casesOn`) on constructors, and elimination of a proof whose branches
ignore the constructor fields (the branch replaces the whole elimination). -/
partial def headNorm (ctx : Ctx) (e : Expr) : NormM Expr := do
  tick
  let env := ctx.env
  match e with
  | .mdata _ b => headNorm ctx b
  | .letE _ _ v b _ => headNorm ctx (b.instantiate1 v)
  | .const c ls =>
    if shouldInline ctx c || transparentCombinators.contains c then
      if let some ci := env.find? c then
        if let some v := ci.value? then
          return ← headNorm ctx (v.instantiateLevelParams ci.levelParams ls)
    return e
  | .proj s i b =>
    let b' ← headNorm ctx b
    match ctorArg? env b' i none with
    | some f => headNorm ctx f
    | none => return .proj s i b'
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .lam .. => headNorm ctx (f.betaRev args.reverse)
    | .mdata _ f' => headNorm ctx (mkAppN f' args)
    | .letE .. | .proj .. =>
      let f' ← headNorm ctx f
      if f' == f then return e else headNorm ctx (mkAppN f' args)
    | .const c ls =>
      if shouldInline ctx c || transparentCombinators.contains c ||
          transparentEliminators.contains c || isMatcherCore env c then
        if let some ci := env.find? c then
          if let some v := ci.value? (allowOpaque := false) then
            return ← headNorm ctx ((v.instantiateLevelParams ci.levelParams ls).beta args)
      if (c == ``Eq.mpr || c == ``Eq.mp || c == ``cast) && args.size ≥ 4 then
        let same ← if args[0]! == args[1]! then pure true else
          (try withTransparency .default (isDefEq args[0]! args[1]!) catch _ => pure false)
        if same then
          return ← headNorm ctx (mkAppN args[3]! (args.extract 4 args.size))
      if let some info := env.getProjectionFnInfo? c then
        if args.size > info.numParams then
          let s ← headNorm ctx args[info.numParams]!
          if let some fld := ctorArg? env s info.i (some info.ctorName) then
            return ← headNorm ctx (mkAppN fld (args.extract (info.numParams + 1) args.size))
      if let some r ← irrelevantElim? ctx c args then
        return ← headNorm ctx r
      let isElim := (env.find? c matches some (.recInfo _)) || isAuxRecursor env c
      if isElim then
        let args' ← args.mapM (headNorm ctx)
        let e2 := mkAppN f args'
        let e3 ← try whnfCore e2 catch _ => pure e2
        if e3 == e2 then return e2 else return ← headNorm ctx e3
      return e
    | _ => return e
  | _ => return e

/-- `I.casesOn`/`I.rec` on a proof (`I` a proposition) with a non-dependent motive whose every
branch ignores the constructor fields: return the first branch body (proof irrelevance). -/
partial def irrelevantElim? (ctx : Ctx) (c : Name) (args : Array Expr) :
    NormM (Option Expr) := do
  let env := ctx.env
  -- layout: (inductive, params, motive position, first minor position, minor field counts,
  -- number of index+major arguments of the motive, total arity)
  let layout? : Option (Name × Nat × Nat × Array Nat × Nat × Nat) :=
    match env.find? c with
    | some (.recInfo rv) =>
      if rv.numMotives != 1 then none else
      let I := rv.getMajorInduct
      some (I, rv.numParams, rv.numParams + 1, rv.rules.toArray.map (·.nfields),
        rv.numIndices + 1, rv.numParams + 1 + rv.numMinors + rv.numIndices + 1)
    | _ =>
      if isCasesOnRecursor env c then
        match env.find? c.getPrefix with
        | some (.inductInfo iv) =>
          let nf := iv.ctors.toArray.map fun k => match env.find? k with
            | some (.ctorInfo cv) => cv.numFields
            | _ => 0
          let majorPos := iv.numParams + 1 + iv.numIndices
          some (c.getPrefix, iv.numParams, majorPos + 1, nf, iv.numIndices + 1,
            majorPos + 1 + iv.ctors.length)
        | _ => none
      else none
  let some (I, np, minorStart, nfields, motiveArity, arity) := layout? | return none
  if nfields.isEmpty || args.size < arity then return none
  unless ← isPropInductiveM I do return none
  let motive ← normAll ctx args[np]!
  let dependent ← lambdaBoundedTelescope motive motiveArity fun xs b =>
    pure (xs.size != motiveArity || xs.any fun x => b.containsFVar x.fvarId!)
  if dependent then return none
  let mut first : Option Expr := none
  for k in [0:nfields.size] do
    let minor ← normAll ctx args[minorStart + k]!
    let nf := nfields[k]!
    let r ← lambdaBoundedTelescope minor nf fun fs body => do
      if fs.size != nf then return none
      if fs.any fun x => body.containsFVar x.fvarId! then return none
      return some body
    match r with
    | none => return none
    | some body => if first.isNone then first := some body
  let some body := first | return none
  return some (mkAppN body (args.extract arity args.size))

/-- Full normalisation (head normalisation everywhere, under binders with fresh variables),
memoised in `NormSt.cache`. -/
partial def normAll (ctx : Ctx) (e : Expr) : NormM Expr := do
  if let some r := (← get).cache[e]? then return r
  let e' ← headNorm ctx e
  let r ← match e' with
    | .app .. =>
      let f := e'.getAppFn
      let f ← if f.isConst || f.isFVar then pure f else normAll ctx f
      let args ← e'.getAppArgs.mapM (normAll ctx)
      pure (mkAppN f args)
    | .lam n t b bi =>
      let t ← normAll ctx t
      withLocalDecl n bi t fun x => do
        let b ← normAll ctx (b.instantiate1 x)
        mkLambdaFVars #[x] b
    | .forallE n t b bi =>
      let t ← normAll ctx t
      withLocalDecl n bi t fun x => do
        let b ← normAll ctx (b.instantiate1 x)
        mkForallFVars #[x] b
    | .proj s i b => pure (.proj s i (← normAll ctx b))
    | _ => pure e'
  modify fun s => { s with cache := (s.cache.insert e r).insert r r }
  return r
end

/-- Does the free variable `h` occur in a proof-relevant position of `e`: not inside a type or
proposition, and not inside a proof that is an argument of a data term? -/
partial def relevantUse (h : FVarId) (e : Expr) (p : Pos := .proof) : MetaM Bool := do
  if !e.containsFVar h then return false
  match e with
  | .fvar id => return id == h
  | .mdata _ b => relevantUse h b p
  | .lam .. => lambdaTelescope e fun _ body => do
      match ← posOf body with
      | none => return false
      | some q => relevantUse h body q
  | .letE _ _ v b _ => relevantUse h (b.instantiate1 v) p
  | .proj _ _ b => relevantUse h b p
  | .app .. =>
    let f := e.getAppFn
    if let .fvar id := f then if id == h then return true
    if !f.isConst && !f.isFVar then
      if ← relevantUse h f p then return true
    for a in e.getAppArgs do
      match ← posOf a with
      | none => pure ()
      | some .proof => if p == .proof then if ← relevantUse h a .proof then return true
      | some .data => if ← relevantUse h a .data then return true
    return false
  | _ => return false

/-- The vacuity guard for a forward checker `proof : T̂ → S`. Returns `some reason` if vacuous,
`none` otherwise; throws if the guard cannot decide (reported as an audit violation). -/
def vacuityGuard (ctx : Ctx) (proof implTy S : Expr) : MetaM (Option String) := do
  withLocalDeclD `h implTy fun h => do
    let body ← (normAll ctx (mkApp proof h)).run' { fuel := normFuel }
    let lam ← mkLambdaFVars #[h] body
    unless ← kernelAccepts (← mkArrow implTy S) lam do
      throwError "normalised proof is not type-correct"
    if !body.containsFVar h.fvarId! then
      return some "the hypothesis does not occur in the normalised proof"
    unless ← relevantUse h.fvarId! body do
      return some "the hypothesis occurs only in types or in proofs inside data (proof-irrelevant)"
    withLocalDeclD `P (.sort .zero) fun P => do
      let body' ← Meta.transform body (pre := fun t => do
        if t.hasLooseBVars then return .continue
        if t == implTy then return .done P
        if (← isProp t) && (← withTransparency .default (isDefEq t implTy)) then
          return .done P
        return .continue)
      withLocalDeclD `h' P fun h' => do
        let body'' := body'.replaceFVar h h'
        let lamP ← mkLambdaFVars #[P, h'] body''
        let tyP ← mkForallFVars #[P] (← mkArrow P S)
        if ← kernelAccepts tyP lamP then
          return some "the proof still type-checks when the hypothesis is an arbitrary proposition"
        return none

/-- The vacuity guard for a backward checker `proof : S₁ → … → Sₙ → T̂` (`ty` is its statement).
Returns `(some reason, unused)` if vacuous and `(none, unused)` otherwise, where `unused` lists the
indices of shadows that the normalised proof does not use relevantly (a hint only: a shadow may be
redundant given the others). The check is `vacuous` if (i) no shadow binder occurs in a
proof-relevant position of the normalised proof, or (ii) the kernel accepts the proof after every
`sᵢ : Sᵢ` is replaced by `sᵢ : Pᵢ` for fresh `Pᵢ : Prop` (with every proposition subterm
definitionally equal to `Sᵢ` also replaced by `Pᵢ`), at type `∀ P₁ … Pₙ, P₁ → … → Pₙ → T̂`.
Like the forward guard, it fails closed: if the normaliser exhausts its budget, or the guard cannot
decide for any other reason, it throws, and the check is reported as an audit violation (the
unnormalised proof does not show whether a shadow is destructured and then ignored). -/
def backwardVacuityGuard (ctx : Ctx) (proof ty : Expr) (n : Nat) (fuel : Nat := normFuel) :
    MetaM (Option String × Array Nat) := do
  if n == 0 then return (none, #[])
  forallBoundedTelescope ty n fun ss implTy => do
    if ss.size != n then throwError "backward checker has fewer than {n} binders"
    let body ← (normAll ctx (mkAppN proof ss)).run' { fuel }
    let lam ← mkLambdaFVars ss body
    unless ← kernelAccepts ty lam do
      throwError "normalised proof is not type-correct"
    let mut unused := #[]
    for i in [0:n] do
      unless ← relevantUse ss[i]!.fvarId! body do unused := unused.push (i + 1)
    if unused.size == n then
      return (some "no shadow hypothesis occurs in a proof-relevant position of the normalised proof",
        unused)
    let shadowTys ← ss.mapM inferType
    let props := (List.range n).toArray.map fun i => (Name.mkSimple s!"P{i + 1}", mkSort .zero)
    withLocalDeclsDND props fun Ps => do
      let body' ← Meta.transform body (pre := fun t => do
        if t.hasLooseBVars then return .continue
        for i in [0:n] do
          if t == shadowTys[i]! then return .done Ps[i]!
        if ← isProp t then
          for i in [0:n] do
            if ← withTransparency .default (isDefEq t shadowTys[i]!) then return .done Ps[i]!
        return .continue)
      let hs := (List.range n).toArray.map fun i => (Name.mkSimple s!"s{i + 1}", Ps[i]!)
      withLocalDeclsDND hs fun ss' => do
        let body'' := body'.replaceFVars ss ss'
        let lamP ← mkLambdaFVars (Ps ++ ss') body''
        let tyP ← mkForallFVars Ps (← mkForallFVars ss' implTy)
        if ← kernelAccepts tyP lamP then
          return (some "the proof still type-checks when every shadow is an arbitrary proposition",
            unused)
        return (none, unused)

/-! ## Content-free shadows, refutable hypotheses and satisfiability witnesses

Defences against passes that certify nothing (found by an adversarial spot check and its
review):

* **`shadow_trusted_free`** (claim flag). A shadow whose statement mentions no constant of the
  trusted library, after inlining the alignment-library helpers it uses, is a closed statement of
  logic or arithmetic. An implementation that restates it passes without saying anything about the
  library. Constants that occur only in the domain of a data binder that the rest of the statement
  does not use do not count (`∀ p : SIRParams, 1 + 1 = 2`). The flag is lifted only by an
  independent `sa_shadow_reviewed` record (hash-pinned) in `Alignment.ReviewedBridges`, for claims
  whose source text is itself arithmetic.
* **`shadow_tautology`** (claim flag). A shadow that holds by reflexivity or by assumption at
  reducible transparency (`∀ p : SIRParams, p.β = p.β`) says nothing, whatever constants it
  mentions. Lifted by the same hash-pinned review record. Both checks are syntactic heuristics:
  they catch the cheap evasions, not every content-free statement.
* **`hypothesis_refuted`** (claim flag). If a hypothesis of an implementation theorem is refuted by
  a sound theorem of the trusted library, or by an alignment-library `@[sa_refutation]` theorem,
  the implementation (and every shadow that shares the hypothesis) is vacuously true. The audit
  builds the refutation `∀ x₁ … xₖ, False` of a prefix of the implementation's binders and has
  the kernel check it. Not applied to an implementation whose conclusion is `False` (an
  impossibility theorem refutes its own hypotheses by design), nor with the implementation itself
  as the refuter; refuters declared under `Alignment.Example` apply only to `EXAMPLE.`/`SELFTEST.`
  claims.
* **`witness_missing`** (hint) / **`witness_invalid`** (claim flag). When an implementation
  hypothesis is headed by a trusted-library predicate that every shadow also mentions, nothing in
  the checks shows that the hypothesis can hold. An `@[sa_witness "c" i]` certificate proves
  `∃ x₁ … xₖ, True` over the binders of the `i`-th implementation theorem up to its last
  hypothesis; without one the claim gets the hint `witness_missing`. -/

/-- Constants of a registered shadow's statement after inlining every alignment-library
declaration it uses (recursively), and a content hash of the shadow and the inlined helpers. -/
def shadowContent (d : Name) : AuditM (NameSet × String) := do
  if let some r := (← get).shadowContent.find? d then return r
  let env := (← read).env
  let mut seen : NameSet := {}
  let mut out : NameSet := {}
  let mut parts : Array String := #[]
  let mut stack := #[d]
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some ci := env.find? c | continue
    let inl := c == d || (isAlignmentModule env (moduleOf env c) && ci.value?.isSome)
    if inl then
      let v := ci.value?.getD (mkConst ``True)
      parts := parts.push (c.toString ++ ":" ++ canonExpr ci.type ++ "=" ++ canonExpr v)
      for x in ci.type.getUsedConstants ++ v.getUsedConstants do
        unless seen.contains x do stack := stack.push x
    else
      out := out.insert c
  let h := toString (fnv1a64 ("|".intercalate (parts.qsort (· < ·)).toList))
  modify fun s => { s with shadowContent := s.shadowContent.insert d (out, h) }
  return (out, h)

/-- Review status of a trusted-free shadow with content hash `h`. -/
def shadowReviewStatus (d : Name) (h : String) : AuditM String := do
  let ctx ← read
  let recs := ctx.ix.reviews.filter fun r => r.decl == d && r.kind == .shadow
  let counted := recs.filter (·.module == reviewModule)
  if counted.any (·.hash == h) then return "reviewed"
  if !counted.isEmpty then return "stale"
  if !recs.isEmpty then return "unreviewed (records outside Alignment.ReviewedBridges ignored)"
  return "unreviewed"

/-- The statement of the registered shadow `d` with every alignment-library definition it uses
unfolded, recursively (δ-reduction of the definitions only; the result is definitionally equal to
the shadow). -/
def inlinedShadow (d : Name) : AuditM Expr := do
  let env := (← read).env
  let some ci := env.find? d | throwError "unknown shadow {d}"
  let some v := ci.value? | throwError "shadow {d} has no value"
  let inl : Name → Bool := fun c => isAlignmentModule env (moduleOf env c) &&
    (match env.find? c with
     | some (.defnInfo _) => true
     | _ => false)
  deltaExpand v inl

/-- Constants that a statement's content depends on: every constant of the statement except
those that occur only in the domain of a binder of a non-propositional type that the rest of the
statement does not use (`∀ p : SIRParams, 1 + 1 = 2` and `∃ p : SIRParams, 1 + 1 = 2` depend on
no `SIRParams` constant). -/
partial def contentConsts (e : Expr) : StateRefT NameSet MetaM Unit := do
  match e with
  | .mdata _ b => contentConsts b
  | .const c _ => modify (·.insert c)
  | .forallE n t b bi | .lam n t b bi =>
    unless !b.hasLooseBVar 0 && !(← isProp t) do contentConsts t
    withLocalDecl n bi t fun x => contentConsts (b.instantiate1 x)
  | .letE _ _ v b _ => contentConsts (b.instantiate1 v)
  | .proj s _ b => modify (·.insert s); contentConsts b
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    -- `@Exists α p` with a predicate that ignores its argument: the domain `α` is not content
    if f.isConstOf ``Exists && args.size == 2 then
      if let .lam _ _ b _ := args[1]!.consumeMData then
        if !b.hasLooseBVar 0 && !(← isProp args[0]!) then
          modify (·.insert ``Exists)
          contentConsts args[1]!
          return
    contentConsts f
    for a in args do contentConsts a
  | _ => pure ()

/-- Is the (inlined) statement true by reflexivity or by assumption at reducible transparency,
whatever its constants mean? After its leading `∀`/`→` binders its conclusion must be `True`,
`a = b`, `a ↔ b` or `HEq a b` with `a` and `b` reducibly defeq, one of its own hypotheses, or a
conjunction of such statements. Trusted definitions are not unfolded, so `ψ.mean = κ` for
`ψ := PGFData.poisson κ _` is not a tautology even though it holds by `rfl`. -/
partial def isTautology (hyps : Array Expr) (e : Expr) : MetaM Bool :=
  forallTelescope e fun xs body => do
    let mut hyps := hyps
    for x in xs do
      if ← isProp (← inferType x) then hyps := hyps.push x
    let b := body.consumeMData
    if b.isConstOf ``True then return true
    let args := b.getAppArgs
    let sides? : Option (Expr × Expr) :=
      if b.isAppOfArity ``Eq 3 then some (args[1]!, args[2]!)
      else if b.isAppOfArity ``Iff 2 then some (args[0]!, args[1]!)
      else if b.isAppOfArity ``HEq 4 then some (args[1]!, args[3]!)
      else none
    if let some (l, r) := sides? then
      if ← withReducible (isDefEq l r) then return true
    if b.isAppOfArity ``And 2 then
      if (← isTautology hyps args[0]!) && (← isTautology hyps args[1]!) then return true
    for h in hyps do
      if ← withReducible (isDefEq (← inferType h) b) then return true
    return false

/-- An implementation theorem whose conclusion is `False` is an impossibility theorem: refuting
its hypotheses is its content, so refutation (and the satisfiability-witness hint) does not apply
to it. -/
def concludesFalse (τ : Expr) : MetaM Bool :=
  forallTelescope τ fun _ body => pure (body.consumeMData.isConstOf ``False)

/-- The head constant of a proposition (syntactic, no reduction). -/
def propHead? (t : Expr) : Option Name := t.consumeMData.getAppFn.constName?

/-- Head constants of the refuted premises of a theorem type, if it has the refuter shape
`∀ ys, P₁ → … → Pₘ → C` with `C` one of `False`, `¬ P` or `a ≠ b` and every `Pⱼ` (and `P`)
headed by a constant. -/
def refuterHeads? (ty : Expr) : MetaM (Option (Array Name)) :=
  forallTelescope ty fun xs body => do
    let body := body.consumeMData
    let extra? : Option (Option Name) :=
      if body.isConstOf ``False then some none
      else if body.isAppOfArity ``Not 1 then some (propHead? body.appArg!)
      else if body.isAppOfArity ``Ne 3 then some (some ``Eq)
      else none
    let some extra := extra? | return none
    let mut heads := #[]
    for x in xs do
      let t ← inferType x
      if ← isProp t then
        let some c := propHead? t | return none
        heads := heads.push c
    if body.isConstOf ``False then return some heads
    let some c := extra | return none
    return some (heads.push c)

/-- Collect the refuters: sound trusted-library theorems of the refuter shape, and the
alignment-library theorems tagged `@[sa_refutation]` (same shape, sound, kernel re-checked).
Returns the JSON list of refuters with their status. -/
def collectRefuters : AuditM (Array Json) := do
  let ctx ← read
  let env := ctx.env
  let trustedThms : Array Name := env.constants.map₁.fold (init := #[]) fun acc n ci =>
    match ci with
    | .thmInfo _ => if ctx.trusted.contains (moduleOf env n) then acc.push n else acc
    | _ => acc
  let regs := ctx.ix.regs.filter (·.kind == .refutation)
  let cands := trustedThms.map (·, "trusted") ++ regs.map fun r => (r.decl, "alignment")
  let mut out := #[]
  let mut js := #[]
  for (n, origin) in cands do
    let mod := toString (moduleOf env n)
    let some ci := env.find? n | do
      js := js.push (Json.mkObj [("decl", toString n), ("module", mod), ("origin", origin),
        ("status", "invalid"), ("reasons", Json.arr #["unknown constant"])])
      continue
    let heads? ← try refuterHeads? ci.type catch _ => pure none
    let some heads := heads? | do
      if origin == "alignment" then
        js := js.push (Json.mkObj [("decl", toString n), ("module", mod), ("origin", origin),
          ("status", "invalid"),
          ("reasons", Json.arr #["statement is not `∀ ys, P₁ → … → Pₘ → False` (or `→ ¬ P`, `→ a ≠ b`)"])])
      continue
    let mut reasons : Array String := #[]
    unless ci matches .thmInfo _ do reasons := reasons.push "not a theorem"
    let bad ← liftAx (nonStandardAxioms env n)
    unless bad.isEmpty do reasons := reasons.push s!"uses non-standard axioms or sorry: {bad.toList}"
    if origin == "alignment" then
      unless isAlignmentModule env (moduleOf env n) do
        reasons := reasons.push "declared outside the alignment library"
      for r in regs.filter (·.decl == n) do
        unless r.module == moduleOf env n do
          reasons := reasons.push s!"sa_refutation applied outside the declaring module ({r.module})"
      unless ← kernelRecheck ci do reasons := reasons.push "kernel re-check of the proof failed"
    if heads.isEmpty then reasons := reasons.push "proves False without premises (inconsistent)"
    js := js.push (Json.mkObj [("decl", toString n), ("module", toString (moduleOf env n)),
      ("origin", origin), ("status", if reasons.isEmpty then "valid" else "invalid"),
      ("auxiliary", n.isInternal),
      ("reasons", Json.arr (reasons.map Json.str)),
      ("heads", Json.arr (heads.map (Json.str ∘ toString)))])
    if reasons.isEmpty then
      out := out.push { decl := n, module := moduleOf env n, origin, heads }
  modify fun s => { s with refuters := out }
  return js

/-- Try to refute the hypotheses of the implementation type `τ` with refuter `r`: match every
refuted premise of `r` against a hypothesis of `τ` (by unification), build the proof
`∀ x₁ … xₖ, False` for the shortest prefix `x₁ … xₖ` of `τ`'s binders it needs, and have the kernel
check it. Returns a description of the refutation, or `none`. -/
def tryRefute (τ : Expr) (r : RefuterInfo) : MetaM (Option String) := do
  let some rci := (← getEnv).find? r.decl | return none
  forallTelescope τ fun xs _ => do
    let hyps ← xs.filterM fun x => do isProp (← inferType x)
    if hyps.isEmpty then return none
    let s ← saveState
    try
      let lvls ← mkFreshLevelMVars rci.levelParams.length
      let rty := rci.type.instantiateLevelParams rci.levelParams lvls
      let (ms, _, body) ← forallMetaTelescope rty
      let body := body.consumeMData
      let mut premises : Array (Option Expr × Expr) := #[]
      for m in ms do
        let t ← inferType m
        if ← isProp t then premises := premises.push (some m, t)
      if body.isAppOfArity ``Not 1 then premises := premises.push (none, body.appArg!)
      else if body.isAppOfArity ``Ne 3 then
        let args := body.getAppArgs
        premises := premises.push (none, ← mkEq args[1]! args[2]!)
      let mut extraProof : Option Expr := none
      let mut used : Array Expr := #[]
      for (m?, t0) in premises do
        let t ← instantiateMVars t0
        let some hc := propHead? t | do s.restore; return none
        let mut found := false
        for h in hyps do
          let ht ← inferType h
          unless propHead? ht == some hc do continue
          let s2 ← saveState
          let ok ← try isDefEq t ht catch _ => pure false
          if ok then
            match m? with
            | some m =>
              if ← isDefEq m h then
                found := true; used := used.push h; break
              else s2.restore
            | none => extraProof := some h; found := true; used := used.push h; break
          else s2.restore
        unless found do
          s.restore; return none
      -- remaining instance arguments of the refuter
      for m in ms do
        let m' ← instantiateMVars m
        if m'.isMVar then
          let t ← instantiateMVars (← inferType m')
          if (← isClass? t).isSome then
            if let some inst ← synthInstance? t then discard <| isDefEq m' inst
      let mut proof := mkAppN (mkConst r.decl lvls) ms
      if let some h := extraProof then proof := mkApp proof h
      let proofI ← instantiateMVars proof
      if proofI.hasMVar || proofI.hasLevelMVar then
        s.restore; return none
      let mut k := 0
      for i in [0:xs.size] do
        if proofI.containsFVar xs[i]!.fvarId! then k := i + 1
      let pre := xs.extract 0 k
      let lam ← mkLambdaFVars pre proofI
      let ty ← mkForallFVars pre (mkConst ``False)
      let ok ← kernelAccepts ty lam
      let hs ← used.mapM fun h => do
        return s!"{← h.fvarId!.getUserName} : {← ppExpr (← inferType h)}"
      s.restore
      if ok then
        return some s!"hypothesis {", ".intercalate hs.toList} refuted by {r.decl} ({r.origin})"
      return none
    catch _ =>
      s.restore
      return none

/-- Head constants of the hypotheses of an implementation type. -/
def hypHeads (τ : Expr) : MetaM (Array Name) :=
  forallTelescope τ fun xs _ => do
    let mut out := #[]
    for x in xs do
      let t ← inferType x
      if ← isProp t then
        if let some c := propHead? t then
          unless out.contains c do out := out.push c
    return out

/-- `∃ x₁ … xₖ, True` over the binders of `τ` up to its last hypothesis (`none` if `τ` has no
hypothesis). This is the statement of an `@[sa_witness]` certificate. -/
def witnessType? (τ : Expr) : MetaM (Option Expr) :=
  forallTelescope τ fun xs _ => do
    let mut last : Option Nat := none
    for i in [0:xs.size] do
      if ← isProp (← inferType xs[i]!) then last := some i
    let some k := last | return none
    let mut body : Expr := mkConst ``True
    for i in (List.range (k + 1)).reverse do
      let x := xs[i]!
      let t ← inferType x
      let u ← getLevel t
      body := mkApp2 (mkConst ``Exists [u]) t (← mkLambdaFVars #[x] body)
    return some body

/-! ## Claims -/

/-- Is `ty` literally `A → B` (non-dependent)? -/
private def arrow? (ty : Expr) : Option (Expr × Expr) :=
  match ty.consumeMData with
  | .forallE _ a b _ => if b.hasLooseBVars then none else some (a, b)
  | _ => none

/-- Is `e` the constant `S` (with universe levels that are distinct parameters, if any)? -/
private def isShadowConst (e : Expr) (S : Name) : Bool :=
  match e.consumeMData with
  | .const n ls => n == S && ls.all (·.isParam) && ls.eraseDups.length == ls.length
  | _ => false

/-- Peel `k` non-dependent arrows whose domains are the given constants. -/
private def peelArrows (ty : Expr) (doms : Array Name) : Option Expr := Id.run do
  let mut t := ty
  for d in doms do
    match arrow? t with
    | some (a, b) => if isShadowConst a d then t := b else return none
    | none => return none
  return some t.consumeMData

/-- Is the (theorem) constant a sound certificate: a theorem without non-standard axioms? -/
def certificateProblems (c : Name) : AuditM (Array String) := do
  let env := (← read).env
  let some ci := env.find? c | return #["unknown constant"]
  let mut probs := #[]
  unless ci matches .thmInfo _ do probs := probs.push s!"{c} is not a theorem"
  unless ← kernelRecheck ci do probs := probs.push s!"{c}: kernel re-check of the proof failed"
  let bad ← liftAx (nonStandardAxioms env c)
  unless bad.isEmpty do probs := probs.push s!"{c} uses non-standard axioms or sorry: {bad.toList}"
  return probs

/-- Evaluate one checker. -/
def evalChecker (c : ClaimEntry) (sc : ClaimScope) (kind : String) (idx : Nat)
    (regs : Array RegEntry) (fails : Array FailEntry) (implTy? : Option Expr)
    (expectedOk : Expr → Bool) (expectedDescr : String) (isForward : Bool)
    (nShadows : Nat := 0) :
    AuditM (CheckResult × Array (String × String)) := do
  let ctx ← read
  let env := ctx.env
  let base : CheckResult := { kind, idx, status := "missing" }
  let mut flags := #[]
  if regs.size > 1 then
    flags := flags.push ("duplicate", s!"{regs.size} {kind} checkers for index {idx}")
  if let some f := fails[0]? then
    if !regs.isEmpty then
      flags := flags.push ("duplicate", s!"{kind} {idx} has both a checker and an sa_fail record")
    let sq := f.reason.startsWith "SHADOW?:"
    let r : CheckResult := { base with status := "fail", reason := f.reason, shadowQuestion := sq }
    return (r, flags)
  let some r := regs[0]? | return (base, flags)
  let d := r.decl
  let res := { base with decl := some d }
  let some ci := env.find? d | return ({ res with status := "fail", reason := "unknown constant" }, flags)
  if ci matches .axiomInfo _ then
    return ({ res with status := "audit_violation", offenders := #[s!"{d} [checker is an axiom]"] }, flags)
  unless ci matches .thmInfo _ do
    return ({ res with status := "fail", reason := "checker is not a theorem" }, flags)
  if moduleOf env d != c.module || r.module != c.module then
    let o := s!"{d} [checker not declared in the claim module {c.module}]"
    return ({ res with status := "audit_violation", offenders := #[o] }, flags)
  let some implTy := implTy? |
    return ({ res with status := "fail", reason := "no implementation type (gap or unknown impl)" }, flags)
  unless expectedOk ci.type do
    let found := toString (← ppExpr ci.type)
    return ({ res with status := "fail", reason := s!"statement is not {expectedDescr}; found: {found}" }, flags)
  let some v := ci.value? | return ({ res with status := "fail", reason := "no proof value" }, flags)
  unless ← kernelRecheck ci do
    return ({ res with status := "audit_violation",
                       offenders := #[s!"{d} [kernel re-check of the proof failed]"] }, flags)
  let (usesSorry, offenders, bridges) ← structuralAudit sc v
  let res := { res with bridgesUsed := bridges }
  if usesSorry then
    return ({ res with status := "sorry", offenders }, flags)
  unless offenders.isEmpty do
    return ({ res with status := "audit_violation", offenders }, flags)
  -- the shadow with the universe levels used by the checker's own statement
  let S? := if isForward then (arrow? ci.type).map (·.2) else none
  if let some S := S? then
    let vac ← try vacuityGuard ctx v implTy S
      catch e => do
        let msg ← e.toMessageData.toString
        pure (some s!"GUARD-ERROR: {msg}")
    if let some why := vac then
      if why.startsWith "GUARD-ERROR: " then
        let o := s!"<vacuity guard could not decide: {why.drop 13}>"
        return ({ res with status := "audit_violation", offenders := #[o] }, flags)
      return ({ res with status := "vacuous", reason := why }, flags)
  if !isForward then
    -- backward checks are vacuity-guarded too: the shadows must be used
    let r ← try (do
        let (why, unused) ← backwardVacuityGuard ctx v ci.type nShadows
        pure (Except.ok (why, unused)))
      catch e => do pure (Except.error (← e.toMessageData.toString))
    match r with
    | .error msg =>
      let o := s!"<vacuity guard could not decide: {msg}>"
      return ({ res with status := "audit_violation", offenders := #[o] }, flags)
    | .ok (some why, unused) =>
      return ({ res with status := "vacuous", reason := why, unusedShadows := unused }, flags)
    | .ok (none, unused) =>
      return ({ res with status := "pass", unusedShadows := unused }, flags)
  return ({ res with status := "pass" }, flags)

/-- Run one check with a fresh heartbeat budget; any error (including a timeout) becomes an
`audit_violation` of that check. -/
def guarded (kind : String) (idx : Nat) (x : AuditM (CheckResult × Array (String × String))) :
    AuditM (CheckResult × Array (String × String)) :=
  tryCatchRuntimeEx (withCurrHeartbeats x) fun e => do
    let msg ← e.toMessageData.toString
    return ({ kind, idx, status := "audit_violation",
              offenders := #[s!"<audit error: {msg.take 300}>"] }, #[])

/-- Audit one claim registration. -/
def evalClaim (c : ClaimEntry) : AuditM ClaimResult := do
  let ctx ← read
  let env := ctx.env
  let ix := ctx.ix
  let mut flags : Array (String × String) := #[]
  let mut res : ClaimResult := { entry := c }
  unless validId c.id do flags := flags.push ("invalid_id", s!"\"{c.id}\" does not match [A-Za-z0-9._-]+")
  let claimModuleOk := if isExampleId c.id then (`Alignment.Example).isPrefixOf c.module
    else c.module == Name.mkStr `Alignment.Checks c.group
  unless claimModuleOk do
    flags := flags.push ("module_mismatch",
      s!"sa_claim is in {c.module}, expected {Name.mkStr `Alignment.Checks c.group}")
  let dups := ix.claims.filter (·.id == c.id)
  if dups.size > 1 then flags := flags.push ("duplicate", s!"sa_claim registered {dups.size} times")
  -- implementation theorems
  if c.impls.isEmpty then flags := flags.push ("gap", "no implementation theorem")
  let mut implInfo := #[]
  for n in c.impls do
    match env.find? n with
    | none => flags := flags.push ("impl_untrusted", s!"{n}: unknown constant")
    | some ci =>
      let m := moduleOf env n
      unless ctx.trusted.contains m do
        flags := flags.push ("impl_untrusted", s!"{n} is declared in {m}, not in the trusted library")
      match ci with
      | .thmInfo _ => pure ()
      | .axiomInfo _ => flags := flags.push ("impl_unsound", s!"{n} is an axiom")
      | _ => flags := flags.push ("impl_untrusted", s!"{n} is not a theorem")
      let axs ← liftAx (axiomsOf env n)
      let bad := axs.filter (!standardAxioms.contains ·)
      let bad := bad.filter (· != n)
      unless bad.isEmpty do
        flags := flags.push ("impl_unsound", s!"{n} depends on {bad.toList}")
      implInfo := implInfo.push (n, m, axs)
  res := { res with implInfo }
  let implTy? := match implTypeOf env c.impls with
    | .ok t => some t
    | .error _ => none
  -- shadow set
  let refs := ix.regsOf c.id .reference
  let shadowRegs := ix.regsOf c.id .shadow
  let expectedShadowModule : Name → Bool := fun m =>
    if isExampleId c.id then (`Alignment.Example).isPrefixOf m
    else m == Name.mkStr `Alignment.Shadows c.group
  let mut incomplete : Array String := #[]
  let isPropDef (d : Name) : Bool := match env.find? d with
    | some (.defnInfo v) => v.type.consumeMData.isProp
    | _ => false
  let checkPropReg (r : RegEntry) (what : String) : Array (String × String) := Id.run do
    let mut fl := #[]
    unless isPropDef r.decl do
      fl := fl.push ("shadow_mismatch", s!"{what} {r.decl} is not a `def … : Prop`")
    let m := moduleOf env r.decl
    unless r.module == m do
      fl := fl.push ("shadow_mismatch", s!"{what} {r.decl}: attribute applied outside its module")
    unless expectedShadowModule m do
      let want := if isExampleId c.id then "Alignment.Example.*"
        else toString (Name.mkStr `Alignment.Shadows c.group)
      fl := fl.push ("shadow_mismatch", s!"{what} {r.decl} is declared in {m}, expected {want}")
    let others := ix.regs.filter fun o =>
      o.decl == r.decl && (o.kind == .shadow || o.kind == .reference) &&
        (o.claim != r.claim || o.idx != r.idx || o.kind != r.kind)
    unless others.isEmpty do
      fl := fl.push ("shadow_mismatch", s!"{r.decl} is registered more than once as a shadow/reference")
    return fl
  match refs.size with
  | 0 => incomplete := incomplete.push "no sa_reference"
  | 1 => pure ()
  | k => flags := flags.push ("shadow_mismatch", s!"{k} sa_reference declarations")
  for r in refs do flags := flags ++ checkPropReg r "reference"
  for r in shadowRegs do flags := flags ++ checkPropReg r "shadow"
  let idxs := shadowRegs.foldl (fun (a : Array Nat) r => if a.contains r.idx then a else a.push r.idx) #[]
  let idxs := idxs.qsort (· < ·)
  let n := idxs.size
  if n == 0 then incomplete := incomplete.push "no shadows"
  unless idxs == (List.range n).toArray.map (· + 1) do
    flags := flags.push ("shadow_mismatch", s!"shadow indices {idxs.toList} are not 1..{n}")
  for i in idxs do
    let k := (shadowRegs.filter (·.idx == i)).size
    if k > 1 then flags := flags.push ("shadow_mismatch", s!"{k} shadows with index {i}")
  let shadowOf (i : Nat) : Option Name := (shadowRegs.find? (·.idx == i)).map (·.decl)
  let shadows := idxs.filterMap fun i => (shadowOf i).map (i, ·)
  let T? := refs[0]?.map (·.decl)
  res := { res with reference := T?, shadows }
  -- informational: statements that are literally the implementation type (weak evidence)
  if let some it := implTy? then
    let same (d : Name) : Bool := match env.find? d with
      | some (.defnInfo v) => v.value.consumeMData == it.consumeMData
      | _ => false
    let mut ident := #[]
    if let some T := T? then if same T then ident := ident.push 0
    for (i, S) in shadows do if same S then ident := ident.push i
    res := { res with identicalToImpl := ident }
  -- content-free shadows: no trusted constant in the content of the statement after inlining
  -- alignment helpers (constants that occur only in the domain of an unused data binder do not
  -- count), or true by reflexivity/assumption at reducible transparency
  let mut shadowConstSets : Array NameSet := #[]
  let mut trustedFree := #[]
  let mut tautological := #[]
  for (i, S) in shadows do
    let (cs, h) ← shadowContent S
    shadowConstSets := shadowConstSets.push cs
    let (content, taut) ← try (do
        let e ← inlinedShadow S
        let ((), content) ← (contentConsts e).run {}
        pure (content, ← isTautology #[] e))
      catch _ => pure (cs, false)
    let hasTrusted := content.toList.any fun x => ctx.trusted.contains (moduleOf env x)
    if !hasTrusted || taut then
      let st ← shadowReviewStatus S h
      unless hasTrusted do
        trustedFree := trustedFree.push (i, S, h, st)
        unless st == "reviewed" do
          flags := flags.push ("shadow_trusted_free",
            s!"S{i} ({S}) mentions no trusted-library constant after inlining alignment helpers, " ++
            s!"except in the domains of unused binders (content hash {h}; review: {st})")
      if taut then
        tautological := tautological.push (i, S, h, st)
        unless st == "reviewed" do
          flags := flags.push ("shadow_tautology",
            s!"S{i} ({S}) holds by reflexivity or assumption at reducible transparency after " ++
            s!"inlining alignment helpers (content hash {h}; review: {st})")
  res := { res with trustedFree, tautological }
  -- refutable implementation hypotheses (not for impossibility theorems, whose content is the
  -- refutation; refuters declared by the worked example / self-test apply only to their claims)
  let mut refutations := #[]
  let mut refutedImpls : Array Name := #[]
  let mut impossible : Array Name := #[]
  let mut hints : Array (String × String) := #[]
  let exampleRoot : Name := `Alignment.Example
  for n in c.impls do
    let some ci := env.find? n | continue
    if ← (try concludesFalse ci.type catch _ => pure false) then
      impossible := impossible.push n
      continue
    let hh ← try hypHeads ci.type catch _ => pure #[]
    if hh.isEmpty then continue
    for r in (← get).refuters do
      if r.decl == n then continue
      if exampleRoot.isPrefixOf r.module && !isExampleId c.id then continue
      unless r.heads.all hh.contains do continue
      match ← (try tryRefute ci.type r catch _ => pure none) with
      | some d =>
        refutations := refutations.push s!"{n}: {d}"
        unless refutedImpls.contains n do refutedImpls := refutedImpls.push n
      | none => pure ()
  unless refutations.isEmpty do
    flags := flags.push ("hypothesis_refuted", "; ".intercalate refutations.toList)
  res := { res with refutations }
  -- satisfiability witnesses
  let mut witnessed : Array Nat := #[]
  let mut witnesses := #[]
  for r in ix.regsOf c.id .witness do
    let mut probs : Array String := #[]
    unless r.module == moduleOf env r.decl && r.module == c.module do
      probs := probs.push s!"not declared in the claim module {c.module}"
    if r.idx == 0 || r.idx > c.impls.size then
      probs := probs.push s!"implementation index {r.idx} is not in 1..{c.impls.size}"
    else
      let impl := c.impls[r.idx - 1]!
      match env.find? impl, env.find? r.decl with
      | some ici, some wci =>
        probs := probs ++ (← certificateProblems r.decl)
        match ← (try witnessType? ici.type catch _ => pure none) with
        | none => probs := probs.push s!"{impl} has no hypothesis to witness"
        | some wt =>
          match wci.value? with
          | some v =>
            unless ← kernelAccepts wt v do
              probs := probs.push
                s!"statement is not `∃ x₁ … xₖ, True` over the binders of {impl} up to its last hypothesis"
          | none => probs := probs.push "no proof value"
      | _, _ => probs := probs.push "unknown constant"
    if probs.isEmpty then
      witnessed := witnessed.push r.idx
      witnesses := witnesses.push (r.idx, r.decl, "valid")
    else
      witnesses := witnesses.push (r.idx, r.decl, "invalid")
      flags := flags.push ("witness_invalid", s!"{r.decl}: {"; ".intercalate probs.toList}")
  res := { res with witnesses }
  -- hint: hypotheses headed by a trusted predicate that every shadow shares, without a witness
  if !shadowConstSets.isEmpty then
    for i in [0:c.impls.size] do
      let n := c.impls[i]!
      if refutedImpls.contains n || impossible.contains n || witnessed.contains (i + 1) then continue
      let some ci := env.find? n | continue
      let hh ← try hypHeads ci.type catch _ => pure #[]
      let shared := hh.filter fun hd =>
        ctx.trusted.contains (moduleOf env hd) && shadowConstSets.all (·.contains hd)
      unless shared.isEmpty do
        hints := hints.push ("witness_missing",
          s!"impl {i + 1} ({n}): its hypotheses headed by {shared.toList} are also assumed by " ++
          s!"every shadow, and no @[sa_witness \"{c.id}\" {i + 1}] certificate shows they can hold")
  -- completeness certificates
  let refFwds := ix.regsOf c.id .refForward
  let completes := ix.regsOf c.id .complete
  for r in refFwds do
    unless idxs.contains r.idx do
      flags := flags.push ("shadow_mismatch", s!"sa_ref_forward for unknown shadow index {r.idx}")
  if let some T := T? then
    for (i, S) in shadows do
      match refFwds.filter (·.idx == i) with
      | #[] => incomplete := incomplete.push s!"no sa_ref_forward {i}"
      | #[r] =>
        let ok : Bool := match env.find? r.decl with
          | some ci => match arrow? ci.type with
            | some (a, b) => isShadowConst a T && isShadowConst b S
            | none => false
          | none => false
        unless ok do incomplete := incomplete.push s!"sa_ref_forward {i} ({r.decl}) is not `T → S{i}`"
        incomplete := incomplete ++ (← certificateProblems r.decl)
      | rs => flags := flags.push ("shadow_mismatch", s!"{rs.size} sa_ref_forward certificates for index {i}")
    match completes with
    | #[] => incomplete := incomplete.push "no sa_complete"
    | #[r] =>
      let ok : Bool := match env.find? r.decl with
        | some ci => match peelArrows ci.type (shadows.map (·.2)) with
          | some t => isShadowConst t T
          | none => false
        | none => false
      unless ok do incomplete := incomplete.push s!"sa_complete ({r.decl}) is not `S1 → … → S{n} → T`"
      incomplete := incomplete ++ (← certificateProblems r.decl)
    | rs => flags := flags.push ("shadow_mismatch", s!"{rs.size} sa_complete certificates")
  for r in refFwds ++ completes do
    unless r.module == moduleOf env r.decl && expectedShadowModule (moduleOf env r.decl) do
      flags := flags.push ("shadow_mismatch", s!"certificate {r.decl} is not declared in the shadow module")
  if !incomplete.isEmpty then flags := flags.push ("incomplete", "; ".intercalate incomplete.toList)
  res := { res with complete := incomplete.isEmpty, incompleteReasons := incomplete }
  -- checkers
  let own := (refs ++ shadowRegs).foldl (init := ({} : NameSet)) fun s r =>
    if isPropDef r.decl then s.insert r.decl else s
  let usable := (← get).bridges.foldl (init := ({} : NameSet)) fun s d b =>
    if b.status == "reviewed" && b.claims.contains c.id then s.insert d else s
  let sc : ClaimScope := { claim := c.id, own, usableBridges := usable }
  let fwdRegs := ix.regsOf c.id .forward
  let fwdFails := ix.fails.filter fun f => f.claim == c.id && f.target != .backward
  for r in fwdRegs do
    unless idxs.contains r.idx do
      flags := flags.push ("shadow_mismatch", s!"forward checker {r.decl} for unknown index {r.idx}")
  for f in fwdFails do
    if let .forward i := f.target then
      unless idxs.contains i do
        flags := flags.push ("shadow_mismatch", s!"sa_fail_forward for unknown index {i}")
  let mut fwd := #[]
  for (i, S) in shadows do
    let regs := fwdRegs.filter (·.idx == i)
    let fails := fwdFails.filter (·.target == .forward i)
    let expectedOk : Expr → Bool := fun ty => match implTy?, arrow? ty with
      | some it, some (a, b) => a.consumeMData == it && isShadowConst b S
      | _, _ => false
    let (r, fl) ← guarded "forward" i
      (evalChecker c sc "forward" i regs fails implTy? expectedOk s!"`T̂ → {S}`" true)
    fwd := fwd.push r
    flags := flags ++ fl
  res := { res with forward := fwd }
  let bwdRegs := ix.regsOf c.id .backward
  let bwdFails := ix.fails.filter fun f => f.claim == c.id && f.target == .backward
  let expectedB : Expr → Bool := fun ty => match implTy?, peelArrows ty (shadows.map (·.2)) with
    | some it, some t => t == it
    | _, _ => false
  let (b, fl) ← guarded "backward" 0
    (evalChecker c sc "backward" 0 bwdRegs bwdFails implTy? expectedB "`S1 → … → Sn → T̂`" false
      shadows.size)
  flags := flags ++ fl
  if b.status == "pass" && !b.unusedShadows.isEmpty then
    hints := hints.push ("backward_unused_shadows",
      s!"the backward checker does not use shadow(s) {b.unusedShadows.toList} (redundant given the others?)")
  return { res with backward := b, flags, hints }

/-! ## JSON -/

private def jStrs (xs : Array String) : Json := Json.arr (xs.map Json.str)
private def jNames (xs : Array Name) : Json := Json.arr (xs.map (Json.str ∘ toString))

def CheckResult.toJson (r : CheckResult) : Json :=
  Json.mkObj [("kind", r.kind), ("idx", r.idx), ("status", r.status),
    ("decl", match r.decl with | some d => Json.str (toString d) | none => Json.null),
    ("reason", r.reason), ("offenders", jStrs r.offenders), ("bridges_used", jNames r.bridgesUsed),
    ("shadow_question", r.shadowQuestion),
    ("unused_shadows", Json.arr (r.unusedShadows.map fun (i : Nat) => (i : Json)))]

def BridgeResult.toJson (b : BridgeResult) : Json :=
  Json.mkObj [("decl", toString b.decl), ("claims", jStrs b.claims), ("module", toString b.module),
    ("hash", b.hash), ("statement", b.statement), ("status", b.status),
    ("reasons", jStrs b.reasons), ("review_reason", b.reviewReason)]

def ClaimResult.toJson (r : ClaimResult) : Json :=
  let c := r.entry
  Json.mkObj [("id", c.id), ("group", c.group), ("required", c.required), ("text", c.text),
    ("impl", jNames c.impls), ("module", toString c.module),
    ("lean_flags", Json.arr (r.flags.map fun (f, d) => Json.mkObj [("flag", f), ("detail", d)])),
    ("complete", r.complete), ("incomplete_reasons", jStrs r.incompleteReasons),
    ("reference", match r.reference with | some d => Json.str (toString d) | none => Json.null),
    ("shadows", Json.arr (r.shadows.map fun (i, d) => Json.mkObj [("idx", i), ("decl", toString d)])),
    ("n_shadows", r.shadows.size),
    ("identical_to_impl", Json.arr (r.identicalToImpl.map fun (i : Nat) => (i : Json))),
    ("hints", Json.arr (r.hints.map fun (h, d) => Json.mkObj [("hint", h), ("detail", d)])),
    ("trusted_free_shadows", Json.arr (r.trustedFree.map fun (i, d, h, st) =>
      Json.mkObj [("idx", i), ("decl", toString d), ("hash", h), ("review", st)])),
    ("tautological_shadows", Json.arr (r.tautological.map fun (i, d, h, st) =>
      Json.mkObj [("idx", i), ("decl", toString d), ("hash", h), ("review", st)])),
    ("refutations", jStrs r.refutations),
    ("witnesses", Json.arr (r.witnesses.map fun (i, d, st) =>
      Json.mkObj [("impl", i), ("decl", toString d), ("status", st)])),
    ("forward", Json.arr (r.forward.map CheckResult.toJson)),
    ("backward", r.backward.toJson),
    ("impl_info", Json.arr (r.implInfo.map fun (n, m, axs) =>
      Json.mkObj [("name", toString n), ("module", toString m), ("axioms", jNames axs)]))]

/-! ## Driver -/

def mkCtx (env : Environment) (roots? : Option (Array Name)) : Ctx :=
  let ix := buildIndex env
  let (trusted, byImport) := trustedModules env roots?
  -- only genuine `def … : Prop` declarations count as registered propositions: anything else
  -- registered as a shadow (e.g. a theorem) is inlined and judged like any helper
  let isPropDef (d : Name) : Bool := match env.find? d with
    | some (.defnInfo v) => v.type.consumeMData.isProp
    | _ => false
  let registeredProps := ix.regs.foldl (init := ({} : NameSet)) fun s r =>
    if (r.kind == .reference || r.kind == .shadow) && isPropDef r.decl then s.insert r.decl else s
  let bridgeDecls := ix.regs.foldl (init := ({} : NameSet)) fun s r =>
    if r.kind == .bridge then s.insert r.decl else s
  let implNames := ix.claims.foldl (init := ({} : NameSet)) fun s c => c.impls.foldl (·.insert ·) s
  let realImplNames := ix.claims.foldl (init := ({} : NameSet)) fun s c =>
    if isExampleId c.id then s else c.impls.foldl (·.insert ·) s
  { env, trusted, trustedByImport := byImport, ix, registeredProps, bridgeDecls,
    implNames, realImplNames }

/-- Run the whole audit and return the JSON document. -/
def runAudit (only? : Option String := none) : MetaM Json := do
  let env ← getEnv
  let roots? ← rootImports
  let ctx := mkCtx env roots?
  let act : AuditM Json := do
    evalBridges
    let refutersJ ← collectRefuters
    let mut claimsJ := #[]
    let mut seen : Array String := #[]
    for c in ctx.ix.claims do
      if let some o := only? then unless c.id == o do continue
      -- duplicates are reported once, from the first registration
      if seen.contains c.id then continue
      seen := seen.push c.id
      let r ← tryCatchRuntimeEx (withCurrHeartbeats (evalClaim c)) fun e => do
        let msg ← e.toMessageData.toString
        pure { entry := c, flags := #[("audit_error", (msg.take 300).toString)] }
      claimsJ := claimsJ.push r.toJson
    let claimIds := ctx.ix.claims.map (·.id)
    let orphans := ctx.ix.regs.filter fun r => r.kind.hasClaim && !claimIds.contains r.claim
    let orphanFails := ctx.ix.fails.filter (!claimIds.contains ·.claim)
    let bridgesJ := (← get).bridges.foldl (init := #[]) fun a _ b => a.push b.toJson
    let reviewsJ := ctx.ix.reviews.map fun r =>
      Json.mkObj [("decl", toString r.decl), ("hash", r.hash), ("reason", r.reason),
        ("rejected", r.rejected), ("module", toString r.module),
        ("kind", match r.kind with | .bridge => "bridge" | .shadow => "shadow"),
        ("counted", r.module == reviewModule)]
    let failsJ := ctx.ix.fails.map fun f =>
      Json.mkObj [("claim", f.claim),
        ("target", match f.target with | .forward i => s!"forward {i}" | .backward => "backward"),
        ("reason", f.reason), ("module", toString f.module),
        ("shadow_question", f.reason.startsWith "SHADOW?:")]
    return Json.mkObj [
      ("tool", "SA-PASS audit for EBCMCategory (Alignment/Audit.lean)"),
      ("lean_version", Lean.versionString),
      ("trusted_root", toString trustedRoot),
      ("trusted_by_import", ctx.trustedByImport),
      ("trusted_modules", jNames (ctx.trusted.toList.toArray.qsort Name.lt)),
      ("core_logic_whitelist", jNames coreLogicWhitelist),
      ("standard_axioms", jNames standardAxioms),
      ("claims", Json.arr claimsJ),
      ("bridges", Json.arr bridgesJ),
      ("reviews", Json.arr reviewsJ),
      ("refuters", Json.arr refutersJ),
      ("fail_records", Json.arr failsJ),
      ("orphan_registrations", Json.arr (orphans.map fun r =>
        Json.mkObj [("kind", r.kind.attrName), ("claim", r.claim), ("idx", r.idx),
          ("decl", toString r.decl)])),
      ("orphan_fail_records", Json.arr (orphanFails.map fun f =>
        Json.mkObj [("claim", f.claim), ("reason", f.reason)]))]
  let (j, _) ← (act.run ctx).run {}
  return j

/-- `#sa_pass_report "path.json"` writes the audit of every registered claim to `path.json`. -/
syntax (name := saPassReport) "#sa_pass_report " str : command

@[command_elab saPassReport] def elabSaPassReport : CommandElab := fun stx => do
  let some path := stx[1].isStrLit? | throwErrorAt stx[1] "expected a path string"
  let j ← liftTermElabM (runAudit none)
  IO.FS.writeFile path (j.pretty ++ "\n")
  let n : Nat := match j.getObjValD "claims" with
    | .arr a => a.size
    | _ => 0
  logInfo m!"SA-PASS audit of {n} claim(s) written to {path}"

/-- `#sa_audit "claim-id"` logs the audit of one claim. -/
syntax (name := saAudit) "#sa_audit " str : command

@[command_elab saAudit] def elabSaAudit : CommandElab := fun stx => do
  let some id := stx[1].isStrLit? | throwErrorAt stx[1] "expected a claim id string"
  let j ← liftTermElabM (runAudit (some id))
  let bridges := match j.getObjValD "bridges" with
    | .arr bs => bs.filter fun b => match b.getObjValD "claims" with
      | .arr cs => cs.contains (Json.str id)
      | _ => false
    | _ => #[]
  let out := Json.mkObj [("claims", j.getObjValD "claims"), ("bridges", Json.arr bridges)]
  logInfo m!"{out.pretty}"

end Alignment.Audit
