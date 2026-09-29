import Lean

/-!
# SA-PASS registry (alignment library, NOT trusted code)

Registration vocabulary for the SA-PASS spec-to-Lean alignment audit of the trusted library
`EBCMCategory.*`. See `Alignment/README.md` for the procedure.

Attributes (all global, applied at the declaration):

* `@[sa_reference "c"]`     the intended formal statement `T` of claim `c` (a `def : Prop`)
* `@[sa_shadow "c" i]`      shadow `Sᵢ` of claim `c` (a `def : Prop`), `i = 1 … n`
* `@[sa_ref_forward "c" i]` completeness certificate `T → Sᵢ`
* `@[sa_complete "c"]`      completeness certificate `S₁ → … → Sₙ → T`
* `@[sa_bridge "c"]`        definition bridge `∀ xs, f xs ↔ Q xs` / `∀ xs, f xs = g xs`, scoped to `c`
* `@[sa_forward "c" i]`     forward checker `T̂ → Sᵢ`
* `@[sa_backward "c"]`      backward checker `S₁ → … → Sₙ → T̂`
* `@[sa_witness "c" i]`     satisfiability witness for the hypotheses of the `i`-th `impl` theorem:
                            `∃ x₁ … xₖ, True` over its binders up to its last hypothesis
* `@[sa_refutation]`        a refuter `∀ ys, P₁ ys → … → False` (or `… → ¬ P ys`): the audit flags
                            every claim whose implementation has hypotheses matching the `Pⱼ`

Commands:

* `sa_claim "c" group "G" required? text "…" impl N₁ N₂ …`
* `sa_fail_forward "c" i "reason"`, `sa_fail_backward "c" "reason"`
* `sa_bridge_reviewed <decl> "<hash>" "<reason>"` (counts only in `Alignment.ReviewedBridges`)
* `sa_bridge_rejected <decl> "<reason>"`          (counts only in `Alignment.ReviewedBridges`)
* `sa_shadow_reviewed <decl> "<hash>" "<reason>"` (counts only in `Alignment.ReviewedBridges`):
  accepts a shadow that mentions no trusted constant (`shadow_trusted_free`)

Term elaborator: `sa_impl% "c"` is the type of the claim's implementation theorem, or the
right-nested conjunction of the types when several `impl` names are given.

Nothing here is checked at registration time beyond syntax and name resolution: every
consistency and soundness check is performed by `Alignment.Audit`, so that mis-registrations
show up in the report instead of breaking the build.
-/

namespace Alignment

open Lean Elab Command Term Meta

/-- Kinds of attribute registrations. -/
inductive RegKind where
  | reference | shadow | refForward | complete | bridge | forward | backward | witness | refutation
  deriving Inhabited, BEq, Repr, Hashable

/-- The attribute spelling of a registration kind. -/
def RegKind.attrName : RegKind → String
  | .reference => "sa_reference"
  | .shadow => "sa_shadow"
  | .refForward => "sa_ref_forward"
  | .complete => "sa_complete"
  | .bridge => "sa_bridge"
  | .forward => "sa_forward"
  | .backward => "sa_backward"
  | .witness => "sa_witness"
  | .refutation => "sa_refutation"

/-- Does this attribute take an index argument? -/
def RegKind.indexed : RegKind → Bool
  | .shadow | .refForward | .forward | .witness => true
  | _ => false

/-- Does this attribute take a claim id? (`sa_refutation` is global.) -/
def RegKind.hasClaim : RegKind → Bool
  | .refutation => false
  | _ => true

/-- An attribute registration `@[sa_… "claim" idx] decl`, recorded in the module `module`. -/
structure RegEntry where
  kind : RegKind
  claim : String
  idx : Nat := 0
  decl : Name
  module : Name
  deriving Inhabited, Repr

/-- A claim registration made by `sa_claim`. `impls` are fully resolved constant names. -/
structure ClaimEntry where
  id : String
  group : String
  required : Bool
  text : String
  impls : Array Name
  module : Name
  deriving Inhabited, Repr

/-- Target of a recorded genuine failure. -/
inductive FailTarget where
  | forward (i : Nat)
  | backward
  deriving Inhabited, BEq, Repr

/-- A recorded genuine failure `sa_fail_forward` / `sa_fail_backward`. -/
structure FailEntry where
  claim : String
  target : FailTarget
  reason : String
  module : Name
  deriving Inhabited, Repr

/-- What a review record is about. -/
inductive ReviewKind where
  /-- a definition bridge (`sa_bridge_reviewed`, `sa_bridge_rejected`) -/
  | bridge
  /-- a shadow that mentions no trusted constant (`sa_shadow_reviewed`) -/
  | shadow
  deriving Inhabited, BEq, Repr

/-- A review record: a bridge review (`sa_bridge_reviewed`) or rejection (`sa_bridge_rejected`),
or the acceptance of a trusted-free shadow (`sa_shadow_reviewed`). -/
structure ReviewEntry where
  decl : Name
  hash : String
  reason : String
  rejected : Bool
  module : Name
  kind : ReviewKind := .bridge
  deriving Inhabited, Repr

/-- One registry entry. -/
inductive Entry where
  | reg (e : RegEntry)
  | claim (e : ClaimEntry)
  | fail (e : FailEntry)
  | review (e : ReviewEntry)
  deriving Inhabited, Repr

/-- The registry: every entry of every imported module, tagged with the index of the module it
was exported from (`none` for entries of the current module). The provenance is authoritative:
the audit ignores the `module` fields written into entries and uses the exporting module. -/
initialize registryExt : SimplePersistentEnvExtension Entry (Array (Option Nat × Entry)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s e => s.push (none, e)
    addImportedFn := fun as => Id.run do
      let mut r := #[]
      for h : i in [0:as.size] do
        for e in as[i] do
          r := r.push (some i, e)
      return r
  }

/-- All registry entries visible in `env`, with the module that actually recorded them. -/
def getEntriesWithModule (env : Environment) : Array (Name × Entry) :=
  (registryExt.getState env).map fun (i?, e) =>
    match i? with
    | some i => (env.header.moduleNames[i]!, e)
    | none => (env.mainModule, e)

/-- All registry entries visible in `env`, with their `module` fields set to the module that
actually recorded them. -/
def getEntries (env : Environment) : Array Entry :=
  (getEntriesWithModule env).map fun (m, e) =>
    match e with
    | .reg r => .reg { r with module := m }
    | .claim c => .claim { c with module := m }
    | .fail f => .fail { f with module := m }
    | .review r => .review { r with module := m }

/-- All `sa_claim` registrations with the given id (more than one is reported as `duplicate`). -/
def findClaims (env : Environment) (id : String) : Array ClaimEntry :=
  (getEntries env).filterMap fun
    | .claim c => if c.id == id then some c else none
    | _ => none

/-- The implementation type `T̂` of a list of implementation theorems: the type of the single
theorem, or the right-nested conjunction of the types. Level parameters are kept as they are. -/
def implTypeOf (env : Environment) (impls : Array Name) : Except String Expr := do
  if impls.isEmpty then
    throw "the claim has no implementation theorem (gap)"
  let mut tys : Array Expr := #[]
  for n in impls do
    match env.find? n with
    | some ci => tys := tys.push ci.type
    | none => throw s!"unknown implementation constant {n}"
  return mkAndN tys.toList

/-! ## Attributes -/

syntax (name := sa_reference) "sa_reference " str : attr
syntax (name := sa_shadow) "sa_shadow " str ppSpace num : attr
syntax (name := sa_ref_forward) "sa_ref_forward " str ppSpace num : attr
syntax (name := sa_complete) "sa_complete " str : attr
syntax (name := sa_bridge) "sa_bridge " str : attr
syntax (name := sa_forward) "sa_forward " str ppSpace num : attr
syntax (name := sa_backward) "sa_backward " str : attr
syntax (name := sa_witness) "sa_witness " str ppSpace num : attr
syntax (name := sa_refutation) "sa_refutation" : attr

/-- Add one entry to the registry of the current module. -/
def addEntry (asyncDecl : Name) (e : Entry) : CoreM Unit :=
  modifyEnv fun env => registryExt.addEntry (asyncDecl := asyncDecl) env e

private def parseRegArgs (kind : RegKind) (stx : Syntax) : AttrM (String × Nat) := do
  unless kind.hasClaim do return ("", 0)
  let some claim := stx[1].isStrLit?
    | throwErrorAt stx "{kind.attrName}: expected a claim id string"
  if kind.indexed then
    let some i := stx[2].isNatLit?
      | throwErrorAt stx "{kind.attrName}: expected an index"
    return (claim, i)
  else
    return (claim, 0)

private def registerRegAttr (kind : RegKind) : IO Unit :=
  registerBuiltinAttribute {
    name := Name.mkSimple kind.attrName
    descr := s!"SA-PASS registration: {kind.attrName}"
    add := fun decl stx attrKind => do
      unless attrKind == AttributeKind.global do
        throwError "{kind.attrName}: the attribute must be global"
      let (claim, idx) ← parseRegArgs kind stx
      let env ← getEnv
      addEntry decl (.reg { kind, claim, idx, decl, module := env.mainModule })
  }

initialize registerRegAttr .reference
initialize registerRegAttr .shadow
initialize registerRegAttr .refForward
initialize registerRegAttr .complete
initialize registerRegAttr .bridge
initialize registerRegAttr .forward
initialize registerRegAttr .backward
initialize registerRegAttr .witness
initialize registerRegAttr .refutation

/-! ## Commands -/

/-- `sa_claim "c" group "G" required? text "…" impl N₁ …` registers claim `c`. The `impl` names
are resolved in the current scope and stored fully qualified. -/
syntax (name := saClaim) "sa_claim " str &"group" str (&"required")? &"text" str
  &"impl" ident* : command

@[command_elab saClaim] def elabSaClaim : CommandElab := fun stx => do
  let some id := stx[1].isStrLit? | throwErrorAt stx[1] "sa_claim: expected a claim id string"
  let some group := stx[3].isStrLit? | throwErrorAt stx[3] "sa_claim: expected a group string"
  let required := !stx[4].isNone
  let some text := stx[6].isStrLit? | throwErrorAt stx[6] "sa_claim: expected a text string"
  let mut impls : Array Name := #[]
  for i in stx[8].getArgs do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo i
    impls := impls.push n
  let env ← getEnv
  unless (findClaims env id).isEmpty do
    logWarning m!"sa_claim: claim \"{id}\" is already registered (the audit reports `duplicate`)"
  modifyEnv fun env => registryExt.addEntry env
    (.claim { id, group, required, text, impls, module := env.mainModule })

/-- `sa_fail_forward "c" i "reason"` records that forward check `i` of claim `c` genuinely
fails. Start the reason with `SHADOW?:` if the blind shadow is believed to misread the text. -/
syntax (name := saFailForward) "sa_fail_forward " str ppSpace num ppSpace str : command

/-- `sa_fail_backward "c" "reason"` records that the backward check of claim `c` genuinely
fails. -/
syntax (name := saFailBackward) "sa_fail_backward " str ppSpace str : command

@[command_elab saFailForward] def elabSaFailForward : CommandElab := fun stx => do
  let some claim := stx[1].isStrLit? | throwErrorAt stx[1] "expected a claim id string"
  let some i := stx[2].isNatLit? | throwErrorAt stx[2] "expected an index"
  let some reason := stx[3].isStrLit? | throwErrorAt stx[3] "expected a reason string"
  modifyEnv fun env => registryExt.addEntry env
    (.fail { claim, target := .forward i, reason, module := env.mainModule })

@[command_elab saFailBackward] def elabSaFailBackward : CommandElab := fun stx => do
  let some claim := stx[1].isStrLit? | throwErrorAt stx[1] "expected a claim id string"
  let some reason := stx[2].isStrLit? | throwErrorAt stx[2] "expected a reason string"
  modifyEnv fun env => registryExt.addEntry env
    (.fail { claim, target := .backward, reason, module := env.mainModule })

/-- `sa_bridge_reviewed decl "hash" "reason"`: an independent review accepting bridge `decl`
whose statement has the given stable hash (printed by the report). Only records made in the
module `Alignment.ReviewedBridges` count; a record whose hash no longer matches the bridge's
statement is reported as `stale` and does not count. -/
syntax (name := saBridgeReviewed) "sa_bridge_reviewed " ident ppSpace str ppSpace str : command

/-- `sa_bridge_rejected decl "reason"`: an independent review rejecting bridge `decl`. Only
records made in `Alignment.ReviewedBridges` count. -/
syntax (name := saBridgeRejected) "sa_bridge_rejected " ident ppSpace str : command

@[command_elab saBridgeReviewed] def elabSaBridgeReviewed : CommandElab := fun stx => do
  let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let some hash := stx[2].isStrLit? | throwErrorAt stx[2] "expected a hash string"
  let some reason := stx[3].isStrLit? | throwErrorAt stx[3] "expected a reason string"
  let env ← getEnv
  unless env.mainModule == `Alignment.ReviewedBridges do
    logWarning m!"sa_bridge_reviewed: records outside Alignment.ReviewedBridges do not count"
  modifyEnv fun env => registryExt.addEntry env
    (.review { decl, hash, reason, rejected := false, module := env.mainModule })

@[command_elab saBridgeRejected] def elabSaBridgeRejected : CommandElab := fun stx => do
  let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let some reason := stx[2].isStrLit? | throwErrorAt stx[2] "expected a reason string"
  modifyEnv fun env => registryExt.addEntry env
    (.review { decl, hash := "", reason, rejected := true, module := env.mainModule })

/-- `sa_shadow_reviewed decl "hash" "reason"`: an independent review accepting that the shadow
`decl` legitimately mentions no trusted-library constant, because the source text is itself a
statement of logic or arithmetic (the audit otherwise flags the claim `shadow_trusted_free`).
The hash is the shadow's content hash printed by the report (it covers the shadow's body and
every alignment-library helper it uses). Only records made in `Alignment.ReviewedBridges`
count; a record whose hash no longer matches is reported as `stale`. -/
syntax (name := saShadowReviewed) "sa_shadow_reviewed " ident ppSpace str ppSpace str : command

@[command_elab saShadowReviewed] def elabSaShadowReviewed : CommandElab := fun stx => do
  let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let some hash := stx[2].isStrLit? | throwErrorAt stx[2] "expected a hash string"
  let some reason := stx[3].isStrLit? | throwErrorAt stx[3] "expected a reason string"
  let env ← getEnv
  unless env.mainModule == `Alignment.ReviewedBridges do
    logWarning m!"sa_shadow_reviewed: records outside Alignment.ReviewedBridges do not count"
  modifyEnv fun env => registryExt.addEntry env
    (.review { decl, hash, reason, rejected := false, module := env.mainModule, kind := .shadow })

/-! ## `sa_impl%` -/

/-- `sa_impl% "c"` elaborates to the implementation type `T̂` of claim `c` (see `implTypeOf`). -/
syntax (name := saImpl) "sa_impl% " str : term

@[term_elab saImpl] def elabSaImpl : TermElab := fun stx _ => do
  let some id := stx[1].isStrLit? | throwErrorAt stx[1] "sa_impl%: expected a claim id string"
  let env ← getEnv
  let some c := (findClaims env id)[0]?
    | throwError "sa_impl%: unknown claim \"{id}\" (register it with `sa_claim` first)"
  match implTypeOf env c.impls with
  | .ok t => return t
  | .error e => throwError "sa_impl% \"{id}\": {e}"

end Alignment
