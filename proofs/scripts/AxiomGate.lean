-- Axiom gate for the trusted library `EBCMCategory` (run by `scripts/axiom_gate.sh`).
-- The import list must name every module under `EBCMCategory/`; the shell script checks this.
import EBCMCategory.CategoricalComposition
import EBCMCategory.ClosureTheorem
import EBCMCategory.ClusteringExtension
import EBCMCategory.CoarseGrain
import EBCMCategory.ConvergenceTheorems
import EBCMCategory.DegreeCorrelation
import EBCMCategory.DynamicLimits
import EBCMCategory.EpiCategory
import EBCMCategory.GaloisPair
import EBCMCategory.Hierarchy
import EBCMCategory.InvariantRegion
import EBCMCategory.MarginalisationCharacterization
import EBCMCategory.MarginalisationDynamicalGap
import EBCMCategory.MarginalisationFunctor
import EBCMCategory.MessagePassingBridge
import EBCMCategory.MethodOfStages
import EBCMCategory.Obstructions
import EBCMCategory.PairwiseClosureConditions
import EBCMCategory.SEIREquations
import EBCMCategory.SurvivalBridge
import EBCMCategory.VolzMeyersEquations

/-!
# Axiom gate

`#axiom_gate` fails (with an error, so `lake env lean` exits non-zero) unless

1. no constant declared in an `EBCMCategory.*` module is an `axiom`, and
2. every constant declared in an `EBCMCategory.*` module (theorems, definitions, instances and
   auxiliary declarations alike) depends only on the standard axioms `propext`, `Quot.sound` and
   `Classical.choice`. This rules out `sorryAx` and `Lean.ofReduceBool` (`native_decide`).

This is `#print axioms` for every declaration of the library, with the dependency traversal
memoised across declarations.
-/

namespace AxiomGate

open Lean Elab Command

/-- The axioms a declaration of the trusted library may depend on. -/
def standardAxioms : Array Name := #[``propext, ``Quot.sound, ``Classical.choice]

/-- Root of the trusted library. -/
def trustedRoot : Name := `EBCMCategory

/-- Memoised axiom dependencies (post-order traversal, no deep recursion). -/
def axiomsOf (env : Environment) (root : Name) : StateM (Std.HashMap Name (Array Name)) (Array Name) := do
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
    | some (.quotInfo v) => v.type.getUsedConstants
    | none => #[]
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
      let mut r : Array Name := #[]
      if let some (.axiomInfo _) := env.find? c then r := #[c]
      for d in (depMap.find? c).getD #[] do
        if let some rd := (← get)[d]? then
          for x in rd do
            unless r.contains x do r := r.push x
      modify (·.insert c r)
  return (← get)[root]?.getD #[]

/-- The problems found among `decls` (pairs of a constant and its module) and the set of axioms
they use. The memo table is threaded through one state computation, so it is never copied. -/
def check (env : Environment) (decls : Array (Name × Name)) :
    StateM (Std.HashMap Name (Array Name)) (Array String × NameSet) := do
  let mut bad : Array String := #[]
  let mut used : NameSet := {}
  for (n, m) in decls do
    if let some (.axiomInfo _) := env.find? n then
      bad := bad.push s!"{n} ({m}) is declared as an axiom"
    let axs ← axiomsOf env n
    for a in axs do used := used.insert a
    let extra := axs.filter (!standardAxioms.contains ·)
    unless extra.isEmpty do
      bad := bad.push s!"{n} ({m}) depends on non-standard axioms {extra.toList}"
  return (bad, used)

/-- The constants declared in modules below `root` (imported modules only). -/
def declsBelow (env : Environment) (root : Name) : Array (Name × Name) :=
  env.constants.map₁.fold (init := #[]) fun acc n _ =>
    match env.getModuleIdxFor? n with
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      if root.isPrefixOf m then acc.push (n, m) else acc
    | none => acc

/-- `#axiom_gate` checks every constant declared in an `EBCMCategory.*` module. -/
syntax (name := axiomGate) "#axiom_gate" (ppSpace ident)? : command

@[command_elab axiomGate] def elabAxiomGate : CommandElab := fun stx => do
  let env ← getEnv
  -- an optional module root overrides `EBCMCategory` (used only to test the gate itself)
  let root := if stx[1].isNone then trustedRoot else stx[1][0].getId
  let decls := declsBelow env root
  let mods := decls.foldl (fun (s : NameSet) (_, m) => s.insert m) {}
  let ((bad, used), _) := (check env decls).run {}
  let usedL := used.toList.map toString
  if decls.isEmpty then
    logError m!"axiom gate FAILED: no declarations found in modules below {root}"
  else if bad.isEmpty then
    logInfo m!"axiom gate PASSED: {decls.size} declarations in {mods.size} {root} modules; axioms used: {usedL}"
  else
    logError m!"axiom gate FAILED ({bad.size} problem(s)):\n{"\n".intercalate bad.toList}"

end AxiomGate

#axiom_gate
