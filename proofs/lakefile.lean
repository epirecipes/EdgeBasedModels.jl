import Lake
open Lake DSL

package "EBCMCategory" where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]

require "leanprover-community" / "mathlib"

require mdgen from git
  "https://github.com/Seasawher/mdgen" @ "main"

@[default_target]
lean_lib «EBCMCategory» where
  globs := #[.submodules `EBCMCategory]

/-- SA-PASS alignment library. NOT trusted code: it registers claims, blind shadow sets,
checkers and bridges against the trusted library `EBCMCategory`. Not a default target; build
with `lake build +Alignment.All +Alignment.Audit` (see `Alignment/README.md`). -/
lean_lib Alignment where
  globs := #[.submodules `Alignment]
