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
