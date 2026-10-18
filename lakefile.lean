import Lake
open Lake DSL

package CFT where
  leanOptions := #[⟨`autoImplicit, false⟩]

-- Public, pinned dependency: the archived project originally referenced a local
-- ../mathlib4 checkout, which is not available to GitHub users.
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.15.0"

@[default_target]
lean_lib CFT where
  globs := #[.submodules `CFT]
