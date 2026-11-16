import Lake
open Lake DSL

package CFT where
  -- Linter noise audited 2026-11-15 (build_v061.log counts: unusedVariables 1308,
  -- unnecessarySeqFocus 133, unreachableTactic 132, unusedTactic 96,
  -- unusedSectionVars 109). These five classes are disabled so build logs stay
  -- readable; the warnings were reviewed in bulk, not fixed one by one.
  leanOptions := #[⟨`autoImplicit, false⟩,
    ⟨`linter.unusedVariables, false⟩, ⟨`linter.unusedSectionVars, false⟩,
    ⟨`linter.unusedTactic, false⟩, ⟨`linter.unreachableTactic, false⟩,
    ⟨`linter.unnecessarySeqFocus, false⟩]

-- Public, pinned dependency: the archived project originally referenced a local
-- ../mathlib4 checkout, which is not available to GitHub users.
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.15.0"

@[default_target]
lean_lib CFT where
  globs := #[.submodules `CFT]
