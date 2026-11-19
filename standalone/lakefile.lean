import Lake
open Lake DSL

package FieldEquations where
  leanOptions := #[⟨`autoImplicit, false⟩,
    ⟨`linter.unusedVariables, false⟩, ⟨`linter.unusedSectionVars, false⟩,
    ⟨`linter.unusedTactic, false⟩, ⟨`linter.unreachableTactic, false⟩,
    ⟨`linter.unnecessarySeqFocus, false⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.15.0"

@[default_target]
lean_lib FieldEquations where
  globs := #[.submodules `FieldEquations]
