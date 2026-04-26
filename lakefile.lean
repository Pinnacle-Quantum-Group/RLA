import Lake
open Lake DSL

package «rlaFormalProofs» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.5.0"

@[default_target]
lean_lib «RLA» where
  srcDir := "formal_proofs"
  globs := #[.submodules `RLA]
