import Lake
open Lake DSL

package «test-lean-claude» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.32.0"

@[default_target]
lean_lib TestLeanClaude where
  globs := #[.one `«wasm2.0», .one `ExtendedDeriveDecEq, .one `HelperLemmas, .one `Subtyping,
    .one `TypingLemmas, .one `TypePreservationPure, .one `ExtensionLemmas,
    .one `TypePreservation, .one `TypeProgress]
