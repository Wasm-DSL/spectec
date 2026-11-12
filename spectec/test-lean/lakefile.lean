import Lake
open Lake DSL

package «test-lean» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.32.0"

@[default_target]
lean_lib TestLean where
  globs := #[.one `«wasm2.0», .one `«custom_notation», .one `typing_lemmas,
    .one `ExtendedDeriveDecEq, .one `sandbox_5, .one `sandbox_10]
