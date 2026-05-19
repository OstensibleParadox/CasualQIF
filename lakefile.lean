import Lake
open Lake DSL

package causal_qif where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib CausalQIF
