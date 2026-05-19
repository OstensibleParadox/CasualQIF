import Lake
open Lake DSL

package causal_qif_archive where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

lean_lib CausalQIFArchive
