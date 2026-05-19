  ## Summary

  Rebuilt /Users/ostensible_paradox/Documents/anon-lean4 as a clean mathematical Lean library named CausalQIF, not a compatibility-preserving merge. Old DSeparation, FiniteQuerySandbox,
  Screenability, and wrapper-style roots are removed from the main public API. The new top-level
  mathematical result is the D-Separation Cut-Set Extraction Theorem, exposed in Lean as:

  theorem stateLeakage_le_of_factorizes_of_dSeparated_of_cutMutualInfo_le

  This theorem proves a Shannon leakage upper bound from verified d-separation, explicit DAG
  factorization, and cut-capacity hypotheses.


## Paper Rewrite After Code Green

  - Replace “scaffold boundary” language with “stratified finite-discrete bridge”.
  - Use the three methodology labels:
      - Stratification of Structural Flow and Quantitative Capacity
      - Trace Compression via Static Abstract Interpretation
      - Well-Defined Modular Boundaries for Measure-Theoretic Obligations
  - State the source-of-truth claim as:
    The unified CausalQIF library proves that a verified d-separation judgment over a finite
    DAG, together with explicit factorization and cut-capacity hypotheses, composes through
    conditional independence and conditional DPI to yield a machine-checked Shannon leakage upper bound.
  - Future work should target continuous models via information-preserving abstraction/
    refinement, not re-open the finite Lean result.

  ## Assumptions

  - CausalQIF is the root namespace and library name.
  - Old public names may be destructively renamed.
  - No compatibility wrappers are added to the main library.
  - Side modules are preserved only in the separate archive package.
  - The main library must be zero-sorry.
  - InfoTheoryBridge must not appear anywhere under CausalQIF.
