# CausalQIF Destructive Reconstruction Plan

  ## Summary

  Rebuild /Users/ostensible_paradox/Documents/anon-lean4 as a clean mathematical Lean library
  named CausalQIF, not a compatibility-preserving merge. Old DSeparation, FiniteQuerySandbox,
  Screenability, and wrapper-style roots are removed from the main public API. The new top-level
  mathematical result is the D-Separation Cut-Set Extraction Theorem, exposed in Lean as:

  theorem stateLeakage_le_of_factorizes_of_dSeparated_of_cutMutualInfo_le

  This theorem proves a Shannon leakage upper bound from verified d-separation, explicit DAG
  factorization, and cut-capacity hypotheses.

  ## Key Changes

  - Rename root package/library to CausalQIF:

    lean_lib CausalQIF

    with root import CausalQIF.lean. No DSeparation.lean, FiniteQuerySandbox.lean, or old-path
    wrappers in the main library.

  - Use this clean module hierarchy:

    CausalQIF/
    ├── Graph/
    │   ├── DirectedAcyclic.lean
    │   ├── Reachability.lean
    │   └── Moralization.lean
    ├── DSeparation/
    │   ├── Path/
    │   ├── MAGWalk.lean
    │   └── Equivalence.lean
    ├── Probability/
    │   ├── FinitePMF.lean
    │   ├── Entropy.lean
    │   └── Markov.lean
    ├── CausalModel/
    │   ├── Factorization.lean
    │   └── DataProcessing.lean
    ├── InformationFlow/
    │   ├── CutSetBound.lean
    │   └── ChannelCapacity.lean
    └── Main.lean

  - Put side-project material into a separate archive package:

    archive/
    ├── lakefile.lean
    └── CausalQIFArchive/
        ├── Screenability/
        ├── PAC/
        └── Impossibility/

    The archive package may depend on CausalQIF; CausalQIF must not depend on the archive.

  ## Public API Naming

  - Normalize names to Lean/mathlib style:

    DAG
    DAG.dSeparated
    dSeparates
    dSeparated_iff_dSeparates
    FinitePMF
    condMutualInfo
    stateLeakage
    cutMutualInfo
    IsMarkovChain
    DAG.Factorizes

  - Main bridge and bound theorem names:

    condMutualInfo_eq_zero_of_isMarkovChain
    isMarkovChain_of_factorizes_of_dSeparates
    condMutualInfo_eq_zero_of_factorizes_of_dSeparates
    condMutualInfo_eq_zero_of_factorizes_of_dSeparated
    stateLeakage_le_of_condMarkov_of_cutMutualInfo_le
    stateLeakage_le_of_factorizes_of_dSeparates_of_cutMutualInfo_le
    stateLeakage_le_of_factorizes_of_dSeparated_of_cutMutualInfo_le
    linearChain_stateLeakage_le_one_of_dSeparated

  - Maintain only a documentation ledger:

    docs/RENAMES.md

    No compatibility wrappers in the main library.

  ## Migration Phases

  - Phase 1: Topology Transfer
      - Replace lakefile.lean root with package causal_qif and lean_lib CausalQIF.
      - Move files into the new hierarchy and rewrite imports to CausalQIF.*.
      - Do not preserve old namespaces. Expect name errors after topology transfer.
      - Immediately after deleting/moving old module paths, run:

        lake clean
        This is mandatory. It prevents stale .olean files from making Lean/LSP believe deleted
        modules still exist and producing false cyclic dependency errors.

  - Phase 2: Rename and Isolate
      - Normalize namespaces and declarations in dependency order:

        Graph → DSeparation → Probability → CausalModel → InformationFlow → Main

      - Delete the old InfoTheoryBridge.lean scaffold from the main library.
      - Move Screenability, PAC, recoverability, and impossibility side modules into the
        separate archive package.
      - After each large rename/delete boundary, run:

        lake clean
        lake build CausalQIF.<Layer>

  - Phase 3: Final Join
      - Port the new DSepCMIBridge.lean result into the clean API:

        condMutualInfo_eq_zero_of_factorizes_of_dSeparates
        condMutualInfo_eq_zero_of_factorizes_of_dSeparated

      - Compose it with cut-set and capacity results in CausalQIF.Main.
      - The main theorem is:

        theorem stateLeakage_le_of_factorizes_of_dSeparated_of_cutMutualInfo_le

      - This replaces the old POPL-facing InfoTheoryBridge.lean two-sorry scaffold with a zero-
        sorry bridge.

  ## Test Plan

  - Run after every phase:

    lake clean
    lake build
    rg "sorry|admit" CausalQIF
    rg "axiom|constant" CausalQIF
    rg "InfoTheoryBridge" CausalQIF

    The final command must return no matches.

  - Required final checks:

    #check @CausalQIF.CausalModel.condMutualInfo_eq_zero_of_factorizes_of_dSeparated
    #check
@CausalQIF.InformationFlow.stateLeakage_le_of_factorizes_of_dSeparated_of_cutMutualInfo_le
    #check @CausalQIF.InformationFlow.linearChain_stateLeakage_le_one_of_dSeparated

  - Archive package checks separately:

    cd archive
    lake clean
    lake build

    Archive failures must not block CausalQIF.

  ## Assumptions

  - CausalQIF is the root namespace and library name.
  - Old public names may be destructively renamed.
  - No compatibility wrappers are added to the main library.
  - Side modules are preserved only in the separate archive package.
  - The main library must be zero-sorry.
  - InfoTheoryBridge must not appear anywhere under CausalQIF.
