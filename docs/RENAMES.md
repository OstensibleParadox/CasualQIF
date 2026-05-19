# CausalQIF Name Migration Ledger

This document records the mapping from old DSeparation/FiniteQuerySandbox names
to the new CausalQIF API. No compatibility wrappers are provided.

## Namespace Migration

| Old Namespace | New Namespace |
|---------------|---------------|
| `DSeparation` | `CausalQIF.Graph`, `CausalQIF.DSeparation` |
| `DSeparation.DAG` | `CausalQIF.Graph.DAG` |
| `FiniteQuerySandbox` | `CausalQIF.Probability`, `CausalQIF.CausalModel`, `CausalQIF.InformationFlow` |

## Type Renames

| Old Name | New Name |
|----------|----------|
| `DSeparation.DAG` | `CausalQIF.Graph.DAG` |
| `FiniteQuerySandbox.DAG` | `CausalQIF.Graph.DAG` |
| `FiniteQuerySandbox.FinitePMF` | `CausalQIF.Probability.FinitePMF` |
| `FiniteQuerySandbox.Trail` | `CausalQIF.DSeparation.Trail` |

## Definition Renames

| Old Name | New Name |
|----------|----------|
| `DSeparation.DAG.HasEdge` | `CausalQIF.Graph.DAG.HasEdge` |
| `DSeparation.DAG.dSeparated` | `CausalQIF.Graph.DAG.dSeparated` |
| `DSeparation.dSeparates` | `CausalQIF.DSeparation.dSeparates` |
| `DSeparation.DisjointSets` | `CausalQIF.DSeparation.DisjointSets` |
| `FiniteQuerySandbox.entropy` | `CausalQIF.Probability.entropy` |
| `FiniteQuerySandbox.condMutualInfo` | `CausalQIF.Probability.condMutualInfo` |
| `FiniteQuerySandbox.FactorizesOverDAG` | `CausalQIF.CausalModel.FactorizesOverDAG` |
| `FiniteQuerySandbox.IsMarkovChain` | `CausalQIF.Probability.IsMarkovChain` |
| `InfoTheory.IsMarkovChain` | `CausalQIF.Probability.IsMarkovChain` |
| `InfoTheory.I_A_cond_C_B` | `CausalQIF.Probability.I_A_cond_C_B` |
| `FiniteQuerySandbox.I_S_M_cond_Ttilde` | `CausalQIF.InformationFlow.stateLeakage` |

## Theorem Renames

| Old Name | New Name |
|----------|----------|
| `DSeparation.dSeparated_iff_dSeparates` | `CausalQIF.DSeparation.dSeparated_iff_dSeparates` |
| `InfoTheory.cond_mutual_info_zero_of_markov` | `CausalQIF.Probability.cond_mutual_info_zero_of_markov` |
| `FiniteQuerySandbox.isMarkovChain_of_factorizes_dsep` | `CausalQIF.CausalModel.isMarkovChain_of_factorizes_dSeparates` |
| `FiniteQuerySandbox.cmi_zero_of_factorizes_dsep` | `CausalQIF.CausalModel.condMutualInfo_eq_zero_of_factorizes_of_dSeparates` |
| (new) | `CausalQIF.condMutualInfo_eq_zero_of_factorizes_of_dSeparated` |
| (new) | `CausalQIF.stateLeakage_le_of_factorizes_of_dSeparated_of_cutMutualInfo_le` |
| (new) | `CausalQIF.linearChain_stateLeakage_le_one_of_dSeparated` |

## Removed Modules

The following modules from the old structure are not part of CausalQIF:

- `DSeparation/InfoTheoryBridge.lean` - replaced by `CausalQIF.CausalModel.Factorization`
- `DSeparation/BayesBall/` - internal implementation detail
- `DSeparation/TraceSynthesis/` - internal implementation detail
- `DSeparation/Counterexample.lean` - moved to archive
- `DSeparation/Examples.lean` - moved to archive

## Archive Modules

Side-project material preserved in `archive/CausalQIFArchive/`:

- `Screenability/` - screenability surrogate theory
- `PAC/` - PAC learning bounds
- `Impossibility/` - finite query impossibility results
