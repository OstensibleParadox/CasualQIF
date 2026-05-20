import CausalQIF.Graph.DirectedAcyclic
import CausalQIF.Graph.Reachability
import CausalQIF.Graph.Moralization
import CausalQIF.DSeparation.Path.Trail
import CausalQIF.DSeparation.MAGWalk
import CausalQIF.DSeparation.Equivalence
import CausalQIF.Probability.FinitePMF
import CausalQIF.Probability.FinitePMF.Marginalize
import CausalQIF.Probability.Entropy
import CausalQIF.Probability.Markov
import CausalQIF.CausalModel.Factorization
import CausalQIF.CausalModel.ProductFactorization
import CausalQIF.InformationFlow.CutSetBound
import CausalQIF.InformationFlow.Duality
import CausalQIF.InformationFlow.ChannelCapacity
import CausalQIF.Main
import CausalQIF.Examples.LinearChain

/-!
# CausalQIF

A Lean 4 library for causal inference with quantitative information flow.

## Main Results

- `DAG.dSeparated`: Graph-theoretic d-separation criterion
- `MAGWalk`: Moralized ancestral graph walk certificates
- `dSeparates`: Trail-based d-separation predicate
- `FactorizesOverDAG`: Semantic DAG factorization
- `isMarkovChain_of_productFactorizes_chain3`: Product-factorized chain instance → Markov chain
- `condMutualInfo_eq_zero_of_isMarkovChain`: Markov chain → CMI = 0
- `CausalModel.condMutualInfo_eq_zero_of_factorizes_of_dSeparates`: D-sep → CMI = 0 bridge
- `cond_dpi`: Conditional data processing inequality
- `condMutualInfo_le_of_dual_witness`: Dual KL witness → CMI upper bound
- `stateLeakage_le_of_factorizes_of_dSeparates_of_cutMutualInfo_le`: Main cut-set leakage bound
- `certified_leakage_gap_of_dSeparated_graph`: H(S∣T̃) ≤ H(S∣T_full) + C
- `stateLeakage_le_of_dual_witness`: Cut-set leakage bound from a dual witness

## Module Hierarchy

```
CausalQIF/
├── Graph/
│   ├── DirectedAcyclic.lean
│   ├── Reachability.lean
│   └── Moralization.lean
├── DSeparation/
│   ├── ActiveRoute.lean
│   ├── BayesBall/
│   │   ├── Basic.lean
│   │   └── Certified.lean
│   ├── Path/
│   │   └── Trail.lean
│   │       ├── Basic.lean
│   │       ├── BayesBall.lean
│   │       ├── Blocking.lean
│   │       └── Triple.lean
│   ├── TraceSynthesis.lean
│   │   ├── Assembly.lean
│   │   ├── Graph.lean
│   │   ├── MinimalWitness.lean
│   │   ├── OpenTrace.lean
│   │   │   ├── BadColliders.lean
│   │   │   ├── Basic.lean
│   │   │   └── Compile.lean
│   │   ├── Split.lean
│   │   └── StaticRoute.lean
│   │       ├── Basic.lean
│   │       └── Reachability.lean
│   ├── MAGWalk.lean
│   └── Equivalence.lean
├── Probability/
│   ├── FinitePMF.lean
│   │   ├── Basic.lean
│   │   ├── Entropy.lean
│   │   ├── Marginal.lean
│   │   └── Marginalize.lean
│   ├── Entropy.lean
│   │   ├── Basic.lean
│   │   ├── ChainRule.lean
│   │   │   ├── Marginals.lean
│   │   │   ├── Reshapes.lean
│   │   │   ├── Bridges.lean
│   │   │   └── Decomposition.lean
│   │   ├── Identities.lean
│   │   │   ├── SumLogIdentities.lean
│   │   │   └── CondMutualInfo.lean
│   │   └── KLDivergence.lean
│   └── Markov.lean
├── CausalModel/
│   ├── Factorization.lean
│   ├── ProductFactorization.lean
│   └── DataProcessing.lean
├── InformationFlow/
│   ├── CutSetBound.lean
│   ├── Duality.lean
│   └── ChannelCapacity.lean
├── Examples/
│   └── LinearChain.lean
└── Main.lean
```
-/
