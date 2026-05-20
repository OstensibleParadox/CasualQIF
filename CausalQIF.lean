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

A clean Lean 4 library for causal inference with quantitative information flow.

## Main Results

- `DAG.dSeparated`: Graph-theoretic d-separation criterion
- `MAGWalk`: Moralized ancestral graph walk certificates
- `dSeparates`: Trail-based d-separation predicate
- `FactorizesOverDAG`: Semantic DAG factorization
- `isMarkovChain_of_productFactorizes_chain3`: Product-factorized chain instance → Markov chain
- `condMutualInfo_eq_zero_of_factorizes_of_dSeparates`: D-sep → CMI = 0 bridge
- `condMutualInfo_le_of_dual_witness`: Dual KL witness → CMI upper bound
- `stateLeakage_le_of_factorizes_of_dSeparates_of_cutMutualInfo_le`: Main theorem
- `stateLeakage_le_of_dual_witness`: Cut-set leakage bound from a dual witness

## Module Hierarchy

```
CausalQIF/
├── Graph/
│   ├── DirectedAcyclic.lean
│   ├── Reachability.lean
│   └── Moralization.lean
├── DSeparation/
│   ├── Path/
│   │   └── Trail.lean
│   ├── MAGWalk.lean
│   └── Equivalence.lean
├── Probability/
│   ├── FinitePMF.lean
│   ├── FinitePMF/
│   │   └── Marginalize.lean
│   ├── Entropy.lean
│   ├── Entropy/
│   │   ├── Basic.lean
│   │   ├── ChainRule.lean
│   │   ├── Identities.lean
│   │   └── KLDivergence.lean
│   └── Markov.lean
├── CausalModel/
│   ├── Factorization.lean
│   └── ProductFactorization.lean
├── InformationFlow/
│   ├── CutSetBound.lean
│   ├── Duality.lean
│   └── ChannelCapacity.lean
└── Main.lean
```
-/
