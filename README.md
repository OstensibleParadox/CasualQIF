# CausalQIF

Formalisation in Lean 4 of Causal Quantitative Information Flow (QIF).

## Scope
- Formalisation of d-separation in DAGs.
- Proofs for conditional mutual information properties.
- State leakage bounds for finite causal models.

## Architecture

The verification pipeline has four layers:

```
             ┌─────────────────────────────────────┐
  DAG/Markov │ DAG/* + MarkovGenerator             │
  automation │ (d-separation, Bayes-ball, MAGWalk,  │
             │  moralization, leaf deletion,        │
             │  FactorizesOverDAG, condMarkov bridge)│
             └─────────────────────────────────────┘
                         ↓ condMarkov_of_factorizes_dsep_fourVar
             ┌─────────────────────────────────────┐
  Cut-set    │ pmf_from_vars → cut_set_dpi_bound    │
  bound      │ → abstract_cut_set_bound             │
             └─────────────────────────────────────┘
                         ↓ h_cap : I_YZ_W(P4) ≤ C
             ┌─────────────────────────────────────┐
  KKT cert   │ KKT_Certificate → capacity_le_of_kkt │
             │ (weighted average)                   │
             └─────────────────────────────────────┘
                         ↓ end-to-end
             ┌─────────────────────────────────────┐
  Case study │ linear_chain_cut_set_bound           │
             │ linear_chain_cut_set_bound_from_dag  │
             └─────────────────────────────────────┘
```

## Usage
Ensure you have the appropriate Lean 4 toolchain installed (see `lean-toolchain`).
To build:
```bash
lake build
```

## License
MIT
