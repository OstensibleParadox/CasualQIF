import CausalQIF.Graph.Reachability

open Finset

namespace CausalQIF.Graph

/-! # Markov Blanket Utilities

This module is the "upper stage" of the Verma-Pearl split: purely graph-theoretic
computations that produce node-set premises for local/blanket Markov conditions.
-/

variable {V : Type} [DecidableEq V] [Fintype V]

def spouses (G : DAG V) (v : V) : Finset V :=
  ((children G v).biUnion fun c => parents G c) \ ({v} : Finset V)

def computeMarkovBlanket (G : DAG V) (v : V) : Finset V :=
  parents G v ∪ children G v ∪ spouses G v

/-- Local-Markov condition triple `({v}, nonDescendants(v) \ parents(v), parents(v))`. -/
def generateMarkovConditions (G : DAG V) (v : V) : Finset V × Finset V × Finset V :=
  ( ({v} : Finset V)
  , nonDescendants G v \ parents G v
  , parents G v
  )

/-- Blanket-Markov condition triple `({v}, V \ ({v} ∪ MB(v)), MB(v))`. -/
def generateMarkovBlanketConditions (G : DAG V) (v : V) : Finset V × Finset V × Finset V :=
  ( ({v} : Finset V)
  , G.nodes \ (({v} : Finset V) ∪ computeMarkovBlanket G v)
  , computeMarkovBlanket G v
  )

end CausalQIF.Graph

