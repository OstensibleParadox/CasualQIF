import CausalQIF.Graph.MarkovBlanket

open Finset

namespace CausalQIF.Graph

def chain3 : DAG (Fin 3) :=
  DAG.ofRank (nodes := ({0, 1, 2} : Finset (Fin 3)))
    (edges := ({(0, 1), (1, 2)} : Finset (Fin 3 × Fin 3)))
    (rank := fun i => i.val)
    (edges_subset := by decide)
    (rank_increases := by decide)

def collider3 : DAG (Fin 3) :=
  DAG.ofRank (nodes := ({0, 1, 2} : Finset (Fin 3)))
    (edges := ({(0, 1), (2, 1)} : Finset (Fin 3 × Fin 3)))
    (rank := fun i => if i = 1 then 1 else 0)
    (edges_subset := by decide)
    (rank_increases := by decide)

end CausalQIF.Graph
