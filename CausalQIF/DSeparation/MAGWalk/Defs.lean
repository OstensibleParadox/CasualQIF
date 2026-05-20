import CausalQIF.Graph.Moralization
import CausalQIF.DSeparation.BayesBall.Certified

open Finset

namespace CausalQIF.DSeparation

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]

/-!
# Moralized Ancestral Graph Walks

`MAGWalk` is a compressed walk language equivalent to reachability in the
moralized ancestral d-separation graph.  A step is either a surviving directed
edge adjacency or a moralization jump between co-parents.
-/

inductive MAGWalk (G : Graph.DAG V) (X Y Z : Finset V) : V → V → Prop where
  | refl (u : V) : MAGWalk G X Y Z u u
  | single {u v : V}
      (hEdge : G.hasEdge u v ∨ G.hasEdge v u)
      (hu : u ∈ G.dSeparationGraphNodes X Y Z)
      (hv : v ∈ G.dSeparationGraphNodes X Y Z) :
      MAGWalk G X Y Z u v
  | jump {u v w : V}
      (huw : G.hasEdge u w)
      (hvw : G.hasEdge v w)
      (hne : u ≠ v)
      (hu : u ∈ G.dSeparationGraphNodes X Y Z)
      (hv : v ∈ G.dSeparationGraphNodes X Y Z)
      (hw : w ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z)) :
      MAGWalk G X Y Z u v
  | trans {u v w : V}
      (huv : MAGWalk G X Y Z u v)
      (hvw : MAGWalk G X Y Z v w) :
      MAGWalk G X Y Z u w

end

end CausalQIF.DSeparation
