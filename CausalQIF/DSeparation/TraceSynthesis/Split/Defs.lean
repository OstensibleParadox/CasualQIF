import CausalQIF.DSeparation.TraceSynthesis.OpenTrace

open Finset
open Classical

namespace CausalQIF.DSeparation

noncomputable section

/-! # Route Splitting

Extraction of the first bad collider from a static route.
-/

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Data extracted from the first bad collider in a static route. -/
structure Split (G : Graph.DAG V) (X Y Z : Finset V) (x y : V) where
  a : V
  b : V
  child : V
  pre : StaticRoute G X Y Z x a
  suf : StaticRoute G X Y Z b y
  huw : G.hasEdge a child
  hbw : G.hasEdge b child
  ha : a ∈ G.dSeparationGraphNodes X Y Z
  hb : b ∈ G.dSeparationGraphNodes X Y Z
  hchildA : child ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z)
  hbad : Disjoint ({child} ∪ Graph.descendants G child) Z
  hprefixZero : countBadColliders TrailDir.outOf pre = 0
  route : StaticRoute G X Y Z x y
  hcount : countBadColliders TrailDir.outOf pre + 1 +
    countBadColliders TrailDir.outOf suf ≤ countBadColliders TrailDir.outOf route

end

end CausalQIF.DSeparation
