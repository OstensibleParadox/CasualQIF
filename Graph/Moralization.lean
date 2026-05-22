import CausalQIF.Graph.Reachability

open Finset

namespace CausalQIF.Graph

noncomputable section

/-! # DAG Moralization

Co-parents, moral graph, d-separation graph, `DAG.dSeparated`.
-/

namespace DAG

variable {V : Type} [DecidableEq V] [Fintype V]

def coParents (G : DAG V) (u v : V) : Prop :=
  ∃ w : V, G.hasEdge u w ∧ G.hasEdge v w ∧ u ≠ v

def moralGraph (G : DAG V) (S : Finset V) : SimpleGraph V where
  Adj u v :=
    let G' := G.ancestralSubgraph S
    u ∈ G'.nodes ∧ v ∈ G'.nodes ∧ u ≠ v ∧
      (G'.hasEdge u v ∨ G'.hasEdge v u ∨ G'.coParents u v)
  symm := by
    intro u v h
    dsimp at h ⊢
    rcases h with ⟨hu, hv, hne, hedge | hedge | hcop⟩
    · exact ⟨hv, hu, Ne.symm hne, Or.inr (Or.inl hedge)⟩
    · exact ⟨hv, hu, Ne.symm hne, Or.inl hedge⟩
    · rcases hcop with ⟨w, huw, hvw, huw_ne⟩
      exact ⟨hv, hu, Ne.symm hne, Or.inr (Or.inr ⟨w, hvw, huw, Ne.symm huw_ne⟩)⟩
  loopless := by
    constructor
    intro u h
    exact h.2.2.1 rfl

def dSeparationGraphNodes (G : DAG V) (X Y Z : Finset V) : Finset V :=
  G.ancestralSubgraphNodes (X ∪ Y ∪ Z) \ Z

def dSeparationGraph (G : DAG V) (X Y Z : Finset V) : SimpleGraph V where
  Adj u v :=
    u ∈ G.dSeparationGraphNodes X Y Z ∧
      v ∈ G.dSeparationGraphNodes X Y Z ∧
      (G.moralGraph (X ∪ Y ∪ Z)).Adj u v
  symm := by
    intro u v h
    exact ⟨h.2.1, h.1, (G.moralGraph (X ∪ Y ∪ Z)).symm h.2.2⟩
  loopless := by
    constructor
    intro u h
    exact (G.moralGraph (X ∪ Y ∪ Z)).loopless.irrefl u h.2.2

def dSeparated (G : DAG V) (X Y Z : Finset V) : Prop :=
  ∀ x, x ∈ X → ∀ y, y ∈ Y → ¬(G.dSeparationGraph X Y Z).Reachable x y

lemma mem_dSeparationGraphNodes_of_ancestor_not_mem
    {G : DAG V} {X Y Z : Finset V} {v : V}
    (hvA : v ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z))
    (hvZ : v ∉ Z) :
    v ∈ G.dSeparationGraphNodes X Y Z := by
  exact Finset.mem_sdiff.mpr ⟨hvA, hvZ⟩

lemma mem_dSeparationGraphNodes_of_mem_left
    {G : DAG V} {X Y Z : Finset V} {v : V}
    (hvX : v ∈ X) (hvG : v ∈ G.nodes) (hvZ : v ∉ Z) :
    v ∈ G.dSeparationGraphNodes X Y Z := by
  exact mem_dSeparationGraphNodes_of_ancestor_not_mem
    (G := G) (X := X) (Y := Y) (Z := Z)
    (DAG.mem_ancestralSubgraphNodes_of_mem
      (G := G) (S := X ∪ Y ∪ Z) (v := v) (by simp [hvX]) hvG)
    hvZ

lemma mem_dSeparationGraphNodes_of_mem_right
    {G : DAG V} {X Y Z : Finset V} {v : V}
    (hvY : v ∈ Y) (hvG : v ∈ G.nodes) (hvZ : v ∉ Z) :
    v ∈ G.dSeparationGraphNodes X Y Z := by
  exact mem_dSeparationGraphNodes_of_ancestor_not_mem
    (G := G) (X := X) (Y := Y) (Z := Z)
    (DAG.mem_ancestralSubgraphNodes_of_mem
      (G := G) (S := X ∪ Y ∪ Z) (v := v) (by simp [hvY]) hvG)
    hvZ

omit [DecidableEq V] [Fintype V] in
lemma not_mem_right_of_disjoint_left {X Z : Finset V} {v : V}
    (hXZ : Disjoint X Z) (hvX : v ∈ X) :
    v ∉ Z := by
  intro hvZ
  exact (Finset.disjoint_left.mp hXZ) hvX hvZ

end DAG

end

end CausalQIF.Graph
