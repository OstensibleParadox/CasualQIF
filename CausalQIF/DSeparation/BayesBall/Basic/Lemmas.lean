import CausalQIF.DSeparation.BayesBall.Basic.Basic

open Finset

namespace CausalQIF.DSeparation

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]

lemma not_mem_Z_of_active_noncollider {G : Graph.DAG V} {Z : Finset V} {a b c : V}
    (hactive : ¬ tripleBlocked G Z a b c)
    (hncoll : ¬ tripleCollider G a b c) :
    b ∉ Z := by
  intro hbZ
  exact hactive (Or.inl ⟨hncoll, hbZ⟩)

lemma not_mem_Z_of_active_directional_noncollider {G : Graph.DAG V} {Z : Finset V}
    {b : V} {arrival departure : TrailDir}
    (hopen : ¬ directionalTripleBlocked G Z b arrival departure)
    (hnot : ¬ (arrival = TrailDir.into ∧ departure = TrailDir.outOf)) :
    b ∉ Z := by
  intro hbZ
  exact hopen (Or.inl ⟨by simpa [TrailDir.colliderAtCurrent] using hnot, hbZ⟩)

lemma collider_mem_ancestralSubgraphNodes_of_active {G : Graph.DAG V} {X Y Z : Finset V}
    {a b c : V}
    (hactive : ¬ tripleBlocked G Z a b c)
    (hcoll : tripleCollider G a b c) :
    b ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z) := by
  classical
  have hnotDis :
      ¬ Disjoint ({b} ∪ Graph.descendants G b) Z := by
    intro hdis
    exact hactive (Or.inr ⟨hcoll, hdis⟩)
  rw [Finset.disjoint_left] at hnotDis
  push Not at hnotDis
  rcases hnotDis with ⟨z, hz_left, hzZ⟩
  have hbG : b ∈ G.nodes := (G.edges_subset hcoll.1).2
  have hreach : Graph.reachable G b z := by
    rcases Finset.mem_union.mp hz_left with hz_single | hz_desc
    · simp at hz_single
      subst z
      exact Relation.ReflTransGen.refl
    · exact (Finset.mem_filter.mp hz_desc).2.2
  have hzS : z ∈ X ∪ Y ∪ Z := by
    simp [hzZ]
  exact Finset.mem_biUnion.mpr
    ⟨z, hzS, by simp [Graph.DAG.ancestors, hbG, hreach]⟩

/--
If a trail segment starts with a forward edge `u → w` and remains active, then
the first target `w` is ancestral to `X ∪ Y ∪ Z`, provided the trail endpoint is.
Forward chains inherit ancestry from the right; a first reversal is an active
collider and is ancestral through `Z`.
-/
lemma first_forward_target_mem_ancestral_of_active
    {G : Graph.DAG V} {X Y Z : Finset V} {u w v : V}
    (h : G.hasEdge u w) (tail : Trail G w v)
    (h_active : ¬ trailBlocked G Z (u :: tail.toList))
    (hvA : v ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z)) :
    w ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z) := by
  induction tail generalizing u with
  | nil w =>
      simpa [Trail.toList] using hvA
  | forward h₂ tail₂ ih =>
      have htail_active :=
        not_trailBlocked_tail_of_not_trailBlocked_cons
          (by simpa [Trail.toList] using h_active)
      have hcA := ih h₂ htail_active hvA
      exact Graph.DAG.mem_ancestralSubgraphNodes_of_hasEdge_left h₂ hcA
  | backward h₂ tail₂ =>
      have hhead :=
        not_tripleBlocked_head_of_not_trailBlocked_trail (t := tail₂)
          (by simpa [Trail.toList] using h_active)
      exact collider_mem_ancestralSubgraphNodes_of_active
        (G := G) (X := X) (Y := Y) (Z := Z) hhead ⟨h, h₂⟩

end

end CausalQIF.DSeparation
