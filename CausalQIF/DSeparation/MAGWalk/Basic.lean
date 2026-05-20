import CausalQIF.DSeparation.MAGWalk.Defs

open Finset

namespace CausalQIF.DSeparation

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]

lemma mem_ancestralSubgraphNodes_of_mem_dSeparationGraphNodes
    {G : Graph.DAG V} {X Y Z : Finset V} {v : V}
    (hv : v ∈ G.dSeparationGraphNodes X Y Z) :
    v ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z) := by
  exact (Finset.mem_sdiff.mp (by simpa [Graph.DAG.dSeparationGraphNodes] using hv)).1

lemma dSeparationGraph_adj_of_mag_single
    {G : Graph.DAG V} {X Y Z : Finset V} {u v : V}
    (hEdge : G.hasEdge u v ∨ G.hasEdge v u)
    (hu : u ∈ G.dSeparationGraphNodes X Y Z)
    (hv : v ∈ G.dSeparationGraphNodes X Y Z) :
    (G.dSeparationGraph X Y Z).Adj u v := by
  have huA0 : u ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z) :=
    mem_ancestralSubgraphNodes_of_mem_dSeparationGraphNodes hu
  have hvA0 : v ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z) :=
    mem_ancestralSubgraphNodes_of_mem_dSeparationGraphNodes hv
  have hne : u ≠ v := by
    rcases hEdge with huv | hvu
    · exact G.ne_of_hasEdge huv
    · exact Ne.symm (G.ne_of_hasEdge hvu)
  refine ⟨hu, hv, ?_⟩
  dsimp [Graph.DAG.moralGraph]
  refine ⟨huA0, hvA0, hne, ?_⟩
  rcases hEdge with huv | hvu
  · left
    exact Finset.mem_filter.mpr ⟨by simpa [Graph.DAG.hasEdge] using huv, huA0, hvA0⟩
  · right
    left
    exact Finset.mem_filter.mpr ⟨by simpa [Graph.DAG.hasEdge] using hvu, hvA0, huA0⟩

lemma dSeparationGraph_adj_of_mag_jump
    {G : Graph.DAG V} {X Y Z : Finset V} {u v w : V}
    (huw : G.hasEdge u w)
    (hvw : G.hasEdge v w)
    (hne : u ≠ v)
    (hu : u ∈ G.dSeparationGraphNodes X Y Z)
    (hv : v ∈ G.dSeparationGraphNodes X Y Z)
    (hw : w ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z)) :
    (G.dSeparationGraph X Y Z).Adj u v := by
  have huA0 : u ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z) :=
    mem_ancestralSubgraphNodes_of_mem_dSeparationGraphNodes hu
  have hvA0 : v ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z) :=
    mem_ancestralSubgraphNodes_of_mem_dSeparationGraphNodes hv
  refine ⟨hu, hv, ?_⟩
  dsimp [Graph.DAG.moralGraph]
  refine ⟨huA0, hvA0, hne, Or.inr (Or.inr ?_)⟩
  refine ⟨w, ?_, ?_, hne⟩
  · exact Finset.mem_filter.mpr ⟨by simpa [Graph.DAG.hasEdge] using huw, huA0, hw⟩
  · exact Finset.mem_filter.mpr ⟨by simpa [Graph.DAG.hasEdge] using hvw, hvA0, hw⟩

theorem MAGWalk.to_dSeparationGraph_reachable
    {G : Graph.DAG V} {X Y Z : Finset V} {u v : V}
    (h : MAGWalk G X Y Z u v) :
    (G.dSeparationGraph X Y Z).Reachable u v := by
  induction h with
  | refl u =>
      exact SimpleGraph.Reachable.refl u
  | single hEdge hu hv =>
      exact SimpleGraph.Adj.reachable (dSeparationGraph_adj_of_mag_single hEdge hu hv)
  | jump huw hvw hne hu hv hw =>
      exact SimpleGraph.Adj.reachable (dSeparationGraph_adj_of_mag_jump huw hvw hne hu hv hw)
  | trans _ _ ihuv ihvw =>
      exact SimpleGraph.Reachable.trans ihuv ihvw

lemma mag_single_or_jump_of_dSeparationGraph_adj
    {G : Graph.DAG V} {X Y Z : Finset V} {u v : V}
    (h : (G.dSeparationGraph X Y Z).Adj u v) :
    MAGWalk G X Y Z u v := by
  rcases h with ⟨hu, hv, hmoral⟩
  dsimp [Graph.DAG.moralGraph] at hmoral
  rcases hmoral with ⟨_, _, hne, hdir | hrev | hcop⟩
  · have hmem :
        (u, v) ∈ G.edges.filter (fun e =>
          e.1 ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z) ∧
            e.2 ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z)) := by
        simpa [Graph.DAG.ancestralSubgraph, Graph.DAG.hasEdge] using hdir
    exact MAGWalk.single (G := G) (X := X) (Y := Y) (Z := Z)
      (Or.inl (by simpa [Graph.DAG.hasEdge] using (Finset.mem_filter.mp hmem).1)) hu hv
  · have hmem :
        (v, u) ∈ G.edges.filter (fun e =>
          e.1 ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z) ∧
            e.2 ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z)) := by
        simpa [Graph.DAG.ancestralSubgraph, Graph.DAG.hasEdge] using hrev
    exact MAGWalk.single (G := G) (X := X) (Y := Y) (Z := Z)
      (Or.inr (by simpa [Graph.DAG.hasEdge] using (Finset.mem_filter.mp hmem).1)) hu hv
  · rcases hcop with ⟨w, huw', hvw', huw_ne_v⟩
    have huw_mem :
        (u, w) ∈ G.edges.filter (fun e =>
          e.1 ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z) ∧
            e.2 ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z)) := by
        simpa [Graph.DAG.ancestralSubgraph, Graph.DAG.hasEdge] using huw'
    have hvw_mem :
        (v, w) ∈ G.edges.filter (fun e =>
          e.1 ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z) ∧
            e.2 ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z)) := by
        simpa [Graph.DAG.ancestralSubgraph, Graph.DAG.hasEdge] using hvw'
    exact MAGWalk.jump (G := G) (X := X) (Y := Y) (Z := Z)
      (by simpa [Graph.DAG.hasEdge] using (Finset.mem_filter.mp huw_mem).1)
      (by simpa [Graph.DAG.hasEdge] using (Finset.mem_filter.mp hvw_mem).1)
      huw_ne_v hu hv (by
        simpa using (Finset.mem_filter.mp huw_mem).2.2)

theorem MAGWalk.of_dSeparationGraph_reachable
    {G : Graph.DAG V} {X Y Z : Finset V} {u v : V}
    (h : (G.dSeparationGraph X Y Z).Reachable u v) :
    MAGWalk G X Y Z u v := by
  rcases h with ⟨p⟩
  induction p with
  | nil =>
      exact MAGWalk.refl _
  | cons hAdj _ ih =>
      exact MAGWalk.trans (mag_single_or_jump_of_dSeparationGraph_adj hAdj) ih

theorem magWalk_iff_dSeparationGraph_reachable
    {G : Graph.DAG V} {X Y Z : Finset V} {u v : V} :
    MAGWalk G X Y Z u v ↔ (G.dSeparationGraph X Y Z).Reachable u v :=
  ⟨MAGWalk.to_dSeparationGraph_reachable, MAGWalk.of_dSeparationGraph_reachable⟩

end

end CausalQIF.DSeparation
