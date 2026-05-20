import CausalQIF.DSeparation.BayesBall.Certified.Basic

open Finset

namespace CausalQIF.DSeparation

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]

def bayesBallPathCert_of_active_trail_outOf
    {G : Graph.DAG V} {X Y Z : Finset V} {u v : V}
    (t : Trail G u v)
    (h_active : ¬ t.isBlocked Z)
    (huZ : u ∉ Z)
    (huA : u ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z))
    (hvD : v ∈ G.dSeparationGraphNodes X Y Z) :
    Σ final_dir, {p : BayesBallPath G Z (u, TrailDir.outOf) (v, final_dir) //
      ∀ {q : V × TrailDir}, BayesBallPath.RequiredState p q →
        q.1 ∈ G.dSeparationGraphNodes X Y Z} := by
  cases t with
  | nil v =>
      refine ⟨TrailDir.outOf, ⟨BayesBallPath.nil (u, TrailDir.outOf), ?_⟩⟩
      intro q hreq
      cases hreq
  | forward h tail =>
      rename_i w₀
      have hstep :
          BayesBallStep G Z (u, TrailDir.outOf) (w₀, TrailDir.into) :=
        BayesBallStep.step (by simpa [TrailDir.edgeIntoCurrent] using h)
          (by
            simpa [Trail.startOpen] using
              (Trail.startOpen_outOf_of_not_mem (G := G) (Z := Z)
                (u := u) (v := v)
                (t := Trail.forward h tail) huZ))
      have htail_active : ¬ trailBlocked G Z (u :: tail.toList) := by
        simpa [Trail.isBlocked, Trail.toList] using h_active
      have hvA : v ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z) :=
        (Finset.mem_sdiff.mp (by
          simpa [Graph.DAG.dSeparationGraphNodes] using hvD)).1
      have hwA : w₀ ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z) :=
        first_forward_target_mem_ancestral_of_active
          (G := G) (X := X) (Y := Y) (Z := Z)
          h tail htail_active hvA
      rcases bayesBallPathCert_of_active_trail_from_prev
          (G := G) (X := X) (Y := Y) (Z := Z)
          (prev := u) (u := w₀) (v := v) (arrival := TrailDir.into)
          (by simpa [TrailDir.edgeIntoCurrent] using h)
          tail htail_active hwA hvD with
        ⟨final_dir, ⟨ptail, hreq_tail⟩⟩
      refine ⟨final_dir, ⟨BayesBallPath.cons hstep ptail, ?_⟩⟩
      intro q hreq
      cases ptail with
      | nil s =>
          cases hreq with
          | one _ =>
              simpa using hvD
      | cons step₂ rest =>
          cases hreq with
          | colliderTarget hcoll =>
              exact hreq_tail
                (BayesBallPath.required_first_target_of_outOf step₂ rest hcoll.2)
          | colliderRest hcoll hrest =>
              exact hreq_tail
                (BayesBallPath.required_rest_of_outOf step₂ rest hcoll.2 hrest)
          | noncolliderTarget hnot =>
              cases step₂ with
              | step hEdge hopen =>
                  have hwZ : w₀ ∉ Z :=
                    not_mem_Z_of_active_directional_noncollider hopen hnot
                  exact Graph.DAG.mem_dSeparationGraphNodes_of_ancestor_not_mem hwA hwZ
          | noncolliderRest _ htailReq =>
              exact hreq_tail htailReq
  | backward h tail =>
      rename_i w₀
      have hstep :
          BayesBallStep G Z (u, TrailDir.outOf) (w₀, TrailDir.outOf) :=
        BayesBallStep.step (by simpa [TrailDir.edgeIntoCurrent] using h)
          (by
            simpa [Trail.startOpen] using
              (Trail.startOpen_outOf_of_not_mem (G := G) (Z := Z)
                (u := u) (v := v)
                (t := Trail.backward h tail) huZ))
      have htail_active : ¬ trailBlocked G Z (u :: tail.toList) := by
        simpa [Trail.isBlocked, Trail.toList] using h_active
      have hwA : w₀ ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z) :=
        Graph.DAG.mem_ancestralSubgraphNodes_of_hasEdge_left h huA
      rcases bayesBallPathCert_of_active_trail_from_prev
          (G := G) (X := X) (Y := Y) (Z := Z)
          (prev := u) (u := w₀) (v := v) (arrival := TrailDir.outOf)
          (by simpa [TrailDir.edgeIntoCurrent] using h)
          tail htail_active hwA hvD with
        ⟨final_dir, ⟨ptail, hreq_tail⟩⟩
      refine ⟨final_dir, ⟨BayesBallPath.cons hstep ptail, ?_⟩⟩
      intro q hreq
      cases ptail with
      | nil s =>
          cases hreq with
          | one _ =>
              simpa using hvD
      | cons step₂ rest =>
          cases hreq with
          | colliderTarget hcoll =>
              cases hcoll.1
          | colliderRest hcoll _ =>
              cases hcoll.1
          | noncolliderTarget hnot =>
              cases step₂ with
              | step hEdge hopen =>
                  have hwZ : w₀ ∉ Z :=
                    not_mem_Z_of_active_directional_noncollider hopen hnot
                  exact Graph.DAG.mem_dSeparationGraphNodes_of_ancestor_not_mem hwA hwZ
          | noncolliderRest _ htailReq =>
              exact hreq_tail htailReq

end

end CausalQIF.DSeparation
