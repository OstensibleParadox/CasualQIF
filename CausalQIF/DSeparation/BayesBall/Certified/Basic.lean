import CausalQIF.DSeparation.BayesBall.Basic

open Finset

namespace CausalQIF.DSeparation

noncomputable section

/-! # Certified Bayes-Ball Paths

Constructors that produce explicit `BayesBallPath` objects together with a proof
that every `RequiredState` node survives deletion of `Z`, i.e. belongs to
`dSeparationGraphNodes`.
-/

variable {V : Type} [DecidableEq V] [Fintype V]

def bayesBallPathCert_of_active_trail_from_prev
    {G : Graph.DAG V} {X Y Z : Finset V}
    {prev u v : V} {arrival : TrailDir}
    (hprev : TrailDir.edgeIntoCurrent G prev u arrival)
    (t : Trail G u v)
    (h_active : ¬ trailBlocked G Z (prev :: t.toList))
    (huA : u ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z))
    (hvD : v ∈ G.dSeparationGraphNodes X Y Z) :
    Σ final_dir, {p : BayesBallPath G Z (u, arrival) (v, final_dir) //
      ∀ {q : V × TrailDir}, BayesBallPath.RequiredState p q →
        q.1 ∈ G.dSeparationGraphNodes X Y Z} := by
  induction t generalizing prev arrival with
  | nil v =>
      refine ⟨arrival, ⟨BayesBallPath.nil (v, arrival), ?_⟩⟩
      intro q hreq
      cases hreq
  | forward h tail ih =>
      rename_i u₀ w₀ v₀
      have hhead : ¬ tripleBlocked G Z prev u₀ w₀ :=
        not_tripleBlocked_head_of_not_trailBlocked_trail (t := tail) h_active
      have hstep :
          BayesBallStep G Z (u₀, arrival) (w₀, TrailDir.into) := by
        exact BayesBallStep.of_active_triple hprev
          (by simpa [TrailDir.edgeIntoCurrent] using h) hhead
      have htail_active : ¬ trailBlocked G Z (u₀ :: tail.toList) :=
        not_trailBlocked_tail_of_not_trailBlocked_cons h_active
      have hvA : v₀ ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z) :=
        (Finset.mem_sdiff.mp (by
          simpa [Graph.DAG.dSeparationGraphNodes] using hvD)).1
      have hwA : w₀ ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z) :=
        first_forward_target_mem_ancestral_of_active
          (G := G) (X := X) (Y := Y) (Z := Z)
          h tail htail_active hvA
      rcases ih (prev := u₀) (arrival := TrailDir.into)
          (by simpa [TrailDir.edgeIntoCurrent] using h)
          htail_active hwA hvD with
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
  | backward h tail ih =>
      rename_i u₀ w₀ v₀
      have hhead : ¬ tripleBlocked G Z prev u₀ w₀ :=
        not_tripleBlocked_head_of_not_trailBlocked_trail (t := tail) h_active
      have hstep :
          BayesBallStep G Z (u₀, arrival) (w₀, TrailDir.outOf) := by
        exact BayesBallStep.of_active_triple hprev
          (by simpa [TrailDir.edgeIntoCurrent] using h) hhead
      have htail_active : ¬ trailBlocked G Z (u₀ :: tail.toList) :=
        not_trailBlocked_tail_of_not_trailBlocked_cons h_active
      have hwA : w₀ ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z) :=
        Graph.DAG.mem_ancestralSubgraphNodes_of_hasEdge_left h huA
      rcases ih (prev := u₀) (arrival := TrailDir.outOf)
          (by simpa [TrailDir.edgeIntoCurrent] using h)
          htail_active hwA hvD with
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
