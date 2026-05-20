import CausalQIF.DSeparation.TraceSynthesis.Split.Defs

open Finset
open Classical

namespace CausalQIF.DSeparation

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]

lemma finalArrival_into_decomp_aux {G : Graph.DAG V} {X Y Z : Finset V} {x a : V}
    (arr_init : TrailDir)
    (pre : StaticRoute G X Y Z x a) :
    pre.finalArrival arr_init = TrailDir.into →
    (∃ h : x = a, pre = h ▸ StaticRoute.nil x ∧ arr_init = TrailDir.into) ∨
    ∃ (a' : V) (pre' : StaticRoute G X Y Z x a') (hEdge : G.hasEdge a' a)
      (hu : a' ∈ G.dSeparationGraphNodes X Y Z) (hv : a ∈ G.dSeparationGraphNodes X Y Z),
      pre = pre'.append (StaticRoute.cons (StaticStep.directForward hEdge hu hv) (StaticRoute.nil a)) := by
  induction pre generalizing arr_init with
  | nil _ =>
      intro harr
      exact Or.inl ⟨rfl, rfl, harr⟩
  | cons step rest ih =>
      intro harr
      cases h_rest_eq : rest with
      | nil _ =>
          subst h_rest_eq
          cases step with
          | directForward hEdge hu hv =>
              exact Or.inr ⟨_, StaticRoute.nil _, hEdge, hu, hv, rfl⟩
          | directBackward _ _ _ =>
              dsimp [StaticRoute.finalArrival, StaticStep.nextArrival] at harr
              contradiction
          | moralJump _ _ _ _ _ _ =>
              dsimp [StaticRoute.finalArrival, StaticStep.nextArrival] at harr
              contradiction
      | cons step2 rest2 =>
          have harr2 : rest.finalArrival step.nextArrival = TrailDir.into := harr
          rcases ih step.nextArrival harr2 with ⟨h_eq, h_nil, _⟩ |
            ⟨a', pre', hEdge, hu, hv, hpre'_eq⟩
          · subst h_eq
            rw [h_nil] at h_rest_eq
            contradiction
          · exact Or.inr ⟨a', StaticRoute.cons step pre', hEdge, hu, hv, by
              dsimp [StaticRoute.append]
              rw [← h_rest_eq]
              rw [hpre'_eq]⟩

lemma finalArrival_into_decomp {G : Graph.DAG V} {X Y Z : Finset V} {x a : V}
    (pre : StaticRoute G X Y Z x a)
    (harr : pre.finalArrival TrailDir.outOf = TrailDir.into) :
    ∃ (a' : V) (pre' : StaticRoute G X Y Z x a') (hEdge : G.hasEdge a' a)
      (hu : a' ∈ G.dSeparationGraphNodes X Y Z) (hv : a ∈ G.dSeparationGraphNodes X Y Z),
      pre = pre'.append (StaticRoute.cons (StaticStep.directForward hEdge hu hv) (StaticRoute.nil a)) := by
  rcases finalArrival_into_decomp_aux TrailDir.outOf pre harr with contra | result
  · rcases contra with ⟨_, _, h_contra⟩
    contradiction
  · exact result

end

end CausalQIF.DSeparation
