import CausalQIF.DSeparation.TraceSynthesis.Split.Basic

open Finset
open Classical

namespace CausalQIF.DSeparation

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]

lemma exists_split_aux {G : Graph.DAG V} {X Y Z : Finset V} {x a y : V}
    (pre : StaticRoute G X Y Z x a)
    (suf : StaticRoute G X Y Z a y)
    (hpre : countBadColliders TrailDir.outOf pre = 0)
    (hroute : countBadColliders TrailDir.outOf (pre.append suf) ≠ 0) :
    ∃ s : Split G X Y Z x y, s.route = pre.append suf := by
  induction len : suf.length generalizing a pre with
  | zero =>
      cases h_suf : suf with
      | nil _ =>
          rw [h_suf, StaticRoute.append_nil] at hroute
          exact False.elim (hroute hpre)
      | cons _ _ =>
          subst h_suf
          simp [StaticRoute.length] at len
  | succ n ih =>
      cases h_suf : suf with
      | nil _ =>
          subst h_suf
          simp [StaticRoute.length] at len
      | cons step rest =>
          rename_i mid
          have hlen : rest.length = n := by
            subst h_suf
            injection len
          let arr := pre.finalArrival TrailDir.outOf
          have harr_eq : arr = pre.finalArrival TrailDir.outOf := rfl
          by_cases hbad : isStepBad arr step
          · cases h_step : step with
            | directForward _ _ _ =>
                exfalso
                subst h_step
                revert hbad
                dsimp [isStepBad]
                intro h
                cases h
            | directBackward hEdge hu hv =>
                have harr_into : pre.finalArrival TrailDir.outOf = TrailDir.into := by
                  subst h_step
                  exact hbad.1
                rcases finalArrival_into_decomp pre harr_into with
                  ⟨a', pre', hEdge', hu', hv', hpre_eq⟩
                use {
                  a := a', b := mid, child := a,
                  pre := pre', suf := rest,
                  huw := hEdge', hbw := hEdge,
                  ha := hu', hb := hv, hchildA := (Finset.mem_sdiff.mp hv').1,
                  hbad := by
                    subst h_step
                    exact hbad.2,
                  hprefixZero := by
                    rw [hpre_eq, countBadColliders_append] at hpre
                    omega,
                  route := pre.append suf,
                  hcount := by
                    rw [h_suf, countBadColliders_append, hpre, zero_add, countBadColliders_cons]
                    have h_bad_eval : isStepBad arr step := hbad
                    rw [if_pos h_bad_eval]
                    have h_step_next : step.nextArrival = TrailDir.outOf := by
                      subst h_step
                      rfl
                    rw [h_step_next]
                    have hpre'_zero : countBadColliders TrailDir.outOf pre' = 0 := by
                      rw [hpre_eq, countBadColliders_append] at hpre
                      omega
                    rw [hpre'_zero]
                }
                subst h_suf h_step
                rfl
            | moralJump huw hvw hne hu hv hwA =>
                rename_i child
                use {
                  a := a, b := mid, child := child,
                  pre := pre, suf := rest,
                  huw := huw, hbw := hvw,
                  ha := hu, hb := hv, hchildA := hwA,
                  hbad := by
                    subst h_step
                    exact hbad,
                  hprefixZero := hpre,
                  route := pre.append suf,
                  hcount := by
                    rw [h_suf, countBadColliders_append, hpre, zero_add, countBadColliders_cons]
                    have h_bad_eval : isStepBad arr step := hbad
                    rw [if_pos h_bad_eval]
                    have h_step_next : step.nextArrival = TrailDir.outOf := by
                      subst h_step
                      rfl
                    rw [h_step_next]
                    omega
                }
                subst h_suf h_step
                rfl
          · let pre' := pre.append (StaticRoute.cons step (StaticRoute.nil mid))
            have heq : pre'.append rest = pre.append suf := by
              subst h_suf
              dsimp [pre']
              rw [StaticRoute.append_assoc]
              rfl
            have hpre' : countBadColliders TrailDir.outOf pre' = 0 := by
              dsimp [pre']
              rw [countBadColliders_append, hpre, zero_add, countBadColliders_cons, if_neg hbad]
              rfl
            have hroute' : countBadColliders TrailDir.outOf (pre'.append rest) ≠ 0 := by
              rw [heq]
              exact hroute
            rcases ih pre' rest hpre' hroute' hlen with ⟨s, hs_route⟩
            use s
            subst h_suf
            rw [heq] at hs_route
            exact hs_route

/--
If a route has a non-zero bad-collider count, it contains at least one bad
collider that can be extracted as a `Split`.
-/
theorem exists_split {G : Graph.DAG V} {X Y Z : Finset V} {x y : V}
    (route : StaticRoute G X Y Z x y) :
    countBadColliders TrailDir.outOf route ≠ 0 →
    ∃ s : Split G X Y Z x y, s.route = route := by
  intro h
  rcases exists_split_aux (StaticRoute.nil x) route rfl h with ⟨s, hs⟩
  use s
  exact hs

end

end CausalQIF.DSeparation
