import CausalQIF.InformationFlow.CutSetBound.Defs

open Finset
open scoped BigOperators Real

namespace CausalQIF.InformationFlow

noncomputable section

variable {State VisibleTrace MissingTrace : Type}
variable [Fintype State] [Fintype VisibleTrace] [Fintype MissingTrace]
variable [DecidableEq State] [DecidableEq VisibleTrace] [DecidableEq MissingTrace]

/--
The Fundamental Theorem of Information-Flow Security
(the verified Refinement Hook for bridging discrete bounds to continuous states).
By the chain rule of entropy: `H(S ∣ T̃) = H(S ∣ T_full) + I(S; M ∣ T̃)`.
-/
lemma entropy_security_decomposition
    (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace)) :
    hSCondTtilde P = hSCondTfull P + stateLeakage P := by
  unfold hSCondTtilde hSCondTfull stateLeakage fullTraceEntropy
  ring

lemma pmfFromVars_apply {CutVars : Type} [Fintype CutVars] [DecidableEq CutVars]
    (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace))
    (cut : CutSetData State VisibleTrace MissingTrace CutVars)
    (s : State) (k : CutVars) (m : MissingTrace) (t : VisibleTrace) :
    (pmfFromVars P cut).pmf (s, k, m, t) =
      if cut.cut_map (s, t, m) = k then P.pmf (s, t, m) else 0 := by
  change
    (∑ x : State × VisibleTrace × MissingTrace,
      if (x.1, cut.cut_map x, x.2.2, x.2.1) = (s, k, m, t) then P.pmf x else 0)
      =
        if cut.cut_map (s, t, m) = k then P.pmf (s, t, m) else 0
  by_cases h : cut.cut_map (s, t, m) = k
  · rw [if_pos h]
    rw [Finset.sum_eq_single (s, t, m)]
    · simp [h]
    · intro x _ hx
      simp only [ite_eq_right_iff]
      intro hcond
      exfalso
      apply hx
      rcases Prod.ext_iff.mp hcond with ⟨hs, rest⟩
      rcases Prod.ext_iff.mp rest with ⟨_, rest2⟩
      rcases Prod.ext_iff.mp rest2 with ⟨hm, ht⟩
      ext
      · exact hs
      · exact ht
      · exact hm
    · intro hmem
      simp at hmem
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro x _
    simp only [ite_eq_right_iff]
    intro hcond
    exfalso
    apply h
    rcases Prod.ext_iff.mp hcond with ⟨hs, rest⟩
    rcases Prod.ext_iff.mp rest with ⟨hcut, rest2⟩
    rcases Prod.ext_iff.mp rest2 with ⟨hm, ht⟩
    have hx : x = (s, t, m) := by
      ext
      · exact hs
      · exact ht
      · exact hm
    simpa [hx] using hcut

lemma marginalQuadFstFth_eq_stateVisibleMass {CutVars : Type} [Fintype CutVars]
    [DecidableEq CutVars]
    (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace))
    (cut : CutSetData State VisibleTrace MissingTrace CutVars) (st : State × VisibleTrace) :
    Probability.marginalQuadFstFth (pmfFromVars P cut) (st.1, st.2) = stateVisibleMass P st := by
  unfold Probability.marginalQuadFstFth stateVisibleMass
  calc
    ∑ k : CutVars, ∑ m : MissingTrace, (pmfFromVars P cut).pmf (st.1, k, m, st.2)
        =
      ∑ k : CutVars, ∑ m : MissingTrace,
        if cut.cut_map (st.1, st.2, m) = k then P.pmf (st.1, st.2, m) else 0 := by
          simp [pmfFromVars_apply]
    _ =
      ∑ m : MissingTrace, ∑ k : CutVars,
        if cut.cut_map (st.1, st.2, m) = k then P.pmf (st.1, st.2, m) else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ m : MissingTrace, P.pmf (st.1, st.2, m) := by
          simp

lemma marginalQuadFth_eq_visibleMass {CutVars : Type} [Fintype CutVars] [DecidableEq CutVars]
    (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace))
    (cut : CutSetData State VisibleTrace MissingTrace CutVars) (t : VisibleTrace) :
    Probability.marginalQuadFth (pmfFromVars P cut) t = visibleMass P t := by
  unfold Probability.marginalQuadFth visibleMass
  calc
    ∑ s : State, ∑ k : CutVars, ∑ m : MissingTrace,
        (pmfFromVars P cut).pmf (s, k, m, t)
        =
      ∑ s : State, ∑ k : CutVars, ∑ m : MissingTrace,
        if cut.cut_map (s, t, m) = k then P.pmf (s, t, m) else 0 := by
          simp [pmfFromVars_apply]
    _ =
      ∑ s : State, ∑ m : MissingTrace, ∑ k : CutVars,
        if cut.cut_map (s, t, m) = k then P.pmf (s, t, m) else 0 := by
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.sum_comm]
    _ = ∑ s : State, ∑ m : MissingTrace, P.pmf (s, t, m) := by
          simp

lemma marginalQuadThdFth_eq_visibleMissingMass_swap {CutVars : Type} [Fintype CutVars]
    [DecidableEq CutVars]
    (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace))
    (cut : CutSetData State VisibleTrace MissingTrace CutVars) (mt : MissingTrace × VisibleTrace) :
    Probability.marginalQuadThdFth (pmfFromVars P cut) mt = visibleMissingMass P (mt.2, mt.1) := by
  unfold Probability.marginalQuadThdFth visibleMissingMass
  change
    (∑ s : State, ∑ k : CutVars, (pmfFromVars P cut).pmf (s, k, mt.1, mt.2))
      =
        ∑ s : State, P.pmf (s, mt.2, mt.1)
  calc
    ∑ s : State, ∑ k : CutVars, (pmfFromVars P cut).pmf (s, k, mt.1, mt.2)
        =
      ∑ s : State, ∑ k : CutVars,
        if cut.cut_map (s, mt.2, mt.1) = k then P.pmf (s, mt.2, mt.1) else 0 := by
          apply Finset.sum_congr rfl
          intro s _
          apply Finset.sum_congr rfl
          intro k _
          simpa using pmfFromVars_apply P cut s k mt.1 mt.2
    _ = ∑ s : State, P.pmf (s, mt.2, mt.1) := by
          simp

lemma marginalQuadFstThdFth_eq_P_swap {CutVars : Type} [Fintype CutVars] [DecidableEq CutVars]
    (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace))
    (cut : CutSetData State VisibleTrace MissingTrace CutVars)
    (smt : State × MissingTrace × VisibleTrace) :
    Probability.marginalQuadFstThdFth (pmfFromVars P cut) smt =
      P.pmf (smt.1, smt.2.2, smt.2.1) := by
  unfold Probability.marginalQuadFstThdFth
  change
    (∑ k : CutVars, (pmfFromVars P cut).pmf (smt.1, k, smt.2.1, smt.2.2))
      =
        P.pmf (smt.1, smt.2.2, smt.2.1)
  calc
    ∑ k : CutVars, (pmfFromVars P cut).pmf (smt.1, k, smt.2.1, smt.2.2)
        =
      ∑ k : CutVars,
        if cut.cut_map (smt.1, smt.2.2, smt.2.1) = k
          then P.pmf (smt.1, smt.2.2, smt.2.1)
          else 0 := by
          apply Finset.sum_congr rfl
          intro k _
          simpa using pmfFromVars_apply P cut smt.1 k smt.2.1 smt.2.2
    _ = P.pmf (smt.1, smt.2.2, smt.2.1) := by
          simp

@[deprecated marginalQuadThdFth_eq_visibleMissingMass_swap (since := "2026-05")]
alias marginalQuad_ThdFth_eq_visibleMissingMass_swap := marginalQuadThdFth_eq_visibleMissingMass_swap
@[deprecated marginalQuadFstFth_eq_stateVisibleMass (since := "2026-05")]
alias marginalQuad_FstFth_eq_stateVisibleMass := marginalQuadFstFth_eq_stateVisibleMass
@[deprecated marginalQuadFstThdFth_eq_P_swap (since := "2026-05")]
alias marginalQuad_FstThdFth_eq_P_swap := marginalQuadFstThdFth_eq_P_swap
@[deprecated marginalQuadFth_eq_visibleMass (since := "2026-05")]
alias marginalQuad_Fth_eq_visibleMass := marginalQuadFth_eq_visibleMass
@[deprecated pmfFromVars_apply (since := "2026-05")]
alias pmf_from_vars_apply := pmfFromVars_apply

end

end CausalQIF.InformationFlow
