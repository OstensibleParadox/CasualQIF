import CausalQIF.InformationFlow.CutSetBound.Basic

open Finset
open scoped BigOperators Real

namespace CausalQIF.InformationFlow

noncomputable section

variable {State VisibleTrace MissingTrace : Type}
variable [Fintype State] [Fintype VisibleTrace] [Fintype MissingTrace]
variable [DecidableEq State] [DecidableEq VisibleTrace] [DecidableEq MissingTrace]

/-- The original leakage CMI equals `condMutualInfo` of the `marginalizeOutSnd` of the four-variable cut PMF. -/
lemma stateLeakage_eq_condMutualInfo_pmfMargOutSnd_pmfFromVars {CutVars : Type} [Fintype CutVars]
    [DecidableEq CutVars]
    (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace))
    (cut : CutSetData State VisibleTrace MissingTrace CutVars) :
    stateLeakage P = Probability.condMutualInfo (Probability.marginalizeOutSnd (pmfFromVars P cut)) := by
  let P4 := pmfFromVars P cut
  have hXW : Probability.entropyOf (Probability.marginalQuadFstFth P4) =
      Probability.entropyOf (stateVisibleMass P) := by
    unfold Probability.entropyOf
    apply sum_congr rfl
    intro xw _
    rw [marginalQuadFstFth_eq_stateVisibleMass]
  have hZW : Probability.entropyOf (Probability.marginalQuadThdFth P4) =
      Probability.entropyOf (visibleMissingMass P) := by
    let e : (MissingTrace × VisibleTrace) ≃ (VisibleTrace × MissingTrace) :=
      Equiv.prodComm MissingTrace VisibleTrace
    exact Probability.entropyOf_equiv_eq e (fun mt => Probability.marginalQuadThdFth P4 mt)
      (visibleMissingMass P)
      (fun mt => by simpa using marginalQuadThdFth_eq_visibleMissingMass_swap P cut mt)
  have hW : Probability.entropyOf (Probability.marginalQuadFth P4) =
      Probability.entropyOf (visibleMass P) := by
    unfold Probability.entropyOf
    apply sum_congr rfl
    intro w _
    rw [marginalQuadFth_eq_visibleMass]
  have hXZW : Probability.entropyOf (Probability.marginalQuadFstThdFth P4) =
      fullTraceEntropy P := by
    let e : (State × MissingTrace × VisibleTrace) ≃ (State × VisibleTrace × MissingTrace) :=
      (Equiv.refl State).prodCongr (Equiv.prodComm MissingTrace VisibleTrace)
    unfold fullTraceEntropy
    exact Probability.entropyOf_equiv_eq e (fun smt => Probability.marginalQuadFstThdFth P4 smt)
      P.pmf
      (fun smt => by simpa using marginalQuadFstThdFth_eq_P_swap P cut smt)
  rw [Probability.condMutualInfo_pmfMargOutSnd]
  unfold stateLeakage
  rw [hXW, hZW, hW, hXZW]

/--
The machine-checked Shannon leakage upper bound.
If the cut-set $K$ d-separates State from MissingTrace, then by DPI:
$I(S; M \mid T) \leq I(K; M \mid T)$.
-/
theorem stateLeakage_le_of_cutMutualInfo_le {CutVars : Type}
    [Fintype CutVars] [DecidableEq CutVars]
    (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace))
    (cut : CutSetData State VisibleTrace MissingTrace CutVars)
    (C : ℝ)
    (h_factor : Probability.condMarkov (pmfFromVars P cut))
    (h_cap : cutCapacity P cut ≤ C) :
    stateLeakage P ≤ C := by
  let P4 := pmfFromVars P cut
  have h_eq : stateLeakage P = Probability.condMutualInfo (Probability.marginalizeOutSnd P4) :=
    stateLeakage_eq_condMutualInfo_pmfMargOutSnd_pmfFromVars P cut
  have h_dpi : Probability.condMutualInfo (Probability.marginalizeOutSnd P4) ≤ Probability.condMutualInfo (Probability.marginalizeOutFst P4) :=
    CausalModel.cond_dpi P4 h_factor
  calc
    stateLeakage P = Probability.condMutualInfo (Probability.marginalizeOutSnd P4) := h_eq
    _ ≤ Probability.condMutualInfo (Probability.marginalizeOutFst P4) := h_dpi
    _ ≤ C := h_cap

@[deprecated stateLeakage_eq_condMutualInfo_pmfMargOutSnd_pmfFromVars (since := "2026-05")]
alias stateLeakage_eq_condMutualInfo_pmfMargOutSnd_pmf_from_vars := stateLeakage_eq_condMutualInfo_pmfMargOutSnd_pmfFromVars

end

end CausalQIF.InformationFlow
