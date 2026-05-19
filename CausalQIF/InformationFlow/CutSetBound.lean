import CausalQIF.CausalModel.Factorization
import CausalQIF.CausalModel.DataProcessing

open Finset
open scoped BigOperators Real

namespace CausalQIF.InformationFlow

noncomputable section

variable {State VisibleTrace MissingTrace : Type}
variable [Fintype State] [Fintype VisibleTrace] [Fintype MissingTrace]
variable [DecidableEq State] [DecidableEq VisibleTrace] [DecidableEq MissingTrace]

/-! ## State Leakage Definitions -/

def stateVisibleMass (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace))
    (st : State × VisibleTrace) : ℝ :=
  ∑ m : MissingTrace, P.pmf (st.1, st.2, m)

def visibleMass (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace))
    (t : VisibleTrace) : ℝ :=
  ∑ s : State, ∑ m : MissingTrace, P.pmf (s, t, m)

def visibleMissingMass (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace))
    (tm : VisibleTrace × MissingTrace) : ℝ :=
  ∑ s : State, P.pmf (s, tm.1, tm.2)

def fullTraceEntropy (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace)) : ℝ :=
  Probability.entropyOf (fun stm : State × VisibleTrace × MissingTrace => P.pmf stm)

/-- 
The Shannon leakage $I(S; M \mid T)$ where $S$ is State, $M$ is MissingTrace, 
and $T$ is VisibleTrace. 
Calculated as $H(S, T) + H(M, T) - H(T) - H(S, M, T)$.
-/
def stateLeakage (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace)) : ℝ :=
  Probability.entropyOf (stateVisibleMass P) +
    Probability.entropyOf (visibleMissingMass P) -
    Probability.entropyOf (visibleMass P) -
    fullTraceEntropy P

/-! ## Conditional State Entropy and the Security Decomposition -/

/-- `H(S ∣ T̃)` — state entropy given the visible trace. -/
def H_S_cond_Ttilde (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace)) : ℝ :=
  Probability.entropyOf (stateVisibleMass P) - Probability.entropyOf (visibleMass P)

/-- `H(S ∣ T_full)`, where `T_full = (T̃, M)`. -/
def H_S_cond_Tfull (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace)) : ℝ :=
  fullTraceEntropy P - Probability.entropyOf (visibleMissingMass P)

/--
The Fundamental Theorem of Information-Flow Security
(the verified Refinement Hook for bridging discrete bounds to continuous states).
By the chain rule of entropy: `H(S ∣ T̃) = H(S ∣ T_full) + I(S; M ∣ T̃)`.
-/
lemma entropy_security_decomposition
    (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace)) :
    H_S_cond_Ttilde P = H_S_cond_Tfull P + stateLeakage P := by
  unfold H_S_cond_Ttilde H_S_cond_Tfull stateLeakage fullTraceEntropy
  ring

/-! ## Cut Mutual Information -/

structure CutSetData (State VisibleTrace MissingTrace CutVars : Type) [Fintype CutVars] [DecidableEq CutVars] where
  cut_map : (State × VisibleTrace × MissingTrace) → CutVars

/--
The 4-variable PMF layout for DPI: (X=State, Y=Cut, Z=Missing, W=Visible).
-/
def pmf_from_vars {CutVars : Type} [Fintype CutVars] [DecidableEq CutVars]
    (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace))
    (cut : CutSetData State VisibleTrace MissingTrace CutVars) :
    Probability.FinitePMF (State × CutVars × MissingTrace × VisibleTrace) :=
  P.map (fun stm => (stm.1, cut.cut_map stm, stm.2.2, stm.2.1))

lemma pmf_from_vars_apply {CutVars : Type} [Fintype CutVars] [DecidableEq CutVars]
    (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace))
    (cut : CutSetData State VisibleTrace MissingTrace CutVars)
    (s : State) (k : CutVars) (m : MissingTrace) (t : VisibleTrace) :
    (pmf_from_vars P cut).pmf (s, k, m, t) =
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

lemma marginalQuad_FstFth_eq_stateVisibleMass {CutVars : Type} [Fintype CutVars]
    [DecidableEq CutVars]
    (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace))
    (cut : CutSetData State VisibleTrace MissingTrace CutVars) (st : State × VisibleTrace) :
    Probability.marginalQuad_FstFth (pmf_from_vars P cut) (st.1, st.2) = stateVisibleMass P st := by
  unfold Probability.marginalQuad_FstFth stateVisibleMass
  calc
    ∑ k : CutVars, ∑ m : MissingTrace, (pmf_from_vars P cut).pmf (st.1, k, m, st.2)
        =
      ∑ k : CutVars, ∑ m : MissingTrace,
        if cut.cut_map (st.1, st.2, m) = k then P.pmf (st.1, st.2, m) else 0 := by
          simp [pmf_from_vars_apply]
    _ =
      ∑ m : MissingTrace, ∑ k : CutVars,
        if cut.cut_map (st.1, st.2, m) = k then P.pmf (st.1, st.2, m) else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ m : MissingTrace, P.pmf (st.1, st.2, m) := by
          simp

lemma marginalQuad_Fth_eq_visibleMass {CutVars : Type} [Fintype CutVars] [DecidableEq CutVars]
    (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace))
    (cut : CutSetData State VisibleTrace MissingTrace CutVars) (t : VisibleTrace) :
    Probability.marginalQuad_Fth (pmf_from_vars P cut) t = visibleMass P t := by
  unfold Probability.marginalQuad_Fth visibleMass
  calc
    ∑ s : State, ∑ k : CutVars, ∑ m : MissingTrace,
        (pmf_from_vars P cut).pmf (s, k, m, t)
        =
      ∑ s : State, ∑ k : CutVars, ∑ m : MissingTrace,
        if cut.cut_map (s, t, m) = k then P.pmf (s, t, m) else 0 := by
          simp [pmf_from_vars_apply]
    _ =
      ∑ s : State, ∑ m : MissingTrace, ∑ k : CutVars,
        if cut.cut_map (s, t, m) = k then P.pmf (s, t, m) else 0 := by
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.sum_comm]
    _ = ∑ s : State, ∑ m : MissingTrace, P.pmf (s, t, m) := by
          simp

lemma marginalQuad_ThdFth_eq_visibleMissingMass_swap {CutVars : Type} [Fintype CutVars]
    [DecidableEq CutVars]
    (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace))
    (cut : CutSetData State VisibleTrace MissingTrace CutVars) (mt : MissingTrace × VisibleTrace) :
    Probability.marginalQuad_ThdFth (pmf_from_vars P cut) mt = visibleMissingMass P (mt.2, mt.1) := by
  unfold Probability.marginalQuad_ThdFth visibleMissingMass
  change
    (∑ s : State, ∑ k : CutVars, (pmf_from_vars P cut).pmf (s, k, mt.1, mt.2))
      =
        ∑ s : State, P.pmf (s, mt.2, mt.1)
  calc
    ∑ s : State, ∑ k : CutVars, (pmf_from_vars P cut).pmf (s, k, mt.1, mt.2)
        =
      ∑ s : State, ∑ k : CutVars,
        if cut.cut_map (s, mt.2, mt.1) = k then P.pmf (s, mt.2, mt.1) else 0 := by
          apply Finset.sum_congr rfl
          intro s _
          apply Finset.sum_congr rfl
          intro k _
          simpa using pmf_from_vars_apply P cut s k mt.1 mt.2
    _ = ∑ s : State, P.pmf (s, mt.2, mt.1) := by
          simp

lemma marginalQuad_FstThdFth_eq_P_swap {CutVars : Type} [Fintype CutVars] [DecidableEq CutVars]
    (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace))
    (cut : CutSetData State VisibleTrace MissingTrace CutVars)
    (smt : State × MissingTrace × VisibleTrace) :
    Probability.marginalQuad_FstThdFth (pmf_from_vars P cut) smt =
      P.pmf (smt.1, smt.2.2, smt.2.1) := by
  unfold Probability.marginalQuad_FstThdFth
  change
    (∑ k : CutVars, (pmf_from_vars P cut).pmf (smt.1, k, smt.2.1, smt.2.2))
      =
        P.pmf (smt.1, smt.2.2, smt.2.1)
  calc
    ∑ k : CutVars, (pmf_from_vars P cut).pmf (smt.1, k, smt.2.1, smt.2.2)
        =
      ∑ k : CutVars,
        if cut.cut_map (smt.1, smt.2.2, smt.2.1) = k
          then P.pmf (smt.1, smt.2.2, smt.2.1)
          else 0 := by
          apply Finset.sum_congr rfl
          intro k _
          simpa using pmf_from_vars_apply P cut smt.1 k smt.2.1 smt.2.2
    _ = P.pmf (smt.1, smt.2.2, smt.2.1) := by
          simp

/-- The original leakage CMI equals `I_XZ_W` of the four-variable cut PMF. -/
lemma stateLeakage_eq_I_XZ_W_pmf_from_vars {CutVars : Type} [Fintype CutVars]
    [DecidableEq CutVars]
    (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace))
    (cut : CutSetData State VisibleTrace MissingTrace CutVars) :
    stateLeakage P = Probability.I_XZ_W (pmf_from_vars P cut) := by
  let P4 := pmf_from_vars P cut
  have hXW : Probability.entropyOf (Probability.marginalQuad_FstFth P4) =
      Probability.entropyOf (stateVisibleMass P) := by
    unfold Probability.entropyOf
    apply sum_congr rfl
    intro xw _
    rw [marginalQuad_FstFth_eq_stateVisibleMass]
  have hZW : Probability.entropyOf (Probability.marginalQuad_ThdFth P4) =
      Probability.entropyOf (visibleMissingMass P) := by
    let e : (MissingTrace × VisibleTrace) ≃ (VisibleTrace × MissingTrace) :=
      Equiv.prodComm MissingTrace VisibleTrace
    exact Probability.entropyOf_equiv_eq e (fun mt => Probability.marginalQuad_ThdFth P4 mt)
      (visibleMissingMass P)
      (fun mt => by simpa using marginalQuad_ThdFth_eq_visibleMissingMass_swap P cut mt)
  have hW : Probability.entropyOf (Probability.marginalQuad_Fth P4) =
      Probability.entropyOf (visibleMass P) := by
    unfold Probability.entropyOf
    apply sum_congr rfl
    intro w _
    rw [marginalQuad_Fth_eq_visibleMass]
  have hXZW : Probability.entropyOf (Probability.marginalQuad_FstThdFth P4) =
      fullTraceEntropy P := by
    let e : (State × MissingTrace × VisibleTrace) ≃ (State × VisibleTrace × MissingTrace) :=
      (Equiv.refl State).prodCongr (Equiv.prodComm MissingTrace VisibleTrace)
    unfold fullTraceEntropy
    exact Probability.entropyOf_equiv_eq e (fun smt => Probability.marginalQuad_FstThdFth P4 smt)
      P.pmf
      (fun smt => by simpa using marginalQuad_FstThdFth_eq_P_swap P cut smt)
  unfold stateLeakage Probability.I_XZ_W
  rw [hXW, hZW, hW, hXZW]

/-- Information-theoretic capacity of the cut: $I(K; M \mid T)$. -/
def cutCapacity {CutVars : Type} [Fintype CutVars] [DecidableEq CutVars]
    (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace))
    (cut : CutSetData State VisibleTrace MissingTrace CutVars) : ℝ :=
  Probability.I_YZ_W (pmf_from_vars P cut)

/-! ## Main Cut-Set Bound Theorem -/

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
    (h_factor : Probability.condMarkov (pmf_from_vars P cut))
    (h_cap : cutCapacity P cut ≤ C) :
    stateLeakage P ≤ C := by
  let P4 := pmf_from_vars P cut
  have h_eq : stateLeakage P = Probability.I_XZ_W P4 :=
    stateLeakage_eq_I_XZ_W_pmf_from_vars P cut
  have h_dpi : Probability.I_XZ_W P4 ≤ Probability.I_YZ_W P4 :=
    CausalModel.cond_dpi P4 h_factor
  calc
    stateLeakage P = Probability.I_XZ_W P4 := h_eq
    _ ≤ Probability.I_YZ_W P4 := h_dpi
    _ ≤ C := h_cap

end

end CausalQIF.InformationFlow
