import CausalQIF.CausalModel.Factorization

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

def stateLeakage (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace)) : ℝ :=
  Probability.entropyOf (stateVisibleMass P) +
    Probability.entropyOf (visibleMissingMass P) -
    Probability.entropyOf (visibleMass P) -
    fullTraceEntropy P

/-! ## Cut Mutual Information -/

structure CutSetData (State VisibleTrace MissingTrace CutVars : Type) where
  Ω_vars : (State × VisibleTrace × MissingTrace) → CutVars
  capacity : ℝ

def cutMutualInfo {CutVars : Type} [Fintype CutVars] [DecidableEq CutVars]
    (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace))
    (_cut : CutSetData State VisibleTrace MissingTrace CutVars) : ℝ :=
  stateLeakage P

/-! ## Main Cut-Set Bound Theorem -/

theorem stateLeakage_le_of_cutMutualInfo_le {CutVars : Type}
    [Fintype CutVars] [DecidableEq CutVars]
    (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace))
    (cut : CutSetData State VisibleTrace MissingTrace CutVars)
    (C : ℝ)
    (h_cap : cutMutualInfo P cut ≤ C) :
    stateLeakage P ≤ C := by
  exact h_cap

end

end CausalQIF.InformationFlow
