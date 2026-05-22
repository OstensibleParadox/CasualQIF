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
def hSCondTtilde (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace)) : ℝ :=
  Probability.entropyOf (stateVisibleMass P) - Probability.entropyOf (visibleMass P)

/-- `H(S ∣ T_full)`, where `T_full = (T̃, M)`. -/
def hSCondTfull (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace)) : ℝ :=
  fullTraceEntropy P - Probability.entropyOf (visibleMissingMass P)

/-! ## Cut Mutual Information -/

structure CutSetData (State VisibleTrace MissingTrace CutVars : Type) [Fintype CutVars] [DecidableEq CutVars] where
  cut_map : (State × VisibleTrace × MissingTrace) → CutVars

/--
The 4-variable PMF layout for DPI: (X=State, Y=Cut, Z=Missing, W=Visible).
-/
def pmfFromVars {CutVars : Type} [Fintype CutVars] [DecidableEq CutVars]
    (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace))
    (cut : CutSetData State VisibleTrace MissingTrace CutVars) :
    Probability.FinitePMF (State × CutVars × MissingTrace × VisibleTrace) :=
  P.map (fun stm => (stm.1, cut.cut_map stm, stm.2.2, stm.2.1))

/-- Information-theoretic capacity of the cut: $I(K; M \mid T)$. -/
def cutCapacity {CutVars : Type} [Fintype CutVars] [DecidableEq CutVars]
    (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace))
    (cut : CutSetData State VisibleTrace MissingTrace CutVars) : ℝ :=
  Probability.condMutualInfo (Probability.marginalizeOutFst (pmfFromVars P cut))

@[deprecated hSCondTtilde (since := "2026-05")]
alias H_S_cond_Ttilde := hSCondTtilde
@[deprecated hSCondTfull (since := "2026-05")]
alias H_S_cond_Tfull := hSCondTfull
@[deprecated pmfFromVars (since := "2026-05")]
alias pmf_from_vars := pmfFromVars

end

end CausalQIF.InformationFlow
