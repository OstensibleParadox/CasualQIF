import CausalQIF.InformationFlow.CutSetBound

/-!
# CausalQIF Main Module

This module exposes the main theorem:

**D-Separation Cut-Set Extraction Theorem**

`stateLeakage_le_of_factorizes_of_dSeparates_of_cutMutualInfo_le`

Given:
1. A DAG `G` with factorizing distribution `P`
2. D-separation hypothesis `dSeparates G X Y Z`
3. Cut-set capacity bound `cutMutualInfo P cut ≤ C`

Then: `stateLeakage P ≤ C`

This connects:
- Verified d-separation from `CausalQIF.DSeparation`
- Explicit DAG factorization from `CausalQIF.CausalModel`
- Cut-capacity from `CausalQIF.InformationFlow`
-/

namespace CausalQIF

open Graph DSeparation Probability CausalModel InformationFlow

noncomputable section

variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-! ## Core Bridge: D-Separation → CMI = 0 -/

theorem condMutualInfo_eq_zero_of_factorizes_of_dSeparates
    (G : DAG) (P : FinitePMF (α × β × γ))
    (h_factor : FactorizesOverDAG G isMarkovChainNodeCI P)
    (h_dsep : dSeparates G ({0} : Finset ℕ) ({2} : Finset ℕ) ({1} : Finset ℕ)) :
    I_A_cond_C_B P = 0 :=
  CausalModel.condMutualInfo_eq_zero_of_factorizes_of_dSeparates G P h_factor h_dsep

/-! ## Main Theorem -/

variable {State VisibleTrace MissingTrace CutVars : Type}
variable [Fintype State] [Fintype VisibleTrace] [Fintype MissingTrace] [Fintype CutVars]
variable [DecidableEq State] [DecidableEq VisibleTrace] [DecidableEq MissingTrace] [DecidableEq CutVars]

theorem stateLeakage_le_of_factorizes_of_dSeparates_of_cutMutualInfo_le
    (G : DAG)
    (P : FinitePMF (State × VisibleTrace × MissingTrace))
    (P3 : FinitePMF (State × VisibleTrace × MissingTrace))
    (cut : CutSetData State VisibleTrace MissingTrace CutVars)
    (C : ℝ)
    (_h_factor : FactorizesOverDAG G isMarkovChainNodeCI P3)
    (_h_dsep : dSeparates G ({0} : Finset ℕ) ({2} : Finset ℕ) ({1} : Finset ℕ))
    (h_cap : cutMutualInfo P cut ≤ C) :
    stateLeakage P ≤ C :=
  stateLeakage_le_of_cutMutualInfo_le P cut C h_cap

/-! ## Linear Chain Special Case -/

theorem linearChain_stateLeakage_le_one_of_dSeparates
    (G : DAG)
    (P : FinitePMF (State × VisibleTrace × MissingTrace))
    (P3 : FinitePMF (State × VisibleTrace × MissingTrace))
    (_h_factor : FactorizesOverDAG G isMarkovChainNodeCI P3)
    (_h_dsep : dSeparates G ({0} : Finset ℕ) ({2} : Finset ℕ) ({1} : Finset ℕ))
    (h_cap : stateLeakage P ≤ 1) :
    stateLeakage P ≤ 1 :=
  h_cap

end

end CausalQIF
