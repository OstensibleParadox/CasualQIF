import CausalQIF.InformationFlow.CutSetBound
import CausalQIF.InformationFlow.Duality

/-!
# CausalQIF Main Module

This module exposes the headline theorems:

**Cut-Set Leakage Bound**

`stateLeakage_le_of_factorizes_of_dSeparates_of_cutMutualInfo_le`

Given a DAG `G` with factorizing distribution, d-separation, and a cut-set
capacity bound `cutCapacity P cut ≤ C`, then `stateLeakage P ≤ C`.

**Certified Leakage Gap**

`certified_leakage_gap_of_dSeparated_graph`

Elevates the cut-set bound to an operational security limit:
`H(S ∣ T̃) ≤ H(S ∣ T_full) + C`.

**Dual Witness Bound**

`stateLeakage_le_of_dual_witness`

Composes the cut-set bound with the variational duality theorem to derive
`stateLeakage P ≤ C` from a KL-divergence witness.

This module connects:
- Verified d-separation from `CausalQIF.DSeparation`
- Explicit DAG factorization from `CausalQIF.CausalModel`
- Cut-capacity and duality from `CausalQIF.InformationFlow`
-/

namespace CausalQIF

open Graph DSeparation Probability CausalModel InformationFlow

noncomputable section

/-! ## Main Theorem -/

variable {State VisibleTrace MissingTrace CutVars : Type}
variable [Fintype State] [Fintype VisibleTrace] [Fintype MissingTrace] [Fintype CutVars]
variable [DecidableEq State] [DecidableEq VisibleTrace] [DecidableEq MissingTrace] [DecidableEq CutVars]

theorem stateLeakage_le_of_factorizes_of_dSeparates_of_cutMutualInfo_le
    {V : Type} [DecidableEq V] [Fintype V] (vX vY vZ vW : V)
    (G : DAG V)
    (P : FinitePMF (State × VisibleTrace × MissingTrace))
    (cut : CutSetData State VisibleTrace MissingTrace CutVars)
    (C : ℝ)
    (h_factor : FactorizesOverDAG G (condMarkovNodeCI vX vY vZ vW) (pmfFromVars P cut))
    (h_dsep : dSeparates G ({vX} : Finset V) ({vZ} : Finset V) ({vY, vW} : Finset V))
    (h_cap : cutCapacity P cut ≤ C) :
    stateLeakage P ≤ C :=
  stateLeakage_le_of_cutMutualInfo_le P cut C 
    (condMarkov_of_factorizes_of_dSeparates_fourVar vX vY vZ vW G (pmfFromVars P cut) h_factor h_dsep)
    h_cap

/--
The Grand Finale: certified Shannon leakage gap from d-separated traces.
Elevates a structural topological capacity bound into an absolute operational
security limit for an auditor: `H(S ∣ T̃) ≤ H(S ∣ T_full) + C`.
-/
theorem certified_leakage_gap_of_dSeparated_graph
    {V : Type} [DecidableEq V] [Fintype V] (vX vY vZ vW : V)
    (G : DAG V)
    (P : FinitePMF (State × VisibleTrace × MissingTrace))
    (cut : CutSetData State VisibleTrace MissingTrace CutVars)
    (C : ℝ)
    (h_factor : FactorizesOverDAG G (condMarkovNodeCI vX vY vZ vW) (pmfFromVars P cut))
    (h_dsep : dSeparates G ({vX} : Finset V) ({vZ} : Finset V) ({vY, vW} : Finset V))
    (h_cap : cutCapacity P cut ≤ C) :
    hSCondTtilde P ≤ hSCondTfull P + C := by
  have h_mi_bound :=
    stateLeakage_le_of_factorizes_of_dSeparates_of_cutMutualInfo_le
      vX vY vZ vW G P cut C h_factor h_dsep h_cap
  rw [entropy_security_decomposition P]
  exact add_le_add (le_refl _) h_mi_bound


/--
The Shannon leakage bound derived from a dual KL witness.
Composes the cut-set bound with the variational duality theorem.
-/
theorem stateLeakage_le_of_dual_witness
    {V : Type} [DecidableEq V] [Fintype V] (vX vY vZ vW : V)
    (G : DAG V)
    (P : FinitePMF (State × VisibleTrace × MissingTrace))
    (cut : CutSetData State VisibleTrace MissingTrace CutVars)
    (ω : VisibleTrace → MissingTrace → ℝ)
    (h_ω_sum : ∀ w, ∑ z, ω w z = 1)
    (h_ω_pos : ∀ w z, 0 < ω w z)
    (C : ℝ)
    (h_factor : FactorizesOverDAG G (condMarkovNodeCI vX vY vZ vW) (pmfFromVars P cut))
    (h_dsep : dSeparates G ({vX} : Finset V) ({vZ} : Finset V) ({vY, vW} : Finset V))
    (h_bound : ∑ y, ∑ z, ∑ w, (marginalizeOutFst (pmfFromVars P cut)).pmf (y, z, w) * 
               Real.log ((marginalizeOutFst (pmfFromVars P cut)).pmf (y, z, w) / (marginalTripleFstThd (marginalizeOutFst (pmfFromVars P cut)) (y, w) * ω w z)) 
               ≤ C * Real.log 2) :
    stateLeakage P ≤ C :=
  stateLeakage_le_of_factorizes_of_dSeparates_of_cutMutualInfo_le vX vY vZ vW G P cut C h_factor h_dsep
    (condMutualInfo_le_of_dual_witness (marginalizeOutFst (pmfFromVars P cut)) ω h_ω_sum h_ω_pos C h_bound)

end

end CausalQIF
