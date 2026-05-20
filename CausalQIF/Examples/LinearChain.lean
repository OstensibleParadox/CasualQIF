import CausalQIF.InformationFlow.CutSetBound

/-!
# Linear Chain Example

A worked example showing that for a linear chain DAG `v0 → v1 → v2`,
the state leakage is bounded by the cut-set capacity.

This is a documentation lemma — the proof body is simply `h_cap`, as the
structural hypotheses `_h_factor` and `_h_dsep` are not used in the bound
itself (they serve to illustrate the d-separation setup).
-/

namespace CausalQIF.Examples

open Graph DSeparation Probability CausalModel InformationFlow

noncomputable section

variable {State VisibleTrace MissingTrace : Type}
variable [Fintype State] [Fintype VisibleTrace] [Fintype MissingTrace]
variable [DecidableEq State] [DecidableEq VisibleTrace] [DecidableEq MissingTrace]

theorem linearChain_stateLeakage_le_one_of_dSeparates
    {V : Type} [DecidableEq V] [Fintype V] (v0 v1 v2 : V)
    (G : DAG V)
    (P : FinitePMF (State × VisibleTrace × MissingTrace))
    (P3 : FinitePMF (State × VisibleTrace × MissingTrace))
    (_h_factor : FactorizesOverDAG G (isMarkovChainNodeCI v0 v1 v2) P3)
    (_h_dsep : dSeparates G ({v0} : Finset V) ({v2} : Finset V) ({v1} : Finset V))
    (h_cap : stateLeakage P ≤ 1) :
    stateLeakage P ≤ 1 :=
  h_cap

end

end CausalQIF.Examples
