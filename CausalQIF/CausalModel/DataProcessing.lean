import CausalQIF.Probability.Entropy

open Finset
open scoped BigOperators Real

namespace CausalQIF.CausalModel

noncomputable section

variable {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]

open Probability

/-- **Conditional Data Processing Inequality**.
    If X-Y-Z is a Markov chain given W, then I(X;Z|W) ≤ I(Y;Z|W). -/
theorem cond_dpi (P : FinitePMF (α × β × γ × δ)) (h : condMarkov P) :
    condMutualInfo (marginalizeOutSnd P) ≤ condMutualInfo (marginalizeOutFst P) := by
  have h_chain_x : condMutualInfo (marginalizeOutSnd P) + condMutualInfo (pmfPairFstFthReshape P) = condMutualInfo (marginalizeOutFst P) + condMutualInfo (pmfPairSndFthReshape P) := by
    rw [condMutualInfo_pmfMargOutSnd, condMutualInfo_pmfPairFstFthReshape, condMutualInfo_pmfMargOutFst, condMutualInfo_pmfPairSndFthReshape]
    ring
  have h_nonneg := condMutualInfo_nonneg (pmfPairFstFthReshape P)
  have h_zero := condMutualInfo_pmfPairSndFthReshape_eq_zero_of_condMarkov P h
  rw [h_zero] at h_chain_x
  linarith

end

end CausalQIF.CausalModel
