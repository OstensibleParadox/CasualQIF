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
    condMutualInfo (pmfMargOutSnd P) ≤ condMutualInfo (pmfMargOutFst P) := by
  have h_chain_x : condMutualInfo (pmfMargOutSnd P) + condMutualInfo (pmfPairFstFthReshape P) = condMutualInfo (pmfMargOutFst P) + condMutualInfo (pmfPairSndFthReshape P) := by
    rw [cond_mutual_info_marg_out_snd, cond_mutual_info_pair_fst_fth_reshape, cond_mutual_info_marg_out_fst, cond_mutual_info_pair_snd_fth_reshape]
    ring
  have h_nonneg := cond_mutual_info_pair_fst_fth_reshape_nonneg P
  have h_zero := cond_mutual_info_pair_snd_fth_reshape_eq_zero_of_cond_markov P h
  rw [h_zero] at h_chain_x
  linarith

end

end CausalQIF.CausalModel
