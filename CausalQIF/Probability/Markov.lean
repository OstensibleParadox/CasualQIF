import CausalQIF.Probability.Entropy

open Finset
open scoped BigOperators Real

namespace CausalQIF.Probability

noncomputable section

variable {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]

/-! ## Markov Chain Definitions -/

def marginalB (P : FinitePMF (α × β × γ)) (b : β) : ℝ :=
  ∑ a : α, ∑ c : γ, P.pmf (a, b, c)

def marginalAB (P : FinitePMF (α × β × γ)) (ab : α × β) : ℝ :=
  ∑ c : γ, P.pmf (ab.1, ab.2, c)

def marginalBC (P : FinitePMF (α × β × γ)) (bc : β × γ) : ℝ :=
  ∑ a : α, P.pmf (a, bc.1, bc.2)

def IsMarkovChain (P : FinitePMF (α × β × γ)) : Prop :=
  ∀ a b c,
    P.pmf (a, b, c) * marginalB P b =
      marginalAB P (a, b) * marginalBC P (b, c)

/-! ## CMI=0 for Markov Chains -/

theorem cond_mutual_info_zero_of_markov (P : FinitePMF (α × β × γ))
    (hMC : IsMarkovChain P) : I_A_cond_C_B P = 0 := by
  sorry

end

end CausalQIF.Probability
