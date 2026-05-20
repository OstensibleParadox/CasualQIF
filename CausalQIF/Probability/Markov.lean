import CausalQIF.Probability.Entropy

open Finset
open scoped BigOperators Real

namespace CausalQIF.Probability

noncomputable section

variable {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]

/-! ## Markov Chain Definitions -/

def marginalTripleSnd (P : FinitePMF (α × β × γ)) (b : β) : ℝ :=
  ∑ a : α, ∑ c : γ, P.pmf (a, b, c)

def marginalTripleFstSnd (P : FinitePMF (α × β × γ)) (ab : α × β) : ℝ :=
  ∑ c : γ, P.pmf (ab.1, ab.2, c)


def IsMarkovChain (P : FinitePMF (α × β × γ)) : Prop :=
  ∀ a b c,
    P.pmf (a, b, c) * marginalTripleSnd P b =
      marginalTripleFstSnd P (a, b) * marginalTripleSndThd P (b, c)

/-! ## CMI=0 for Markov Chains -/

def equivTripleReshapeFstThdSnd : (α × γ × β) ≃ (α × β × γ) where
  toFun x := (x.1, x.2.2, x.2.1)
  invFun x := (x.1, x.2.2, x.2.1)
  left_inv := by intro; rfl
  right_inv := by intro; rfl

def pmfTripleReshapeFstThdSnd (P : FinitePMF (α × β × γ)) : FinitePMF (α × γ × β) :=
  FinitePMF.comapEquiv equivTripleReshapeFstThdSnd.symm P

theorem condMutualInfo_eq_zero_of_isMarkovChain (P : FinitePMF (α × β × γ))
    (hMC : IsMarkovChain P) : condMutualInfo (pmfTripleReshapeFstThdSnd P) = 0 := by
  refine condMutualInfo_eq_zero_of_condIndep (pmfTripleReshapeFstThdSnd P) ?_
  intro a c b
  simpa [pmfTripleReshapeFstThdSnd, FinitePMF.comapEquiv, equivTripleReshapeFstThdSnd, marginalTripleSnd, marginalTripleFstSnd,
    marginalTripleThd, marginalTripleFstThd, marginalTripleSndThd] using hMC a b c

@[deprecated marginalTripleFstSnd (since := "2026-05")]
alias marginalTriple_FstSnd := marginalTripleFstSnd
@[deprecated marginalTripleSnd (since := "2026-05")]
alias marginalTriple_Snd := marginalTripleSnd

end

end CausalQIF.Probability
