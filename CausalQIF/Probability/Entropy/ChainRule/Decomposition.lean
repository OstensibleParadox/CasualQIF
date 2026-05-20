import CausalQIF.Probability.Entropy.ChainRule.Bridges
import CausalQIF.Probability.Entropy.Identities

open Finset
open scoped BigOperators Real

namespace CausalQIF.Probability

noncomputable section

/-! # Chain-Rule Decompositions and DPI

Two chain-rule decompositions of `condMutualInfo (pmfPairFstSnd P)` and the
data-processing-inequality scaffolding (`condMarkov`, non-negativity, and the
zero-CMI ⇐ `condMarkov` corollary).
-/

variable {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]

lemma condMutualInfo_pmfPairFstSnd_eq_add_pmfMargOutSnd_add_pmfPairFstFthReshape (P : FinitePMF (α × β × γ × δ)) :
    condMutualInfo (pmfPairFstSnd P) = condMutualInfo (marginalizeOutSnd P) + condMutualInfo (pmfPairFstFthReshape P) := by
  rw [condMutualInfo_pmfPairFstSnd, condMutualInfo_pmfMargOutSnd, condMutualInfo_pmfPairFstFthReshape]
  have h_ent : entropy P = entropyOf P.pmf := rfl
  rw [h_ent]
  ring

lemma condMutualInfo_pmfPairFstSnd_eq_add_pmfMargOutFst_add_pmfPairSndFthReshape (P : FinitePMF (α × β × γ × δ)) :
    condMutualInfo (pmfPairFstSnd P) = condMutualInfo (marginalizeOutFst P) + condMutualInfo (pmfPairSndFthReshape P) := by
  rw [condMutualInfo_pmfPairFstSnd, condMutualInfo_pmfMargOutFst, condMutualInfo_pmfPairSndFthReshape]
  have h_ent : entropy P = entropyOf P.pmf := rfl
  rw [h_ent]
  ring

/-- Conditional Markovity as a concrete equality. -/
def condMarkov (P : FinitePMF (α × β × γ × δ)) : Prop :=
  ∀ x y z w,
    P.pmf (x, y, z, w) * marginalQuadSndFth P (y, w)
      =
    marginalQuadFstSndFth P (x, y, w) * marginalQuadSndThdFth P (y, z, w)



lemma condMutualInfo_pmfPairSndFthReshape_eq_zero_of_condMarkov
    (P : FinitePMF (α × β × γ × δ)) (h : condMarkov P) :
    condMutualInfo (pmfPairSndFthReshape P) = 0 := by
  have hzero := condMutualInfo_eq_zero_of_condIndep (pmfPairSndFthReshape P) ?_
  · exact hzero
  · intro x z yw
    rcases yw with ⟨y, w⟩
    simpa [condIndep, pmfPairSndFthReshape, FinitePMF.comapEquiv, equivPairSndFthReshape, marginalTripleThd,
      marginalTripleFstThd, marginalTripleSndThd, marginalQuadSndFth, marginalQuadFstSndFth,
      marginalQuadSndThdFth] using h x y z w

@[deprecated condMutualInfo_pmfPairSndFthReshape_eq_zero_of_condMarkov (since := "2026-05")]
alias cond_mutual_info_pair_snd_fth_reshape_eq_zero_of_cond_markov := condMutualInfo_pmfPairSndFthReshape_eq_zero_of_condMarkov

end

end CausalQIF.Probability
