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

lemma cond_mutual_info_pair_fst_snd_eq_add_marg_out_snd_add_pair_fst_fth (P : FinitePMF (α × β × γ × δ)) :
    condMutualInfo (pmfPairFstSnd P) = condMutualInfo (pmfMargOutSnd P) + condMutualInfo (pmfPairFstFthReshape P) := by
  rw [cond_mutual_info_pair_fst_snd, cond_mutual_info_marg_out_snd, cond_mutual_info_pair_fst_fth_reshape]
  have h_ent : entropy P = entropyOf P.pmf := rfl
  rw [h_ent]
  ring

lemma cond_mutual_info_pair_fst_snd_eq_add_marg_out_fst_add_pair_snd_fth (P : FinitePMF (α × β × γ × δ)) :
    condMutualInfo (pmfPairFstSnd P) = condMutualInfo (pmfMargOutFst P) + condMutualInfo (pmfPairSndFthReshape P) := by
  rw [cond_mutual_info_pair_fst_snd, cond_mutual_info_marg_out_fst, cond_mutual_info_pair_snd_fth_reshape]
  have h_ent : entropy P = entropyOf P.pmf := rfl
  rw [h_ent]
  ring

/-- Conditional Markovity as a concrete equality. -/
def condMarkov (P : FinitePMF (α × β × γ × δ)) : Prop :=
  ∀ x y z w,
    P.pmf (x, y, z, w) * marginalQuad_SndFth P (y, w)
      =
    marginalQuad_FstSndFth P (x, y, w) * marginalQuad_SndThdFth P (y, z, w)

lemma cond_mutual_info_pair_fst_fth_reshape_nonneg (P : FinitePMF (α × β × γ × δ)) : 0 ≤ condMutualInfo (pmfPairFstFthReshape P) := by
  exact condMutualInfo_nonneg (pmfPairFstFthReshape P)

lemma cond_mutual_info_pair_snd_fth_reshape_eq_zero_of_cond_markov
    (P : FinitePMF (α × β × γ × δ)) (h : condMarkov P) :
    condMutualInfo (pmfPairSndFthReshape P) = 0 := by
  have hzero := condMutualInfo_eq_zero_of_condIndep (pmfPairSndFthReshape P) ?_
  · exact hzero
  · intro x z yw
    rcases yw with ⟨y, w⟩
    simpa [condIndep, pmfPairSndFthReshape, FinitePMF.comapEquiv, equivPairSndFthReshape, marginalTriple_Thd,
      marginalTriple_FstThd, marginalTriple_SndThd, marginalQuad_SndFth, marginalQuad_FstSndFth,
      marginalQuad_SndThdFth] using h x y z w

end

end CausalQIF.Probability
