import CausalQIF.Probability.Entropy.ChainRule.Bridges.Basic

open Finset
open scoped BigOperators Real

namespace CausalQIF.Probability

noncomputable section

variable {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]

lemma condMutualInfo_pmfMargOutSnd (P : FinitePMF (α × β × γ × δ)) :
    condMutualInfo (marginalizeOutSnd P) = entropyOf (marginalQuadFstFth P) +
    entropyOf (marginalQuadThdFth P) -
    entropyOf (marginalQuadFth P) -
    entropyOf (marginalQuadFstThdFth P) := by
  have hXW : entropyOf (marginalTripleFstThd (marginalizeOutSnd P)) = entropyOf (marginalQuadFstFth P) := by
    apply congrArg entropyOf
    funext xw
    rcases xw with ⟨x, w⟩
    dsimp [marginalTripleFstThd, marginalQuadFstFth, marginalizeOutSnd, marginalizeLeafPMF, FinitePMF.comapEquiv, equivMarginalizeOutSnd]
    exact sum_comm
  have hZW : entropyOf (marginalTripleSndThd (marginalizeOutSnd P)) = entropyOf (marginalQuadThdFth P) := by
    apply congrArg entropyOf
    funext zw
    rcases zw with ⟨z, w⟩
    dsimp [marginalTripleSndThd, marginalQuadThdFth, marginalizeOutSnd, marginalizeLeafPMF, FinitePMF.comapEquiv, equivMarginalizeOutSnd]
  have hW : entropyOf (marginalTripleThd (marginalizeOutSnd P)) = entropyOf (marginalQuadFth P) := by
    apply congrArg entropyOf
    funext w
    dsimp [marginalTripleThd, marginalQuadFth, marginalizeOutSnd, marginalizeLeafPMF, FinitePMF.comapEquiv, equivMarginalizeOutSnd]
    apply sum_congr rfl; intro x _
    exact sum_comm
  have hXZW : entropy (marginalizeOutSnd P) = entropyOf (marginalQuadFstThdFth P) := by rfl
  unfold condMutualInfo
  rw [hXW, hZW, hW, hXZW]

lemma condMutualInfo_pmfMargOutFst (P : FinitePMF (α × β × γ × δ)) :
    condMutualInfo (marginalizeOutFst P) = entropyOf (marginalQuadSndFth P) +
    entropyOf (marginalQuadThdFth P) -
    entropyOf (marginalQuadFth P) -
    entropyOf (marginalQuadSndThdFth P) := by
  have hYW : entropyOf (marginalTripleFstThd (marginalizeOutFst P)) = entropyOf (marginalQuadSndFth P) := by
    apply congrArg entropyOf
    funext yw
    rcases yw with ⟨y, w⟩
    dsimp [marginalTripleFstThd, marginalQuadSndFth, marginalizeOutFst, marginalizeLeafPMF, FinitePMF.comapEquiv, equivMarginalizeOutFst]
    exact sum_comm
  have hZW : entropyOf (marginalTripleSndThd (marginalizeOutFst P)) = entropyOf (marginalQuadThdFth P) := by
    apply congrArg entropyOf
    funext zw
    rcases zw with ⟨z, w⟩
    dsimp [marginalTripleSndThd, marginalQuadThdFth, marginalizeOutFst, marginalizeLeafPMF, FinitePMF.comapEquiv, equivMarginalizeOutFst]
    exact sum_comm
  have hW : entropyOf (marginalTripleThd (marginalizeOutFst P)) = entropyOf (marginalQuadFth P) := by
    apply congrArg entropyOf
    funext w
    dsimp [marginalTripleThd, marginalQuadFth, marginalizeOutFst, marginalizeLeafPMF, FinitePMF.comapEquiv, equivMarginalizeOutFst]
    have h1 : (∑ y : β, ∑ z : γ, ∑ leaf : α, P.pmf (leaf, y, z, w)) = ∑ y : β, ∑ leaf : α, ∑ z : γ, P.pmf (leaf, y, z, w) := by
      apply sum_congr rfl; intro y _
      exact sum_comm
    rw [h1]
    exact sum_comm
  have hYZW : entropy (marginalizeOutFst P) = entropyOf (marginalQuadSndThdFth P) := by rfl
  unfold condMutualInfo
  rw [hYW, hZW, hW, hYZW]

lemma condMutualInfo_pmfPairFstSnd (P : FinitePMF (α × β × γ × δ)) :
    condMutualInfo (pmfPairFstSnd P) = entropyOf (marginalQuadFstSndFth P) +
    entropyOf (marginalQuadThdFth P) -
    entropyOf (marginalQuadFth P) -
    entropy P := by
  have hXYW : entropyOf (marginalTripleFstThd (pmfPairFstSnd P)) = entropyOf (marginalQuadFstSndFth P) := by
    let eXYW : (α × β) × δ ≃ α × β × δ := {
      toFun := fun t => (t.1.1, t.1.2, t.2)
      invFun := fun t => ((t.1, t.2.1), t.2.2)
      left_inv := by intro t; rcases t with ⟨⟨x, y⟩, w⟩; rfl
      right_inv := by intro t; rcases t with ⟨x, y, w⟩; rfl
    }
    refine entropyOf_equiv_eq eXYW (marginalTripleFstThd (pmfPairFstSnd P)) (marginalQuadFstSndFth P) ?_
    intro xyw
    rcases xyw with ⟨⟨x, y⟩, w⟩
    rfl
  have hZW : entropyOf (marginalTripleSndThd (pmfPairFstSnd P)) = entropyOf (marginalQuadThdFth P) := by
    apply congrArg entropyOf
    funext zw
    rcases zw with ⟨z, w⟩
    dsimp [marginalTripleSndThd, marginalQuadThdFth, pmfPairFstSnd, FinitePMF.comapEquiv, equivPairFstSnd]
    have h : ∑ xy : α × β, P.pmf (xy.1, xy.2, z, w) = ∑ x : α, ∑ y : β, P.pmf (x, y, z, w) := by
      exact Fintype.sum_prod_type (fun xy => P.pmf (xy.1, xy.2, z, w))
    exact h
  have hW : entropyOf (marginalTripleThd (pmfPairFstSnd P)) = entropyOf (marginalQuadFth P) := by
    apply congrArg entropyOf
    funext w
    dsimp [marginalTripleThd, marginalQuadFth, pmfPairFstSnd, FinitePMF.comapEquiv, equivPairFstSnd]
    have h1 : (∑ xy : α × β, ∑ z : γ, P.pmf (xy.1, xy.2, z, w)) = ∑ z : γ, ∑ xy : α × β, P.pmf (xy.1, xy.2, z, w) := sum_comm
    rw [h1]
    have h2 : (∑ z : γ, ∑ xy : α × β, P.pmf (xy.1, xy.2, z, w)) = ∑ z : γ, ∑ x : α, ∑ y : β, P.pmf (x, y, z, w) := by
      apply sum_congr rfl; intro z _
      exact Fintype.sum_prod_type (fun xy => P.pmf (xy.1, xy.2, z, w))
    rw [h2]
    have h3 : (∑ z : γ, ∑ x : α, ∑ y : β, P.pmf (x, y, z, w)) = ∑ x : α, ∑ z : γ, ∑ y : β, P.pmf (x, y, z, w) := sum_comm
    rw [h3]
    apply sum_congr rfl; intro x _
    exact sum_comm
  have hXYZW : entropy (pmfPairFstSnd P) = entropy P := by
    symm
    refine entropyOf_equiv_eq equivPairFstSnd.symm P.pmf (pmfPairFstSnd P).pmf ?_
    intro t; rcases t with ⟨x, y, z, w⟩; rfl
  unfold condMutualInfo
  have hP : entropy P = entropyOf P.pmf := rfl
  rw [hXYW, hZW, hW, hXYZW, hP]

@[deprecated condMutualInfo_pmfMargOutFst (since := "2026-05")]
alias cond_mutual_info_marg_out_fst := condMutualInfo_pmfMargOutFst
@[deprecated condMutualInfo_pmfMargOutSnd (since := "2026-05")]
alias cond_mutual_info_marg_out_snd := condMutualInfo_pmfMargOutSnd
@[deprecated condMutualInfo_pmfPairFstSnd (since := "2026-05")]
alias cond_mutual_info_pair_fst_snd := condMutualInfo_pmfPairFstSnd

end

end CausalQIF.Probability
