import CausalQIF.Probability.Entropy.ChainRule.Marginals
import CausalQIF.Probability.Entropy.ChainRule.Reshapes

open Finset
open scoped BigOperators Real

namespace CausalQIF.Probability

noncomputable section

/-! # Bridge Lemmas: condMutualInfo ↔ H+H-H-H

For each of the five PMF transports in `Reshapes`, an equality between the
native `condMutualInfo` of the transported PMF and the four-term
`entropyOf`-formula over the underlying four-tuple marginals. These bridges
are the algebraic interface used by every downstream chain-rule and DPI proof.
-/

variable {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]

lemma cond_mutual_info_pair_fst_fth_reshape (P : FinitePMF (α × β × γ × δ)) :
    condMutualInfo (pmfPairFstFthReshape P) = entropyOf (marginalQuad_FstSndFth P) +
    entropyOf (marginalQuad_FstThdFth P) -
    entropyOf (marginalQuad_FstFth P) -
    entropyOf P.pmf := by
  let eXYW : α × β × δ ≃ β × (α × δ) := {
    toFun := fun t => (t.2.1, (t.1, t.2.2))
    invFun := fun t => (t.2.1, t.1, t.2.2)
    left_inv := by intro t; rcases t with ⟨x, y, w⟩; rfl
    right_inv := by intro t; rcases t with ⟨y, x, w⟩; rfl
  }
  let eXZW : α × γ × δ ≃ γ × (α × δ) := {
    toFun := fun t => (t.2.1, (t.1, t.2.2))
    invFun := fun t => (t.2.1, t.1, t.2.2)
    left_inv := by intro t; rcases t with ⟨x, z, w⟩; rfl
    right_inv := by intro t; rcases t with ⟨z, x, w⟩; rfl
  }
  have hXYW : entropyOf (marginalTriple_FstThd (pmfPairFstFthReshape P)) =
      entropyOf (marginalQuad_FstSndFth P) := by
    symm
    refine entropyOf_equiv_eq eXYW (marginalQuad_FstSndFth P)
      (marginalTriple_FstThd (pmfPairFstFthReshape P)) ?_
    intro xyw
    rcases xyw with ⟨x, y, w⟩
    rfl
  have hXZW : entropyOf (marginalTriple_SndThd (pmfPairFstFthReshape P)) =
      entropyOf (marginalQuad_FstThdFth P) := by
    symm
    refine entropyOf_equiv_eq eXZW (marginalQuad_FstThdFth P)
      (marginalTriple_SndThd (pmfPairFstFthReshape P)) ?_
    intro xzw
    rcases xzw with ⟨x, z, w⟩
    rfl
  have hXW : entropyOf (marginalTriple_Thd (pmfPairFstFthReshape P)) =
      entropyOf (marginalQuad_FstFth P) := by
    apply congrArg entropyOf
    funext xw
    rcases xw with ⟨x, w⟩
    rfl
  have hFull : entropyOf (fun yz_xw : β × γ × (α × δ) => (pmfPairFstFthReshape P).pmf yz_xw) =
      entropyOf P.pmf := by
    symm
    refine entropyOf_equiv_eq equivPairFstFthReshape.symm
      P.pmf
      (fun yz_xw : β × γ × (α × δ) => (pmfPairFstFthReshape P).pmf yz_xw) ?_
    intro xyzw
    rcases xyzw with ⟨x, y, z, w⟩
    rfl
  unfold condMutualInfo entropy
  rw [hXYW, hXZW, hXW, hFull]

lemma cond_mutual_info_pair_snd_fth_reshape (P : FinitePMF (α × β × γ × δ)) :
    condMutualInfo (pmfPairSndFthReshape P) = entropyOf (marginalQuad_FstSndFth P) +
    entropyOf (marginalQuad_SndThdFth P) -
    entropyOf (marginalQuad_SndFth P) -
    entropyOf P.pmf := by
  let eXYW : α × β × δ ≃ α × (β × δ) := {
    toFun := fun t => (t.1, (t.2.1, t.2.2))
    invFun := fun t => (t.1, t.2.1, t.2.2)
    left_inv := by intro t; rcases t with ⟨x, y, w⟩; rfl
    right_inv := by intro t; rcases t with ⟨x, y, w⟩; rfl
  }
  let eYZW : β × γ × δ ≃ γ × (β × δ) := {
    toFun := fun t => (t.2.1, (t.1, t.2.2))
    invFun := fun t => (t.2.1, t.1, t.2.2)
    left_inv := by intro t; rcases t with ⟨y, z, w⟩; rfl
    right_inv := by intro t; rcases t with ⟨z, y, w⟩; rfl
  }
  have hXYW : entropyOf (marginalTriple_FstThd (pmfPairSndFthReshape P)) =
      entropyOf (marginalQuad_FstSndFth P) := by
    symm
    refine entropyOf_equiv_eq eXYW (marginalQuad_FstSndFth P)
      (marginalTriple_FstThd (pmfPairSndFthReshape P)) ?_
    intro xyw
    rcases xyw with ⟨x, y, w⟩
    rfl
  have hYZW : entropyOf (marginalTriple_SndThd (pmfPairSndFthReshape P)) =
      entropyOf (marginalQuad_SndThdFth P) := by
    symm
    refine entropyOf_equiv_eq eYZW (marginalQuad_SndThdFth P)
      (marginalTriple_SndThd (pmfPairSndFthReshape P)) ?_
    intro yzw
    rcases yzw with ⟨y, z, w⟩
    rfl
  have hYW : entropyOf (marginalTriple_Thd (pmfPairSndFthReshape P)) =
      entropyOf (marginalQuad_SndFth P) := by
    apply congrArg entropyOf
    funext yw
    rcases yw with ⟨y, w⟩
    rfl
  have hFull : entropyOf (fun xz_yw : α × γ × (β × δ) => (pmfPairSndFthReshape P).pmf xz_yw) =
      entropyOf P.pmf := by
    symm
    refine entropyOf_equiv_eq equivPairSndFthReshape.symm
      P.pmf
      (fun xz_yw : α × γ × (β × δ) => (pmfPairSndFthReshape P).pmf xz_yw) ?_
    intro xyzw
    rcases xyzw with ⟨x, y, z, w⟩
    rfl
  unfold condMutualInfo entropy
  rw [hXYW, hYZW, hYW, hFull]

lemma cond_mutual_info_marg_out_snd (P : FinitePMF (α × β × γ × δ)) :
    condMutualInfo (pmfMargOutSnd P) = entropyOf (marginalQuad_FstFth P) +
    entropyOf (marginalQuad_ThdFth P) -
    entropyOf (marginalQuad_Fth P) -
    entropyOf (marginalQuad_FstThdFth P) := by
  have hXW : entropyOf (marginalTriple_FstThd (pmfMargOutSnd P)) = entropyOf (marginalQuad_FstFth P) := by
    apply congrArg entropyOf
    funext xw
    rcases xw with ⟨x, w⟩
    dsimp [marginalTriple_FstThd, marginalQuad_FstFth, pmfMargOutSnd, marginalizeLeafPMF, FinitePMF.comapEquiv, equivMargOutSnd]
    exact sum_comm
  have hZW : entropyOf (marginalTriple_SndThd (pmfMargOutSnd P)) = entropyOf (marginalQuad_ThdFth P) := by
    apply congrArg entropyOf
    funext zw
    rcases zw with ⟨z, w⟩
    dsimp [marginalTriple_SndThd, marginalQuad_ThdFth, pmfMargOutSnd, marginalizeLeafPMF, FinitePMF.comapEquiv, equivMargOutSnd]
  have hW : entropyOf (marginalTriple_Thd (pmfMargOutSnd P)) = entropyOf (marginalQuad_Fth P) := by
    apply congrArg entropyOf
    funext w
    dsimp [marginalTriple_Thd, marginalQuad_Fth, pmfMargOutSnd, marginalizeLeafPMF, FinitePMF.comapEquiv, equivMargOutSnd]
    apply sum_congr rfl; intro x _
    exact sum_comm
  have hXZW : entropy (pmfMargOutSnd P) = entropyOf (marginalQuad_FstThdFth P) := by rfl
  unfold condMutualInfo
  rw [hXW, hZW, hW, hXZW]

lemma cond_mutual_info_marg_out_fst (P : FinitePMF (α × β × γ × δ)) :
    condMutualInfo (pmfMargOutFst P) = entropyOf (marginalQuad_SndFth P) +
    entropyOf (marginalQuad_ThdFth P) -
    entropyOf (marginalQuad_Fth P) -
    entropyOf (marginalQuad_SndThdFth P) := by
  have hYW : entropyOf (marginalTriple_FstThd (pmfMargOutFst P)) = entropyOf (marginalQuad_SndFth P) := by
    apply congrArg entropyOf
    funext yw
    rcases yw with ⟨y, w⟩
    dsimp [marginalTriple_FstThd, marginalQuad_SndFth, pmfMargOutFst, marginalizeLeafPMF, FinitePMF.comapEquiv, equivMargOutFst]
    exact sum_comm
  have hZW : entropyOf (marginalTriple_SndThd (pmfMargOutFst P)) = entropyOf (marginalQuad_ThdFth P) := by
    apply congrArg entropyOf
    funext zw
    rcases zw with ⟨z, w⟩
    dsimp [marginalTriple_SndThd, marginalQuad_ThdFth, pmfMargOutFst, marginalizeLeafPMF, FinitePMF.comapEquiv, equivMargOutFst]
    exact sum_comm
  have hW : entropyOf (marginalTriple_Thd (pmfMargOutFst P)) = entropyOf (marginalQuad_Fth P) := by
    apply congrArg entropyOf
    funext w
    dsimp [marginalTriple_Thd, marginalQuad_Fth, pmfMargOutFst, marginalizeLeafPMF, FinitePMF.comapEquiv, equivMargOutFst]
    have h1 : (∑ y : β, ∑ z : γ, ∑ leaf : α, P.pmf (leaf, y, z, w)) = ∑ y : β, ∑ leaf : α, ∑ z : γ, P.pmf (leaf, y, z, w) := by
      apply sum_congr rfl; intro y _
      exact sum_comm
    rw [h1]
    exact sum_comm
  have hYZW : entropy (pmfMargOutFst P) = entropyOf (marginalQuad_SndThdFth P) := by rfl
  unfold condMutualInfo
  rw [hYW, hZW, hW, hYZW]

lemma cond_mutual_info_pair_fst_snd (P : FinitePMF (α × β × γ × δ)) :
    condMutualInfo (pmfPairFstSnd P) = entropyOf (marginalQuad_FstSndFth P) +
    entropyOf (marginalQuad_ThdFth P) -
    entropyOf (marginalQuad_Fth P) -
    entropy P := by
  have hXYW : entropyOf (marginalTriple_FstThd (pmfPairFstSnd P)) = entropyOf (marginalQuad_FstSndFth P) := by
    let eXYW : (α × β) × δ ≃ α × β × δ := {
      toFun := fun t => (t.1.1, t.1.2, t.2)
      invFun := fun t => ((t.1, t.2.1), t.2.2)
      left_inv := by intro t; rcases t with ⟨⟨x, y⟩, w⟩; rfl
      right_inv := by intro t; rcases t with ⟨x, y, w⟩; rfl
    }
    refine entropyOf_equiv_eq eXYW (marginalTriple_FstThd (pmfPairFstSnd P)) (marginalQuad_FstSndFth P) ?_
    intro xyw
    rcases xyw with ⟨⟨x, y⟩, w⟩
    rfl
  have hZW : entropyOf (marginalTriple_SndThd (pmfPairFstSnd P)) = entropyOf (marginalQuad_ThdFth P) := by
    apply congrArg entropyOf
    funext zw
    rcases zw with ⟨z, w⟩
    dsimp [marginalTriple_SndThd, marginalQuad_ThdFth, pmfPairFstSnd, FinitePMF.comapEquiv, equivPairFstSnd]
    have h : ∑ xy : α × β, P.pmf (xy.1, xy.2, z, w) = ∑ x : α, ∑ y : β, P.pmf (x, y, z, w) := by
      exact Fintype.sum_prod_type (fun xy => P.pmf (xy.1, xy.2, z, w))
    exact h
  have hW : entropyOf (marginalTriple_Thd (pmfPairFstSnd P)) = entropyOf (marginalQuad_Fth P) := by
    apply congrArg entropyOf
    funext w
    dsimp [marginalTriple_Thd, marginalQuad_Fth, pmfPairFstSnd, FinitePMF.comapEquiv, equivPairFstSnd]
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

end

end CausalQIF.Probability
