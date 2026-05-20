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

lemma condMutualInfo_pmfPairFstFthReshape (P : FinitePMF (α × β × γ × δ)) :
    condMutualInfo (pmfPairFstFthReshape P) = entropyOf (marginalQuadFstSndFth P) +
    entropyOf (marginalQuadFstThdFth P) -
    entropyOf (marginalQuadFstFth P) -
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
  have hXYW : entropyOf (marginalTripleFstThd (pmfPairFstFthReshape P)) =
      entropyOf (marginalQuadFstSndFth P) := by
    symm
    refine entropyOf_equiv_eq eXYW (marginalQuadFstSndFth P)
      (marginalTripleFstThd (pmfPairFstFthReshape P)) ?_
    intro xyw
    rcases xyw with ⟨x, y, w⟩
    rfl
  have hXZW : entropyOf (marginalTripleSndThd (pmfPairFstFthReshape P)) =
      entropyOf (marginalQuadFstThdFth P) := by
    symm
    refine entropyOf_equiv_eq eXZW (marginalQuadFstThdFth P)
      (marginalTripleSndThd (pmfPairFstFthReshape P)) ?_
    intro xzw
    rcases xzw with ⟨x, z, w⟩
    rfl
  have hXW : entropyOf (marginalTripleThd (pmfPairFstFthReshape P)) =
      entropyOf (marginalQuadFstFth P) := by
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

lemma condMutualInfo_pmfPairSndFthReshape (P : FinitePMF (α × β × γ × δ)) :
    condMutualInfo (pmfPairSndFthReshape P) = entropyOf (marginalQuadFstSndFth P) +
    entropyOf (marginalQuadSndThdFth P) -
    entropyOf (marginalQuadSndFth P) -
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
  have hXYW : entropyOf (marginalTripleFstThd (pmfPairSndFthReshape P)) =
      entropyOf (marginalQuadFstSndFth P) := by
    symm
    refine entropyOf_equiv_eq eXYW (marginalQuadFstSndFth P)
      (marginalTripleFstThd (pmfPairSndFthReshape P)) ?_
    intro xyw
    rcases xyw with ⟨x, y, w⟩
    rfl
  have hYZW : entropyOf (marginalTripleSndThd (pmfPairSndFthReshape P)) =
      entropyOf (marginalQuadSndThdFth P) := by
    symm
    refine entropyOf_equiv_eq eYZW (marginalQuadSndThdFth P)
      (marginalTripleSndThd (pmfPairSndFthReshape P)) ?_
    intro yzw
    rcases yzw with ⟨y, z, w⟩
    rfl
  have hYW : entropyOf (marginalTripleThd (pmfPairSndFthReshape P)) =
      entropyOf (marginalQuadSndFth P) := by
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

@[deprecated condMutualInfo_pmfPairFstFthReshape (since := "2026-05")]
alias cond_mutual_info_pair_fst_fth_reshape := condMutualInfo_pmfPairFstFthReshape
@[deprecated condMutualInfo_pmfPairSndFthReshape (since := "2026-05")]
alias cond_mutual_info_pair_snd_fth_reshape := condMutualInfo_pmfPairSndFthReshape

end

end CausalQIF.Probability
