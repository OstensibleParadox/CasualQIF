import CausalQIF.Probability.Entropy.Basic
import CausalQIF.Probability.Entropy.Identities

open Finset
open scoped BigOperators Real

namespace CausalQIF.Probability

noncomputable section

variable {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]

/-! ## Four-variable Conditional Mutual Information and DPI -/

def marginalQuad_FstFth (P : FinitePMF (α × β × γ × δ)) (xw : α × δ) : ℝ :=
  ∑ y : β, ∑ z : γ, P.pmf (xw.1, y, z, xw.2)

def marginalQuad_SndFth (P : FinitePMF (α × β × γ × δ)) (yw : β × δ) : ℝ :=
  ∑ x : α, ∑ z : γ, P.pmf (x, yw.1, z, yw.2)

def marginalQuad_ThdFth (P : FinitePMF (α × β × γ × δ)) (zw : γ × δ) : ℝ :=
  ∑ x : α, ∑ y : β, P.pmf (x, y, zw.1, zw.2)

def marginalQuad_Fth (P : FinitePMF (α × β × γ × δ)) (w : δ) : ℝ :=
  ∑ x : α, ∑ y : β, ∑ z : γ, P.pmf (x, y, z, w)

def marginalQuad_FstThdFth (P : FinitePMF (α × β × γ × δ)) (xzw : α × γ × δ) : ℝ :=
  ∑ y : β, P.pmf (xzw.1, y, xzw.2.1, xzw.2.2)

def marginalQuad_SndThdFth (P : FinitePMF (α × β × γ × δ)) (yzw : β × γ × δ) : ℝ :=
  ∑ x : α, P.pmf (x, yzw.1, yzw.2.1, yzw.2.2)

def marginalQuad_FstSndFth (P : FinitePMF (α × β × γ × δ)) (xyw : α × β × δ) : ℝ :=
  ∑ z : γ, P.pmf (xyw.1, xyw.2.1, z, xyw.2.2)

/-- `I(X;Z | W)` for a four-variable PMF `(X,Y,Z,W)`. -/
def I_XZ_W (P : FinitePMF (α × β × γ × δ)) : ℝ :=
  entropyOf (marginalQuad_FstFth P) +
    entropyOf (marginalQuad_ThdFth P) -
    entropyOf (marginalQuad_Fth P) -
    entropyOf (marginalQuad_FstThdFth P)

/-- `I(Y;Z | W)` for a four-variable PMF `(X,Y,Z,W)`. -/
def I_YZ_W (P : FinitePMF (α × β × γ × δ)) : ℝ :=
  entropyOf (marginalQuad_SndFth P) +
    entropyOf (marginalQuad_ThdFth P) -
    entropyOf (marginalQuad_Fth P) -
    entropyOf (marginalQuad_SndThdFth P)

/-- `I(Y;Z | X,W)` for a four-variable PMF `(X,Y,Z,W)`. -/
def I_YZ_XW (P : FinitePMF (α × β × γ × δ)) : ℝ :=
  entropyOf (marginalQuad_FstSndFth P) +
    entropyOf (marginalQuad_FstThdFth P) -
    entropyOf (marginalQuad_FstFth P) -
    entropyOf P.pmf

/-- `I(X;Z | Y,W)` for a four-variable PMF `(X,Y,Z,W)`. -/
def I_XZ_YW (P : FinitePMF (α × β × γ × δ)) : ℝ :=
  entropyOf (marginalQuad_FstSndFth P) +
    entropyOf (marginalQuad_SndThdFth P) -
    entropyOf (marginalQuad_SndFth P) -
    entropyOf P.pmf

/-- `I((X,Y);Z | W)` for a four-variable PMF `(X,Y,Z,W)`. -/
def I_XY_Z_W (P : FinitePMF (α × β × γ × δ)) : ℝ :=
  entropyOf (marginalQuad_FstSndFth P) +
    entropyOf (marginalQuad_ThdFth P) -
    entropyOf (marginalQuad_Fth P) -
    entropyOf P.pmf

lemma I_XY_Z_W_eq_I_XZ_W_add_I_YZ_XW (P : FinitePMF (α × β × γ × δ)) :
    I_XY_Z_W P = I_XZ_W P + I_YZ_XW P := by
  unfold I_XY_Z_W I_XZ_W I_YZ_XW
  ring

lemma I_XY_Z_W_eq_I_YZ_W_add_I_XZ_YW (P : FinitePMF (α × β × γ × δ)) :
    I_XY_Z_W P = I_YZ_W P + I_XZ_YW P := by
  unfold I_XY_Z_W I_YZ_W I_XZ_YW
  ring

def equivYZXW : β × γ × (α × δ) ≃ α × β × γ × δ where
  toFun t := (t.2.2.1, t.1, t.2.1, t.2.2.2)
  invFun t := (t.2.1, t.2.2.1, (t.1, t.2.2.2))
  left_inv := by
    intro t
    rcases t with ⟨y, z, x, w⟩
    rfl
  right_inv := by
    intro t
    rcases t with ⟨x, y, z, w⟩
    rfl

def equivXZYW : α × γ × (β × δ) ≃ α × β × γ × δ where
  toFun t := (t.1, t.2.2.1, t.2.1, t.2.2.2)
  invFun t := (t.1, t.2.2.1, (t.2.1, t.2.2.2))
  left_inv := by
    intro t
    rcases t with ⟨x, z, y, w⟩
    rfl
  right_inv := by
    intro t
    rcases t with ⟨x, y, z, w⟩
    rfl

def pmfYZXW (P : FinitePMF (α × β × γ × δ)) :
    FinitePMF (β × γ × (α × δ)) :=
  FinitePMF.comapEquiv equivYZXW P

def pmfXZYW (P : FinitePMF (α × β × γ × δ)) :
    FinitePMF (α × γ × (β × δ)) :=
  FinitePMF.comapEquiv equivXZYW P

lemma condMutualInfo_pmfYZXW (P : FinitePMF (α × β × γ × δ)) :
    condMutualInfo (pmfYZXW P) = I_YZ_XW P := by
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
  have hXYW : entropyOf (marginalTriple_FstThd (pmfYZXW P)) =
      entropyOf (marginalQuad_FstSndFth P) := by
    symm
    refine entropyOf_equiv_eq eXYW (marginalQuad_FstSndFth P)
      (marginalTriple_FstThd (pmfYZXW P)) ?_
    intro xyw
    rcases xyw with ⟨x, y, w⟩
    rfl
  have hXZW : entropyOf (marginalTriple_SndThd (pmfYZXW P)) =
      entropyOf (marginalQuad_FstThdFth P) := by
    symm
    refine entropyOf_equiv_eq eXZW (marginalQuad_FstThdFth P)
      (marginalTriple_SndThd (pmfYZXW P)) ?_
    intro xzw
    rcases xzw with ⟨x, z, w⟩
    rfl
  have hXW : entropyOf (marginalTriple_Thd (pmfYZXW P)) =
      entropyOf (marginalQuad_FstFth P) := by
    apply congrArg entropyOf
    funext xw
    rcases xw with ⟨x, w⟩
    rfl
  have hFull : entropyOf (fun yz_xw : β × γ × (α × δ) => (pmfYZXW P).pmf yz_xw) =
      entropyOf P.pmf := by
    symm
    refine entropyOf_equiv_eq equivYZXW.symm
      P.pmf
      (fun yz_xw : β × γ × (α × δ) => (pmfYZXW P).pmf yz_xw) ?_
    intro xyzw
    rcases xyzw with ⟨x, y, z, w⟩
    rfl
  unfold condMutualInfo I_YZ_XW entropy
  rw [hXYW, hXZW, hXW, hFull]

lemma condMutualInfo_pmfXZYW (P : FinitePMF (α × β × γ × δ)) :
    condMutualInfo (pmfXZYW P) = I_XZ_YW P := by
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
  have hXYW : entropyOf (marginalTriple_FstThd (pmfXZYW P)) =
      entropyOf (marginalQuad_FstSndFth P) := by
    symm
    refine entropyOf_equiv_eq eXYW (marginalQuad_FstSndFth P)
      (marginalTriple_FstThd (pmfXZYW P)) ?_
    intro xyw
    rcases xyw with ⟨x, y, w⟩
    rfl
  have hYZW : entropyOf (marginalTriple_SndThd (pmfXZYW P)) =
      entropyOf (marginalQuad_SndThdFth P) := by
    symm
    refine entropyOf_equiv_eq eYZW (marginalQuad_SndThdFth P)
      (marginalTriple_SndThd (pmfXZYW P)) ?_
    intro yzw
    rcases yzw with ⟨y, z, w⟩
    rfl
  have hYW : entropyOf (marginalTriple_Thd (pmfXZYW P)) =
      entropyOf (marginalQuad_SndFth P) := by
    apply congrArg entropyOf
    funext yw
    rcases yw with ⟨y, w⟩
    rfl
  have hFull : entropyOf (fun xz_yw : α × γ × (β × δ) => (pmfXZYW P).pmf xz_yw) =
      entropyOf P.pmf := by
    symm
    refine entropyOf_equiv_eq equivXZYW.symm
      P.pmf
      (fun xz_yw : α × γ × (β × δ) => (pmfXZYW P).pmf xz_yw) ?_
    intro xyzw
    rcases xyzw with ⟨x, y, z, w⟩
    rfl
  unfold condMutualInfo I_XZ_YW entropy
  rw [hXYW, hYZW, hYW, hFull]

/-- Conditional Markovity as a concrete equality. -/
def condMarkov (P : FinitePMF (α × β × γ × δ)) : Prop :=
  ∀ x y z w,
    P.pmf (x, y, z, w) * marginalQuad_SndFth P (y, w)
      =
    marginalQuad_FstSndFth P (x, y, w) * marginalQuad_SndThdFth P (y, z, w)

lemma I_YZ_XW_nonneg (P : FinitePMF (α × β × γ × δ)) : 0 ≤ I_YZ_XW P := by
  have h := condMutualInfo_nonneg (pmfYZXW P)
  rwa [condMutualInfo_pmfYZXW P] at h

lemma I_XZ_YW_eq_zero_of_condMarkov
    (P : FinitePMF (α × β × γ × δ)) (h : condMarkov P) :
    I_XZ_YW P = 0 := by
  have hzero := condMutualInfo_eq_zero_of_condIndep (pmfXZYW P) ?_
  · rwa [condMutualInfo_pmfXZYW P] at hzero
  · intro x z yw
    rcases yw with ⟨y, w⟩
    simpa [condIndep, pmfXZYW, FinitePMF.comapEquiv, equivXZYW, marginalTriple_Thd,
      marginalTriple_FstThd, marginalTriple_SndThd, marginalQuad_SndFth, marginalQuad_FstSndFth,
      marginalQuad_SndThdFth] using h x y z w

end

end CausalQIF.Probability
