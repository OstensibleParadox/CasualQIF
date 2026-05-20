import CausalQIF.Probability.Entropy.Basic
import CausalQIF.Probability.FinitePMF.Marginalize

open Finset
open scoped BigOperators Real

namespace CausalQIF.Probability

noncomputable section

/-! # Reshape Equivs and PMF Transports

Five `Equiv`s reshaping a 4-tuple into a 3-tuple-shaped carrier and the
associated PMF transports used by the bridge lemmas:

* `equivPairFstFthReshape` / `pmfPairFstFthReshape` — group (Fst,Fth) as the
  conditioning pair.
* `equivPairSndFthReshape` / `pmfPairSndFthReshape` — group (Snd,Fth) as the
  conditioning pair.
* `equivMargOutSnd` / `pmfMargOutSnd` — marginalize the second coordinate out.
* `equivMargOutFst` / `pmfMargOutFst` — marginalize the first coordinate out.
* `equivPairFstSnd` / `pmfPairFstSnd` — group (Fst,Snd) as one coordinate.
-/

variable {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]

def equivPairFstFthReshape : β × γ × (α × δ) ≃ α × β × γ × δ where
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

def equivPairSndFthReshape : α × γ × (β × δ) ≃ α × β × γ × δ where
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

def pmfPairFstFthReshape (P : FinitePMF (α × β × γ × δ)) :
    FinitePMF (β × γ × (α × δ)) :=
  FinitePMF.comapEquiv equivPairFstFthReshape P

def pmfPairSndFthReshape (P : FinitePMF (α × β × γ × δ)) :
    FinitePMF (α × γ × (β × δ)) :=
  FinitePMF.comapEquiv equivPairSndFthReshape P

@[deprecated equivMarginalizeOutSnd (since := "2026-05")]
alias equivMargOutSnd := equivMarginalizeOutSnd

@[deprecated marginalizeOutSnd (since := "2026-05")]
alias pmfMargOutSnd := marginalizeOutSnd

@[deprecated equivMarginalizeOutFst (since := "2026-05")]
alias equivMargOutFst := equivMarginalizeOutFst

@[deprecated marginalizeOutFst (since := "2026-05")]
alias pmfMargOutFst := marginalizeOutFst

def equivPairFstSnd : (α × β) × γ × δ ≃ α × β × γ × δ where
  toFun t := (t.1.1, t.1.2, t.2.1, t.2.2)
  invFun t := ((t.1, t.2.1), t.2.2.1, t.2.2.2)
  left_inv := by intro t; rcases t with ⟨⟨x, y⟩, z, w⟩; rfl
  right_inv := by intro t; rcases t with ⟨x, y, z, w⟩; rfl

def pmfPairFstSnd (P : FinitePMF (α × β × γ × δ)) : FinitePMF ((α × β) × γ × δ) :=
  FinitePMF.comapEquiv equivPairFstSnd P

end

end CausalQIF.Probability
