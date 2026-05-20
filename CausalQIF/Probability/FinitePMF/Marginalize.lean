import CausalQIF.Probability.FinitePMF

open Finset
open scoped BigOperators Real

namespace CausalQIF.Probability

noncomputable section

/-!
# Four-Variable Marginalization Helpers

Additive projections from a four-variable PMF to three-variable PMFs. Each
projection is implemented by reshaping the retained variables into the main
component and then using `marginalizeLeafPMF` to sum out the leaf.
-/

variable {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]

/-- Reshape `(β, γ, δ)` as the retained part and `α` as the leaf to sum out. -/
def equivMarginalizeOutFst : (β × γ × δ) × α ≃ α × β × γ × δ where
  toFun t := (t.2, t.1.1, t.1.2.1, t.1.2.2)
  invFun t := ((t.2.1, t.2.2.1, t.2.2.2), t.1)
  left_inv := by
    intro t
    rcases t with ⟨⟨b, c, d⟩, a⟩
    rfl
  right_inv := by
    intro t
    rcases t with ⟨a, b, c, d⟩
    rfl

/-- Marginalize out the first component of a four-variable PMF. -/
def marginalizeOutFst (P : FinitePMF (α × β × γ × δ)) : FinitePMF (β × γ × δ) :=
  marginalizeLeafPMF (FinitePMF.comapEquiv equivMarginalizeOutFst P)

/-- Reshape `(α, γ, δ)` as the retained part and `β` as the leaf to sum out. -/
def equivMarginalizeOutSnd : (α × γ × δ) × β ≃ α × β × γ × δ where
  toFun t := (t.1.1, t.2, t.1.2.1, t.1.2.2)
  invFun t := ((t.1, t.2.2.1, t.2.2.2), t.2.1)
  left_inv := by
    intro t
    rcases t with ⟨⟨a, c, d⟩, b⟩
    rfl
  right_inv := by
    intro t
    rcases t with ⟨a, b, c, d⟩
    rfl

/-- Marginalize out the second component of a four-variable PMF. -/
def marginalizeOutSnd (P : FinitePMF (α × β × γ × δ)) : FinitePMF (α × γ × δ) :=
  marginalizeLeafPMF (FinitePMF.comapEquiv equivMarginalizeOutSnd P)

/-- Reshape `(α, β, δ)` as the retained part and `γ` as the leaf to sum out. -/
def equivMarginalizeOutThd : (α × β × δ) × γ ≃ α × β × γ × δ where
  toFun t := (t.1.1, t.1.2.1, t.2, t.1.2.2)
  invFun t := ((t.1, t.2.1, t.2.2.2), t.2.2.1)
  left_inv := by
    intro t
    rcases t with ⟨⟨a, b, d⟩, c⟩
    rfl
  right_inv := by
    intro t
    rcases t with ⟨a, b, c, d⟩
    rfl

/-- Marginalize out the third component of a four-variable PMF. -/
def marginalizeOutThd (P : FinitePMF (α × β × γ × δ)) : FinitePMF (α × β × δ) :=
  marginalizeLeafPMF (FinitePMF.comapEquiv equivMarginalizeOutThd P)

end

end CausalQIF.Probability
