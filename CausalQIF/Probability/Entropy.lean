import CausalQIF.Probability.FinitePMF

open Finset
open scoped BigOperators Real

namespace CausalQIF.Probability

noncomputable section

variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-! ## Conditional Mutual Information -/

def I_A_cond_C_B (P : FinitePMF (α × β × γ)) : ℝ :=
  entropyOf (marginalXZMass P) + entropyOf (marginalYZMass P) -
  entropyOf (marginalZMass P) - entropy P

/-! ## Conditional Independence -/

def condIndep (P : FinitePMF (α × β × γ)) : Prop :=
  ∀ a b z,
    P.pmf (a, b, z) * marginalZMass P z =
      marginalXZMass P (a, z) * marginalYZMass P (b, z)

end

end CausalQIF.Probability
