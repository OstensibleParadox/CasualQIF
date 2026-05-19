import CausalQIF.DSeparation.Path.Trail
import CausalQIF.Probability.Markov

open Finset
open scoped BigOperators Real

namespace CausalQIF.CausalModel

noncomputable section

variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-! ## DAG Factorization -/

abbrev CondIndepPredicate (Ω : Type) [Fintype Ω] [DecidableEq Ω] :=
  Probability.FinitePMF Ω → Finset ℕ → Finset ℕ → Finset ℕ → Prop

def FactorizesOverDAG {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (G : Graph.DAG) (CI : CondIndepPredicate Ω) (P : Probability.FinitePMF Ω) : Prop :=
  ∀ X Y Z : Finset ℕ, DSeparation.dSeparates G X Y Z → CI P X Y Z

/-! ## 3-Variable Markov Adapter -/

def isMarkovChainNodeCI (P : Probability.FinitePMF (α × β × γ)) (X Y Z : Finset ℕ) : Prop :=
  X = ({0} : Finset ℕ) →
    Y = ({2} : Finset ℕ) →
      Z = ({1} : Finset ℕ) →
        Probability.IsMarkovChain P

/-! ## Bridge Theorems -/

theorem isMarkovChain_of_factorizes_of_dSeparates
    (G : Graph.DAG) (P : Probability.FinitePMF (α × β × γ))
    (h_factor : FactorizesOverDAG G isMarkovChainNodeCI P)
    (h_dsep : DSeparation.dSeparates G ({0} : Finset ℕ) ({2} : Finset ℕ) ({1} : Finset ℕ)) :
    Probability.IsMarkovChain P :=
  h_factor ({0} : Finset ℕ) ({2} : Finset ℕ) ({1} : Finset ℕ) h_dsep rfl rfl rfl

theorem condMutualInfo_eq_zero_of_factorizes_of_dSeparates
    (G : Graph.DAG) (P : Probability.FinitePMF (α × β × γ))
    (h_factor : FactorizesOverDAG G isMarkovChainNodeCI P)
    (h_dsep : DSeparation.dSeparates G ({0} : Finset ℕ) ({2} : Finset ℕ) ({1} : Finset ℕ)) :
    Probability.I_A_cond_C_B P = 0 :=
  Probability.condMutualInfo_eq_zero_of_isMarkovChain P
    (isMarkovChain_of_factorizes_of_dSeparates G P h_factor h_dsep)

end

end CausalQIF.CausalModel
