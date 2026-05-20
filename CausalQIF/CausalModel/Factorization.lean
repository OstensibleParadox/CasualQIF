import CausalQIF.DSeparation.Path.Trail
import CausalQIF.Probability.Markov

open Finset
open scoped BigOperators Real

namespace CausalQIF.CausalModel

noncomputable section

variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-! ## DAG Factorization -/

abbrev CondIndepPredicate (Ω : Type) [Fintype Ω] [DecidableEq Ω] (V : Type) [DecidableEq V] [Fintype V] :=
  Probability.FinitePMF Ω → Finset V → Finset V → Finset V → Prop

def FactorizesOverDAG {Ω : Type} [Fintype Ω] [DecidableEq Ω] {V : Type} [DecidableEq V] [Fintype V]
    (G : Graph.DAG V) (CI : CondIndepPredicate Ω V) (P : Probability.FinitePMF Ω) : Prop :=
  ∀ X Y Z : Finset V, DSeparation.dSeparates G X Y Z → CI P X Y Z

/-! ## 3-Variable Markov Adapter -/

def isMarkovChainNodeCI {V : Type} [DecidableEq V] [Fintype V] (v0 v1 v2 : V)
    (P : Probability.FinitePMF (α × β × γ)) (X Y Z : Finset V) : Prop :=
  X = ({v0} : Finset V) →
    Y = ({v2} : Finset V) →
      Z = ({v1} : Finset V) →
        Probability.IsMarkovChain P

/-! ## Bridge Theorems -/

theorem isMarkovChain_of_factorizes_of_dSeparates
    {V : Type} [DecidableEq V] [Fintype V] (v0 v1 v2 : V)
    (G : Graph.DAG V) (P : Probability.FinitePMF (α × β × γ))
    (h_factor : FactorizesOverDAG G (isMarkovChainNodeCI v0 v1 v2) P)
    (h_dsep : DSeparation.dSeparates G ({v0} : Finset V) ({v2} : Finset V) ({v1} : Finset V)) :
    Probability.IsMarkovChain P :=
  h_factor ({v0} : Finset V) ({v2} : Finset V) ({v1} : Finset V) h_dsep rfl rfl rfl

theorem condMutualInfo_eq_zero_of_factorizes_of_dSeparates
    {V : Type} [DecidableEq V] [Fintype V] (v0 v1 v2 : V)
    (G : Graph.DAG V) (P : Probability.FinitePMF (α × β × γ))
    (h_factor : FactorizesOverDAG G (isMarkovChainNodeCI v0 v1 v2) P)
    (h_dsep : DSeparation.dSeparates G ({v0} : Finset V) ({v2} : Finset V) ({v1} : Finset V)) :
    Probability.condMutualInfo (Probability.pmfTripleReshapeFstThdSnd P) = 0 :=
  Probability.condMutualInfo_eq_zero_of_isMarkovChain P
    (isMarkovChain_of_factorizes_of_dSeparates v0 v1 v2 G P h_factor h_dsep)

/-! ## 4-Variable condMarkov Adapter -/

variable {δ : Type} [Fintype δ] [DecidableEq δ]

/-- Node-set-premised adapter pinning the cut-PMF tuple layout
`(State, CutVars, MissingTrace, VisibleTrace)`.

Argument order matches `CondIndepPredicate`'s `(P, X, Y, Z)`: position 2 (`Y`) is
the d-separation target and position 3 (`Z`) is the conditioning set. -/
def condMarkovNodeCI {V : Type} [DecidableEq V] [Fintype V] (vX vY vZ vW : V)
    (P : Probability.FinitePMF (α × β × γ × δ)) (X Y Z : Finset V) : Prop :=
  X = ({vX} : Finset V) →
    Y = ({vZ} : Finset V) →
      Z = ({vY, vW} : Finset V) →
        Probability.condMarkov P

theorem condMarkov_of_factorizes_of_dSeparates_fourVar
    {V : Type} [DecidableEq V] [Fintype V] (vX vY vZ vW : V)
    (G : Graph.DAG V) (P : Probability.FinitePMF (α × β × γ × δ))
    (h_factor : FactorizesOverDAG G (condMarkovNodeCI (α := α) (β := β) (γ := γ) (δ := δ) vX vY vZ vW) P)
    (h_dsep : DSeparation.dSeparates G
      ({vX} : Finset V) ({vZ} : Finset V) ({vY, vW} : Finset V)) :
    Probability.condMarkov P :=
  h_factor ({vX} : Finset V) ({vZ} : Finset V) ({vY, vW} : Finset V) h_dsep rfl rfl rfl

end

end CausalQIF.CausalModel
