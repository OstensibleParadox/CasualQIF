import CausalQIF.CausalModel.Factorization
import CausalQIF.Probability.Markov

open Finset
open scoped BigOperators Real

namespace CausalQIF.CausalModel

noncomputable section

open Probability

variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/--
Product factorization for a 3-node linear chain 0 -> 1 -> 2.

The distribution P(a, b, c) factorizes if P(a, b, c) = P(a) * P(b | a) * P(c | b).
-/
def ProductFactorizes_chain3 (P : FinitePMF (α × β × γ)) : Prop :=
  ∀ a b c,
    P.pmf (a, b, c) * marginalTriple_Snd P b =
      marginalTriple_FstSnd P (a, b) * marginalTriple_SndThd P (b, c)

/--
Direct derivation of the Markov property from product factorization for the chain instance.
This closes Debt 1 for the showcased linear chain.
-/
theorem isMarkovChain_of_productFactorizes_chain3 (P : FinitePMF (α × β × γ))
    (h : ProductFactorizes_chain3 P) : IsMarkovChain P := by
  -- By definition in Markov.lean, IsMarkovChain P is exactly 
  -- ∀ a b c, P(a,b,c) * P(b) = P(a,b) * P(b,c)
  exact h

end

end CausalQIF.CausalModel
