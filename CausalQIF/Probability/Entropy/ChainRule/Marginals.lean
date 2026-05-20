import CausalQIF.Probability.Entropy.Basic

open Finset
open scoped BigOperators Real

namespace CausalQIF.Probability

noncomputable section

/-! # Four-Variable Marginals

The seven retain-position marginals of a `FinitePMF (α × β × γ × δ)` used by
the four-variable conditional-mutual-information bridges. Each `marginalQuad_*`
sums out the complementary positions of a 4-tuple.
-/

variable {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]

def marginalQuadFstFth (P : FinitePMF (α × β × γ × δ)) (xw : α × δ) : ℝ :=
  ∑ y : β, ∑ z : γ, P.pmf (xw.1, y, z, xw.2)

def marginalQuadSndFth (P : FinitePMF (α × β × γ × δ)) (yw : β × δ) : ℝ :=
  ∑ x : α, ∑ z : γ, P.pmf (x, yw.1, z, yw.2)

def marginalQuadThdFth (P : FinitePMF (α × β × γ × δ)) (zw : γ × δ) : ℝ :=
  ∑ x : α, ∑ y : β, P.pmf (x, y, zw.1, zw.2)

def marginalQuadFth (P : FinitePMF (α × β × γ × δ)) (w : δ) : ℝ :=
  ∑ x : α, ∑ y : β, ∑ z : γ, P.pmf (x, y, z, w)

def marginalQuadFstThdFth (P : FinitePMF (α × β × γ × δ)) (xzw : α × γ × δ) : ℝ :=
  ∑ y : β, P.pmf (xzw.1, y, xzw.2.1, xzw.2.2)

def marginalQuadSndThdFth (P : FinitePMF (α × β × γ × δ)) (yzw : β × γ × δ) : ℝ :=
  ∑ x : α, P.pmf (x, yzw.1, yzw.2.1, yzw.2.2)

def marginalQuadFstSndFth (P : FinitePMF (α × β × γ × δ)) (xyw : α × β × δ) : ℝ :=
  ∑ z : γ, P.pmf (xyw.1, xyw.2.1, z, xyw.2.2)

@[deprecated marginalQuadFstSndFth (since := "2026-05")]
alias marginalQuad_FstSndFth := marginalQuadFstSndFth
@[deprecated marginalQuadFstThdFth (since := "2026-05")]
alias marginalQuad_FstThdFth := marginalQuadFstThdFth
@[deprecated marginalQuadSndThdFth (since := "2026-05")]
alias marginalQuad_SndThdFth := marginalQuadSndThdFth
@[deprecated marginalQuadFstFth (since := "2026-05")]
alias marginalQuad_FstFth := marginalQuadFstFth
@[deprecated marginalQuadSndFth (since := "2026-05")]
alias marginalQuad_SndFth := marginalQuadSndFth
@[deprecated marginalQuadThdFth (since := "2026-05")]
alias marginalQuad_ThdFth := marginalQuadThdFth
@[deprecated marginalQuadFth (since := "2026-05")]
alias marginalQuad_Fth := marginalQuadFth

end

end CausalQIF.Probability
