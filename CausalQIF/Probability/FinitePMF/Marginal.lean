import CausalQIF.Probability.FinitePMF.Basic

open Finset
open scoped BigOperators Real

namespace CausalQIF.Probability

noncomputable section

/-! # Two- and Three-Variable Marginals

Position-indexed marginals of `FinitePMF`. For 2-tuples: `marginalPairFst`,
`marginalPairSnd`, and the general 2→1 transporter `marginalizeLeafPMF`.
For 3-tuples: `marginalTripleThd`, `marginalTripleFstThd`,
`marginalTripleSndThd`, plus their non-negativity, summation, and pullback
identities.
-/

variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-! ## Pair marginals -/

def marginalPairFst (P : FinitePMF (α × β)) (x : α) : ℝ :=
  ∑ y : β, P.pmf (x, y)

def marginalPairSnd (P : FinitePMF (α × β)) (y : β) : ℝ :=
  ∑ x : α, P.pmf (x, y)

lemma marginalPairFst_nonneg (P : FinitePMF (α × β)) (x : α) :
    0 ≤ marginalPairFst P x :=
  Finset.sum_nonneg (fun y _ => P.pmf_nonneg (x, y))

lemma marginalPairSnd_nonneg (P : FinitePMF (α × β)) (y : β) :
    0 ≤ marginalPairSnd P y :=
  Finset.sum_nonneg (fun x _ => P.pmf_nonneg (x, y))

lemma marginalPairFst_sum_one (P : FinitePMF (α × β)) :
    ∑ x : α, marginalPairFst P x = 1 := by
  unfold marginalPairFst
  rw [← Finset.sum_product]
  exact P.sum_one

lemma marginalPairSnd_sum_one (P : FinitePMF (α × β)) :
    ∑ y : β, marginalPairSnd P y = 1 := by
  unfold marginalPairSnd
  rw [Finset.sum_comm]
  rw [← Finset.sum_product]
  exact P.sum_one

def marginalizeLeafPMF (P : FinitePMF (α × β)) : FinitePMF α where
  pmf x := ∑ leaf : β, P.pmf (x, leaf)
  pmf_nonneg x := by
    exact Finset.sum_nonneg fun leaf _ => P.pmf_nonneg (x, leaf)
  sum_one := by
    calc
      ∑ x : α, ∑ leaf : β, P.pmf (x, leaf)
          = ∑ p : α × β, P.pmf p := (Finset.sum_product (f := P.pmf) (s := univ) (t := univ)).symm
      _ = 1 := P.sum_one

/-! ## Three-variable marginals -/

def marginalTripleThd (P : FinitePMF (α × β × γ)) (z : γ) : ℝ :=
  ∑ x : α, ∑ y : β, P.pmf (x, y, z)

def marginalTripleFstThd (P : FinitePMF (α × β × γ)) (xz : α × γ) : ℝ :=
  ∑ y : β, P.pmf (xz.1, y, xz.2)

def marginalTripleSndThd (P : FinitePMF (α × β × γ)) (yz : β × γ) : ℝ :=
  ∑ x : α, P.pmf (x, yz.1, yz.2)

lemma marginalTripleFstThd_nonneg (P : FinitePMF (α × β × γ)) (xz : α × γ) :
    0 ≤ marginalTripleFstThd P xz :=
  Finset.sum_nonneg (fun y _ => P.pmf_nonneg (xz.1, y, xz.2))

lemma marginalTripleSndThd_nonneg (P : FinitePMF (α × β × γ)) (yz : β × γ) :
    0 ≤ marginalTripleSndThd P yz :=
  Finset.sum_nonneg (fun x _ => P.pmf_nonneg (x, yz.1, yz.2))

lemma marginalTripleThd_nonneg (P : FinitePMF (α × β × γ)) (z : γ) :
    0 ≤ marginalTripleThd P z :=
  Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => P.pmf_nonneg (x, y, z)))

lemma marginalTripleFstThd_sum_thd (P : FinitePMF (α × β × γ)) (z : γ) :
    ∑ x : α, marginalTripleFstThd P (x, z) = marginalTripleThd P z := by
  rfl

lemma marginalTripleSndThd_sum_thd (P : FinitePMF (α × β × γ)) (z : γ) :
    ∑ y : β, marginalTripleSndThd P (y, z) = marginalTripleThd P z := by
  unfold marginalTripleSndThd marginalTripleThd
  rw [Finset.sum_comm]

lemma marginalTripleThd_sum_one (P : FinitePMF (α × β × γ)) :
    ∑ z : γ, marginalTripleThd P z = 1 := by
  have hsum : (∑ x : α, ∑ y : β, ∑ z : γ, P.pmf (x, y, z)) = 1 := by
    calc
      (∑ x : α, ∑ y : β, ∑ z : γ, P.pmf (x, y, z))
          = ∑ x : α, ∑ yz : β × γ, P.pmf (x, yz.1, yz.2) := by
            apply Finset.sum_congr rfl
            intro x _
            rw [← Fintype.sum_prod_type' (fun y z => P.pmf (x, y, z))]
      _ = ∑ xyz : α × β × γ, P.pmf xyz := by
            rw [← Fintype.sum_prod_type]
      _ = 1 := P.sum_one
  unfold marginalTripleThd
  rw [Finset.sum_comm]
  rw [show (∑ x : α, ∑ z : γ, ∑ y : β, P.pmf (x, y, z))
      = ∑ x : α, ∑ y : β, ∑ z : γ, P.pmf (x, y, z) by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_comm]]
  exact hsum

/-! ## Pullback Lemmas -/

lemma marginalTripleFstThd_pullback (P : FinitePMF (α × β × γ)) (f : α × γ → ℝ) :
    ∑ xz : α × γ, marginalTripleFstThd P xz * f xz =
    ∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * f (a, c) := by
  unfold marginalTripleFstThd
  calc
    ∑ xz : α × γ, (∑ y : β, P.pmf (xz.1, y, xz.2)) * f xz
        = ∑ xz : α × γ, ∑ y : β, P.pmf (xz.1, y, xz.2) * f xz := by
          refine Finset.sum_congr rfl (fun xz _ => ?_)
          rw [Finset.sum_mul]
    _ = ∑ y : β, ∑ xz : α × γ, P.pmf (xz.1, y, xz.2) * f xz := by rw [Finset.sum_comm]
    _ = ∑ y : β, ∑ a : α, ∑ c : γ, P.pmf (a, y, c) * f (a, c) := by
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [Fintype.sum_prod_type]
    _ = ∑ a : α, ∑ y : β, ∑ c : γ, P.pmf (a, y, c) * f (a, c) := by rw [Finset.sum_comm]
    _ = ∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * f (a, c) := rfl

lemma marginalTripleSndThd_pullback (P : FinitePMF (α × β × γ)) (f : β × γ → ℝ) :
    ∑ yz : β × γ, marginalTripleSndThd P yz * f yz =
    ∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * f (b, c) := by
  unfold marginalTripleSndThd
  calc
    ∑ yz : β × γ, (∑ x : α, P.pmf (x, yz.1, yz.2)) * f yz
        = ∑ yz : β × γ, ∑ x : α, P.pmf (x, yz.1, yz.2) * f yz := by
          refine Finset.sum_congr rfl (fun yz _ => ?_)
          rw [Finset.sum_mul]
    _ = ∑ x : α, ∑ yz : β × γ, P.pmf (x, yz.1, yz.2) * f yz := by rw [Finset.sum_comm]
    _ = ∑ x : α, ∑ b : β, ∑ c : γ, P.pmf (x, b, c) * f (b, c) := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Fintype.sum_prod_type]
    _ = ∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * f (b, c) := rfl

lemma marginalTripleThd_pullback (P : FinitePMF (α × β × γ)) (f : γ → ℝ) :
    ∑ z : γ, marginalTripleThd P z * f z =
    ∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * f c := by
  unfold marginalTripleThd
  calc
    ∑ c : γ, (∑ a : α, ∑ b : β, P.pmf (a, b, c)) * f c
        = ∑ c : γ, ∑ a : α, ∑ b : β, P.pmf (a, b, c) * f c := by
          refine Finset.sum_congr rfl (fun c _ => ?_)
          simp_rw [Finset.sum_mul]
    _ = ∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * f c := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_comm)

@[deprecated marginalTripleSndThd_pullback (since := "2026-05")]
alias marginalTriple_SndThd_pullback := marginalTripleSndThd_pullback
@[deprecated marginalTripleFstThd_sum_thd (since := "2026-05")]
alias marginalTriple_FstThd_sum_thd := marginalTripleFstThd_sum_thd
@[deprecated marginalTripleSndThd_sum_thd (since := "2026-05")]
alias marginalTriple_SndThd_sum_thd := marginalTripleSndThd_sum_thd
@[deprecated marginalTripleFstThd_nonneg (since := "2026-05")]
alias marginalTriple_FstThd_nonneg := marginalTripleFstThd_nonneg
@[deprecated marginalTripleSndThd_nonneg (since := "2026-05")]
alias marginalTriple_SndThd_nonneg := marginalTripleSndThd_nonneg
@[deprecated marginalTripleThd_sum_one (since := "2026-05")]
alias marginalTriple_Thd_sum_one := marginalTripleThd_sum_one
@[deprecated marginalTripleThd_nonneg (since := "2026-05")]
alias marginalTriple_Thd_nonneg := marginalTripleThd_nonneg
@[deprecated marginalTripleFstThd (since := "2026-05")]
alias marginalTriple_FstThd := marginalTripleFstThd
@[deprecated marginalTripleSndThd (since := "2026-05")]
alias marginalTriple_SndThd := marginalTripleSndThd
@[deprecated marginalTripleThd (since := "2026-05")]
alias marginalTriple_Thd := marginalTripleThd
@[deprecated marginalPairFst (since := "2026-05")]
alias marginalPair_Fst := marginalPairFst
@[deprecated marginalPairSnd (since := "2026-05")]
alias marginalPair_Snd := marginalPairSnd

end

end CausalQIF.Probability
