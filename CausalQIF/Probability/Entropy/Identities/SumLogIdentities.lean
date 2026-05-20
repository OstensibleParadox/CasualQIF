import CausalQIF.Probability.Entropy.Basic

open Finset
open scoped BigOperators Real

namespace CausalQIF.Probability

noncomputable section

/-! # Sum-Log Marginal Identities

Three algebraic identities reshaping `∑ xyz, P xyz * log (marginal P …)` into
the form `∑ ·, marginal P · * log (marginal P ·)`, one per 3-tuple marginal
(`FstThd`, `SndThd`, `Thd`). Pure summation rewrites; no probability hypotheses.
-/

variable {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]

lemma sum_pmf_log_marginalTriple_FstThd (P : FinitePMF (α × β × γ)) :
    (∑ xyz : α × β × γ,
      P.pmf xyz * Real.log (marginalTriple_FstThd P (xyz.1, xyz.2.2)))
      =
    ∑ xz : α × γ, marginalTriple_FstThd P xz * Real.log (marginalTriple_FstThd P xz) := by
  calc
    (∑ xyz : α × β × γ,
      P.pmf xyz * Real.log (marginalTriple_FstThd P (xyz.1, xyz.2.2)))
        = ∑ x : α, ∑ y : β, ∑ z : γ,
            P.pmf (x, y, z) * Real.log (marginalTriple_FstThd P (x, z)) := by
          rw [Fintype.sum_prod_type]
          congr with x
          rw [Fintype.sum_prod_type]
    _ = ∑ x : α, ∑ z : γ, ∑ y : β,
            P.pmf (x, y, z) * Real.log (marginalTriple_FstThd P (x, z)) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_comm]
    _ = ∑ x : α, ∑ z : γ,
            marginalTriple_FstThd P (x, z) * Real.log (marginalTriple_FstThd P (x, z)) := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro z _
          rw [← Finset.sum_mul]
          rfl
    _ = ∑ xz : α × γ, marginalTriple_FstThd P xz * Real.log (marginalTriple_FstThd P xz) := by
          rw [← Fintype.sum_prod_type' (fun x z =>
            marginalTriple_FstThd P (x, z) * Real.log (marginalTriple_FstThd P (x, z)))]

lemma sum_pmf_log_marginalTriple_SndThd (P : FinitePMF (α × β × γ)) :
    (∑ xyz : α × β × γ,
      P.pmf xyz * Real.log (marginalTriple_SndThd P (xyz.2.1, xyz.2.2)))
      =
    ∑ yz : β × γ, marginalTriple_SndThd P yz * Real.log (marginalTriple_SndThd P yz) := by
  calc
    (∑ xyz : α × β × γ,
      P.pmf xyz * Real.log (marginalTriple_SndThd P (xyz.2.1, xyz.2.2)))
        = ∑ x : α, ∑ y : β, ∑ z : γ,
            P.pmf (x, y, z) * Real.log (marginalTriple_SndThd P (y, z)) := by
          rw [Fintype.sum_prod_type]
          congr with x
          rw [Fintype.sum_prod_type]
    _ = ∑ y : β, ∑ z : γ, ∑ x : α,
            P.pmf (x, y, z) * Real.log (marginalTriple_SndThd P (y, z)) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro y _
          rw [Finset.sum_comm]
    _ = ∑ y : β, ∑ z : γ,
            marginalTriple_SndThd P (y, z) * Real.log (marginalTriple_SndThd P (y, z)) := by
          apply Finset.sum_congr rfl
          intro y _
          apply Finset.sum_congr rfl
          intro z _
          rw [← Finset.sum_mul]
          rfl
    _ = ∑ yz : β × γ, marginalTriple_SndThd P yz * Real.log (marginalTriple_SndThd P yz) := by
          rw [← Fintype.sum_prod_type' (fun y z =>
            marginalTriple_SndThd P (y, z) * Real.log (marginalTriple_SndThd P (y, z)))]

lemma sum_pmf_log_marginalTriple_Thd (P : FinitePMF (α × β × γ)) :
    (∑ xyz : α × β × γ,
      P.pmf xyz * Real.log (marginalTriple_Thd P xyz.2.2))
      =
    ∑ z : γ, marginalTriple_Thd P z * Real.log (marginalTriple_Thd P z) := by
  calc
    (∑ xyz : α × β × γ,
      P.pmf xyz * Real.log (marginalTriple_Thd P xyz.2.2))
        = ∑ x : α, ∑ y : β, ∑ z : γ,
            P.pmf (x, y, z) * Real.log (marginalTriple_Thd P z) := by
          rw [Fintype.sum_prod_type]
          congr with x
          rw [Fintype.sum_prod_type]
    _ = ∑ x : α, ∑ z : γ, ∑ y : β,
            P.pmf (x, y, z) * Real.log (marginalTriple_Thd P z) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_comm]
    _ = ∑ z : γ, ∑ x : α, ∑ y : β,
            P.pmf (x, y, z) * Real.log (marginalTriple_Thd P z) := by
          rw [Finset.sum_comm]
    _ = ∑ z : γ,
            marginalTriple_Thd P z * Real.log (marginalTriple_Thd P z) := by
          apply Finset.sum_congr rfl
          intro z _
          rw [show (∑ x : α, ∑ y : β,
              P.pmf (x, y, z) * Real.log (marginalTriple_Thd P z))
              =
              ∑ x : α, (∑ y : β, P.pmf (x, y, z)) * Real.log (marginalTriple_Thd P z) by
                apply Finset.sum_congr rfl
                intro x _
                rw [← Finset.sum_mul]]
          rw [← Finset.sum_mul]
          rfl

end

end CausalQIF.Probability
