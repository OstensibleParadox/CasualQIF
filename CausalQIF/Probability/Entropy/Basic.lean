import CausalQIF.Probability.FinitePMF

open Finset
open scoped BigOperators Real

namespace CausalQIF.Probability

noncomputable section

variable {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]

/-! ## Conditional Mutual Information -/

def condMutualInfo (P : FinitePMF (α × β × γ)) : ℝ :=
  entropyOf (marginalTripleFstThd P) + entropyOf (marginalTripleSndThd P) -
  entropyOf (marginalTripleThd P) - entropy P

/-! ## Conditional Independence -/

def condIndep (P : FinitePMF (α × β × γ)) : Prop :=
  ∀ a b z,
    P.pmf (a, b, z) * marginalTripleThd P z =
      marginalTripleFstThd P (a, z) * marginalTripleSndThd P (b, z)

def condProductMass (P : FinitePMF (α × β × γ)) (xyz : α × β × γ) : ℝ :=
  marginalTripleFstThd P (xyz.1, xyz.2.2) *
    marginalTripleSndThd P (xyz.2.1, xyz.2.2) /
    marginalTripleThd P xyz.2.2

lemma condProductMass_nonneg (P : FinitePMF (α × β × γ)) (xyz : α × β × γ) :
    0 ≤ condProductMass P xyz := by
  unfold condProductMass
  exact div_nonneg
    (mul_nonneg (marginalTripleFstThd_nonneg P (xyz.1, xyz.2.2))
      (marginalTripleSndThd_nonneg P (xyz.2.1, xyz.2.2)))
    (marginalTripleThd_nonneg P xyz.2.2)

lemma pmf_le_marginalTripleFstThd (P : FinitePMF (α × β × γ)) (x : α) (y : β) (z : γ) :
    P.pmf (x, y, z) ≤ marginalTripleFstThd P (x, z) := by
  unfold marginalTripleFstThd
  exact Finset.single_le_sum (fun y' _ => P.pmf_nonneg (x, y', z)) (Finset.mem_univ y)

lemma pmf_le_marginalTripleSndThd (P : FinitePMF (α × β × γ)) (x : α) (y : β) (z : γ) :
    P.pmf (x, y, z) ≤ marginalTripleSndThd P (y, z) := by
  unfold marginalTripleSndThd
  exact Finset.single_le_sum (fun x' _ => P.pmf_nonneg (x', y, z)) (Finset.mem_univ x)

lemma marginalTripleFstThd_le_marginalTripleThd (P : FinitePMF (α × β × γ)) (x : α) (z : γ) :
    marginalTripleFstThd P (x, z) ≤ marginalTripleThd P z := by
  have h_nonneg : ∀ x : α, 0 ≤ marginalTripleFstThd P (x, z) :=
    fun x => marginalTripleFstThd_nonneg P (x, z)
  have hle : marginalTripleFstThd P (x, z) ≤ ∑ x : α, marginalTripleFstThd P (x, z) :=
    Finset.single_le_sum (fun x _ => h_nonneg x) (Finset.mem_univ x)
  rwa [marginalTripleFstThd_sum_thd P z] at hle

lemma condProductMass_pos_of_pmf_ne_zero
    (P : FinitePMF (α × β × γ)) (xyz : α × β × γ)
    (hxyz : P.pmf xyz ≠ 0) :
    0 < condProductMass P xyz := by
  rcases xyz with ⟨x, y, z⟩
  have hp_pos : 0 < P.pmf (x, y, z) :=
    lt_of_le_of_ne (P.pmf_nonneg (x, y, z)) (Ne.symm hxyz)
  have hxz_pos : 0 < marginalTripleFstThd P (x, z) :=
    lt_of_lt_of_le hp_pos (pmf_le_marginalTripleFstThd P x y z)
  have hyz_pos : 0 < marginalTripleSndThd P (y, z) :=
    lt_of_lt_of_le hp_pos (pmf_le_marginalTripleSndThd P x y z)
  have hz_pos : 0 < marginalTripleThd P z :=
    lt_of_lt_of_le hxz_pos (marginalTripleFstThd_le_marginalTripleThd P x z)
  unfold condProductMass
  exact div_pos (mul_pos hxz_pos hyz_pos) hz_pos

lemma condProductMass_sum_fiber (P : FinitePMF (α × β × γ)) (z : γ) :
    (∑ x : α, ∑ y : β, condProductMass P (x, y, z)) = marginalTripleThd P z := by
  by_cases hz : marginalTripleThd P z = 0
  · have hxz_zero : ∀ x : α, marginalTripleFstThd P (x, z) = 0 := by
      intro x; have hle := marginalTripleFstThd_le_marginalTripleThd P x z
      have hnonneg := marginalTripleFstThd_nonneg P (x, z); linarith
    simp [condProductMass, hz, hxz_zero]
  · have hz_pos : 0 < marginalTripleThd P z := lt_of_le_of_ne (marginalTripleThd_nonneg P z) (Ne.symm hz)
    calc
      (∑ x : α, ∑ y : β, condProductMass P (x, y, z))
          = ∑ x : α, ∑ y : β, marginalTripleFstThd P (x, z) * marginalTripleSndThd P (y, z) / marginalTripleThd P z := rfl
      _ = ∑ x : α, marginalTripleFstThd P (x, z) := by
            apply Finset.sum_congr rfl; intro x _
            have hterm : ∀ y : β, marginalTripleFstThd P (x, z) * marginalTripleSndThd P (y, z) / marginalTripleThd P z
                = (marginalTripleFstThd P (x, z) / marginalTripleThd P z) * marginalTripleSndThd P (y, z) := by
              intro y; field_simp [hz]
            simp_rw [hterm]; rw [← Finset.mul_sum, marginalTripleSndThd_sum_thd P z]; field_simp [hz]
      _ = marginalTripleThd P z := marginalTripleFstThd_sum_thd P z

lemma condProductMass_sum_one (P : FinitePMF (α × β × γ)) :
    ∑ xyz : α × β × γ, condProductMass P xyz = 1 := by
  calc
    ∑ xyz : α × β × γ, condProductMass P xyz
        = ∑ x : α, ∑ y : β, ∑ z : γ, condProductMass P (x, y, z) := by
          rw [Fintype.sum_prod_type]
          congr with x
          rw [Fintype.sum_prod_type]
    _ = ∑ x : α, ∑ z : γ, ∑ y : β, condProductMass P (x, y, z) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_comm]
    _ = ∑ z : γ, ∑ x : α, ∑ y : β, condProductMass P (x, y, z) := by
          rw [Finset.sum_comm]
    _ = ∑ z : γ, marginalTripleThd P z := by apply Finset.sum_congr rfl; intro z _; exact condProductMass_sum_fiber P z
    _ = 1 := marginalTripleThd_sum_one P

@[deprecated marginalTripleFstThd_le_marginalTripleThd (since := "2026-05")]
alias marginalTriple_FstThd_le_marginalTriple_Thd := marginalTripleFstThd_le_marginalTripleThd
@[deprecated pmf_le_marginalTripleFstThd (since := "2026-05")]
alias pmf_le_marginalTriple_FstThd := pmf_le_marginalTripleFstThd
@[deprecated pmf_le_marginalTripleSndThd (since := "2026-05")]
alias pmf_le_marginalTriple_SndThd := pmf_le_marginalTripleSndThd

end

end CausalQIF.Probability
