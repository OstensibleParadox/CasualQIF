import CausalQIF.Probability.FinitePMF

open Finset
open scoped BigOperators Real

namespace CausalQIF.Probability

noncomputable section

variable {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]

/-! ## Conditional Mutual Information -/

def condMutualInfo (P : FinitePMF (α × β × γ)) : ℝ :=
  entropyOf (marginalTriple_FstThd P) + entropyOf (marginalTriple_SndThd P) -
  entropyOf (marginalTriple_Thd P) - entropy P

/-! ## Conditional Independence -/

def condIndep (P : FinitePMF (α × β × γ)) : Prop :=
  ∀ a b z,
    P.pmf (a, b, z) * marginalTriple_Thd P z =
      marginalTriple_FstThd P (a, z) * marginalTriple_SndThd P (b, z)

def condProductMass (P : FinitePMF (α × β × γ)) (xyz : α × β × γ) : ℝ :=
  marginalTriple_FstThd P (xyz.1, xyz.2.2) *
    marginalTriple_SndThd P (xyz.2.1, xyz.2.2) /
    marginalTriple_Thd P xyz.2.2

lemma condProductMass_nonneg (P : FinitePMF (α × β × γ)) (xyz : α × β × γ) :
    0 ≤ condProductMass P xyz := by
  unfold condProductMass
  exact div_nonneg
    (mul_nonneg (marginalTriple_FstThd_nonneg P (xyz.1, xyz.2.2))
      (marginalTriple_SndThd_nonneg P (xyz.2.1, xyz.2.2)))
    (marginalTriple_Thd_nonneg P xyz.2.2)

lemma pmf_le_marginalTriple_FstThd (P : FinitePMF (α × β × γ)) (x : α) (y : β) (z : γ) :
    P.pmf (x, y, z) ≤ marginalTriple_FstThd P (x, z) := by
  unfold marginalTriple_FstThd
  exact Finset.single_le_sum (fun y' _ => P.pmf_nonneg (x, y', z)) (Finset.mem_univ y)

lemma pmf_le_marginalTriple_SndThd (P : FinitePMF (α × β × γ)) (x : α) (y : β) (z : γ) :
    P.pmf (x, y, z) ≤ marginalTriple_SndThd P (y, z) := by
  unfold marginalTriple_SndThd
  exact Finset.single_le_sum (fun x' _ => P.pmf_nonneg (x', y, z)) (Finset.mem_univ x)

lemma marginalTriple_FstThd_le_marginalTriple_Thd (P : FinitePMF (α × β × γ)) (x : α) (z : γ) :
    marginalTriple_FstThd P (x, z) ≤ marginalTriple_Thd P z := by
  have h_nonneg : ∀ x : α, 0 ≤ marginalTriple_FstThd P (x, z) :=
    fun x => marginalTriple_FstThd_nonneg P (x, z)
  have hle : marginalTriple_FstThd P (x, z) ≤ ∑ x : α, marginalTriple_FstThd P (x, z) :=
    Finset.single_le_sum (fun x _ => h_nonneg x) (Finset.mem_univ x)
  rwa [marginalTriple_FstThd_sum_thd P z] at hle

lemma condProductMass_pos_of_pmf_ne_zero
    (P : FinitePMF (α × β × γ)) (xyz : α × β × γ)
    (hxyz : P.pmf xyz ≠ 0) :
    0 < condProductMass P xyz := by
  rcases xyz with ⟨x, y, z⟩
  have hp_pos : 0 < P.pmf (x, y, z) :=
    lt_of_le_of_ne (P.pmf_nonneg (x, y, z)) (Ne.symm hxyz)
  have hxz_pos : 0 < marginalTriple_FstThd P (x, z) :=
    lt_of_lt_of_le hp_pos (pmf_le_marginalTriple_FstThd P x y z)
  have hyz_pos : 0 < marginalTriple_SndThd P (y, z) :=
    lt_of_lt_of_le hp_pos (pmf_le_marginalTriple_SndThd P x y z)
  have hz_pos : 0 < marginalTriple_Thd P z :=
    lt_of_lt_of_le hxz_pos (marginalTriple_FstThd_le_marginalTriple_Thd P x z)
  unfold condProductMass
  exact div_pos (mul_pos hxz_pos hyz_pos) hz_pos

lemma condProductMass_sum_fiber (P : FinitePMF (α × β × γ)) (z : γ) :
    (∑ x : α, ∑ y : β, condProductMass P (x, y, z)) = marginalTriple_Thd P z := by
  by_cases hz : marginalTriple_Thd P z = 0
  · have hxz_zero : ∀ x : α, marginalTriple_FstThd P (x, z) = 0 := by
      intro x; have hle := marginalTriple_FstThd_le_marginalTriple_Thd P x z
      have hnonneg := marginalTriple_FstThd_nonneg P (x, z); linarith
    simp [condProductMass, hz, hxz_zero]
  · have hz_pos : 0 < marginalTriple_Thd P z := lt_of_le_of_ne (marginalTriple_Thd_nonneg P z) (Ne.symm hz)
    calc
      (∑ x : α, ∑ y : β, condProductMass P (x, y, z))
          = ∑ x : α, ∑ y : β, marginalTriple_FstThd P (x, z) * marginalTriple_SndThd P (y, z) / marginalTriple_Thd P z := rfl
      _ = ∑ x : α, marginalTriple_FstThd P (x, z) := by
            apply Finset.sum_congr rfl; intro x _
            have hterm : ∀ y : β, marginalTriple_FstThd P (x, z) * marginalTriple_SndThd P (y, z) / marginalTriple_Thd P z
                = (marginalTriple_FstThd P (x, z) / marginalTriple_Thd P z) * marginalTriple_SndThd P (y, z) := by
              intro y; field_simp [hz]
            simp_rw [hterm]; rw [← Finset.mul_sum, marginalTriple_SndThd_sum_thd P z]; field_simp [hz]
      _ = marginalTriple_Thd P z := marginalTriple_FstThd_sum_thd P z

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
    _ = ∑ z : γ, marginalTriple_Thd P z := by apply Finset.sum_congr rfl; intro z _; exact condProductMass_sum_fiber P z
    _ = 1 := marginalTriple_Thd_sum_one P

end

end CausalQIF.Probability
