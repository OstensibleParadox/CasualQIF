import CausalQIF.Probability.Entropy.KLDivergence
import CausalQIF.Probability.Entropy.Basic
import CausalQIF.Probability.Entropy.Identities.SumLogIdentities

open Finset
open scoped BigOperators Real

namespace CausalQIF.Probability

noncomputable section

/-! # Conditional Mutual Information Identities

KL-divergence bridge for `condMutualInfo`, the resulting non-negativity, and
the zero-CMI ⇐ conditional-independence corollary.
-/

variable {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]

lemma condMutualInfo_kl_identity (P : FinitePMF (α × β × γ)) :
    (∑ xyz : α × β × γ, P.pmf xyz * Real.log (P.pmf xyz / condProductMass P xyz))
      = condMutualInfo P * Real.log 2 := by
  let A : ℝ := ∑ xyz : α × β × γ, P.pmf xyz * Real.log (P.pmf xyz)
  let B : ℝ := ∑ xz : α × γ, marginalTripleFstThd P xz * Real.log (marginalTripleFstThd P xz)
  let C : ℝ := ∑ yz : β × γ, marginalTripleSndThd P yz * Real.log (marginalTripleSndThd P yz)
  let D : ℝ := ∑ z : γ, marginalTripleThd P z * Real.log (marginalTripleThd P z)
  have hterm : ∀ xyz : α × β × γ,
      P.pmf xyz * Real.log (P.pmf xyz / condProductMass P xyz)
        =
      ((P.pmf xyz * Real.log (P.pmf xyz)
        - P.pmf xyz * Real.log (marginalTripleFstThd P (xyz.1, xyz.2.2)))
        - P.pmf xyz * Real.log (marginalTripleSndThd P (xyz.2.1, xyz.2.2)))
        + P.pmf xyz * Real.log (marginalTripleThd P xyz.2.2) := by
    intro xyz
    by_cases hxyz : P.pmf xyz = 0
    · simp [hxyz]
    · rcases xyz with ⟨x, y, z⟩
      have hp_pos : 0 < P.pmf (x, y, z) :=
        lt_of_le_of_ne (P.pmf_nonneg (x, y, z)) (Ne.symm hxyz)
      have hxz_pos : 0 < marginalTripleFstThd P (x, z) :=
        lt_of_lt_of_le hp_pos (pmf_le_marginalTripleFstThd P x y z)
      have hyz_pos : 0 < marginalTripleSndThd P (y, z) :=
        lt_of_lt_of_le hp_pos (pmf_le_marginalTripleSndThd P x y z)
      have hz_pos : 0 < marginalTripleThd P z :=
        lt_of_lt_of_le hxz_pos (marginalTripleFstThd_le_marginalTripleThd P x z)
      have hq_pos : 0 < condProductMass P (x, y, z) :=
        condProductMass_pos_of_pmf_ne_zero P (x, y, z) hxyz
      have hlogq : Real.log (condProductMass P (x, y, z))
          =
          Real.log (marginalTripleFstThd P (x, z)) +
          Real.log (marginalTripleSndThd P (y, z)) -
          Real.log (marginalTripleThd P z) := by
        unfold condProductMass
        rw [Real.log_div (mul_ne_zero hxz_pos.ne' hyz_pos.ne') hz_pos.ne']
        rw [Real.log_mul hxz_pos.ne' hyz_pos.ne']
      rw [Real.log_div hp_pos.ne' hq_pos.ne', hlogq]
      ring
  have hsum :
      (∑ xyz : α × β × γ,
        P.pmf xyz * Real.log (P.pmf xyz / condProductMass P xyz))
        = A - B - C + D := by
    calc
      (∑ xyz : α × β × γ,
        P.pmf xyz * Real.log (P.pmf xyz / condProductMass P xyz))
          =
        ∑ xyz : α × β × γ,
          (((P.pmf xyz * Real.log (P.pmf xyz)
            - P.pmf xyz * Real.log (marginalTripleFstThd P (xyz.1, xyz.2.2)))
            - P.pmf xyz * Real.log (marginalTripleSndThd P (xyz.2.1, xyz.2.2)))
            + P.pmf xyz * Real.log (marginalTripleThd P xyz.2.2)) := by
            apply Finset.sum_congr rfl
            intro xyz _
            exact hterm xyz
      _ = A - B - C + D := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
            rw [sum_pmf_log_marginalTripleFstThd P, sum_pmf_log_marginalTripleSndThd P,
              sum_pmf_log_marginalTripleThd P]
  have hHXZ := entropyOf_mul_log2 (marginalTripleFstThd P)
  have hHYZ := entropyOf_mul_log2 (marginalTripleSndThd P)
  have hHZ := entropyOf_mul_log2 (marginalTripleThd P)
  have hHXYZ := entropyOf_mul_log2 (fun xyz : α × β × γ => P.pmf xyz)
  have hcmi : condMutualInfo P * Real.log 2 = A - B - C + D := by
    unfold condMutualInfo
    calc
      (entropyOf (marginalTripleFstThd P) + entropyOf (marginalTripleSndThd P) -
          entropyOf (marginalTripleThd P) -
          entropyOf (fun xyz : α × β × γ => P.pmf xyz)) * Real.log 2
          =
        entropyOf (marginalTripleFstThd P) * Real.log 2 +
          entropyOf (marginalTripleSndThd P) * Real.log 2 -
          entropyOf (marginalTripleThd P) * Real.log 2 -
          entropyOf (fun xyz : α × β × γ => P.pmf xyz) * Real.log 2 := by
            ring
      _ = A - B - C + D := by
            rw [hHXZ, hHYZ, hHZ, hHXYZ]
            simp [A, B, C, D]
            ring
  rw [hsum, hcmi]

lemma condMutualInfo_nonneg (P : FinitePMF (α × β × γ)) :
    0 ≤ condMutualInfo P := by
  have hkl := kl_nonneg_support P.pmf (condProductMass P)
    P.pmf_nonneg
    (condProductMass_nonneg P)
    (condProductMass_pos_of_pmf_ne_zero P)
    P.sum_one
    (condProductMass_sum_one P)
  rw [condMutualInfo_kl_identity P] at hkl
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  by_contra hneg
  push Not at hneg
  have hmul_neg : condMutualInfo P * Real.log 2 < 0 :=
    mul_neg_of_neg_of_pos hneg hlog2_pos
  linarith

theorem condMutualInfo_eq_zero_of_condIndep (P : FinitePMF (α × β × γ))
    (hIndep : condIndep P) : condMutualInfo P = 0 := by
  have hkl_zero : (∑ xyz : α × β × γ, P.pmf xyz * Real.log (P.pmf xyz / condProductMass P xyz)) = 0 := by
    apply Finset.sum_eq_zero; intro xyz _; by_cases hx : P.pmf xyz = 0
    · simp [hx]
    · rcases xyz with ⟨a, b, z⟩; have h_eq := hIndep a b z
      have hz_pos : 0 < marginalTripleThd P z := by
        have hp_pos : 0 < P.pmf (a, b, z) := lt_of_le_of_ne (P.pmf_nonneg _) (Ne.symm hx)
        have hXZ_pos : 0 < marginalTripleFstThd P (a, z) := lt_of_lt_of_le hp_pos (pmf_le_marginalTripleFstThd P a b z)
        exact lt_of_lt_of_le hXZ_pos (marginalTripleFstThd_le_marginalTripleThd P a z)
      have hq_eq : condProductMass P (a, b, z) = P.pmf (a, b, z) := by
        unfold condProductMass; rw [← h_eq]; field_simp [hz_pos.ne']
      simp [hq_eq, hx]
  have hmul := condMutualInfo_kl_identity P
  rw [hkl_zero] at hmul
  have hlog2 : Real.log 2 ≠ 0 := by positivity
  exact (mul_eq_zero.mp hmul.symm).resolve_right hlog2

end

end CausalQIF.Probability
