import CausalQIF.Probability.Entropy
import CausalQIF.Probability.Markov
import CausalQIF.Probability.Entropy.KLDivergence
import CausalQIF.Probability.Entropy.Identities

open Finset
open scoped BigOperators Real

namespace CausalQIF.InformationFlow

noncomputable section

open Probability

variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/--
Variational upper bound on conditional mutual information via a dual witness distribution.

If there exists a collection of distributions ω(b|c) such that the KL divergence 
between the true joint P(a,b,c) and the factorized witness P(a,c)ω(b|c) 
is bounded by C bits, then I(A; B | C) ≤ C.
-/
theorem condMutualInfo_le_of_dual_witness
    (P : FinitePMF (α × β × γ))
    (ω : γ → β → ℝ)
    (h_ω_sum : ∀ c, ∑ b, ω c b = 1)
    (h_ω_pos : ∀ c b, 0 < ω c b)
    (C : ℝ)
    (h_bound : ∑ a, ∑ b, ∑ c, P.pmf (a, b, c) * Real.log (P.pmf (a, b, c) / (marginalTriple_FstThd P (a, c) * ω c b)) 
               ≤ C * Real.log 2) :
    condMutualInfo P ≤ C := by
  -- 1. Relate condMutualInfo to the natural-log sum
  have h_cmi_scale : condMutualInfo P * Real.log 2 = 
      ∑ a, ∑ b, ∑ c, P.pmf (a, b, c) * Real.log (P.pmf (a, b, c) * marginalTriple_Thd P c / (marginalTriple_FstThd P (a, c) * marginalTriple_SndThd P (b, c))) := by
    rw [← condMutualInfo_kl_identity P]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro a _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro c _
    unfold condProductMass
    field_simp

  -- 2. Variational Identity (Topsoe)
  -- Σ P(a,b,c) log(P_bc / (P_c * ω)) = Σ_c P_c * KL(P(b|c) || ω(b|c)) ≥ 0
  have h_diff_nonneg : 0 ≤ 
      (∑ a, ∑ b, ∑ c, P.pmf (a, b, c) * Real.log (P.pmf (a, b, c) / (marginalTriple_FstThd P (a, c) * ω c b))) - 
      (∑ a, ∑ b, ∑ c, P.pmf (a, b, c) * Real.log (P.pmf (a, b, c) * marginalTriple_Thd P c / (marginalTriple_FstThd P (a, c) * marginalTriple_SndThd P (b, c)))) := by
    simp_rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub]
    have h_inner : ∀ a b c,
        P.pmf (a, b, c) *
          (Real.log (P.pmf (a, b, c) / (marginalTriple_FstThd P (a, c) * ω c b)) -
            Real.log (P.pmf (a, b, c) * marginalTriple_Thd P c /
              (marginalTriple_FstThd P (a, c) * marginalTriple_SndThd P (b, c)))) =
        P.pmf (a, b, c) *
          Real.log (marginalTriple_SndThd P (b, c) / (marginalTriple_Thd P c * ω c b)) := by
      intro a b c
      by_cases h_abc : P.pmf (a, b, c) = 0
      · simp [h_abc]
      · have hp_pos : 0 < P.pmf (a, b, c) := lt_of_le_of_ne (P.pmf_nonneg _) (Ne.symm h_abc)
        have h_ac_pos : 0 < marginalTriple_FstThd P (a, c) := lt_of_lt_of_le hp_pos (pmf_le_marginalTriple_FstThd P a b c)
        have h_bc_pos : 0 < marginalTriple_SndThd P (b, c) := lt_of_lt_of_le hp_pos (pmf_le_marginalTriple_SndThd P a b c)
        have h_c_pos : 0 < marginalTriple_Thd P c := lt_of_lt_of_le h_ac_pos (marginalTriple_FstThd_le_marginalTriple_Thd P a c)
        have h_w_pos : 0 < ω c b := h_ω_pos c b
        have hlog :
            Real.log (P.pmf (a, b, c) / (marginalTriple_FstThd P (a, c) * ω c b)) -
                Real.log (P.pmf (a, b, c) * marginalTriple_Thd P c /
                  (marginalTriple_FstThd P (a, c) * marginalTriple_SndThd P (b, c))) =
              Real.log (marginalTriple_SndThd P (b, c) / (marginalTriple_Thd P c * ω c b)) := by
          have h₁ :
              Real.log (P.pmf (a, b, c) / (marginalTriple_FstThd P (a, c) * ω c b)) =
                Real.log (P.pmf (a, b, c)) -
                  (Real.log (marginalTriple_FstThd P (a, c)) + Real.log (ω c b)) := by
            rw [Real.log_div hp_pos.ne' (mul_pos h_ac_pos h_w_pos).ne',
              Real.log_mul h_ac_pos.ne' h_w_pos.ne']
          have h₂ :
              Real.log (P.pmf (a, b, c) * marginalTriple_Thd P c /
                  (marginalTriple_FstThd P (a, c) * marginalTriple_SndThd P (b, c))) =
                (Real.log (P.pmf (a, b, c)) + Real.log (marginalTriple_Thd P c)) -
                  (Real.log (marginalTriple_FstThd P (a, c)) +
                    Real.log (marginalTriple_SndThd P (b, c))) := by
            rw [Real.log_div (mul_pos hp_pos h_c_pos).ne' (mul_pos h_ac_pos h_bc_pos).ne',
              Real.log_mul hp_pos.ne' h_c_pos.ne',
              Real.log_mul h_ac_pos.ne' h_bc_pos.ne']
          have h₃ :
              Real.log (marginalTriple_SndThd P (b, c) / (marginalTriple_Thd P c * ω c b)) =
                Real.log (marginalTriple_SndThd P (b, c)) -
                  (Real.log (marginalTriple_Thd P c) + Real.log (ω c b)) := by
            rw [Real.log_div h_bc_pos.ne' (mul_pos h_c_pos h_w_pos).ne',
              Real.log_mul h_c_pos.ne' h_w_pos.ne']
          rw [h₁, h₂, h₃]
          ring
        rw [hlog]
    simp_rw [h_inner]
    rw [← marginalTriple_SndThd_pullback P
      (fun yz : β × γ =>
        Real.log (marginalTriple_SndThd P yz / (marginalTriple_Thd P yz.2 * ω yz.2 yz.1)))]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_nonneg; intro c _
    by_cases hc : marginalTriple_Thd P c = 0
    · have h_bc_zero : ∀ b, marginalTriple_SndThd P (b, c) = 0 := by
        intro b
        have hle : marginalTriple_SndThd P (b, c) ≤ ∑ b, marginalTriple_SndThd P (b, c) :=
          Finset.single_le_sum (fun b _ => marginalTriple_SndThd_nonneg P (b, c)) (Finset.mem_univ b)
        rw [marginalTriple_SndThd_sum_thd P c, hc] at hle
        exact le_antisymm hle (marginalTriple_SndThd_nonneg P (b, c))
      simp [h_bc_zero]
    · have hc_pos : 0 < marginalTriple_Thd P c := lt_of_le_of_ne (marginalTriple_Thd_nonneg P c) (Ne.symm hc)
      let p := fun b => marginalTriple_SndThd P (b, c) / marginalTriple_Thd P c
      let q := fun b => ω c b
      have h_kl_nonneg := klDivergence_nonneg p q ?_ ?_ ?_ ?_ ?_
      · have h_sum_eq :
            (∑ b, marginalTriple_SndThd P (b, c) *
              Real.log (marginalTriple_SndThd P (b, c) /
                (marginalTriple_Thd P c * ω c b))) =
            marginalTriple_Thd P c * klDivergence p q := by
          unfold klDivergence p q
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro b _
          by_cases hbc : marginalTriple_SndThd P (b, c) = 0
          · simp [hbc]
          · have hbc_pos : 0 < marginalTriple_SndThd P (b, c) :=
              lt_of_le_of_ne (marginalTriple_SndThd_nonneg P (b, c)) (Ne.symm hbc)
            have hw_pos : 0 < ω c b := h_ω_pos c b
            have harg :
                (marginalTriple_SndThd P (b, c) / marginalTriple_Thd P c) / ω c b =
                  marginalTriple_SndThd P (b, c) / (marginalTriple_Thd P c * ω c b) := by
              field_simp [hc, hw_pos.ne']
            rw [harg]
            field_simp [hc]
        rw [h_sum_eq]
        exact mul_nonneg hc_pos.le h_kl_nonneg
      · intro b; exact div_nonneg (marginalTriple_SndThd_nonneg P (b, c)) hc_pos.le
      · intro b; exact le_of_lt (h_ω_pos c b)
      · intro b h_p_ne_zero; exact h_ω_pos c b
      · unfold p
        rw [← Finset.sum_div, marginalTriple_SndThd_sum_thd P c]
        field_simp [hc]
      · exact h_ω_sum c

  -- 3. Combine
  have h_scaled_bound : condMutualInfo P * Real.log 2 ≤ C * Real.log 2 := by
    rw [h_cmi_scale]
    linarith [h_diff_nonneg, h_bound]
  
  -- 4. Final bit-valued bound
  have h_log2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  exact le_of_mul_le_mul_right h_scaled_bound h_log2_pos

end

end CausalQIF.InformationFlow
