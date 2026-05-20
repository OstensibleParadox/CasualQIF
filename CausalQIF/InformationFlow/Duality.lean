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
    (h_bound : ∑ a, ∑ b, ∑ c, P.pmf (a, b, c) * Real.log (P.pmf (a, b, c) / (marginalTripleFstThd P (a, c) * ω c b)) 
               ≤ C * Real.log 2) :
    condMutualInfo P ≤ C := by
  -- 1. Relate condMutualInfo to the natural-log sum
  have h_cmi_scale : condMutualInfo P * Real.log 2 = 
      ∑ a, ∑ b, ∑ c, P.pmf (a, b, c) * Real.log (P.pmf (a, b, c) * marginalTripleThd P c / (marginalTripleFstThd P (a, c) * marginalTripleSndThd P (b, c))) := by
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
      (∑ a, ∑ b, ∑ c, P.pmf (a, b, c) * Real.log (P.pmf (a, b, c) / (marginalTripleFstThd P (a, c) * ω c b))) - 
      (∑ a, ∑ b, ∑ c, P.pmf (a, b, c) * Real.log (P.pmf (a, b, c) * marginalTripleThd P c / (marginalTripleFstThd P (a, c) * marginalTripleSndThd P (b, c)))) := by
    simp_rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub]
    have h_inner : ∀ a b c,
        P.pmf (a, b, c) *
          (Real.log (P.pmf (a, b, c) / (marginalTripleFstThd P (a, c) * ω c b)) -
            Real.log (P.pmf (a, b, c) * marginalTripleThd P c /
              (marginalTripleFstThd P (a, c) * marginalTripleSndThd P (b, c)))) =
        P.pmf (a, b, c) *
          Real.log (marginalTripleSndThd P (b, c) / (marginalTripleThd P c * ω c b)) := by
      intro a b c
      by_cases h_abc : P.pmf (a, b, c) = 0
      · simp [h_abc]
      · have hp_pos : 0 < P.pmf (a, b, c) := lt_of_le_of_ne (P.pmf_nonneg _) (Ne.symm h_abc)
        have h_ac_pos : 0 < marginalTripleFstThd P (a, c) := lt_of_lt_of_le hp_pos (pmf_le_marginalTripleFstThd P a b c)
        have h_bc_pos : 0 < marginalTripleSndThd P (b, c) := lt_of_lt_of_le hp_pos (pmf_le_marginalTripleSndThd P a b c)
        have h_c_pos : 0 < marginalTripleThd P c := lt_of_lt_of_le h_ac_pos (marginalTripleFstThd_le_marginalTripleThd P a c)
        have h_w_pos : 0 < ω c b := h_ω_pos c b
        have hlog :
            Real.log (P.pmf (a, b, c) / (marginalTripleFstThd P (a, c) * ω c b)) -
                Real.log (P.pmf (a, b, c) * marginalTripleThd P c /
                  (marginalTripleFstThd P (a, c) * marginalTripleSndThd P (b, c))) =
              Real.log (marginalTripleSndThd P (b, c) / (marginalTripleThd P c * ω c b)) := by
          have h₁ :
              Real.log (P.pmf (a, b, c) / (marginalTripleFstThd P (a, c) * ω c b)) =
                Real.log (P.pmf (a, b, c)) -
                  (Real.log (marginalTripleFstThd P (a, c)) + Real.log (ω c b)) := by
            rw [Real.log_div hp_pos.ne' (mul_pos h_ac_pos h_w_pos).ne',
              Real.log_mul h_ac_pos.ne' h_w_pos.ne']
          have h₂ :
              Real.log (P.pmf (a, b, c) * marginalTripleThd P c /
                  (marginalTripleFstThd P (a, c) * marginalTripleSndThd P (b, c))) =
                (Real.log (P.pmf (a, b, c)) + Real.log (marginalTripleThd P c)) -
                  (Real.log (marginalTripleFstThd P (a, c)) +
                    Real.log (marginalTripleSndThd P (b, c))) := by
            rw [Real.log_div (mul_pos hp_pos h_c_pos).ne' (mul_pos h_ac_pos h_bc_pos).ne',
              Real.log_mul hp_pos.ne' h_c_pos.ne',
              Real.log_mul h_ac_pos.ne' h_bc_pos.ne']
          have h₃ :
              Real.log (marginalTripleSndThd P (b, c) / (marginalTripleThd P c * ω c b)) =
                Real.log (marginalTripleSndThd P (b, c)) -
                  (Real.log (marginalTripleThd P c) + Real.log (ω c b)) := by
            rw [Real.log_div h_bc_pos.ne' (mul_pos h_c_pos h_w_pos).ne',
              Real.log_mul h_c_pos.ne' h_w_pos.ne']
          rw [h₁, h₂, h₃]
          ring
        rw [hlog]
    simp_rw [h_inner]
    rw [← marginalTripleSndThd_pullback P
      (fun yz : β × γ =>
        Real.log (marginalTripleSndThd P yz / (marginalTripleThd P yz.2 * ω yz.2 yz.1)))]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_nonneg; intro c _
    by_cases hc : marginalTripleThd P c = 0
    · have h_bc_zero : ∀ b, marginalTripleSndThd P (b, c) = 0 := by
        intro b
        have hle : marginalTripleSndThd P (b, c) ≤ ∑ b, marginalTripleSndThd P (b, c) :=
          Finset.single_le_sum (fun b _ => marginalTripleSndThd_nonneg P (b, c)) (Finset.mem_univ b)
        rw [marginalTripleSndThd_sum_thd P c, hc] at hle
        exact le_antisymm hle (marginalTripleSndThd_nonneg P (b, c))
      simp [h_bc_zero]
    · have hc_pos : 0 < marginalTripleThd P c := lt_of_le_of_ne (marginalTripleThd_nonneg P c) (Ne.symm hc)
      let p := fun b => marginalTripleSndThd P (b, c) / marginalTripleThd P c
      let q := fun b => ω c b
      have h_kl_nonneg := klDivergence_nonneg p q ?_ ?_ ?_ ?_ ?_
      · have h_sum_eq :
            (∑ b, marginalTripleSndThd P (b, c) *
              Real.log (marginalTripleSndThd P (b, c) /
                (marginalTripleThd P c * ω c b))) =
            marginalTripleThd P c * klDivergence p q := by
          unfold klDivergence p q
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro b _
          by_cases hbc : marginalTripleSndThd P (b, c) = 0
          · simp [hbc]
          · have hbc_pos : 0 < marginalTripleSndThd P (b, c) :=
              lt_of_le_of_ne (marginalTripleSndThd_nonneg P (b, c)) (Ne.symm hbc)
            have hw_pos : 0 < ω c b := h_ω_pos c b
            have harg :
                (marginalTripleSndThd P (b, c) / marginalTripleThd P c) / ω c b =
                  marginalTripleSndThd P (b, c) / (marginalTripleThd P c * ω c b) := by
              field_simp [hc, hw_pos.ne']
            rw [harg]
            field_simp [hc]
        rw [h_sum_eq]
        exact mul_nonneg hc_pos.le h_kl_nonneg
      · intro b; exact div_nonneg (marginalTripleSndThd_nonneg P (b, c)) hc_pos.le
      · intro b; exact le_of_lt (h_ω_pos c b)
      · intro b h_p_ne_zero; exact h_ω_pos c b
      · unfold p
        rw [← Finset.sum_div, marginalTripleSndThd_sum_thd P c]
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
