import CausalQIF.Probability.FinitePMF

open Finset
open scoped BigOperators Real

namespace CausalQIF.Probability

noncomputable section

variable {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]

/-! ## KL-Divergence and Nonnegativity Foundations -/

lemma kl_nonneg_support {ι : Type} [Fintype ι] [DecidableEq ι]
    (p q : ι → ℝ)
    (hp_nonneg : ∀ x, 0 ≤ p x)
    (hq_nonneg : ∀ x, 0 ≤ q x)
    (h_support : ∀ x, p x ≠ 0 → 0 < q x)
    (hp_sum : ∑ x, p x = 1)
    (hq_sum : ∑ x, q x = 1) :
    0 ≤ ∑ x, p x * Real.log (p x / q x) := by
  have h_term : ∀ x, p x * Real.log (p x / q x) ≥ p x - q x := by
    intro x
    by_cases hpx : p x = 0
    · rw [hpx]
      have h0 : (0 : ℝ) / q x = 0 := by simp
      simp [h0]
      linarith [hq_nonneg x]
    · have hpx_pos : 0 < p x := lt_of_le_of_ne (hp_nonneg x) (Ne.symm hpx)
      have hqx_pos : 0 < q x := h_support x hpx
      have h1 : Real.log (q x / p x) ≤ q x / p x - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hqx_pos hpx_pos)
      have h2 : p x * Real.log (q x / p x) ≤ q x - p x := by
        have h_mul : p x * (q x / p x - 1) = q x - p x := by
          field_simp [hpx_pos.ne']
        have h3 : p x * Real.log (q x / p x) ≤ p x * (q x / p x - 1) := by
          apply mul_le_mul_of_nonneg_left h1 (le_of_lt hpx_pos)
        linarith [h3, h_mul]
      have h3 : p x * Real.log (p x / q x) = -(p x * Real.log (q x / p x)) := by
        rw [← mul_neg]
        congr
        rw [show Real.log (p x / q x) = -Real.log (q x / p x) by
          rw [Real.log_div (by exact hpx_pos.ne') (by exact hqx_pos.ne')]
          rw [Real.log_div (by exact hqx_pos.ne') (by exact hpx_pos.ne')]
          ring]
      rw [h3]
      linarith [h2]
  have hsum : ∑ x, p x * Real.log (p x / q x) ≥ ∑ x, (p x - q x) := by
    apply Finset.sum_le_sum
    intro x _
    exact h_term x
  have h_eq : ∑ x, (p x - q x) = 0 := by
    rw [Finset.sum_sub_distrib]
    linarith [hp_sum, hq_sum]
  linarith [hsum, h_eq]

def klDivergence {ι : Type} [Fintype ι] (p q : ι → ℝ) : ℝ :=
  ∑ x, p x * Real.log (p x / q x)

lemma klDivergence_nonneg
    {ι : Type} [Fintype ι] [DecidableEq ι] (p q : ι → ℝ)
    (hp_nonneg : ∀ x, 0 ≤ p x)
    (hq_nonneg : ∀ x, 0 ≤ q x)
    (h_support : ∀ x, p x ≠ 0 → 0 < q x)
    (hp_sum_one : ∑ x, p x = 1)
    (hq_sum_one : ∑ x, q x = 1) :
    0 ≤ klDivergence p q :=
  kl_nonneg_support p q hp_nonneg hq_nonneg h_support hp_sum_one hq_sum_one

/--
The generalized Pythagorean theorem for KL divergence.

If p, m, q are distributions (or positive functions) such that
the inner product (p - m, log (m / q)) vanishes, then
KL(p || q) = KL(p || m) + KL(m || q).
This formalizes the orthogonal m-projection argument from Layer 3
of information geometry without requiring continuous-time dynamics.
-/
lemma kl_pythagorean {ι : Type} [Fintype ι] [DecidableEq ι]
    (p m q : ι → ℝ)
    (hp_pos : ∀ x, p x ≠ 0 → 0 < p x)
    (hm_pos : ∀ x, 0 < m x)
    (hq_pos : ∀ x, 0 < q x)
    (h_ortho : ∑ x, (p x - m x) * Real.log (m x / q x) = 0) :
    klDivergence p q = klDivergence p m + klDivergence m q := by
  unfold klDivergence
  have h1 : ∑ x, p x * Real.log (p x / q x) = ∑ x, (p x * Real.log (p x / m x) + p x * Real.log (m x / q x)) := by
    apply sum_congr rfl
    intro x _
    by_cases hpx : p x = 0
    · simp [hpx]
    · have hpx_gt : 0 < p x := hp_pos x hpx
      have hmx_gt : 0 < m x := hm_pos x
      have hqx_gt : 0 < q x := hq_pos x
      have hlog : Real.log (p x / q x) = Real.log (p x / m x) + Real.log (m x / q x) := by
        rw [Real.log_div hpx_gt.ne' hqx_gt.ne', Real.log_div hpx_gt.ne' hmx_gt.ne', Real.log_div hmx_gt.ne' hqx_gt.ne']
        ring
      rw [hlog]
      ring
  rw [h1, sum_add_distrib]
  have h2 : ∑ x, p x * Real.log (m x / q x) = ∑ x, m x * Real.log (m x / q x) := by
    have h3 : ∑ x, (p x - m x) * Real.log (m x / q x) = 0 := h_ortho
    have h4 : ∑ x, (p x * Real.log (m x / q x) - m x * Real.log (m x / q x)) = 0 := by
      calc ∑ x, (p x * Real.log (m x / q x) - m x * Real.log (m x / q x))
        _ = ∑ x, (p x - m x) * Real.log (m x / q x) := by
          apply sum_congr rfl
          intro x _
          ring
        _ = 0 := h3
    rw [sum_sub_distrib] at h4
    linarith
  linarith

end

end CausalQIF.Probability
