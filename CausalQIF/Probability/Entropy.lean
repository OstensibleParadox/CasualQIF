import CausalQIF.Probability.FinitePMF

open Finset
open scoped BigOperators Real

namespace CausalQIF.Probability

noncomputable section

variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-! ## Conditional Mutual Information -/

def condMutualInfo (P : FinitePMF (α × β × γ)) : ℝ :=
  entropyOf (marginalXZMass P) + entropyOf (marginalYZMass P) -
  entropyOf (marginalZMass P) - entropy P

/-! ## Conditional Independence -/

def condIndep (P : FinitePMF (α × β × γ)) : Prop :=
  ∀ a b z,
    P.pmf (a, b, z) * marginalZMass P z =
      marginalXZMass P (a, z) * marginalYZMass P (b, z)

theorem condMutualInfo_eq_zero_of_condIndep (P : FinitePMF (α × β × γ))
    (hIndep : condIndep P) : condMutualInfo P = 0 := by
  have h_entropy_mul_log2 : condMutualInfo P * Real.log 2 =
      -(∑ xz : α × γ, marginalXZMass P xz * Real.log (marginalXZMass P xz))
      -(∑ yz : β × γ, marginalYZMass P yz * Real.log (marginalYZMass P yz))
      +(∑ z : γ, marginalZMass P z * Real.log (marginalZMass P z))
      +(∑ abc : α × β × γ, P.pmf abc * Real.log (P.pmf abc)) := by
    unfold condMutualInfo entropy
    have hXZ := entropyOf_mul_log2 (marginalXZMass P)
    have hYZ := entropyOf_mul_log2 (marginalYZMass P)
    have hZ  := entropyOf_mul_log2 (marginalZMass P)
    have hP  := entropyOf_mul_log2 (P.pmf)
    ring_nf
    rw [hXZ, hYZ, hZ, hP]
    ring
  have h_pull_XZ : ∑ xz : α × γ, marginalXZMass P xz * Real.log (marginalXZMass P xz) =
      ∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * Real.log (marginalXZMass P (a, c)) := by
    simpa using marginalXZMass_pullback P (fun xz => Real.log (marginalXZMass P xz))
  have h_pull_YZ : ∑ yz : β × γ, marginalYZMass P yz * Real.log (marginalYZMass P yz) =
      ∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * Real.log (marginalYZMass P (b, c)) := by
    simpa using marginalYZMass_pullback P (fun yz => Real.log (marginalYZMass P yz))
  have h_pull_Z : ∑ z : γ, marginalZMass P z * Real.log (marginalZMass P z) =
      ∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * Real.log (marginalZMass P c) := by
    simpa using marginalZMass_pullback P (fun z => Real.log (marginalZMass P z))
  have h_pull_P : ∑ abc : α × β × γ, P.pmf abc * Real.log (P.pmf abc) =
      ∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * Real.log (P.pmf (a, b, c)) := by
    simp [Fintype.sum_prod_type]
  rw [h_pull_XZ, h_pull_YZ, h_pull_Z, h_pull_P] at h_entropy_mul_log2
  have h_term_zero : ∀ a b c,
      P.pmf (a, b, c) * (Real.log (P.pmf (a, b, c)) + Real.log (marginalZMass P c)
      - Real.log (marginalXZMass P (a, c)) - Real.log (marginalYZMass P (b, c))) = 0 := by
    intro a b c
    by_cases hx : P.pmf (a, b, c) = 0
    · simp [hx]
    · have hp_pos : 0 < P.pmf (a, b, c) := lt_of_le_of_ne (P.pmf_nonneg _) (Ne.symm hx)
      have hXZ_pos : 0 < marginalXZMass P (a, c) := by
        unfold marginalXZMass
        have : P.pmf (a, b, c) ≤ ∑ b' : β, P.pmf (a, b', c) :=
          Finset.single_le_sum (fun b' _ => P.pmf_nonneg (a, b', c)) (Finset.mem_univ b)
        exact lt_of_lt_of_le hp_pos this
      have hYZ_pos : 0 < marginalYZMass P (b, c) := by
        unfold marginalYZMass
        have : P.pmf (a, b, c) ≤ ∑ a' : α, P.pmf (a', b, c) :=
          Finset.single_le_sum (fun a' _ => P.pmf_nonneg (a', b, c)) (Finset.mem_univ a)
        exact lt_of_lt_of_le hp_pos this
      have hZ_pos : 0 < marginalZMass P c := by
        unfold marginalZMass
        have h_single : P.pmf (a, b, c) ≤ ∑ a' : α, ∑ b' : β, P.pmf (a', b', c) :=
          calc
            P.pmf (a, b, c) ≤ ∑ b' : β, P.pmf (a, b', c) :=
              Finset.single_le_sum (fun b' _ => P.pmf_nonneg (a, b', c)) (Finset.mem_univ b)
            _ ≤ ∑ a' : α, ∑ b' : β, P.pmf (a', b', c) :=
              Finset.single_le_sum (fun a' _ =>
                Finset.sum_nonneg (fun b' _ => P.pmf_nonneg (a', b', c))) (Finset.mem_univ a)
        exact lt_of_lt_of_le hp_pos h_single
      have hIndep_eq := hIndep a b c
      have h_log_eq : Real.log (P.pmf (a, b, c)) + Real.log (marginalZMass P c) =
          Real.log (marginalXZMass P (a, c)) + Real.log (marginalYZMass P (b, c)) := by
        calc
          Real.log (P.pmf (a, b, c)) + Real.log (marginalZMass P c) =
              Real.log ((P.pmf (a, b, c)) * (marginalZMass P c)) := by
            rw [Real.log_mul (ne_of_gt hp_pos) (ne_of_gt hZ_pos)]
          _ = Real.log ((marginalXZMass P (a, c)) * (marginalYZMass P (b, c))) := by rw [hIndep_eq]
          _ = Real.log (marginalXZMass P (a, c)) + Real.log (marginalYZMass P (b, c)) := by
            rw [Real.log_mul (ne_of_gt hXZ_pos) (ne_of_gt hYZ_pos)]
      have h_inner_zero : Real.log (P.pmf (a, b, c)) + Real.log (marginalZMass P c)
          - Real.log (marginalXZMass P (a, c)) - Real.log (marginalYZMass P (b, c)) = 0 := by
        linarith [h_log_eq]
      simp [h_inner_zero]
  have h_term_zero_expanded : ∀ a b c,
      -(P.pmf (a, b, c) * Real.log (marginalXZMass P (a, c))) -
          P.pmf (a, b, c) * Real.log (marginalYZMass P (b, c)) +
        P.pmf (a, b, c) * Real.log (marginalZMass P c) +
          P.pmf (a, b, c) * Real.log (P.pmf (a, b, c)) = 0 := by
    intro a b c
    have h := h_term_zero a b c
    ring_nf at h ⊢
    exact h
  have h_rhs_zero :
      -∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * Real.log (marginalXZMass P (a, c)) -
            ∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * Real.log (marginalYZMass P (b, c)) +
          ∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * Real.log (marginalZMass P c) +
        ∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * Real.log (P.pmf (a, b, c)) = 0 := by
    calc
      -∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * Real.log (marginalXZMass P (a, c)) -
            ∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * Real.log (marginalYZMass P (b, c)) +
          ∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * Real.log (marginalZMass P c) +
        ∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * Real.log (P.pmf (a, b, c)) =
          ∑ a : α, ∑ b : β, ∑ c : γ,
            (-(P.pmf (a, b, c) * Real.log (marginalXZMass P (a, c))) -
                P.pmf (a, b, c) * Real.log (marginalYZMass P (b, c)) +
              P.pmf (a, b, c) * Real.log (marginalZMass P c) +
                P.pmf (a, b, c) * Real.log (P.pmf (a, b, c))) := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib]
      _ = 0 := by
        simp [h_term_zero_expanded]
  rw [h_rhs_zero] at h_entropy_mul_log2
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  rcases mul_eq_zero.mp h_entropy_mul_log2 with (h | h)
  · exact h
  · exfalso; linarith

end

end CausalQIF.Probability
