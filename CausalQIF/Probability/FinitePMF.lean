import Mathlib

open Finset
open scoped BigOperators Real

namespace CausalQIF.Probability

noncomputable section

/-! # Finite Discrete Probability -/

variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

structure FinitePMF (α : Type) [Fintype α] [DecidableEq α] where
  pmf : α → ℝ
  pmf_nonneg : ∀ x, 0 ≤ pmf x
  sum_one : ∑ x : α, pmf x = 1

def FinitePMF.comapEquiv {η θ : Type} [Fintype η] [DecidableEq η] [Fintype θ]
    [DecidableEq θ] (e : θ ≃ η) (P : FinitePMF η) : FinitePMF θ where
  pmf x := P.pmf (e x)
  pmf_nonneg x := P.pmf_nonneg (e x)
  sum_one := by
    calc
      ∑ x : θ, P.pmf (e x) = ∑ y : η, P.pmf y := Equiv.sum_comp e P.pmf
      _ = 1 := P.sum_one

def negMulLog2 (p : ℝ) : ℝ :=
  -(p * (Real.log p / Real.log 2))

def entropyOf {η : Type} [Fintype η] [DecidableEq η] (mass : η → ℝ) : ℝ :=
  ∑ x : η, negMulLog2 (mass x)

def entropy (P : FinitePMF α) : ℝ :=
  entropyOf P.pmf

lemma negMulLog2_nonneg {p : ℝ} (hp_nonneg : 0 ≤ p) (hp_le_one : p ≤ 1) :
    0 ≤ negMulLog2 p := by
  unfold negMulLog2
  by_cases hp : p = 0
  · simp [hp]
  · have hp_pos : 0 < p := lt_of_le_of_ne hp_nonneg (Ne.symm hp)
    have hlog_le : Real.log p ≤ 0 :=
      (Real.log_le_sub_one_of_pos hp_pos).trans (by linarith : p - 1 ≤ 0)
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have h_div_le : Real.log p / Real.log 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hlog_le hlog2_pos.le
    have h_prod_le : p * (Real.log p / Real.log 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hp_nonneg h_div_le
    linarith

lemma pmf_le_one (P : FinitePMF α) (x : α) :
    P.pmf x ≤ 1 := by
  have h_nonneg : ∀ y, 0 ≤ P.pmf y := P.pmf_nonneg
  have : P.pmf x ≤ ∑ y : α, P.pmf y :=
    Finset.single_le_sum (fun y _ => h_nonneg y) (Finset.mem_univ x)
  linarith [P.sum_one]

lemma entropy_nonneg (P : FinitePMF α) :
    0 ≤ entropy P := by
  unfold entropy entropyOf
  exact Finset.sum_nonneg (fun x _ => negMulLog2_nonneg (P.pmf_nonneg x) (pmf_le_one P x))

lemma entropyOf_mul_log2 {η : Type} [Fintype η] [DecidableEq η] (mass : η → ℝ) :
    entropyOf mass * Real.log 2 = -∑ x : η, mass x * Real.log (mass x) := by
  unfold entropyOf negMulLog2
  have hlog2_ne_zero : Real.log 2 ≠ 0 := by positivity
  rw [Finset.sum_mul]
  calc
    ∑ x : η, (-(mass x * (Real.log (mass x) / Real.log 2))) * Real.log 2
        = ∑ x : η, -(mass x * Real.log (mass x)) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          field_simp [hlog2_ne_zero]
    _ = -∑ x : η, mass x * Real.log (mass x) := by rw [Finset.sum_neg_distrib]

/-! ## Marginals -/

def marginalLeftMass (P : FinitePMF (α × β)) (x : α) : ℝ :=
  ∑ y : β, P.pmf (x, y)

def marginalRightMass (P : FinitePMF (α × β)) (y : β) : ℝ :=
  ∑ x : α, P.pmf (x, y)

lemma marginalLeftMass_nonneg (P : FinitePMF (α × β)) (x : α) :
    0 ≤ marginalLeftMass P x :=
  Finset.sum_nonneg (fun y _ => P.pmf_nonneg (x, y))

lemma marginalRightMass_nonneg (P : FinitePMF (α × β)) (y : β) :
    0 ≤ marginalRightMass P y :=
  Finset.sum_nonneg (fun x _ => P.pmf_nonneg (x, y))

lemma marginalLeftMass_sum_one (P : FinitePMF (α × β)) :
    ∑ x : α, marginalLeftMass P x = 1 := by
  unfold marginalLeftMass
  rw [← Finset.sum_product]
  exact P.sum_one

lemma marginalRightMass_sum_one (P : FinitePMF (α × β)) :
    ∑ y : β, marginalRightMass P y = 1 := by
  unfold marginalRightMass
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

def marginalZMass (P : FinitePMF (α × β × γ)) (z : γ) : ℝ :=
  ∑ x : α, ∑ y : β, P.pmf (x, y, z)

def marginalXZMass (P : FinitePMF (α × β × γ)) (xz : α × γ) : ℝ :=
  ∑ y : β, P.pmf (xz.1, y, xz.2)

def marginalYZMass (P : FinitePMF (α × β × γ)) (yz : β × γ) : ℝ :=
  ∑ x : α, P.pmf (x, yz.1, yz.2)

/-! ## Pullback Lemmas -/

lemma marginalXZMass_pullback (P : FinitePMF (α × β × γ)) (f : α × γ → ℝ) :
    ∑ xz : α × γ, marginalXZMass P xz * f xz =
    ∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * f (a, c) := by
  unfold marginalXZMass
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

lemma marginalYZMass_pullback (P : FinitePMF (α × β × γ)) (f : β × γ → ℝ) :
    ∑ yz : β × γ, marginalYZMass P yz * f yz =
    ∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * f (b, c) := by
  unfold marginalYZMass
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

lemma marginalZMass_pullback (P : FinitePMF (α × β × γ)) (f : γ → ℝ) :
    ∑ z : γ, marginalZMass P z * f z =
    ∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * f c := by
  unfold marginalZMass
  calc
    ∑ c : γ, (∑ a : α, ∑ b : β, P.pmf (a, b, c)) * f c
        = ∑ c : γ, ∑ a : α, ∑ b : β, P.pmf (a, b, c) * f c := by
          refine Finset.sum_congr rfl (fun c _ => ?_)
          simp_rw [Finset.sum_mul]
    _ = ∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * f c := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_comm)

end

end CausalQIF.Probability
