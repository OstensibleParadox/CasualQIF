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

/-- 
Unified distribution pushforward (map).
Given P : FinitePMF α and function f : α → β, constructs a distribution on β.
Conservation of mass guaranteed by Finset.sum_comm.
-/
def FinitePMF.map
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (P : FinitePMF α) (f : α → β) : FinitePMF β where
  pmf y := ∑ x : α, if f x = y then P.pmf x else 0
  pmf_nonneg y := by
    apply Finset.sum_nonneg
    intro x _
    by_cases h : f x = y
    · simp [h, P.pmf_nonneg x]
    · simp [h]
  sum_one := by
    calc
      ∑ y : β, ∑ x : α, (if f x = y then P.pmf x else 0)
          = ∑ x : α, ∑ y : β, (if f x = y then P.pmf x else 0) := by
            exact Finset.sum_comm
      _ = ∑ x : α, P.pmf x := by
        apply Finset.sum_congr rfl
        intro x _
        calc
          ∑ y : β, (if f x = y then P.pmf x else 0)
              = P.pmf x * ∑ y : β, (if f x = y then (1 : ℝ) else 0) := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro y _
                  by_cases h : f x = y
                  · simp [h]
                  · simp [h]
          _ = P.pmf x := by simp
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

lemma entropyOf_equiv_eq {η θ : Type} [Fintype η] [DecidableEq η] [Fintype θ]
    [DecidableEq θ] (e : η ≃ θ) (f : η → ℝ) (g : θ → ℝ)
    (h : ∀ x, f x = g (e x)) :
    entropyOf f = entropyOf g := by
  unfold entropyOf
  calc
    ∑ x : η, negMulLog2 (f x)
        = ∑ x : η, negMulLog2 (g (e x)) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [h x]
    _ = ∑ y : θ, negMulLog2 (g y) := Equiv.sum_comp e (fun y => negMulLog2 (g y))

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

def marginalPair_Fst (P : FinitePMF (α × β)) (x : α) : ℝ :=
  ∑ y : β, P.pmf (x, y)

def marginalPair_Snd (P : FinitePMF (α × β)) (y : β) : ℝ :=
  ∑ x : α, P.pmf (x, y)

lemma marginalPair_Fst_nonneg (P : FinitePMF (α × β)) (x : α) :
    0 ≤ marginalPair_Fst P x :=
  Finset.sum_nonneg (fun y _ => P.pmf_nonneg (x, y))

lemma marginalPair_Snd_nonneg (P : FinitePMF (α × β)) (y : β) :
    0 ≤ marginalPair_Snd P y :=
  Finset.sum_nonneg (fun x _ => P.pmf_nonneg (x, y))

lemma marginalPair_Fst_sum_one (P : FinitePMF (α × β)) :
    ∑ x : α, marginalPair_Fst P x = 1 := by
  unfold marginalPair_Fst
  rw [← Finset.sum_product]
  exact P.sum_one

lemma marginalPair_Snd_sum_one (P : FinitePMF (α × β)) :
    ∑ y : β, marginalPair_Snd P y = 1 := by
  unfold marginalPair_Snd
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

def marginalTriple_Thd (P : FinitePMF (α × β × γ)) (z : γ) : ℝ :=
  ∑ x : α, ∑ y : β, P.pmf (x, y, z)

def marginalTriple_FstThd (P : FinitePMF (α × β × γ)) (xz : α × γ) : ℝ :=
  ∑ y : β, P.pmf (xz.1, y, xz.2)

def marginalTriple_SndThd (P : FinitePMF (α × β × γ)) (yz : β × γ) : ℝ :=
  ∑ x : α, P.pmf (x, yz.1, yz.2)

lemma marginalTriple_FstThd_nonneg (P : FinitePMF (α × β × γ)) (xz : α × γ) :
    0 ≤ marginalTriple_FstThd P xz :=
  Finset.sum_nonneg (fun y _ => P.pmf_nonneg (xz.1, y, xz.2))

lemma marginalTriple_SndThd_nonneg (P : FinitePMF (α × β × γ)) (yz : β × γ) :
    0 ≤ marginalTriple_SndThd P yz :=
  Finset.sum_nonneg (fun x _ => P.pmf_nonneg (x, yz.1, yz.2))

lemma marginalTriple_Thd_nonneg (P : FinitePMF (α × β × γ)) (z : γ) :
    0 ≤ marginalTriple_Thd P z :=
  Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => P.pmf_nonneg (x, y, z)))

lemma marginalTriple_FstThd_sum_thd (P : FinitePMF (α × β × γ)) (z : γ) :
    ∑ x : α, marginalTriple_FstThd P (x, z) = marginalTriple_Thd P z := by
  rfl

lemma marginalTriple_SndThd_sum_thd (P : FinitePMF (α × β × γ)) (z : γ) :
    ∑ y : β, marginalTriple_SndThd P (y, z) = marginalTriple_Thd P z := by
  unfold marginalTriple_SndThd marginalTriple_Thd
  rw [Finset.sum_comm]

lemma marginalTriple_Thd_sum_one (P : FinitePMF (α × β × γ)) :
    ∑ z : γ, marginalTriple_Thd P z = 1 := by
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
  unfold marginalTriple_Thd
  rw [Finset.sum_comm]
  rw [show (∑ x : α, ∑ z : γ, ∑ y : β, P.pmf (x, y, z))
      = ∑ x : α, ∑ y : β, ∑ z : γ, P.pmf (x, y, z) by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_comm]]
  exact hsum

/-! ## Pullback Lemmas -/

lemma marginalTriple_FstThd_pullback (P : FinitePMF (α × β × γ)) (f : α × γ → ℝ) :
    ∑ xz : α × γ, marginalTriple_FstThd P xz * f xz =
    ∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * f (a, c) := by
  unfold marginalTriple_FstThd
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

lemma marginalTriple_SndThd_pullback (P : FinitePMF (α × β × γ)) (f : β × γ → ℝ) :
    ∑ yz : β × γ, marginalTriple_SndThd P yz * f yz =
    ∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * f (b, c) := by
  unfold marginalTriple_SndThd
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

lemma marginalTriple_Thd_pullback (P : FinitePMF (α × β × γ)) (f : γ → ℝ) :
    ∑ z : γ, marginalTriple_Thd P z * f z =
    ∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * f c := by
  unfold marginalTriple_Thd
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
