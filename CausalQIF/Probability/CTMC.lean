import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Matrix
open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A valid Continuous-Time Markov Chain (CTMC) generator matrix.
It satisfies two properties:
1. Off-diagonal elements are non-negative.
2. Each row sums to zero. -/
structure IsGenerator (Q : Matrix α α ℝ) : Prop where
  off_diag_nonneg : ∀ i j, i ≠ j → 0 ≤ Q i j
  row_sum_zero : ∀ i, ∑ j, Q i j = 0

/-- The Erbar-Maas logarithmic mean, which acts as the mobility
for the entropy gradient flow on finite CTMCs. -/
noncomputable def logMean (a b : ℝ) : ℝ :=
  if a = b then a else (a - b) / (Real.log a - Real.log b)

/-- A fast reset/restoring generator on the intervened coordinate `x_star`.
- If `x ≠ x_star`, it transitions to `x_star` with rate 1.
- If `x = x_star`, it is absorbing (rate 0 out).
Diagonal elements are chosen to make row sums zero. -/
def restoringGenerator (x_star : α) : Matrix α α ℝ :=
  fun i j =>
    if i = x_star then
      0
    else
      if j = x_star then 1
      else if i = j then -1
      else 0

/-- The intervened generator for Pearl surgery.
Constructed by adding a fast restoring generator to the original generator.
As `λ → ∞`, this forces the system to collapse onto the intervention face. -/
def Q_lambda (Q_do : Matrix α α ℝ) (x_star : α) (lambda : ℝ) : Matrix α α ℝ :=
  Q_do + lambda • restoringGenerator x_star

/-- The restoring generator is a valid CTMC generator. -/
lemma isGenerator_restoringGenerator (x_star : α) : IsGenerator (restoringGenerator x_star) := by
  constructor
  · intro i j hij
    dsimp [restoringGenerator]
    by_cases h1 : i = x_star
    · simp [h1]
    · by_cases h2 : j = x_star
      · simp [h1, h2]
      · by_cases h3 : i = j
        · exact False.elim (hij h3)
        · simp [h1, h2, h3]
  · intro i
    dsimp [restoringGenerator]
    split_ifs with h1
    · simp
    · have h_ne : i ≠ x_star := h1
      have H : ∑ j ∈ ({x_star, i} : Finset α), (if j = x_star then (1 : ℝ) else if i = j then -1 else 0) =
               ∑ j, (if j = x_star then (1 : ℝ) else if i = j then -1 else 0) := by
        apply sum_subset (subset_univ ({x_star, i} : Finset α))
        intro x _ hx
        simp at hx
        have hx1 : x ≠ x_star := hx.1
        have hx2 : x ≠ i := hx.2
        have hx2_symm : i ≠ x := hx2.symm
        simp [hx1, hx2_symm]
      rw [← H]
      rw [sum_pair h_ne.symm]
      simp [h_ne]

/-- The algebraic rate of change of KL divergence KL(p || π) along the direction p * Q.
This represents `(d/dt) D(T_t p_0 || π)` at `t = 0`. -/
noncomputable def klDerivative (Q : Matrix α α ℝ) (p π : α → ℝ) : ℝ :=
  ∑ i, (∑ j, p j * Q j i) * Real.log (p i / π i)

/-- The discrete Fisher information for a finite Markov chain. -/
noncomputable def discreteFisherInfo (Q : Matrix α α ℝ) (p π : α → ℝ) : ℝ :=
  - ∑ i, (∑ j, p j * Q j i) * Real.log (p i / π i)

/-- The de Bruijn identity for finite CTMCs.
Algebraically connects the time derivative of relative entropy to the discrete Fisher information.
`(d/dt) D(T_t p_0 || γ) = - I(p_t || γ)` -/
theorem deBruijn_identity {α : Type*} [Fintype α] (Q : Matrix α α ℝ) (p π : α → ℝ) :
  klDerivative Q p π = - discreteFisherInfo Q p π := by
  dsimp [klDerivative, discreteFisherInfo]
  ring
