/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2Moments
public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2Separable

/-!
# Coefficients of a table as values with indicator modes

With the modes replaced by the indicator of one mode in each variable (`indicatorModes`), the
value with replaced modes of a table is its coefficient of that mode
(`approxEval_indicatorModes`). Every identity for values with replaced modes, for instance one
built from the transforms of `TrigPoly2Multiplier`, therefore gives the coefficients of the
table, and the moments are the weighted sums of the absolute values with indicator modes
(`moment_eq_sum_abs_approxEval`). A block form (`moment_le_of_approxEval`) bounds the moments
of a table whose coefficients vanish outside one block of kinds by bounds of the coefficients in
the block.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.TrigPoly2

open Finset

variable {Mβ Mθ : ℕ} {R : Type} [Field R] [Algebra R ℝ]

/-- The indicator of the mode `(i₀, k₀)`. -/
def indicatorModes (i₀ : Fin 2) (k₀ : ℕ) : Fin 2 → ℕ → ℝ :=
  fun i k ↦ if i = i₀ ∧ k = k₀ then 1 else 0

theorem approxEval_indicatorModes (p : TrigPoly2 Mβ Mθ R) (i₀ j₀ : Fin 2) (k₀ : Fin (Mβ + 1))
    (l₀ : Fin (Mθ + 1)) :
    p.approxEval (indicatorModes i₀ k₀) (indicatorModes j₀ l₀) =
      algebraMap R ℝ (p.coeff i₀ j₀ k₀ l₀) := by
  unfold approxEval
  rw [Fintype.sum_eq_single i₀ fun i hi ↦ by simp [indicatorModes, hi],
    Fintype.sum_eq_single j₀ fun j hj ↦ by simp [indicatorModes, hj],
    Fintype.sum_eq_single k₀ fun k hk ↦ by simp [indicatorModes, Fin.val_inj, hk],
    Fintype.sum_eq_single l₀ fun l hl ↦ by simp [indicatorModes, Fin.val_inj, hl]]
  simp [indicatorModes]

/-- The moments as weighted sums of the values with indicator modes. -/
theorem moment_eq_sum_abs_approxEval (p : TrigPoly2 Mβ Mθ R) (a b : ℕ) :
    p.moment a b = ∑ i, ∑ j, ∑ k : Fin (Mβ + 1), ∑ l : Fin (Mθ + 1),
      |p.approxEval (indicatorModes i k) (indicatorModes j l)| * (k : ℝ) ^ a * (l : ℝ) ^ b := by
  simp only [moment, approxEval_indicatorModes]

/-- **Moments of a block.** If the values with indicator modes vanish outside the kinds
`(0, j₀)` and are bounded there by `G k l`, the moment is at most `∑ G k l k^a l^b`. -/
theorem moment_le_of_approxEval (p : TrigPoly2 Mβ Mθ R) (j₀ : Fin 2) (G : ℕ → ℕ → ℝ)
    (hp : ∀ i j (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)), ¬(i = 0 ∧ j = j₀) →
      p.approxEval (indicatorModes i k) (indicatorModes j l) = 0)
    (hG : ∀ (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)),
      |p.approxEval (indicatorModes 0 k) (indicatorModes j₀ l)| ≤ G k l) (a b : ℕ) :
    p.moment a b ≤
      ∑ k ∈ range (Mβ + 1), ∑ l ∈ range (Mθ + 1), G k l * (k : ℝ) ^ a * (l : ℝ) ^ b := by
  rw [moment_eq_sum_abs_approxEval,
    Fintype.sum_eq_single 0 fun i hi ↦ sum_eq_zero fun j _ ↦ sum_eq_zero fun k _ ↦
      sum_eq_zero fun l _ ↦ by rw [hp i j k l (by tauto)]; simp,
    Fintype.sum_eq_single j₀ fun j hj ↦ sum_eq_zero fun k _ ↦ sum_eq_zero fun l _ ↦ by
      rw [hp 0 j k l (by tauto)]; simp]
  rw [← Fin.sum_univ_eq_sum_range (fun k ↦ ∑ l ∈ range (Mθ + 1), G k l * (k : ℝ) ^ a * (l : ℝ) ^ b)]
  refine sum_le_sum fun k _ ↦ ?_
  rw [← Fin.sum_univ_eq_sum_range (fun l ↦ G k l * (k : ℝ) ^ a * (l : ℝ) ^ b)]
  exact sum_le_sum fun l _ ↦ mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hG k l)
    (by positivity)) (by positivity)

end PDE.Analysis.TrigPoly2
