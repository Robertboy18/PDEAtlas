/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.FirstVariation.CompactDomain

/-!
# Matrix and value coordinates of the first variation

The full differential of `L(P,z,x)` is evaluated on variations with zero spatial
component. Freezing the other arguments gives the matrix and value derivatives,
and the standard finite bases expand their action into scalar coordinates.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Elementwise

namespace PDE.CalculusOfVariations

variable {n m : ℕ}
  {L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ}
  {P : Matrix (Fin m) (Fin n) ℝ} {z : ℝ^m} {x : ℝ^n}

/-- Freezing value and position restricts the full differential to matrix directions. -/
theorem fderiv_lagrangian_matrix_apply
    (hL : DifferentiableAt ℝ
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      (P, (z, x))) (Q : Matrix (Fin m) (Fin n) ℝ) :
    fderiv ℝ (fun A ↦ L A z x) P Q =
      fderiv ℝ (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦
        L a.1 a.2.1 a.2.2) (P, (z, x)) (Q, (0, 0)) := by
  have hp := hL.hasFDerivAt.comp P (hasFDerivAt_prodMk_left (𝕜 := ℝ) P (z, x))
  exact congrArg (fun A ↦ A Q) hp.fderiv

/-- Freezing matrix and position restricts the full differential to value directions. -/
theorem fderiv_lagrangian_value_apply
    (hL : DifferentiableAt ℝ
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      (P, (z, x))) (w : ℝ^m) :
    fderiv ℝ (fun y ↦ L P y x) z w =
      fderiv ℝ (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦
        L a.1 a.2.1 a.2.2) (P, (z, x)) (0, (w, 0)) := by
  have hz := hL.hasFDerivAt.comp z
    ((hasFDerivAt_const P z).prodMk (hasFDerivAt_prodMk_left (𝕜 := ℝ) z x))
  exact congrArg (fun A ↦ A w) hz.fderiv

/-- The full density differential in a matrix/value direction is the sum of the
frozen-variable derivatives paired with the entries of that direction. -/
theorem fderiv_lagrangian_apply_matrix_value
    (hL : DifferentiableAt ℝ
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      (P, (z, x))) (Q : Matrix (Fin m) (Fin n) ℝ) (w : ℝ^m) :
    fderiv ℝ (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦
      L a.1 a.2.1 a.2.2) (P, (z, x)) (Q, (w, 0)) =
        (∑ k, ∑ i, Q k i * fderiv ℝ (fun A ↦ L A z x) P (Matrix.single k i 1)) +
        ∑ k, w k * fderiv ℝ (fun y ↦ L P y x) z (EuclideanSpace.single k 1) := by
  have hsplit :
      fderiv ℝ (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦
        L a.1 a.2.1 a.2.2) (P, (z, x)) (Q, (w, 0)) =
      fderiv ℝ (fun A ↦ L A z x) P Q + fderiv ℝ (fun y ↦ L P y x) z w := by
    rw [fderiv_lagrangian_matrix_apply hL, fderiv_lagrangian_value_apply hL]
    rw [← map_add]
    simp
  rw [hsplit]
  congr 1
  · nth_rw 1 [Matrix.matrix_eq_sum_single Q]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    have heq : Matrix.single k i (Q k i) = Q k i • Matrix.single k i (1 : ℝ) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [heq, map_smul, smul_eq_mul]
  · nth_rw 1 [← (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr w]
    simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply, smul_eq_mul]

end PDE.CalculusOfVariations
