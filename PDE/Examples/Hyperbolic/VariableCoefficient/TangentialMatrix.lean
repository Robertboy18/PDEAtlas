/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Classical.VariableCoefficient.FinitePropagation
import PDE.FDeriv.Euclidean.Laplacian
import CAS.ExactTactic
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# A nonconstant matrix with a proper radial eikonal function

In two dimensions, `A(x) = I + (x₂, -x₁) ⊗ (x₂, -x₁)` is smooth and
uniformly elliptic with lower constant one. It is nonconstant and unbounded.
Its extra quadratic term acts tangentially, so `q(x) = ‖x‖` solves the exact
matrix eikonal equation and has compact sublevels. The theorem
`finite_propagation_eikonal_cone` then gives finite propagation in the cones
`‖x‖ < T - t` (`finite_propagation`).
-/

@[expose] public noncomputable section

namespace PDE.Examples.Hyperbolic.VariableCoefficient.TangentialMatrix

open WaveEquation.VariableCoefficient

open Set PDE.Common PDE.Analysis

/-- The identity plus a nonconstant positive tangential rank-one matrix. -/
def principalMatrix (x : ℝ^2) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 + (x 1) ^ 2, -x 0 * x 1; -x 0 * x 1, 1 + (x 0) ^ 2]

/-- Each entry is `C¹`. -/
theorem contDiff_principalMatrix (i j : Fin 2) :
    ContDiff ℝ 1 (fun x ↦ principalMatrix x i j) := by
  fin_cases i <;> fin_cases j <;> dsimp [principalMatrix] <;> fun_prop

/-- The example matrix is symmetric at every point. -/
theorem principalMatrix_symmetric (x : ℝ^2) (i j : Fin 2) :
    principalMatrix x i j = principalMatrix x j i := by
  fin_cases i <;> fin_cases j <;> rfl

/-- The quadratic form is the Euclidean energy plus the square of a tangential component. -/
theorem principalMatrix_quadratic (x v : ℝ^2) :
    (∑ i, ∑ j, principalMatrix x i j * v i * v j) =
      ‖v‖ ^ 2 + (x 1 * v 0 - x 0 * v 1) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two, principalMatrix]
  cas

/-- The matrix is elliptic with constant `1`. -/
theorem principalMatrix_elliptic (x v : ℝ^2) :
    1 * ‖v‖ ^ 2 ≤ ∑ i, ∑ j, principalMatrix x i j * v i * v j := by
  rw [principalMatrix_quadratic, one_mul]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- The matrix values at zero and a coordinate unit vector differ. -/
theorem principalMatrix_nonconstant :
    principalMatrix (EuclideanSpace.single 1 1) ≠ principalMatrix 0 := by
  intro h
  have hh := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ ↦ A 0 0) h
  norm_num [principalMatrix] at hh

/-- The Euclidean radius solves the eikonal equation for this variable matrix. -/
theorem principalMatrix_eikonal (x : ℝ^2) (hx : x ≠ 0) :
    (∑ i, ∑ j, principalMatrix x i j *
      (∂[i] (norm : ℝ^2 → ℝ)) x * (∂[j] (norm : ℝ^2 → ℝ)) x) = 1 := by
  simp_rw [EuclideanLaplacian.partialDeriv_norm_of_ne_zero _]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have halgebra (X Y N : ℝ) (hN : N ≠ 0) :
      (1 + Y ^ 2) * (X / N) * (X / N) +
        (-X * Y) * (X / N) * (Y / N) +
        ((-X * Y) * (Y / N) * (X / N) +
          (1 + X ^ 2) * (Y / N) * (Y / N)) =
        (X ^ 2 + Y ^ 2) / N ^ 2 := by
    cas using hN
  simp only [Fin.sum_univ_two, principalMatrix]
  change (1 + (x 1) ^ 2) * (x 0 / ‖x‖) * (x 0 / ‖x‖) +
    (-x 0 * x 1) * (x 0 / ‖x‖) * (x 1 / ‖x‖) +
    ((-x 0 * x 1) * (x 1 / ‖x‖) * (x 0 / ‖x‖) +
      (1 + (x 0) ^ 2) * (x 1 / ‖x‖) * (x 1 / ‖x‖)) = 1
  rw [halgebra _ _ _ hn]
  have hs : (x 0) ^ 2 + (x 1) ^ 2 = ‖x‖ ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  rw [hs, div_self (pow_ne_zero 2 hn)]

/-- Every radius sublevel is a compact Euclidean ball. -/
theorem isCompact_radius_sublevel (r : ℝ) :
    IsCompact {x : ℝ^2 | ‖x‖ ≤ r} := by
  simpa [Metric.closedBall, dist_zero_right] using isCompact_closedBall (0 : ℝ^2) r

/-- A solution with zero data on `‖x‖ < T` vanishes in the cone `‖x‖ < T - t` and at
`(T, 0)`. -/
theorem finite_propagation {T : ℝ} (hT : 0 < T) {u : ℝ^(2 + 1) → ℝ}
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0})
    (hu₀ : ContDiffOn ℝ 1 u {p | 0 ≤ p 0})
    (hpde : ∀ t : ℝ, 0 < t → ∀ x, ‖x‖ < T - t →
      waveOperator principalMatrix u (timeSpaceCons t x) = 0)
    (hpos : ∀ x : ℝ^2, ‖x‖ < T → u (timeSpaceCons 0 x) = 0)
    (hvel : ∀ x : ℝ^2, ‖x‖ < T →
      derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = 0) :
    (∀ t ∈ Ico 0 T, ∀ x : ℝ^2, ‖x‖ < T - t → u (timeSpaceCons t x) = 0) ∧
      u (timeSpaceCons T (0 : ℝ^2)) = 0 :=
  finite_propagation_eikonal_cone contDiff_principalMatrix principalMatrix_symmetric
    zero_lt_one principalMatrix_elliptic continuous_norm (norm_zero)
    (fun _ hx ↦ norm_pos_iff.mpr hx) (fun _ hx ↦ contDiffAt_norm ℝ hx)
    principalMatrix_eikonal hT (fun r _ ↦ isCompact_radius_sublevel r) hu hu₀ hpde hpos hvel

end PDE.Examples.Hyperbolic.VariableCoefficient.TangentialMatrix
