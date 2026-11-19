/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.Viscosity.UniformEstimates
public import PDE.Hyperbolic.FirstOrder.Coefficients.Matrix
public import PDE.Analysis.Calculus.Trigonometric.LinearPhase
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# A spatially and temporally variable coupled symmetric field

The matrix has diagonal entries `sin x`, `-sin x` and off-diagonal
entries `cos(x+t)`. Every entry and its first two differentials are bounded by `4`
on every closed time slab. Two values of the matrix do not commute, so no fixed
orthogonal basis diagonalizes the whole family.
-/

@[expose] public noncomputable section

namespace PDE.Examples.Hyperbolic.Viscosity

open Set PDE.Common PDE.Analysis
open scoped Matrix

/-- A bounded, variable, coupled symmetric transport matrix in one spatial dimension. -/
def coupledMatrix (_j : Fin 1) (y : SpaceTime 1) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.sin (y 1), Real.cos (y 1 + y 0);
    Real.cos (y 1 + y 0), -Real.sin (y 1)]

/-- Every matrix entry is `C²`. -/
theorem coupledMatrix_contDiff (j : Fin 1) (p q : Fin 2) :
    ContDiff ℝ 2 (fun y ↦ coupledMatrix j y p q) := by
  fin_cases p <;> fin_cases q <;> dsimp [coupledMatrix] <;> fun_prop

/-- The matrix is symmetric at every spacetime point. -/
theorem coupledMatrix_isSymm (j : Fin 1) (y : SpaceTime 1) :
    (coupledMatrix j y).IsSymm := by
  ext p q
  fin_cases p <;> fin_cases q <;> rfl

/-- The coupled matrices define a symmetric first-order system on any domain. -/
theorem coupled_nativeSystem_isSymmetric (f : SpaceTime 1 → ℝ^2)
    (Ω : Set (SpaceTime 1)) :
    (PDE.Hyperbolic.FirstOrder.LinearFirstOrderSystem.ofMatrices
      coupledMatrix f Ω).IsSymmetric := by
  exact (PDE.Hyperbolic.FirstOrder.LinearFirstOrderSystem.ofMatrices_isSymmetric_iff
    coupledMatrix f Ω).mpr fun y _ j ↦ coupledMatrix_isSymm j y

/-- The first row of the operator is `∂ₜu₀ + sin x ∂ₓu₀ + cos(x + t) ∂ₓu₁`. -/
theorem coupled_nativeSystem_firstRow (f u : SpaceTime 1 → ℝ^2)
    (Ω : Set (SpaceTime 1)) (y : SpaceTime 1) :
    (PDE.Hyperbolic.FirstOrder.LinearFirstOrderSystem.ofMatrices
      coupledMatrix f Ω).operator u y 0 =
      (∂[0] u) y 0 +
        (Real.sin (y 1) * (∂[1] u) y 0 +
          Real.cos (y 1 + y 0) * (∂[1] u) y 1) := by
  rw [PDE.Hyperbolic.FirstOrder.LinearFirstOrderSystem.ofMatrices_operator_apply]
  simp [coupledMatrix, Fin.sum_univ_succ]

/-- Two spatial values do not commute, so one fixed orthogonal basis cannot
diagonalize the entire coefficient family. -/
theorem coupledMatrix_not_commute :
    ¬Commute (coupledMatrix 0 (timeSpaceCons 0 (0 : ℝ^1)))
      (coupledMatrix 0 (timeSpaceCons 0 (EuclideanSpace.single 0 (Real.pi / 2)))) := by
  intro h
  have heq := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ ↦ A 0 1) h.eq
  norm_num [coupledMatrix, Matrix.mul_apply, Fin.sum_univ_two, timeSpaceCons] at heq

/-- Coordinate functionals contract the Euclidean norm. -/
private theorem norm_coordinate_le (i : Fin 2) :
    ‖(EuclideanSpace.proj i : SpaceTime 1 →L[ℝ] ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro y
  simpa using PiLp.norm_apply_le y i

/-- Every entry and its differentials of order at most two are bounded by `4`. -/
theorem coupledMatrix_norm_iteratedFDeriv_le (j : Fin 1) (p q : Fin 2)
    (k : ℕ) (hk : k ≤ 2) (y : SpaceTime 1) :
    ‖iteratedFDeriv ℝ k (fun z ↦ coupledMatrix j z p q) y‖ ≤ 4 := by
  have hsin : ‖iteratedFDeriv ℝ k (fun z : SpaceTime 1 ↦ Real.sin (z 1)) y‖ ≤ 4 := by
    apply (norm_iteratedFDeriv_sin_linear_le (EuclideanSpace.proj 1) k y).trans
    have h := pow_le_pow_left₀ (norm_nonneg _) (norm_coordinate_le 1) k
    exact h.trans (by norm_num)
  have hcos :
      ‖iteratedFDeriv ℝ k (fun z : SpaceTime 1 ↦ Real.cos (z 1 + z 0)) y‖ ≤ 4 := by
    let L : SpaceTime 1 →L[ℝ] ℝ := EuclideanSpace.proj 1 + EuclideanSpace.proj 0
    have hL : ‖L‖ ≤ 2 :=
      (norm_add_le _ _).trans (by linarith [norm_coordinate_le 1, norm_coordinate_le 0])
    apply (norm_iteratedFDeriv_cos_linear_le L k y).trans
    apply (pow_le_pow_left₀ (norm_nonneg _) hL k).trans
    interval_cases k <;> norm_num
  fin_cases p <;> fin_cases q
  · exact hsin
  · exact hcos
  · exact hcos
  · change ‖iteratedFDeriv ℝ k (fun z : SpaceTime 1 ↦ -Real.sin (z 1)) y‖ ≤ 4
    rw [show (fun z : SpaceTime 1 ↦ -Real.sin (z 1)) =
      -(fun z : SpaceTime 1 ↦ Real.sin (z 1)) from rfl,
      iteratedFDeriv_neg_apply, norm_neg]
    exact hsin

/-- Every entry is bounded by `4`. -/
theorem coupledMatrix_norm_le (j : Fin 1) (p q : Fin 2) (y : SpaceTime 1) :
    ‖coupledMatrix j y p q‖ ≤ 4 := by
  simpa only [norm_iteratedFDeriv_zero] using
    coupledMatrix_norm_iteratedFDeriv_le j p q 0 (by norm_num) y

/-- On the slab `0 ≤ t ≤ T`, the first differential of every entry is bounded by `4`. -/
theorem coupledMatrix_norm_fderivWithin_le {T : ℝ} (hT : 0 < T)
    (j : Fin 1) (p q : Fin 2) (y : SpaceTime 1) (hy : y 0 ∈ Icc 0 T) :
    ‖fderivWithin ℝ (fun z ↦ coupledMatrix j z p q) {z | z 0 ∈ Icc 0 T} y‖ ≤ 4 := by
  rw [DifferentiableAt.fderivWithin
    ((coupledMatrix_contDiff j p q).differentiable (by norm_num) y)
    (uniqueDiffOn_closed_timeSlab hT y hy), ← norm_iteratedFDeriv_one]
  exact coupledMatrix_norm_iteratedFDeriv_le j p q 1 (by norm_num) y

/-- The full second differential within the same slab has the same uniform bound. -/
theorem coupledMatrix_norm_iteratedFDerivWithin_le {T : ℝ} (hT : 0 < T)
    (j : Fin 1) (p q : Fin 2) (y : SpaceTime 1) (hy : y 0 ∈ Icc 0 T) :
    ‖iteratedFDerivWithin ℝ 2 (fun z ↦ coupledMatrix j z p q)
      {z | z 0 ∈ Icc 0 T} y‖ ≤ 4 := by
  rw [iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_closed_timeSlab hT)
    (coupledMatrix_contDiff j p q).contDiffAt hy]
  exact coupledMatrix_norm_iteratedFDeriv_le j p q 2 le_rfl y

/-- The off-diagonal transport entry depends on time. -/
theorem coupledMatrix_offDiagonal_timeDerivative (y : SpaceTime 1) :
    (∂[(0 : Fin 2)] (fun z ↦ coupledMatrix 0 z 0 1)) y =
      -Real.sin (y 1 + y 0) := by
  change (∂[(0 : Fin 2)] (fun z : ℝ^2 ↦ Real.cos (z 1 + z 0))) y = _
  cas

/-- The diagonal transport entry depends on space. -/
theorem coupledMatrix_diagonal_spatialDerivative (y : SpaceTime 1) :
    (∂[(1 : Fin 2)] (fun z ↦ coupledMatrix 0 z 0 0)) y =
      Real.cos (y 1) := by
  change (∂[(1 : Fin 2)] (fun z : ℝ^2 ↦ Real.sin (z 1))) y = _
  cas

/-- The mixed derivative `∂ₓ∂ₜ cos(x + t) = -cos(x + t)`. -/
theorem coupledMatrix_offDiagonal_mixedDerivative (y : SpaceTime 1) :
    (∂[(1 : Fin 2)] (∂[(0 : Fin 2)]
      (fun z ↦ coupledMatrix 0 z 0 1))) y = -Real.cos (y 1 + y 0) := by
  rw [show ∂[(0 : Fin 2)] (fun z ↦ coupledMatrix 0 z 0 1) =
    (fun z ↦ -Real.sin (z 1 + z 0)) from funext coupledMatrix_offDiagonal_timeDerivative]
  cas

end PDE.Examples.Hyperbolic.Viscosity
