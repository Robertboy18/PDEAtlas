/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Classical.VariableCoefficient.DomainOfDependence
public import Mathlib.Analysis.SpecialFunctions.Arsinh
import PDE.FDeriv.Euclidean.Laplacian
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# A coupled matrix with quadratic radial growth

The matrix `(1 + ‖x‖²)I + (x₂, -x₁) ⊗ (x₂, -x₁)` has lower ellipticity
constant one and quadratic growth. Its eikonal radius is `arsinh ‖x‖`.
The general comparison theorem derives its logarithmic lower bound and compact
sublevels directly from the matrix bound.
For this matrix, arbitrary classical solutions with displacement `x₁` and right
velocity one agree with the wave `t + x₁` throughout the cone and at its vertex.
-/

@[expose] public noncomputable section

namespace PDE.Examples.Hyperbolic.VariableCoefficient.QuadraticGrowth

open WaveEquation.VariableCoefficient

open Set PDE.Common PDE.Analysis.Eikonal

/-- An unbounded symmetric matrix whose radial and tangential eigenvalues both grow. -/
def principalMatrix (x : ℝ^2) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 + (x 0) ^ 2 + 2 * (x 1) ^ 2, -x 0 * x 1;
    -x 0 * x 1, 1 + 2 * (x 0) ^ 2 + (x 1) ^ 2]

/-- Each entry is `C¹`. -/
theorem contDiff_principalMatrix (i j : Fin 2) :
    ContDiff ℝ 1 (fun x ↦ principalMatrix x i j) := by
  fin_cases i <;> fin_cases j <;> dsimp [principalMatrix] <;> fun_prop

/-- The matrix is symmetric everywhere. -/
theorem principalMatrix_symmetric (x : ℝ^2) (i j : Fin 2) :
    principalMatrix x i j = principalMatrix x j i := by
  fin_cases i <;> fin_cases j <;> rfl

/-- The quadratic form is `(1 + ‖x‖²)‖v‖² + (x₂v₁ - x₁v₂)²`. -/
theorem principalMatrix_quadratic (x v : ℝ^2) :
    (∑ i, ∑ j, principalMatrix x i j * v i * v j) =
      (1 + ‖x‖ ^ 2) * ‖v‖ ^ 2 + (x 1 * v 0 - x 0 * v 1) ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, principalMatrix]
  cas

/-- The matrix is elliptic with constant `1`. -/
theorem principalMatrix_elliptic (x v : ℝ^2) :
    1 * ‖v‖ ^ 2 ≤ ∑ i, ∑ j, principalMatrix x i j * v i * v j := by
  rw [principalMatrix_quadratic]
  nlinarith [sq_nonneg (x 1 * v 0 - x 0 * v 1),
    mul_nonneg (sq_nonneg ‖x‖) (sq_nonneg ‖v‖)]

/-- The upper quadratic growth bound has the fixed constant `C = 2`. -/
theorem principalMatrix_upper (x v : ℝ^2) :
    (∑ i, ∑ j, principalMatrix x i j * v i * v j) ≤
      (2 : ℝ) ^ 2 * (1 + ‖x - 0‖ ^ 2) * ‖v‖ ^ 2 := by
  have hid : ‖x‖ ^ 2 * ‖v‖ ^ 2 - (x 1 * v 0 - x 0 * v 1) ^ 2 =
      (x 0 * v 0 + x 1 * v 1) ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    cas
  rw [principalMatrix_quadratic, sub_zero]
  nlinarith [sq_nonneg (x 0 * v 0 + x 1 * v 1),
    mul_nonneg (sq_nonneg ‖x‖) (sq_nonneg ‖v‖), sq_nonneg ‖v‖]

/-- The matrix has a nonzero coupling entry. -/
theorem principalMatrix_coupled :
    principalMatrix !₂[1, 1] 0 1 = -1 := by
  norm_num [principalMatrix]

/-- The optical radius for this radial growth. -/
def opticalRadius (x : ℝ^2) : ℝ := Real.arsinh ‖x‖

/-- The optical radius is continuous. -/
theorem continuous_opticalRadius : Continuous opticalRadius :=
  Real.continuous_arsinh.comp continuous_norm

/-- The optical radius vanishes at the origin. -/
@[simp] theorem opticalRadius_zero : opticalRadius 0 = 0 := by
  simp [opticalRadius]

/-- It is positive at every other point. -/
theorem opticalRadius_pos (x : ℝ^2) (hx : x ≠ 0) : 0 < opticalRadius x :=
  Real.arsinh_pos_iff.mpr (norm_pos_iff.mpr hx)

/-- The radius is continuously differentiable off the origin. -/
theorem contDiffAt_opticalRadius (x : ℝ^2) (hx : x ≠ 0) :
    ContDiffAt ℝ 1 opticalRadius x :=
  Real.contDiff_arsinh.contDiffAt.comp x (contDiffAt_norm ℝ hx)

/-- `∂ᵢ arsinh ‖x‖ = (xᵢ / ‖x‖) / √(1 + ‖x‖²)` away from the origin. -/
theorem partialDeriv_opticalRadius (i : Fin 2) (x : ℝ^2) (hx : x ≠ 0) :
    (∂[i] opticalRadius) x =
      (x i / ‖x‖) * (Real.sqrt (1 + ‖x‖ ^ 2))⁻¹ := by
  unfold opticalRadius
  have hd : DifferentiableAt ℝ (norm : ℝ^2 → ℝ) x :=
    (contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 norm x).differentiableAt_one
  rw [partialDeriv_comp_real i (Real.differentiable_arsinh _)
    hd,
    EuclideanLaplacian.partialDeriv_norm_of_ne_zero _,
    (Real.hasDerivAt_arsinh _).deriv]

/-- The optical radius solves the matrix eikonal equation away from the origin. -/
theorem principalMatrix_eikonal (x : ℝ^2) (hx : x ≠ 0) :
    (∑ i, ∑ j, principalMatrix x i j *
      (∂[i] opticalRadius) x * (∂[j] opticalRadius) x) = 1 := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hp : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have hs : Real.sqrt (1 + ‖x‖ ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have halgebra (X Y N S : ℝ) (hN : N ≠ 0) (hS : S ≠ 0) :
      (1 + X ^ 2 + 2 * Y ^ 2) * (X / N * S⁻¹) * (X / N * S⁻¹) +
        (-X * Y) * (X / N * S⁻¹) * (Y / N * S⁻¹) +
        ((-X * Y) * (Y / N * S⁻¹) * (X / N * S⁻¹) +
          (1 + 2 * X ^ 2 + Y ^ 2) * (Y / N * S⁻¹) * (Y / N * S⁻¹)) =
        (1 + (X ^ 2 + Y ^ 2)) * (X ^ 2 + Y ^ 2) / (N ^ 2 * S ^ 2) := by
    cas
  simp only [partialDeriv_opticalRadius _ _ hx, Fin.sum_univ_two, principalMatrix]
  change (1 + (x 0) ^ 2 + 2 * (x 1) ^ 2) *
      (x 0 / ‖x‖ * (Real.sqrt (1 + ‖x‖ ^ 2))⁻¹) *
      (x 0 / ‖x‖ * (Real.sqrt (1 + ‖x‖ ^ 2))⁻¹) +
    (-x 0 * x 1) * (x 0 / ‖x‖ * (Real.sqrt (1 + ‖x‖ ^ 2))⁻¹) *
      (x 1 / ‖x‖ * (Real.sqrt (1 + ‖x‖ ^ 2))⁻¹) +
    ((-x 0 * x 1) * (x 1 / ‖x‖ * (Real.sqrt (1 + ‖x‖ ^ 2))⁻¹) *
      (x 0 / ‖x‖ * (Real.sqrt (1 + ‖x‖ ^ 2))⁻¹) +
    (1 + 2 * (x 0) ^ 2 + (x 1) ^ 2) *
      (x 1 / ‖x‖ * (Real.sqrt (1 + ‖x‖ ^ 2))⁻¹) *
      (x 1 / ‖x‖ * (Real.sqrt (1 + ‖x‖ ^ 2))⁻¹)) = 1
  rw [halgebra _ _ _ _ hn hs]
  have hnorm : (x 0) ^ 2 + (x 1) ^ 2 = ‖x‖ ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  rw [hnorm, Real.sq_sqrt hp.le, mul_comm (1 + ‖x‖ ^ 2),
    div_self (mul_ne_zero (pow_ne_zero 2 hn) hp.ne')]

/-- The matrix comparison theorem gives the logarithmic lower bound for this radius. -/
theorem log_lower_bound (x : ℝ^2) :
    Real.log (1 + ‖x‖ ^ 2) / 4 ≤ opticalRadius x := by
  have hh :=
    logarithmicRadius_le_of_matrix_eikonal (by norm_num : (0 : ℝ) < 2)
      principalMatrix_upper continuous_opticalRadius opticalRadius_zero opticalRadius_pos
      (fun y hy ↦ (contDiffAt_opticalRadius y hy).differentiableAt (by norm_num))
      principalMatrix_eikonal x
  norm_num [logarithmicRadius] at hh
  exact hh

/-- Every sublevel of the optical radius is compact. -/
theorem isCompact_opticalRadius_sublevel (r : ℝ) :
    IsCompact {x | opticalRadius x ≤ r} :=
  isCompact_sublevel_of_matrix_eikonal (by norm_num : (0 : ℝ) < 2)
    principalMatrix_upper continuous_opticalRadius opticalRadius_zero opticalRadius_pos
    (fun y hy ↦ (contDiffAt_opticalRadius y hy).differentiableAt (by norm_num))
    principalMatrix_eikonal r

/-- A nonstationary wave with nonzero displacement and velocity. -/
def affineWave (p : ℝ^3) : ℝ := p 0 + p 1

/-- The affine wave is `C^k` for every `k`. -/
theorem contDiff_affineWave (k : ℕ) : ContDiff ℝ k affineWave := by
  unfold affineWave
  fun_prop

/-- All second derivatives of the affine wave vanish. -/
theorem secondPartialDeriv_affineWave (i j : Fin 3) (p : ℝ^3) :
    (∂[i] (∂[j] affineWave)) p = 0 := by
  have hfirst (k : Fin 3) :
      ∂[k] affineWave = fun _ ↦ if k = 2 then (0 : ℝ) else 1 := by
    funext z
    fin_cases k <;> norm_num only [Fin.isValue, Fin.reduceEq, ↓reduceIte] <;>
      unfold affineWave <;> cas
  rw [hfirst]
  fin_cases i <;> fin_cases j <;>
    norm_num only [Fin.isValue, Fin.reduceEq, ↓reduceIte] <;> cas

/-- The affine wave solves the variable-coefficient wave equation. -/
theorem waveOperator_affineWave (p : ℝ^3) :
    waveOperator principalMatrix affineWave p = 0 := by
  simp [waveOperator, secondPartialDeriv_affineWave]

/-- The initial velocity of the affine wave is `1`. -/
theorem affineWave_initial_velocity (x : ℝ^2) :
    derivWithin (fun t ↦ affineWave (timeSpaceCons t x)) (Ici 0) 0 = 1 := by
  have hd : HasDerivAt (fun t ↦ affineWave (timeSpaceCons t x)) 1 0 := by
    change HasDerivAt (fun t ↦ t + x 0) 1 0
    cas
  exact hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 0 (by simp))

/-- Every classical solution with displacement `x₁` and velocity `1` on the base of the
cone `arsinh ‖x‖ < T - t` equals `t + x₁` in the cone and at its vertex. -/
theorem affineWave_unique {T : ℝ} (hT : 0 < T) {u : ℝ^3 → ℝ}
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0})
    (hu₀ : ContDiffOn ℝ 1 u {p | 0 ≤ p 0})
    (hpde : ∀ t : ℝ, 0 < t → ∀ x, opticalRadius x < T - t →
      waveOperator principalMatrix u (timeSpaceCons t x) = 0)
    (hpos : ∀ x, opticalRadius x < T → u (timeSpaceCons 0 x) = x 0)
    (hvel : ∀ x, opticalRadius x < T →
      derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = 1) :
    (∀ t ∈ Ico 0 T, ∀ x, opticalRadius x < T - t →
      u (timeSpaceCons t x) = t + x 0) ∧ u (timeSpaceCons T (0 : ℝ^2)) = T := by
  have h := eq_on_eikonal_cone_of_initial_eq_of_quadratic_growth
    contDiff_principalMatrix principalMatrix_symmetric zero_lt_one principalMatrix_elliptic
    (by norm_num : (0 : ℝ) < 2) principalMatrix_upper
    continuous_opticalRadius opticalRadius_zero opticalRadius_pos contDiffAt_opticalRadius
    principalMatrix_eikonal hT hu (contDiff_affineWave 2).contDiffOn
    hu₀ (contDiff_affineWave 1).contDiffOn hpde (fun _ _ _ _ ↦ waveOperator_affineWave _)
    (fun x hx ↦ by
      change u (timeSpaceCons 0 x) = 0 + x 0
      simpa using hpos x hx)
    (fun x hx ↦ (hvel x hx).trans (affineWave_initial_velocity x).symm)
  change (∀ t ∈ Ico 0 T, ∀ x, opticalRadius x < T - t →
    u (timeSpaceCons t x) = t + x 0) ∧ u (timeSpaceCons T (0 : ℝ^2)) = T + 0 at h
  simpa using h

end PDE.Examples.Hyperbolic.VariableCoefficient.QuadraticGrowth
