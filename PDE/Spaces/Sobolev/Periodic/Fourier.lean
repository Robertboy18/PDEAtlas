/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.PeriodicAveraging.Differentiation

/-!
# Fourier coefficients of periodic derivatives

Integration by parts against torus characters identifies the Fourier coefficients
of coordinate derivatives. All derivative hypotheses refer to the real coordinate
flows on Mathlib's unit torus.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter AddCircle UnitAddTorus
open PDE.Analysis.PeriodicAveraging
open scoped ENNReal Topology ComplexConjugate

namespace SobolevSpace.Periodic

/-- A torus character turns translation into multiplication. -/
theorem mFourier_apply_add {n : ℕ} (k : Fin n → ℤ)
    (x y : UnitAddTorus (Fin n)) :
    mFourier k (x + y) = mFourier k x * mFourier k y := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply,
    zsmul_add, toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

/-- Restricting a torus character to a coordinate gives a circle character. -/
theorem mFourier_coordinateShift {n : ℕ} (k : Fin n → ℤ) (i : Fin n) (t : ℝ) :
    mFourier k (coordinateShift i t) = fourier (k i) (t : UnitAddCircle) := by
  classical
  simp only [mFourier, ContinuousMap.coe_mk, coordinateShift]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

/-- The character `mFourier k` has derivative `2πi kᵢ mFourier k` along the `i`th coordinate
flow. -/
theorem hasDerivAt_mFourier_coordinate {n : ℕ} (k : Fin n → ℤ)
    (x : UnitAddTorus (Fin n)) (i : Fin n) (t : ℝ) :
    HasDerivAt (fun s ↦ mFourier k (x + coordinateShift i s))
      ((2 * Real.pi * Complex.I * k i) * mFourier k (x + coordinateShift i t)) t := by
  simp_rw [mFourier_apply_add, mFourier_coordinateShift]
  convert (hasDerivAt_fourier 1 (k i) t).const_mul (mFourier k x) using 1
  simp [mul_comm, mul_left_comm, mul_assoc]

/-- If `du` is the derivative of `u` along the `i`th coordinate flow, then
`mFourierCoeff du k = 2πi kᵢ mFourierCoeff u k` for every frequency `k`. -/
theorem mFourierCoeff_coordinate_derivative {n : ℕ}
    (u du : C(UnitAddTorus (Fin n), ℂ)) (i : Fin n)
    (hu : ∀ x t, HasDerivAt (fun s ↦ u (x + coordinateShift i s))
      (du (x + coordinateShift i t)) t) (k : Fin n → ℤ) :
    mFourierCoeff du k = (2 * Real.pi * Complex.I * k i) * mFourierCoeff u k := by
  let c : ℂ := 2 * Real.pi * Complex.I * k i
  have h := integral_mul_coordinate_derivative u du (mFourier (-k))
    ((-c) • mFourier (-k)) i hu (fun x t ↦ by
      simpa [c] using hasDerivAt_mFourier_coordinate (-k) x i t)
  change (∫ x, u x * (-c * mFourier (-k) x) ∂cellMeasure n) =
    -(∫ x, du x * mFourier (-k) x ∂cellMeasure n) at h
  simp_rw [mul_left_comm (u _), mul_comm (u _) (mFourier (-k) _)] at h
  rw [integral_const_mul] at h
  simp_rw [mul_comm (du _) (mFourier (-k) _)] at h
  change -c * mFourierCoeff u k = -mFourierCoeff du k at h
  exact (neg_injective (by simpa using h)).symm

end SobolevSpace.Periodic
