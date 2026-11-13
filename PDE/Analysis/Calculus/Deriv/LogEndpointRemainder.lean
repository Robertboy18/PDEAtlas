/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Deriv.EndpointRemainder
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import CAS.ExactTactic

/-!
# Endpoint remainders after removing a logarithmic derivative

A derivative of the form `K - α log (L - x)` has an explicit primitive
continuous at `L`. Subtracting it before estimating the remainder avoids
assuming that the original derivative stays bounded at the endpoint.

The first remainder is bounded by `E (L - x)`. Integrating once more retains
the factor `1/2`, giving `E (L - x)² / 2`. Both estimates use continuity at the
endpoint and derivatives only in the open interval.
-/

@[expose] public noncomputable section

open Set

namespace PDE.Analysis

/-- The primitive of `K - α log (L - x)` whose endpoint value is `A`. -/
def rightLogSlope (L A K α x : ℝ) : ℝ :=
  A - (L - x) * (K + α) + α * ((L - x) * Real.log (L - x))

/-- The primitive of `rightLogSlope` with value zero at the right endpoint. -/
def rightLogPrimitive (L A K α x : ℝ) : ℝ :=
  -(L - x) * A + (L - x) ^ 2 / 2 * (K + 3 * α / 2) -
    α / 2 * ((L - x) * ((L - x) * Real.log (L - x)))

/-- Multiplication by the endpoint distance removes the logarithmic singularity. -/
theorem continuous_rightLogSlope (L A K α : ℝ) :
    Continuous (rightLogSlope L A K α) := by
  unfold rightLogSlope
  exact (continuous_const.sub ((continuous_const.sub continuous_id).mul
    continuous_const)).add
      (continuous_const.mul (Real.continuous_mul_log.comp
        (continuous_const.sub continuous_id)))

/-- The second primitive is continuous through its endpoint as well. -/
theorem continuous_rightLogPrimitive (L A K α : ℝ) :
    Continuous (rightLogPrimitive L A K α) := by
  unfold rightLogPrimitive
  fun_prop

/-- The first primitive takes its prescribed endpoint value. -/
@[simp]
theorem rightLogSlope_self (L A K α : ℝ) : rightLogSlope L A K α L = A := by
  simp [rightLogSlope]

/-- The second primitive vanishes at the endpoint. -/
@[simp]
theorem rightLogPrimitive_self (L A K α : ℝ) :
    rightLogPrimitive L A K α L = 0 := by
  simp [rightLogPrimitive]

/-- Away from the endpoint, differentiation recovers the logarithmic term. -/
theorem hasDerivAt_rightLogSlope (L A K α : ℝ) {x : ℝ} (hx : x < L) :
    HasDerivAt (rightLogSlope L A K α) (K - α * Real.log (L - x)) x := by
  unfold rightLogSlope
  have hr : 0 < L - x := sub_pos.mpr hx
  cas using hr

/-- The second primitive differentiates to the first on the open left half-line. -/
theorem hasDerivAt_rightLogPrimitive (L A K α : ℝ) {x : ℝ} (hx : x < L) :
    HasDerivAt (rightLogPrimitive L A K α) (rightLogSlope L A K α x) x := by
  unfold rightLogPrimitive rightLogSlope
  have hr : 0 < L - x := sub_pos.mpr hx
  cas using hr

/-- Removing a logarithmic derivative leaves a linear endpoint remainder. -/
theorem abs_sub_rightLogSlope_le
    {u u' : ℝ → ℝ} {x L A K α E : ℝ} (hx : x ≤ L)
    (hu : ContinuousOn u (Icc x L)) (hvalue : u L = A)
    (hderiv : ∀ y ∈ Ioo x L, HasDerivAt u (u' y) y)
    (herror : ∀ y ∈ Ioo x L, |u' y - (K - α * Real.log (L - y))| ≤ E) :
    |u x - rightLogSlope L A K α x| ≤ E * (L - x) := by
  let v (y : ℝ) := u y - rightLogSlope L A K α y
  let v' (y : ℝ) := u' y - (K - α * Real.log (L - y))
  have hvc : ContinuousOn v (Icc x L) :=
    hu.sub (continuous_rightLogSlope L A K α).continuousOn
  have hvd (y : ℝ) (hy : y ∈ Ioo x L) : HasDerivAt v (v' y) y :=
    (hderiv y hy).sub (hasDerivAt_rightLogSlope L A K α hy.2)
  have hb (y : ℝ) (hy : y ∈ Ioo x L) : ‖v' y - 0‖ ≤ E * (L - y) ^ (0 : ℝ) := by
    simpa only [v', sub_zero, Real.norm_eq_abs, Real.rpow_zero, mul_one] using herror y hy
  have h := norm_sub_sub_smul_le_of_deriv_power_bound_right
    (m := (0 : ℝ)) (p := 0) hx (by norm_num) hvc hvd hb
  simpa only [v, rightLogSlope_self, hvalue, sub_self, sub_zero, smul_zero,
    Real.norm_eq_abs, zero_add, div_one, Real.rpow_one] using h

/-- A linearly vanishing slope error gives a quadratic remainder with the exact factor `1/2`. -/
theorem abs_sub_rightLogPrimitive_le
    {u u' : ℝ → ℝ} {x L A K α E : ℝ} (hx : x ≤ L)
    (hu : ContinuousOn u (Icc x L)) (hvalue : u L = 0)
    (hderiv : ∀ y ∈ Ioo x L, HasDerivAt u (u' y) y)
    (herror : ∀ y ∈ Ioo x L,
      |u' y - rightLogSlope L A K α y| ≤ E * (L - y)) :
    |u x - rightLogPrimitive L A K α x| ≤ E / 2 * (L - x) ^ 2 := by
  let v (y : ℝ) := u y - rightLogPrimitive L A K α y
  let v' (y : ℝ) := u' y - rightLogSlope L A K α y
  have hvc : ContinuousOn v (Icc x L) :=
    hu.sub (continuous_rightLogPrimitive L A K α).continuousOn
  have hvd (y : ℝ) (hy : y ∈ Ioo x L) : HasDerivAt v (v' y) y :=
    (hderiv y hy).sub (hasDerivAt_rightLogPrimitive L A K α hy.2)
  have hb (y : ℝ) (hy : y ∈ Ioo x L) : ‖v' y - 0‖ ≤ E * (L - y) ^ (1 : ℝ) := by
    simpa only [v', sub_zero, Real.norm_eq_abs, Real.rpow_one] using herror y hy
  have h := norm_sub_sub_smul_le_of_deriv_power_bound_right
    (m := (0 : ℝ)) (p := 1) hx (by norm_num) hvc hvd hb
  norm_num only [v, rightLogPrimitive_self, hvalue, sub_zero, smul_zero,
    Real.norm_eq_abs, Real.rpow_two] at h
  exact h

end PDE.Analysis
