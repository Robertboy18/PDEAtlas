/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Homogenization.PeriodicCell.GradientSpace
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.MeasureTheory.Function.Holder

/-!
# Bounded periodic elliptic coefficient fields

An `L∞` field of linear maps acts boundedly on vector-valued `L²` by Mathlib's
bilinear Hölder construction. Pointwise almost-everywhere ellipticity then gives
coercivity of the integral form, with the original constant. Symmetry is not needed.
-/

@[expose] public noncomputable section

open MeasureTheory Filter PDE.Analysis.PeriodicAveraging
open scoped ENNReal InnerProductSpace

namespace PDE.Elliptic.Homogenization.PeriodicCell

variable {n : ℕ} (A : Lp ((ℝ^n) →L[ℝ] (ℝ^n)) ∞ (cellMeasure n))

/-- Multiplication by the bounded periodic coefficient as an operator on `L²`. -/
def coefficientOperator : Lp (ℝ^n) 2 (cellMeasure n) →L[ℝ] Lp (ℝ^n) 2 (cellMeasure n) :=
  (ContinuousLinearMap.id ℝ ((ℝ^n) →L[ℝ] (ℝ^n))).holderL (cellMeasure n) ∞ 2 2 A

/-- The multiplier has the expected pointwise representative. -/
theorem coefficientOperator_ae (v : Lp (ℝ^n) 2 (cellMeasure n)) :
    coefficientOperator A v =ᵐ[cellMeasure n] fun x ↦ A x (v x) :=
  (ContinuousLinearMap.id ℝ ((ℝ^n) →L[ℝ] (ℝ^n))).coeFn_holder A v

/-- The bounded coefficient form on periodic vector fields. -/
def coefficientForm : Lp (ℝ^n) 2 (cellMeasure n) →L[ℝ]
    Lp (ℝ^n) 2 (cellMeasure n) →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (coefficientOperator A) (.id ℝ _)

/-- The Hilbert coefficient form is the integral of the pointwise flux pairing. -/
theorem coefficientForm_eq_integral (v w : Lp (ℝ^n) 2 (cellMeasure n)) :
    coefficientForm A v w = ∫ x, ⟪A x (v x), w x⟫_ℝ ∂cellMeasure n := by
  change ⟪coefficientOperator A v, w⟫_ℝ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coefficientOperator_ae A v] with x hx
  rw [hx]

/-- Pointwise almost-everywhere ellipticity integrates to the same quadratic bound. -/
theorem coefficientForm_lower_bound (α : ℝ)
    (hA : ∀ᵐ x ∂cellMeasure n, ∀ ξ : ℝ^n, α * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    (v : Lp (ℝ^n) 2 (cellMeasure n)) :
    α * ‖v‖ ^ 2 ≤ coefficientForm A v v := by
  rw [← real_inner_self_eq_norm_sq]
  change α * ⟪v, v⟫_ℝ ≤ ⟪coefficientOperator A v, v⟫_ℝ
  rw [L2.inner_def, L2.inner_def, ← integral_const_mul]
  apply integral_mono_ae ((L2.integrable_inner v v).const_mul α)
    (L2.integrable_inner (coefficientOperator A v) v)
  filter_upwards [hA, coefficientOperator_ae A v] with x hx hv
  rw [hv, real_inner_self_eq_norm_sq]
  exact hx (v x)

/-- A positive pointwise ellipticity constant gives coercivity on periodic `L²`. -/
theorem coefficientForm_isCoercive {α : ℝ} (hα : 0 < α)
    (hA : ∀ᵐ x ∂cellMeasure n, ∀ ξ : ℝ^n, α * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ) :
    IsCoercive (coefficientForm A) := by
  refine ⟨α, hα, fun v ↦ ?_⟩
  simpa only [pow_two, mul_assoc] using coefficientForm_lower_bound A α hA v

end PDE.Elliptic.Homogenization.PeriodicCell
