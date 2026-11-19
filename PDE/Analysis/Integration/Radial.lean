/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Geometry.EuclideanBall
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Radial integrals in `ℝ^n`

For `n ≥ 1` the integral of a radial function over `ℝ^n` is
`∫ f (|x|) dx = σ ∫₀^∞ r^(n-1) f (r) dr` (`integral_radial`), where `σ` is the area of the unit
sphere, `PDE.Analysis.unitSphereArea n`. When the profile `f` vanishes beyond a radius `R ≥ 0`,
the right side is the interval integral over `[0, R]` (`integral_radial_of_support`), which is
the form that `cas` evaluates for a polynomial profile. The integral of a radial function over
the ball of radius `R` about the origin has the same right side (`integral_ball_radial`). None
of the statements assumes integrability.

The first is Mathlib's `MeasureTheory.integral_fun_norm_addHaar` with
`MeasureTheory.Measure.toSphere_real_apply_univ`. In the plane it is
`PDE.Analysis.integral_radialPlane`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.Analysis

/-- In `ℝ^n`, `n ≥ 1`, `∫ f (|x|) dx = σ ∫₀^∞ r^(n-1) f (r) dr` for every `f : ℝ → ℝ`, with
`σ = unitSphereArea n`. -/
theorem integral_radial (n : ℕ) [Fact (0 < n)] (f : ℝ → ℝ) :
    ∫ x : ℝ^n, f ‖x‖ = unitSphereArea n * ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * f r := by
  have : Nonempty (Fin n) := ⟨⟨0, Fact.out⟩⟩
  have hsphere : unitSphereArea n = n * (volume : Measure (ℝ^n)).real (Metric.ball 0 1) := by
    change (volume : Measure (ℝ^n)).toSphere.real univ = _
    rw [Measure.toSphere_real_apply_univ, finrank_euclideanSpace_fin]
  rw [hsphere]
  simpa [nsmul_eq_mul, smul_eq_mul, mul_assoc] using
    integral_fun_norm_addHaar (volume : Measure (ℝ^n)) f

/-- In `ℝ^n`, `n ≥ 1`, `∫ f (|x|) dx = σ ∫₀ᴿ r^(n-1) f (r) dr` when `f` vanishes on `(R, ∞)` and
`R ≥ 0`, with `σ = unitSphereArea n`. -/
theorem integral_radial_of_support (n : ℕ) [Fact (0 < n)] {f : ℝ → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hf : ∀ r, R < r → f r = 0) :
    ∫ x : ℝ^n, f ‖x‖ = unitSphereArea n * ∫ r in (0 : ℝ)..R, r ^ (n - 1) * f r := by
  rw [integral_radial, intervalIntegral.integral_of_le hR,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
      fun r hr ↦ by rw [hf r (not_le.mp fun h ↦ hr.2 ⟨hr.1, h⟩), mul_zero]]

/-- In `ℝ^n`, `n ≥ 1`, the integral of a radial function over the ball of radius `R ≥ 0` about
the origin is `∫_{|x| < R} f (|x|) dx = σ ∫₀ᴿ r^(n-1) f (r) dr` for every `f : ℝ → ℝ`, with
`σ = unitSphereArea n`. -/
theorem integral_ball_radial (n : ℕ) [Fact (0 < n)] (f : ℝ → ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ∫ x in Metric.ball (0 : ℝ^n) R, f ‖x‖ =
      unitSphereArea n * ∫ r in (0 : ℝ)..R, r ^ (n - 1) * f r := by
  have hball : (∫ x in Metric.ball (0 : ℝ^n) R, f ‖x‖) =
      ∫ x : ℝ^n, (Iio R).indicator f ‖x‖ := by
    rw [← integral_indicator measurableSet_ball]
    exact integral_congr_ae (.of_forall fun x ↦ by
      simp only [indicator, mem_Iio, Metric.mem_ball, dist_zero_right])
  rw [hball, integral_radial_of_support n (f := (Iio R).indicator f) hR fun r hr ↦
    indicator_of_notMem (s := Iio R) (not_lt.mpr hr.le) f]
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [(volume : Measure ℝ).ae_ne R] with r hrR hr
  rw [uIoc_of_le hR] at hr
  rw [indicator_of_mem (s := Iio R) (lt_of_le_of_ne hr.2 hrR)]

end PDE.Analysis
