/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Poisson
public import PDE.Hyperbolic.Models.Wave.KirchhoffRepresentation
public import PDE.Analysis.Integration.SphereProjection.Scaling
public import PDE.Analysis.Calculus.CoordinateProjection

/-!
# Hadamard descent for Poisson's disk formula

Lift the planar data constantly in the third spatial coordinate. Projecting
Kirchhoff's sphere integral onto the disk yields the Poisson formula,
including its normalization and square-root singularity.
-/

open scoped Gradient

@[expose] public noncomputable section

namespace WaveEquation

open MeasureTheory PDE.Analysis

/-- The numerator in Poisson's formula is continuous for `C¹` displacement data. -/
theorem continuous_poisson_numerator {g h : ℝ^2 → ℝ}
    (hg : ContDiff ℝ 1 g) (hh : Continuous h) (x : ℝ^2) (t : ℝ) :
    Continuous (fun y ↦ g y + t * h y + ∑ i, ∇ g y i * (y i - x i)) := by
  have he : (fun y ↦ g y + t * h y + ∑ i, ∇ g y i * (y i - x i)) =
      fun y ↦ g y + t * h y + fderiv ℝ g y (y - x) := by
    funext y
    simp [PDE.fderiv_apply_eq_sum_partialDeriv_mul]
  rw [he]
  exact (hg.continuous.add (continuous_const.mul hh)).add
    ((hg.continuous_fderiv_apply one_ne_zero).comp
      (continuous_id.prodMk (continuous_id.sub continuous_const)))

/-- The disk integral defining Poisson's candidate is integrable at every nonzero time. -/
theorem integrableOn_poissonFormula_integrand {g h : ℝ^2 → ℝ}
    (hg : ContDiff ℝ 1 g) (hh : Continuous h) (x : ℝ^2) {t : ℝ} (ht : t ≠ 0) :
    IntegrableOn (fun y ↦ (g y + t * h y + ∑ i, ∇ g y i * (y i - x i)) /
      Real.sqrt (t ^ 2 - ‖y - x‖ ^ 2)) (Metric.ball x |t|) := by
  simpa only [sq_abs] using integrableOn_ball_sqrt_weight
    (continuous_poisson_numerator hg hh x t) x (abs_pos.mpr ht)

/-- The directional displacement term commutes with lifting planar data. -/
theorem poisson_gradient_descent {g : ℝ^2 → ℝ} (hg : Differentiable ℝ g) (y z : ℝ^3) :
    (∑ i, ∇ (g ∘ coordinateProjection) y i * (y i - z i)) = ∑ i,
      ∇ g (coordinateProjection y) i * (coordinateProjection y i - coordinateProjection z i) := by
  simp only [PDE.gradient_apply_eq_partialDeriv, ← PiLp.sub_apply,
    ← PDE.fderiv_apply_eq_sum_partialDeriv_mul]
  rw [fderiv_comp y (hg _) coordinateProjection.differentiableAt,
    ContinuousLinearMap.comp_apply, coordinateProjection.fderiv, map_sub]

/-- Hadamard descent identifies the original disk integral with Kirchhoff's
sphere integral for data independent of the third coordinate. -/
theorem poissonFormula_eq_kirchhoffFormula {g h : ℝ^2 → ℝ}
    (hg : ContDiff ℝ 1 g) (hh : Continuous h) (z : ℝ^3) (t : ℝ) :
    poissonFormula g h (coordinateProjection z) t =
      kirchhoffFormula (g ∘ coordinateProjection) (h ∘ coordinateProjection) z t := by
  by_cases ht : |t| = 0
  · simp [poissonFormula, kirchhoffFormula, ht]
  have hr : 0 < |t| := lt_of_le_of_ne (abs_nonneg t) (Ne.symm ht)
  let f : ℝ^2 → ℝ := fun y ↦ g y + t * h y + ∑ i, ∇ g y i * (y i - coordinateProjection z i)
  have hf : Continuous f := continuous_poisson_numerator hg hh (coordinateProjection z) t
  have hi : (fun y : ℝ^3 ↦ t * (h ∘ coordinateProjection) y + (g ∘ coordinateProjection) y +
      ∑ i, ∇ (g ∘ coordinateProjection) y i * (y i - z i)) = f ∘ coordinateProjection := by
    funext y
    rw [poisson_gradient_descent (hg.differentiable one_ne_zero)]
    simp only [f, Function.comp_apply]
    ring
  simp only [poissonFormula, kirchhoffFormula, ht, ↓reduceDIte]
  rw [hi, sphereIntegral_coordinateProjection hf z hr]
  change (1 / (2 * Real.pi * |t|)) * (∫ y in Metric.ball (coordinateProjection z) |t|,
        f y / Real.sqrt (t ^ 2 - ‖y - coordinateProjection z‖ ^ 2)) = _
  rw [sq_abs]
  field_simp [abs_ne_zero.mp ht]
  rw [sq_abs]
  ring

/-- Evaluate the descended solution on the horizontal plane. -/
theorem poissonFormula_eq_descent {g h : ℝ^2 → ℝ}
    (hg : ContDiff ℝ 1 g) (hh : Continuous h) (x : ℝ^2) (t : ℝ) :
    poissonFormula g h x t = kirchhoffFormula (g ∘ coordinateProjection) (h ∘ coordinateProjection)
      (coordinateInclusion x) t := by
  simpa only [coordinateProjection_coordinateInclusion] using
    poissonFormula_eq_kirchhoffFormula hg hh (coordinateInclusion x) t

/-- The disk formula agrees with the signed-radius spherical-mean representation. -/
theorem poissonFormula_eq_sphericalMean {g h : ℝ^2 → ℝ}
    (hg : ContDiff ℝ 1 g) (hh : Continuous h) (x : ℝ^2) (t : ℝ) :
    poissonFormula g h x t = deriv (fun r ↦ r * unitSphereAverage 3 (g ∘ coordinateProjection)
      (coordinateInclusion x) r) t + t *
      unitSphereAverage 3 (h ∘ coordinateProjection) (coordinateInclusion x) t := by
  rw [poissonFormula_eq_descent hg hh,
    kirchhoffFormula_eq_sphericalMean (hg.comp coordinateProjection.contDiff)
      (hh.comp coordinateProjection.continuous)]

end WaveEquation
