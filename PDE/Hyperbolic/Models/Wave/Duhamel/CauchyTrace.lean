/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Duhamel.SourceMoment
import CAS.IntegrationTactic

/-!
# Spherical Cauchy traces and bounded forcing

Kirchhoff's formula separates the displacement mean from the spherical average
of velocity and the outward radial derivative. A bounded source contributes
at most a quadratic function of the elapsed time.
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE PDE.Analysis PDE.Common
open scoped Topology

namespace WaveEquation

/-- The normalized velocity and radial derivative on a Cauchy sphere. -/
def sphericalCauchyTrace (g h : ℝ^3 → ℝ) (x : ℝ^3) (d : ℝ) : ℝ :=
  (∫ ω : Metric.sphere (0 : ℝ^3) 1,
    h (x + d • (ω : ℝ^3)) +
      fderiv ℝ g (x + d • (ω : ℝ^3)) (ω : ℝ^3)
    ∂((volume : Measure (ℝ^3)).toSphere)) / unitSphereArea 3

/-- Kirchhoff's formula separates the bounded displacement mean from the
spherical Cauchy trace that may concentrate at shrinking radii. -/
theorem kirchhoffFormula_eq_mean_add_sphericalCauchyTrace {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 1 g)
    (hh : Continuous h) (x : ℝ^3) (d : ℝ) :
    kirchhoffFormula g h x d = unitSphereAverage 3 g x d + d * sphericalCauchyTrace g h x d := by
  let μ := (volume : Measure (ℝ^3)).toSphere
  let p := fun ω : Metric.sphere (0 : ℝ^3) 1 ↦ x + d • (ω : ℝ^3)
  have hp : Continuous p := by fun_prop
  have hi {v : Metric.sphere (0 : ℝ^3) 1 → ℝ} (hv : Continuous v) : Integrable v μ :=
    hv.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (fun _ _ ↦ mem_univ _))
  have hhint : Integrable (fun ω : Metric.sphere (0 : ℝ^3) 1 ↦
      h (x + d • (ω : ℝ^3))) ((volume : Measure (ℝ^3)).toSphere) := hi (hh.comp hp)
  have hdint : Integrable (fun ω : Metric.sphere (0 : ℝ^3) 1 ↦
      fderiv ℝ g (x + d • (ω : ℝ^3)) (ω : ℝ^3)) ((volume : Measure (ℝ^3)).toSphere) :=
    hi ((hg.continuous_fderiv_apply one_ne_zero).comp (hp.prodMk continuous_subtype_val))
  have hd := ((hasDerivAt_id d).fun_mul (hasDerivAt_unitSphereAverage g x d hg)).deriv
  simp only [one_mul, id_eq] at hd
  rw [kirchhoffFormula_eq_sphericalMean hg hh, hd]
  unfold sphericalCauchyTrace
  rw [integral_add hhint hdint]
  simp only [add_div, mul_add, unitSphereAverage]
  ac_rfl

/-- If `‖F‖ ≤ A` on the backward cone with apex `(t, x)`, the retarded term at `(t, x)`
is at most `t² A / 2`. -/
theorem norm_oddDuhamelSolution_zero_le_quadratic_on_cone {F : ℝ^4 → ℝ} {t A : ℝ} (ht : 0 ≤ t)
    (x : ℝ^3) (hbound : ∀ s ∈ Ioc 0 t, ∀ y : ℝ^3, ‖y - x‖ ≤ t - s → ‖F (timeSpaceCons s y)‖ ≤ A) :
    ‖oddDuhamelSolution 0 F (timeSpaceCons t x)‖ ≤ t ^ 2 * A / 2 := by
  have hi : IntervalIntegrable (fun s : ℝ ↦ (t - s) * A) volume 0 t :=
    (continuous_const.sub continuous_id |>.mul continuous_const).intervalIntegrable 0 t
  have he : (∫ s in (0 : ℝ)..t, (t - s) * A) = t ^ 2 * A / 2 := by
    cas
  exact he ▸ norm_oddDuhamelSolution_zero_le_source_moment ht hi x hbound

end WaveEquation
