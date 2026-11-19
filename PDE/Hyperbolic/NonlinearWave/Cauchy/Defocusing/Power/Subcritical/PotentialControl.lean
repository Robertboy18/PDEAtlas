/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RetardedPotential
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.SobolevControl
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Uniform control of subcritical power potentials

On balls with bounded radius, a bound on `‖Du‖₂ + r⁻¹ ‖u‖₂` controls the inverse-distance potential
of `|u|^p` by the amplitude power `max (p - 4) 0`. The constant is independent of the amplitude and
the ball radius. Both singular integrability and L⁶ membership follow from arbitrary H¹ data.

This is the functional estimate that the proof of Theorem 3 of Evans, §12.3.3, applies to the
retarded cone trace: (20)-(21) and the two cases of step 3. The trace itself and its H¹ bound from
the wave equation are not used; the H¹ bound is a hypothesis.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.3.3, proof of Theorem 3, equations (20)-(21) and step 3.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- The square root of the sixth-power integral is the cube of the L⁶ norm. -/
theorem sqrt_integral_six {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : MemLp f 6 μ) :
    √(∫ x, |f x| ^ 6 ∂μ) = (eLpNorm f 6 μ).toReal ^ 3 := by
  have hnorm : ‖hf.toLp f‖ ^ 6 = ∫ x, |f x| ^ 6 ∂μ := by
    have h := Lp.norm_rpow_eq_integral (by norm_num : (6 : ℝ≥0∞) ≠ 0)
      (by norm_num : (6 : ℝ≥0∞) ≠ ∞) (hf.toLp f)
    simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat, Real.norm_eq_abs] at h
    exact h.trans (integral_congr_ae (hf.coeFn_toLp.fun_comp fun z : ℝ ↦ |z| ^ 6))
  rw [Lp.norm_toLp] at hnorm
  rw [← hnorm, show (eLpNorm f 6 μ).toReal ^ 6 =
    ((eLpNorm f 6 μ).toReal ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]

/-- On every fixed radius range, bounded scaled H¹ norm controls the power
potential. The constant does not depend on the real power or the amplitude. -/
theorem exists_power_potential_bound (T E : ℝ) (hE : 0 ≤ E) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (r p A : ℝ), 0 < r → r ≤ T → 1 ≤ p → 1 ≤ A → ∀ U : H¹(ball (0 : ℝ^3) r), ‖∇ U‖ ≤ E →
        ‖wkpBaseCoordinateCLM U‖ / r ≤ E → (∀ᵐ x ∂domainMeasure 3 (ball 0 r),
        |baseRepresentative U x| ≤ A) → IntegrableOn (fun x ↦ |baseRepresentative U x| ^ p / ‖x‖)
        (ball (0 : ℝ^3) r) ∧
      (∫ x in ball (0 : ℝ^3) r, |baseRepresentative U x| ^ p / ‖x‖) ≤ K * A ^ max (p - 4) 0 := by
  obtain ⟨C, hC, hS⟩ := exists_sobolev_bound_ball
  refine ⟨√10 * E * (√(volume.real (ball (0 : ℝ^3) T)) + (C * (2 * E)) ^ 3),
    by positivity, ?_⟩
  intro r p A hr hrT hp hA U hgrad hbase hamp
  have h6 := memLp_six_ball 0 hr U
  obtain ⟨hi, hb⟩ := h1_power_potential_bound hr hp hA U h6 hamp
  have hhardy : 4 * ‖∇ U‖ ^ 2 + 6 / r ^ 2 * ‖wkpBaseCoordinateCLM U‖ ^ 2 ≤
      10 * E ^ 2 := by
    have hg := pow_le_pow_left₀ (norm_nonneg (∇ U)) hgrad 2
    have hu := pow_le_pow_left₀ (div_nonneg (norm_nonneg (wkpBaseCoordinateCLM U)) hr.le) hbase 2
    have hid : 6 / r ^ 2 * ‖wkpBaseCoordinateCLM U‖ ^ 2 =
        6 * (‖wkpBaseCoordinateCLM U‖ / r) ^ 2 := by ring
    rw [hid]
    nlinarith
  have hroot : √(4 * ‖∇ U‖ ^ 2 + 6 / r ^ 2 * ‖wkpBaseCoordinateCLM U‖ ^ 2) ≤
      √10 * E := by
    calc
      _ ≤ √(10 * E ^ 2) := Real.sqrt_le_sqrt hhardy
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 10), Real.sqrt_sq hE]
  have hsix : √(∫ x in ball (0 : ℝ^3) r, |baseRepresentative U x| ^ 6) ≤
      (C * (2 * E)) ^ 3 := by
    rw [sqrt_integral_six h6]
    apply pow_le_pow_left₀ ENNReal.toReal_nonneg
    exact (hS 0 r hr U).trans
      (mul_le_mul_of_nonneg_left (by linarith : ‖∇ U‖ + ‖wkpBaseCoordinateCLM U‖ / r ≤ 2 * E) hC.le)
  have hvol : √(volume.real (ball (0 : ℝ^3) r)) ≤ √(volume.real (ball (0 : ℝ^3) T)) :=
    Real.sqrt_le_sqrt (measureReal_mono (ball_subset_ball hrT) measure_ball_lt_top.ne)
  refine ⟨hi, hb.trans ?_⟩
  have h := mul_le_mul
    (mul_le_mul_of_nonneg_left hroot (Real.rpow_nonneg (zero_le_one.trans hA) (max (p - 4) 0)))
    (add_le_add hvol hsix) (by positivity) (by positivity)
  convert h using 1
  ring

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
