/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.BoundaryRegularity
import CAS.Analysis.SpecialFunctions.Log.Bounds

/-!
# Decay of compact planar Green potentials

The two logarithmic kernels cancel at spatial infinity. If the source is
supported in the radius-`R` ball, the potential is bounded by its
`L¹` mass on the upper half-plane times `R / (π (|x| - R))`. No reflection symmetry or zero
boundary condition on the source is required.

## Main results

* `norm_halfSpaceGreenFunction_le_exterior`: the cancellation of the two logarithms gives
  inverse-distance decay of the Green function outside any ball containing the source point.
* `norm_halfSpaceGreenPotential_le_exterior`: outside its source ball the Green potential is at
  most the `L¹` mass times `R / (π (|x| - R))`.
* `tendsto_halfSpaceGreenPotential_cocompact`: the Green potential of a continuous compact source
  tends to zero at spatial infinity.
-/

@[expose] public noncomputable section

namespace GreenFunction

open MeasureTheory Filter Topology Set SobolevSpace

/-- Cancellation of the two logarithms gives inverse-distance decay outside
any ball containing the source point. -/
theorem norm_halfSpaceGreenFunction_le_exterior {R : ℝ} {y x : ℝ^2}
    (hy : ‖y‖ ≤ R) (hx : R < ‖x‖) :
    ‖halfSpaceGreenFunction y x‖ ≤ R / (Real.pi * (‖x‖ - R)) := by
  have hd : 0 < ‖x‖ - R := sub_pos.mpr hx
  have hdist (z : ℝ^2) (hz : ‖z‖ ≤ R) : ‖x‖ - R ≤ ‖x - z‖ := by
    have ht : ‖x‖ ≤ ‖x - z‖ + ‖z‖ := by
      simpa only [sub_add_cancel] using norm_add_le (x - z) z
    linarith
  have hreflection : ‖HalfSpace.reflect 2 y‖ ≤ R := by
    simpa only [HalfSpace.norm_reflect] using hy
  have hlog : |Real.log ‖x - y‖ - Real.log ‖x - HalfSpace.reflect 2 y‖| ≤
      (‖x‖ - R)⁻¹ * |‖x - y‖ - ‖x - HalfSpace.reflect 2 y‖| := by
    simpa only [div_eq_inv_mul] using
      CAS.Analysis.abs_log_sub_log_le hd (hdist y hy) (hdist _ hreflection)
  have hsep : |‖x - y‖ - ‖x - HalfSpace.reflect 2 y‖| ≤ 2 * R := by
    calc
      _ ≤ ‖(x - y) - (x - HalfSpace.reflect 2 y)‖ := abs_norm_sub_norm_le _ _
      _ = ‖HalfSpace.reflect 2 y - y‖ := by congr 1; abel
      _ ≤ ‖HalfSpace.reflect 2 y‖ + ‖y‖ := norm_sub_le _ _
      _ ≤ 2 * R := by linarith
  rw [halfSpaceGreenFunction, PotentialTheory.fundamentalSolution_two,
    PotentialTheory.fundamentalSolution_two, ← mul_sub, norm_mul, norm_neg]
  have hC : 0 ≤ 1 / (2 * Real.pi) := by positivity
  rw [Real.norm_eq_abs (1 / (2 * Real.pi)), abs_of_nonneg hC, Real.norm_eq_abs]
  calc
    _ ≤ (1 / (2 * Real.pi)) * ((‖x‖ - R)⁻¹ * (2 * R)) :=
      mul_le_mul_of_nonneg_left
        (hlog.trans (mul_le_mul_of_nonneg_left hsep (inv_nonneg.mpr hd.le))) hC
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

/-- The physical `L¹` mass controls the Green potential outside its source ball. -/
theorem norm_halfSpaceGreenPotential_le_exterior {f : ℝ^2 → ℝ}
    (hf : IntegrableOn f (HalfSpace.upper 2)) {R : ℝ}
    (hR : ∀ y, R < ‖y‖ → f y = 0) {x : ℝ^2} (hx : R < ‖x‖) :
    ‖halfSpaceGreenPotential f x‖ ≤
      (R / (Real.pi * (‖x‖ - R))) * ∫ y in HalfSpace.upper 2, ‖f y‖ := by
  have hbound (y : ℝ^2) :
      ‖halfSpaceGreenFunction y x * f y‖ ≤
        (R / (Real.pi * (‖x‖ - R))) * ‖f y‖ := by
    by_cases hy : R < ‖y‖
    · simp only [hR y hy, mul_zero, norm_zero, le_refl]
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (norm_halfSpaceGreenFunction_le_exterior (le_of_not_gt hy) hx) (norm_nonneg _)
  have hi := norm_integral_le_of_norm_le
    (hf.norm.const_mul (R / (Real.pi * (‖x‖ - R)))) (Eventually.of_forall hbound)
  simpa only [halfSpaceGreenPotential, integral_const_mul] using hi

/-- Every continuous compact planar source has a Green potential tending to zero
at spatial infinity, uniformly over observation directions. -/
theorem tendsto_halfSpaceGreenPotential_cocompact {f : ℝ^2 → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) :
    Tendsto (halfSpaceGreenPotential f) (cocompact (ℝ^2)) (𝓝 0) := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.exists_norm_le
  have hsupport (y : ℝ^2) (hy : R < ‖y‖) : f y = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    exact (not_lt_of_ge (hR y hmem)) hy
  let M : ℝ := ∫ y in HalfSpace.upper 2, ‖f y‖
  have harg : Tendsto (fun x : ℝ^2 ↦ ‖x‖ - R) (cocompact (ℝ^2)) atTop := by
    simpa only [sub_eq_add_neg, Function.comp_def, id_eq] using
      (tendsto_atTop_add_const_right atTop (-R) tendsto_id).comp
        tendsto_norm_cocompact_atTop
  have hlim : Tendsto (fun x : ℝ^2 ↦
      (R / (Real.pi * (‖x‖ - R))) * M) (cocompact (ℝ^2)) (𝓝 0) := by
    simpa only [mul_zero] using
      ((tendsto_inv_atTop_zero.comp harg).const_mul (R / Real.pi * M)).congr
        (fun x ↦ by dsimp; simp only [div_eq_mul_inv, mul_inv_rev]; ring)
  apply squeeze_zero_norm' _ hlim
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop R] with x hx
  exact norm_halfSpaceGreenPotential_le_exterior
    (hf.integrable_of_hasCompactSupport hc).integrableOn hsupport hx

end GreenFunction
