/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Radial.AngularDerivative
public import PDE.Analysis.MeasureTheory.Lp.RadialPower.NearFar
public import PDE.Common.Euclidean
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Finite energy of scalar radial-angular fields

Inverse-square radial values and inverse-cube radial derivatives give finite
energy for the scalar field and its derivative in three dimensions. A bounded
radial factor near zero suffices; the field need not be continuous at zero.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Radial

open Metric NormedSpace MeasureTheory

private theorem exists_bound_on_unit_interval {f : ℝ → ℝ} (hf : Continuous f) :
    ∃ C ≥ 0, ∀ r ∈ Set.Icc (0 : ℝ) 1, |f r| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := (isCompact_Icc.image hf).isBounded.exists_pos_norm_le
  exact ⟨C, hC.le, fun r hr ↦ by
    simpa only [Real.norm_eq_abs] using hbound _ (Set.mem_image_of_mem _ hr)⟩

/-- Scalar radial-angular fields with inverse-square radial decay have finite energy. -/
theorem memLp_two_radial_mul_normalize {f : ℝ → ℝ} (hf : Continuous f)
    {H : ℝ^3 → ℝ} (hH : Continuous H)
    (hfar : ∃ a ≥ 0, ∀ r : ℝ, 1 ≤ r → |f r| ≤ a / r ^ 2) :
    MemLp (fun x : ℝ^3 ↦ f ‖x‖ * H (NormedSpace.normalize x)) 2 volume := by
  obtain ⟨A, hA, hAbound⟩ := exists_norm_comp_normalize_le hH
  obtain ⟨b, hb, hbbound⟩ := exists_bound_on_unit_interval hf
  obtain ⟨a, ha, htail⟩ := hfar
  have hn : Measurable (NormedSpace.normalize : ℝ^3 → ℝ^3) := by
    unfold NormedSpace.normalize
    exact measurable_norm.inv.smul measurable_id
  apply memLp_two_of_near_inv_radius_far_inv_sq
    ((hf.measurable.comp measurable_norm).mul (hH.measurable.comp hn)).aestronglyMeasurable
    (by norm_num) (by norm_num) (mul_nonneg ha hA.le)
  · intro x hx hsmall
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
    calc
      _ = |f ‖x‖| * ‖H (NormedSpace.normalize x)‖ := by
        simp only [Pi.mul_apply, Function.comp_apply, norm_mul, Real.norm_eq_abs]
      _ ≤ b * A := mul_le_mul (hbbound ‖x‖ ⟨hr.le, hsmall⟩)
        (hAbound x) (norm_nonneg _) hb
      _ ≤ (b * A) / ‖x‖ :=
        (le_div_iff₀ hr).mpr (mul_le_of_le_one_right (mul_nonneg hb hA.le) hsmall)
  · intro x _ hlarge
    calc
      _ = |f ‖x‖| * ‖H (NormedSpace.normalize x)‖ := by
        simp only [Pi.mul_apply, Function.comp_apply, norm_mul, Real.norm_eq_abs]
      _ ≤ (a / ‖x‖ ^ 2) * A :=
        mul_le_mul (htail ‖x‖ hlarge) (hAbound x) (norm_nonneg _) (by positivity)
      _ = (a * A) / ‖x‖ ^ 2 := by ring

/-- The classical derivative has finite energy even when the origin value is discontinuous. -/
theorem memLp_two_fderiv_radial_mul_normalize {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {H : ℝ^3 → ℝ} (hH : ContDiff ℝ 1 H)
    (hfar : ∃ a ≥ 0, ∃ d ≥ 0, ∀ r : ℝ, 1 ≤ r →
      |f r| ≤ a / r ^ 2 ∧ |deriv f r| ≤ d / r ^ 3) :
    MemLp (fderiv ℝ (fun x : ℝ^3 ↦ f ‖x‖ * H (NormedSpace.normalize x)))
      2 volume := by
  let : NormedSpace ℝ (ℝ^3 →L[ℝ] ℝ) := inferInstance
  obtain ⟨A, hA, hAbound⟩ := exists_norm_comp_normalize_le hH.continuous
  obtain ⟨D, hD, hDbound⟩ := exists_norm_comp_normalize_le
    (hH.continuous_fderiv (by norm_num))
  obtain ⟨b, hb, hbbound⟩ := exists_bound_on_unit_interval hf.continuous
  obtain ⟨e, he, hebound⟩ := exists_bound_on_unit_interval hf.continuous_deriv_one
  obtain ⟨a, ha, d, hd, htail⟩ := hfar
  have hbound (x : ℝ^3) (hx : x ≠ 0) :
      ‖fderiv ℝ (fun y ↦ f ‖y‖ * H (NormedSpace.normalize y)) x‖ ≤
        |f ‖x‖| * ‖fderiv ℝ H (NormedSpace.normalize x)‖ * (2 / ‖x‖) +
          |deriv f ‖x‖| * ‖H (NormedSpace.normalize x)‖ :=
    norm_fderiv_radial_smul_normalize_le hx
      (hf.differentiable (by norm_num)).differentiableAt
      (hH.differentiable (by norm_num)).differentiableAt
  apply memLp_two_of_near_inv_radius_far_inv_sq
    (measurable_fderiv ℝ _).aestronglyMeasurable
    (by norm_num) (by norm_num) (by positivity : 0 ≤ 2 * a * D + d * A)
  · intro x hx hsmall
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
    refine (hbound x hx).trans ?_
    calc
      _ ≤ b * D * (2 / ‖x‖) + e * A := by
        gcongr
        · exact hbbound ‖x‖ ⟨hr.le, hsmall⟩
        · exact hDbound x
        · exact hebound ‖x‖ ⟨hr.le, hsmall⟩
        · exact hAbound x
      _ ≤ (2 * b * D + e * A) / ‖x‖ := by
        apply (le_div_iff₀ hr).mpr
        have hmul := mul_le_of_le_one_right (mul_nonneg he hA.le) hsmall
        field_simp
        nlinarith
  · intro x hx hlarge
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
    obtain ⟨hvalue, hfirst⟩ := htail ‖x‖ hlarge
    refine (hbound x hx).trans ?_
    calc
      _ ≤ (a / ‖x‖ ^ 2) * D * (2 / ‖x‖) + (d / ‖x‖ ^ 3) * A := by
        gcongr
        · exact hDbound x
        · exact hAbound x
      _ = (2 * a * D + d * A) / ‖x‖ ^ 3 := by field_simp
      _ ≤ (2 * a * D + d * A) / ‖x‖ ^ 2 := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        simpa only [mul_one, ← pow_succ] using
          mul_le_mul_of_nonneg_left hlarge (sq_nonneg ‖x‖)

end PDE.Analysis.Radial
