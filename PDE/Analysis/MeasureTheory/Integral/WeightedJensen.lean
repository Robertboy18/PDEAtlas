/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convex.Differentiable.Supporting
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Jensen's inequality with an integrable probability density

A supporting line of a convex function at the weighted mean (from its right derivative) gives
Jensen's inequality for a nonnegative weight of integral one. All three weighted integrability
conditions are explicit; no totalized integral is used as a finite expectation.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace PDE.Analysis

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Weighted Jensen inequality on the nonnegative half-line, proved by integrating a supporting
line at the weighted mean `m`. No differentiability is needed: for `m > 0` the right derivative
of the convex function gives the supporting line; for `m = 0` the weight vanishes wherever `u`
does not, so both sides equal `F 0`. The weight is integrable because its integral is `1`. -/
theorem convex_map_integral_mul_le
    {w u : X → ℝ} {F : ℝ → ℝ}
    (hwpos : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hunit : ∫ x, w x ∂μ = 1)
    (hu : Integrable (fun x ↦ w x * u x) μ)
    (hu_nonneg : ∀ᵐ x ∂μ, 0 ≤ u x)
    (hFu : Integrable (fun x ↦ w x * F (u x)) μ)
    (hconvex : ConvexOn ℝ (Ici 0) F) :
    F (∫ x, w x * u x ∂μ) ≤ ∫ x, w x * F (u x) ∂μ := by
  have hw : Integrable w μ := by
    by_contra h
    rw [integral_undef h] at hunit
    exact zero_ne_one hunit
  let m := ∫ x, w x * u x ∂μ
  have hwu : 0 ≤ᵐ[μ] fun x ↦ w x * u x := by
    filter_upwards [hwpos, hu_nonneg] with x hx hy using mul_nonneg hx hy
  have hm : 0 ≤ m := integral_nonneg_of_ae hwu
  rcases hm.eq_or_lt with hm0 | hmpos
  · -- `m = 0`: `w u = 0` a.e., so `w F(u) = w F(0)` a.e.
    have hzero : (fun x ↦ w x * u x) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hwu hu).mp hm0.symm
    have hcongr : (fun x ↦ w x * F (u x)) =ᵐ[μ] fun x ↦ w x * F 0 := by
      filter_upwards [hzero] with x hx
      rcases mul_eq_zero.mp hx with h | h
      · simp [h]
      · simp [h]
    change F m ≤ _
    rw [integral_congr_ae hcongr, integral_mul_const, hunit, one_mul, ← hm0]
  -- `m > 0`: a supporting line with the right derivative `c` at `m`
  have hint : m ∈ interior (Ici (0 : ℝ)) := by rwa [interior_Ici]
  set c := derivWithin F (Ioi m) m
  have hsupport (y : ℝ) (hy : 0 ≤ y) : F m + c * (y - m) ≤ F y := by
    rcases lt_trichotomy y m with hym | rfl | hmy
    · have h1 := hconvex.slope_le_leftDeriv_of_mem_interior (mem_Ici.mpr hy) hint hym
      have h2 := hconvex.leftDeriv_le_rightDeriv_of_mem_interior hint
      have h := h1.trans h2
      rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hym)] at h
      nlinarith
    · simp
    · have h := hconvex.rightDeriv_le_slope_of_mem_interior hint (mem_Ici.mpr hy) hmy
      rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hmy)] at h
      nlinarith
  have hpoint : ∀ᵐ x ∂μ,
      w x * (F m + c * (u x - m)) ≤ w x * F (u x) := by
    filter_upwards [hwpos, hu_nonneg] with x hx hy
    exact mul_le_mul_of_nonneg_left (hsupport (u x) hy) hx
  have hid : (fun x ↦ w x * (F m + c * (u x - m))) =
      fun x ↦ w x * F m + c * (w x * u x - w x * m) := by
    funext x
    ring
  change (fun x ↦ w x * (F m + c * (u x - m))) ≤ᵐ[μ]
    (fun x ↦ w x * F (u x)) at hpoint
  rw [hid] at hpoint
  have hlinear : Integrable (fun x ↦ w x * u x - w x * m) μ :=
    hu.sub (hw.mul_const m)
  have hscaled : Integrable (fun x ↦ c * (w x * u x - w x * m)) μ :=
    hlinear.const_mul c
  have hconstant : Integrable (fun x ↦ w x * F m) μ := hw.mul_const (F m)
  have hle := integral_mono_ae (hconstant.add hscaled) hFu hpoint
  have hsum : (∫ x, w x * F m + c * (w x * u x - w x * m) ∂μ) =
      (∫ x, w x * F m ∂μ) + ∫ x, c * (w x * u x - w x * m) ∂μ :=
    integral_add hconstant hscaled
  have hsub : (∫ x, w x * u x - w x * m ∂μ) =
      (∫ x, w x * u x ∂μ) - ∫ x, w x * m ∂μ := integral_sub hu (hw.mul_const m)
  change (∫ x, w x * F m + c * (w x * u x - w x * m) ∂μ) ≤ _ at hle
  rw [hsum, integral_mul_const, integral_const_mul, hsub, integral_mul_const,
    hunit] at hle
  simpa only [m, one_mul, sub_self, mul_zero, add_zero] using hle

end PDE.Analysis
