/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Radial.AngularDerivative
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Continuous differentiability of radial-angular fields at the origin

Let `f : ℝ → ℝ` be twice continuously differentiable with `f 0 = 0` and `f' 0 = 0`, and let `H`
be continuously differentiable on a finite-dimensional inner product space. Then `|f r| ≤ C r²`
and `|f' r| ≤ C |r|` on `[-1, 1]`. The field `x ↦ f ‖x‖ • H (x / ‖x‖)` is therefore bounded by
a multiple of `‖x‖²` near the origin, so it is differentiable there with zero derivative, and
the derivative bound of `AngularDerivative` makes its derivative `O(‖x‖)` off the origin. The
field is continuously differentiable on the whole space although the normalization is singular
at the origin. An even radial factor has zero derivative at the origin.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Radial

open NormedSpace Asymptotics Filter Set
open scoped Topology

/-- An even real function has zero derivative at the origin, differentiable there or not. -/
theorem deriv_zero_of_even {f : ℝ → ℝ} (hf : Function.Even f) : deriv f 0 = 0 := by
  have h := deriv_comp_neg (f := f) (x := (0 : ℝ))
  rw [show (fun x ↦ f (-x)) = f from funext hf, neg_zero] at h
  linarith

/-- A twice continuously differentiable function with a critical point at the origin has
derivative at most `C |r|` on `[-1, 1]`. -/
theorem exists_abs_deriv_le_mul_abs {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hf' : deriv f 0 = 0) :
    ∃ C ≥ 0, ∀ r, |r| ≤ 1 → |deriv f r| ≤ C * |r| := by
  have hd : ContDiff ℝ 1 (deriv f) := ContDiff.deriv' (n := 1) hf
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hd.continuous_deriv_one.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun r hr ↦ ?_⟩
  have h := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (f := deriv f) (fun x _ ↦ (hd.differentiable one_ne_zero).differentiableAt)
    (fun x hx ↦ (hC x hx).trans (le_max_left C 0))
    (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num) (abs_le.mp hr)
  simpa only [hf', sub_zero, Real.norm_eq_abs] using h

/-- A twice continuously differentiable function vanishing to second order at the origin is
at most `C r²` on `[-1, 1]`. -/
theorem exists_abs_le_mul_sq {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hf0 : f 0 = 0)
    (hf' : deriv f 0 = 0) : ∃ C ≥ 0, ∀ r, |r| ≤ 1 → |f r| ≤ C * r ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_deriv_le_mul_abs hf hf'
  refine ⟨C, hC0, fun r hr ↦ ?_⟩
  have hdiff : ∀ x ∈ uIcc (0 : ℝ) r, DifferentiableAt ℝ f x :=
    fun x _ ↦ (hf.differentiable (by norm_num)).differentiableAt
  have hbound : ∀ x ∈ uIcc (0 : ℝ) r, ‖deriv f x‖ ≤ C * |r| := by
    intro x hx
    have hxr : |x| ≤ |r| := by
      rcases Set.mem_uIcc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]
        exact h2
      · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]
        linarith
    rw [Real.norm_eq_abs]
    exact (hC x (hxr.trans hr)).trans (mul_le_mul_of_nonneg_left hxr hC0)
  have h := (convex_uIcc (0 : ℝ) r).norm_image_sub_le_of_norm_deriv_le hdiff hbound
    left_mem_uIcc right_mem_uIcc
  rw [hf0, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at h
  calc
    |f r| ≤ C * |r| * |r| := h
    _ = C * r ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A radial factor vanishing to second order times a continuous field of the direction is
differentiable at the origin with zero derivative. -/
theorem hasFDerivAt_radial_smul_normalize_zero {f : ℝ → ℝ} {H : E → F}
    (hf : ∃ C, ∀ r, |r| ≤ 1 → |f r| ≤ C * r ^ 2) (hH : Continuous H) :
    HasFDerivAt (fun y ↦ f ‖y‖ • H (normalize y)) (0 : E →L[ℝ] F) 0 := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨K, -, hK⟩ := exists_norm_comp_normalize_le hH
  have hf0 : f 0 = 0 := by
    have h := hC 0 (by norm_num)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      abs_nonpos_iff] at h
    exact h
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add, norm_zero, hf0, zero_smul, sub_zero, _root_.zero_apply]
  refine IsBigO.trans_isLittleO (g := fun y : E ↦ ‖y‖ ^ 2) ?_ (isLittleO_norm_pow_id one_lt_two)
  refine IsBigO.of_bound (C * K) ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : E) one_pos] with y hy
  rw [Metric.mem_closedBall, dist_zero_right] at hy
  have hr := hC ‖y‖ (by rw [abs_norm]; exact hy)
  rw [norm_smul, Real.norm_eq_abs, norm_pow, norm_norm]
  calc
    |f ‖y‖| * ‖H (normalize y)‖ ≤ (C * ‖y‖ ^ 2) * K :=
      mul_le_mul hr (hK y) (norm_nonneg _) ((abs_nonneg _).trans hr)
    _ = C * K * ‖y‖ ^ 2 := by ring

/-- Off the origin and inside the unit ball the derivative of such a field is at most a multiple
of the radius. -/
theorem exists_norm_fderiv_radial_smul_normalize_le {f : ℝ → ℝ} {H : E → F}
    (hf : ContDiff ℝ 2 f) (hf0 : f 0 = 0) (hf' : deriv f 0 = 0) (hH : ContDiff ℝ 1 H) :
    ∃ C, ∀ x : E, x ≠ 0 → ‖x‖ ≤ 1 →
      ‖fderiv ℝ (fun y ↦ f ‖y‖ • H (normalize y)) x‖ ≤ C * ‖x‖ := by
  obtain ⟨A, hA0, hA⟩ := exists_abs_le_mul_sq hf hf0 hf'
  obtain ⟨D, hD0, hD⟩ := exists_abs_deriv_le_mul_abs hf hf'
  obtain ⟨K, hK0, hK⟩ := exists_norm_comp_normalize_le hH.continuous
  obtain ⟨K', hK'0, hK'⟩ := exists_norm_comp_normalize_le (hH.continuous_fderiv one_ne_zero)
  refine ⟨2 * A * K' + D * K, fun x hx hx1 ↦ ?_⟩
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h1 : |‖x‖| ≤ 1 := by rw [abs_norm]; exact hx1
  refine (norm_fderiv_radial_smul_normalize_le hx
    ((hf.differentiable (by norm_num)).differentiableAt)
    ((hH.differentiable one_ne_zero).differentiableAt)).trans ?_
  have hfx := hA ‖x‖ h1
  have hdx := hD ‖x‖ h1
  rw [abs_norm] at hdx
  calc
    |f ‖x‖| * ‖fderiv ℝ H (normalize x)‖ * (2 / ‖x‖) + |deriv f ‖x‖| * ‖H (normalize x)‖
        ≤ (A * ‖x‖ ^ 2) * K' * (2 / ‖x‖) + (D * ‖x‖) * K :=
      add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul hfx (hK' x) (norm_nonneg _)
          (by positivity)) (by positivity))
        (mul_le_mul hdx (hK x) (norm_nonneg _) (by positivity))
    _ = (2 * A * K' + D * K) * ‖x‖ := by field_simp

/-- A twice continuously differentiable radial factor with `f 0 = 0` and `f' 0 = 0` times a
continuously differentiable field of the direction is continuously differentiable on the
whole space, including the origin. -/
theorem contDiff_one_radial_smul_normalize {f : ℝ → ℝ} {H : E → F}
    (hf : ContDiff ℝ 2 f) (hf0 : f 0 = 0) (hf' : deriv f 0 = 0) (hH : ContDiff ℝ 1 H) :
    ContDiff ℝ 1 (fun y ↦ f ‖y‖ • H (normalize y)) := by
  set g : E → F := fun y ↦ f ‖y‖ • H (normalize y) with hg
  obtain ⟨A, -, hA⟩ := exists_abs_le_mul_sq hf hf0 hf'
  have h0 : HasFDerivAt g (0 : E →L[ℝ] F) 0 :=
    hasFDerivAt_radial_smul_normalize_zero ⟨A, hA⟩ hH.continuous
  have hoff {x : E} (hx : x ≠ 0) : ContDiffAt ℝ 1 g x := by
    have hn : ContDiffAt ℝ 1 (normalize : E → E) x :=
      ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id
    exact ((hf.of_le (by norm_num)).contDiffAt.comp x (contDiffAt_norm ℝ hx)).smul
      (hH.contDiffAt.comp x hn)
  obtain ⟨C, hC⟩ := exists_norm_fderiv_radial_smul_normalize_le hf hf0 hf' hH
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x ↦ ?_, continuous_iff_continuousAt.mpr fun x ↦ ?_⟩
  · by_cases hx : x = 0
    · subst hx
      exact h0.differentiableAt
    · exact (hoff hx).differentiableAt one_ne_zero
  · by_cases hx : x = 0
    · subst hx
      rw [ContinuousAt, h0.fderiv, tendsto_iff_norm_sub_tendsto_zero]
      simp only [sub_zero]
      refine squeeze_zero_norm' ?_ (Continuous.tendsto'
        (continuous_const.mul continuous_norm : Continuous fun y : E ↦ C * ‖y‖) 0 0 (by simp))
      filter_upwards [Metric.closedBall_mem_nhds (0 : E) one_pos] with y hy
      rw [Metric.mem_closedBall, dist_zero_right] at hy
      rw [norm_norm]
      by_cases hy0 : y = 0
      · subst hy0
        rw [h0.fderiv]
        simp
      · exact hC y hy0 hy
    · exact ((hoff hx).fderiv_right (m := 0) le_rfl).continuousAt

/-- An even twice continuously differentiable radial factor vanishing at the origin times a
continuous field of the direction has zero derivative at the origin. -/
theorem hasFDerivAt_radial_smul_normalize_zero_of_even {f : ℝ → ℝ} {H : E → F}
    (hf : ContDiff ℝ 2 f) (heven : ∀ r, f (-r) = f r) (hf0 : f 0 = 0) (hH : Continuous H) :
    HasFDerivAt (fun y ↦ f ‖y‖ • H (normalize y)) (0 : E →L[ℝ] F) 0 := by
  obtain ⟨A, -, hA⟩ := exists_abs_le_mul_sq hf hf0 (deriv_zero_of_even heven)
  exact hasFDerivAt_radial_smul_normalize_zero ⟨A, hA⟩ hH

/-- An even twice continuously differentiable radial factor vanishing at the origin times a
continuously differentiable field of the direction is continuously differentiable on the
whole space. -/
theorem contDiff_one_radial_smul_normalize_of_even {f : ℝ → ℝ} {H : E → F}
    (hf : ContDiff ℝ 2 f) (heven : ∀ r, f (-r) = f r) (hf0 : f 0 = 0) (hH : ContDiff ℝ 1 H) :
    ContDiff ℝ 1 (fun y ↦ f ‖y‖ • H (normalize y)) :=
  contDiff_one_radial_smul_normalize hf hf0 (deriv_zero_of_even heven) hH

end PDE.Analysis.Radial
