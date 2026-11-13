/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Poincare.WeightedRay
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import CAS.ExactTactic

/-!
# Ray kernels for coefficients singular at the origin

A coefficient bounded by `A / (‖x‖² (1 + ‖x‖)²)` can be unbounded near the
origin. Its outward ray kernel nevertheless has the locally integrable
majorant `A / ‖y‖`. This separates the core integrability requirement from
the stronger bounded-coefficient hypothesis of the global quartic estimates.

Throughout, `H₊ = {x : ℝ² | 0 ≤ x₀}` is the closed right half-plane.
-/

@[expose] public noncomputable section

open PDE.Common (coordinateClosedHalfSpace measurableSet_coordinateClosedHalfSpace
  smul_mem_coordinateClosedHalfSpace_iff)

local notation "H₊" => coordinateClosedHalfSpace (0 : Fin 2)

open PDE.FDeriv

open MeasureTheory Filter
open scoped Topology

namespace SobolevSpace.Weighted

/-- Quadratic singularity at zero and quartic decay at infinity give
absolute ray integrability and an inverse-radius kernel bound. -/
theorem ray_integrable_and_kernel_le_of_singular_quartic_bound
    (W : (ℝ^2 → ℝ)) (A : ℝ) (hA : 0 ≤ A) (hWmeas : Measurable W)
    (hW : ∀ x ∈ H₊, 0 ≤ W x)
    (hbound : ∀ x ∈ H₊, x ≠ 0 →
      W x ≤ A / (‖x‖ ^ 2 * (1 + ‖x‖) ^ 2))
    (y : (ℝ^2)) (hy : y ∈ H₊) (hy0 : y ≠ 0) :
    IntervalIntegrable (fun t : ℝ ↦ (t ^ 4)⁻¹ * W (t⁻¹ • y)) volume 0 1 ∧
      weightedPoincareRayKernel W y ≤ A / ‖y‖ := by
  let d := ‖y‖
  have hd : 0 < d := norm_pos_iff.mpr hy0
  let B := A / d ^ 2
  have hB : 0 ≤ B := div_nonneg hA (sq_nonneg d)
  have hmajorant : IntervalIntegrable (fun t : ℝ ↦ B / (t + d) ^ 2) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
    exact continuousOn_const.div ((continuous_id.add continuous_const).pow 2).continuousOn
      (fun t ht ↦ ne_of_gt (pow_pos (add_pos_of_nonneg_of_pos ht.1 hd) 2))
  have hpoint (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
      (t ^ 4)⁻¹ * W (t⁻¹ • y) ≤ B / (t + d) ^ 2 := by
    have hty : t⁻¹ • y ∈ H₊ :=
      (smul_mem_coordinateClosedHalfSpace_iff (0 : Fin 2) (inv_pos.mpr ht.1) y).2 hy
    have hnorm : ‖t⁻¹ • y‖ = t⁻¹ * d := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht.1.le)]
    have hne : t⁻¹ • y ≠ 0 := smul_ne_zero (inv_ne_zero ht.1.ne') hy0
    calc
      _ ≤ (t ^ 4)⁻¹ * (A / (‖t⁻¹ • y‖ ^ 2 * (1 + ‖t⁻¹ • y‖) ^ 2)) :=
        mul_le_mul_of_nonneg_left (hbound _ hty hne)
          (inv_nonneg.mpr (pow_nonneg ht.1.le 4))
      _ = B / (t + d) ^ 2 := by
        rw [hnorm]
        dsimp only [B]
        have htne : t ≠ 0 := ht.1.ne'
        have hdne : d ≠ 0 := hd.ne'
        have htd : t + d ≠ 0 := (add_pos ht.1 hd).ne'
        have hden : 1 + t⁻¹ * d ≠ 0 :=
          (add_pos_of_pos_of_nonneg zero_lt_one
            (mul_nonneg (inv_nonneg.mpr ht.1.le) hd.le)).ne'
        cas [htne, hdne, htd, hden]
  have hkernel : IntervalIntegrable
      (fun t : ℝ ↦ (t ^ 4)⁻¹ * W (t⁻¹ • y)) volume 0 1 := by
    apply hmajorant.mono_fun
      (((measurable_id.pow_const 4).inv.mul
        (hWmeas.comp (measurable_id.inv.smul_const y))).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    have ht' : t ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa only [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    have hty : t⁻¹ • y ∈ H₊ :=
      (smul_mem_coordinateClosedHalfSpace_iff (0 : Fin 2) (inv_pos.mpr ht'.1) y).2 hy
    change ‖(t ^ 4)⁻¹ * W (t⁻¹ • y)‖ ≤ ‖B / (t + d) ^ 2‖
    rw [Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr (pow_nonneg ht'.1.le 4))
      (hW _ hty)), Real.norm_of_nonneg (div_nonneg hB (sq_nonneg _))]
    exact hpoint t ht'
  have hcompare :
      (∫ t in (0 : ℝ)..1, (t ^ 4)⁻¹ * W (t⁻¹ • y)) ≤
        ∫ t in (0 : ℝ)..1, B / (t + d) ^ 2 := by
    apply intervalIntegral.integral_mono_on (by norm_num) hkernel hmajorant
    intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | ht0
    · simpa using div_nonneg hB (sq_nonneg d)
    · exact hpoint t ⟨ht0, ht.2⟩
  have hzero : (0 : ℝ) ∉ Set.uIcc d (1 + d) := by
    rw [Set.uIcc_of_le (by linarith : d ≤ 1 + d)]
    intro h
    exact (not_le_of_gt hd) h.1
  have hexact : (∫ t in (0 : ℝ)..1, B / (t + d) ^ 2) =
      B * (d⁻¹ - (1 + d)⁻¹) := by
    calc
      _ = B * ∫ t in (0 : ℝ)..1, (t + d) ^ (-2 : ℤ) := by
        simp only [zpow_neg, zpow_ofNat, div_eq_mul_inv, intervalIntegral.integral_const_mul]
      _ = B * ∫ t in d..(1 + d), t ^ (-2 : ℤ) := by
        simpa only [zero_add] using congrArg (fun q : ℝ ↦ B * q)
          (intervalIntegral.integral_comp_add_right
            (f := fun t : ℝ ↦ t ^ (-2 : ℤ)) (a := 0) (b := 1) d)
      _ = _ := by
        rw [integral_zpow (Or.inr ⟨by norm_num, hzero⟩)]
        norm_num only [Int.reduceAdd, Int.cast_neg, Int.cast_ofNat, zpow_neg, zpow_ofNat]
        cas
  refine ⟨hkernel, ?_⟩
  calc
    weightedPoincareRayKernel W y ≤ d ^ 2 * (B * (d⁻¹ - (1 + d)⁻¹)) :=
      mul_le_mul_of_nonneg_left (hcompare.trans_eq hexact) (sq_nonneg d)
    _ ≤ d ^ 2 * (B * d⁻¹) := by
      gcongr
      exact sub_le_self _ (inv_nonneg.mpr (by positivity))
    _ = A / ‖y‖ := by
      change d ^ 2 * (A / d ^ 2 * d⁻¹) = A / d
      cas using hd.ne'

/-- The singular-quartic coefficient bound suffices for the exact core ray
moment on any bounded half-ball. No vanishing of the coefficient is assumed. -/
theorem integrableOn_ray_kernel_of_singular_quartic_bound
    (W : (ℝ^2 → ℝ)) (A R : ℝ) (hA : 0 ≤ A) (hWmeas : Measurable W)
    (hW : ∀ x ∈ H₊, 0 ≤ W x)
    (hbound : ∀ x ∈ H₊, x ≠ 0 →
      W x ≤ A / (‖x‖ ^ 2 * (1 + ‖x‖) ^ 2)) :
    IntegrableOn (weightedPoincareRayKernel W)
      (H₊ ∩ Metric.ball (0 : (ℝ^2)) R) := by
  let f : (ℝ^2 → ℝ) := H₊.indicator (weightedPoincareRayKernel W)
  have hfmeas : Measurable f :=
    (measurable_weightedPoincareRayKernel hWmeas).indicator
      (measurableSet_coordinateClosedHalfSpace (0 : Fin 2))
  have hi : IntegrableOn f (Metric.ball (0 : (ℝ^2)) R) := by
    refine integrableOn_ball_of_norm_le_rpow (C := A) (α := 1)
      (by simp) (by norm_num) ?_ hfmeas.aestronglyMeasurable
    filter_upwards [] with y
    by_cases hy : y ∈ H₊
    · change ‖H₊.indicator (weightedPoincareRayKernel W) y‖ ≤ _
      rw [Set.indicator_of_mem hy,
        Real.norm_of_nonneg (weightedPoincareRayKernel_nonneg hW hy)]
      by_cases hy0 : y = (0 : (ℝ^2))
      · simp [hy0]
      · simpa only [Real.rpow_neg_one, div_eq_mul_inv] using
          (ray_integrable_and_kernel_le_of_singular_quartic_bound
            W A hA hWmeas hW hbound y hy hy0).2
    · change ‖H₊.indicator (weightedPoincareRayKernel W) y‖ ≤ _
      rw [Set.indicator_of_notMem hy, norm_zero]
      exact mul_nonneg hA (Real.rpow_nonneg (norm_nonneg _) _)
  exact (integrableOn_indicator_iff
    (measurableSet_coordinateClosedHalfSpace (0 : Fin 2)).nullMeasurableSet).1 hi

end SobolevSpace.Weighted
