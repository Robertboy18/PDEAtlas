/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Deriv.CoordinateQuotient
public import PDE.Analysis.Fourier.HilbertTransform.CompactBounds

/-!
# A linear origin remainder for the Hilbert transform

Compact support and linear growth of the derivative bound the Hilbert transform
of the coordinate quotient. Principal-value cancellation then controls the original
transform's displacement from its value at zero.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace PDE.Analysis

/-- A compact C¹ input with a linear origin bound on its derivative has a
linear origin remainder in its Hilbert transform. The estimate follows by
applying the compact Lipschitz bound to the coordinate quotient. -/
theorem abs_hilbertPV_sub_zero_le_of_deriv_le_mul_abs
    {q : ℝ → ℝ} {K : ℝ≥0} {R x : ℝ}
    (hq : ContDiff ℝ 1 q) (hq0 : q 0 = 0)
    (hb : ∀ y, ‖deriv q y‖ ≤ K * |y|)
    (hs : ∀ y, R ≤ |y| → q y = 0) (hx : |x| ≤ R) :
    |hilbertPV q x - hilbertPV q 0| ≤
      ((4 + 8 * R ^ 2) * K / Real.pi) * |x| := by
  have hR : 0 ≤ R := (abs_nonneg x).trans hx
  have hqc : HasCompactSupport q := by
    apply HasCompactSupport.intro (K := Icc (-R) R) isCompact_Icc
    intro y hy
    exact hs y (le_of_not_ge fun h ↦ hy (abs_le.mp h))
  have hdc : HasCompactSupport (fun y ↦ q y / y) := by
    apply HasCompactSupport.intro (K := Icc (-R) R) isCompact_Icc
    intro y hy
    rw [hs y (le_of_not_ge fun h ↦ hy (abs_le.mp h)), zero_div]
  have hd := lipschitzWith_div_id_of_deriv_le_mul_abs hq.differentiable_one hq0 hb
  have hbound (y : ℝ) : |q y / y| ≤ 2 * (K : ℝ) * R := by
    by_cases hy : |y| ≤ R
    · have hv := hd.norm_sub_le y 0
      simp only [div_zero, sub_zero, Real.norm_eq_abs, NNReal.coe_mul, NNReal.coe_ofNat] at hv
      exact hv.trans (mul_le_mul_of_nonneg_left hy (by positivity))
    · rw [hs y (le_of_not_ge hy), zero_div, abs_zero]
      positivity
  have hh := abs_hilbertPV_le_of_lipschitzWith_of_support hd hdc hbound
    (fun y hy ↦ by rw [hs y hy, zero_div]) hx
  by_cases hx0 : x = 0
  · simp [hx0]
  rw [hilbertPV_div_id_of_differentiableAt
    (memLp_one_iff_integrable.mp (hq.continuous.memLp_of_hasCompactSupport hqc))
    hq0 (hq.differentiable_one 0) hx0 (hq.differentiable_one x), abs_div] at hh
  have hh' := (div_le_iff₀ (abs_pos.mpr hx0)).mp hh
  convert hh' using 1
  push_cast
  ring

end PDE.Analysis
