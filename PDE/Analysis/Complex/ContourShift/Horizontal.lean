/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Horizontal contour shifts

For a Banach-valued entire function, Mathlib's Cauchy theorem on rectangles
identifies two horizontal line integrals once the vertical boundary error
tends to zero. Integrability is required only on the two horizontal lines.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Complex
open scoped Topology

namespace PDE.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Horizontal contour shifting from the Cauchy rectangle identity and
vanishing vertical boundary error. -/
theorem integral_horizontal_shift_of_tendsto
    {f : ℂ → E} (hf : Differentiable ℂ f) (c : ℝ)
    (h₀ : Integrable (fun x : ℝ ↦ f x))
    (hc : Integrable (fun x : ℝ ↦ f (x + c * I)))
    (hvertical : Tendsto (fun T : ℝ ↦
      I • (∫ y : ℝ in (0 : ℝ)..c, f (T + y * I)) -
        I • (∫ y : ℝ in (0 : ℝ)..c, f (-T + y * I))) atTop (𝓝 0)) :
    (∫ x : ℝ, f (x + c * I)) = ∫ x : ℝ, f x := by
  have hrect (T : ℝ) :
      (∫ x : ℝ in -T..T, f (x + c * I)) =
        (∫ x : ℝ in -T..T, f x) +
          (I • (∫ y : ℝ in (0 : ℝ)..c, f (T + y * I)) -
            I • (∫ y : ℝ in (0 : ℝ)..c, f (-T + y * I))) := by
    have h := integral_boundary_rect_eq_zero_of_differentiableOn f (-T)
      (T + c * I) hf.differentiableOn
    simp only [neg_im, ofReal_im, neg_zero, ofReal_zero, zero_mul, add_zero,
      neg_re, ofReal_re, add_re, mul_re, I_re, mul_zero, I_im, tsub_zero,
      add_im, mul_im, mul_one, zero_add, ofReal_neg] at h
    symm
    apply eq_of_sub_eq_zero
    convert h using 1
    abel
  have htop := intervalIntegral_tendsto_integral hc
    tendsto_neg_atTop_atBot tendsto_id
  have hbottom := intervalIntegral_tendsto_integral h₀
    tendsto_neg_atTop_atBot tendsto_id
  have hlimit := hbottom.add hvertical
  simp only [add_zero] at hlimit
  exact tendsto_nhds_unique htop (hlimit.congr fun T ↦ (hrect T).symm)

end PDE.Analysis
