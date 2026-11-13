/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.IntegralPotential.ConjugateGrowth
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Integral potentials with linearly growing derivatives

A continuously differentiable scalar potential whose derivative has linear
growth defines a strictly Fréchet differentiable functional on `L²` of a finite
measure. Neither convexity nor a Lipschitz derivative is needed. The derivative
is the actual integral pairing with the continuous superposition operator.
The constants at zero are unrestricted.
-/

@[expose] public section

noncomputable section

open Filter Set MeasureTheory Metric
open scoped ENNReal Topology

namespace PDE.Analysis

/-- Linear growth of an actual derivative bounds the potential quadratically,
including its unrestricted value at zero. -/
theorem norm_le_quadratic_of_deriv_growth
    {G g : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ s, HasDerivAt G (g s) s)
    (hg : ∀ s, |g s| ≤ C * (1 + |s|)) (s : ℝ) :
    |G s| ≤ |G 0| + C + (2 * C) * |s| ^ 2 := by
  have hb : ∀ t ∈ closedBall (0 : ℝ) |s|, ‖g t‖ ≤ C * (1 + |s|) := by
    intro t ht
    have ht' : |t| ≤ |s| := by simpa [Real.dist_eq] using ht
    exact (hg t).trans (mul_le_mul_of_nonneg_left (by linarith : 1 + |t| ≤ 1 + |s|) hC)
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ ↦ (hd t).hasDerivWithinAt) hb (convex_closedBall (0 : ℝ) |s|)
    (by simp : (0 : ℝ) ∈ closedBall 0 |s|) (by simp : s ∈ closedBall 0 |s|)
  have hsum : |G s| ≤ |G s - G 0| + |G 0| := by
    simpa only [sub_add_cancel] using abs_add_le (G s - G 0) (G 0)
  have hq : |s| ≤ 1 + |s| ^ 2 := by nlinarith [sq_nonneg (|s| - 1)]
  have hcq := mul_le_mul_of_nonneg_left hq hC
  simp only [sub_zero, Real.norm_eq_abs] at hm
  nlinarith

end PDE.Analysis

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  {G g : ℝ → ℝ} {C : ℝ}

/-- A continuous scalar map of linear growth acts on `L²`, with a nonzero
constant offset allowed because the measure is finite. -/
theorem memLp_comp_of_linear_growth
    (hg : Continuous g) (hbound : ∀ s, |g s| ≤ C * (1 + |s|))
    (u : Lp ℝ 2 μ) : MemLp (fun x ↦ g (u x)) 2 μ := by
  apply (Lp.memLp u).comp_of_norm_le (G := fun _ ↦ g)
    (hg.measurable.comp measurable_snd) (memLp_const C)
  exact ae_of_all μ fun _ s ↦ by simpa [mul_add] using hbound s

/-- Linear growth of the derivative gives integrability of the potential on
`L²`; no normalization of its value at zero is imposed. -/
theorem integrable_potential_L2_of_deriv_growth
    (hC : 0 ≤ C) (hd : ∀ s, HasDerivAt G (g s) s)
    (hg : ∀ s, |g s| ≤ C * (1 + |s|)) (u : Lp ℝ 2 μ) :
    Integrable (fun x ↦ G (u x)) μ := by
  have hcont : Continuous G := continuous_iff_continuousAt.mpr fun s ↦ (hd s).continuousAt
  apply (Lp.memLp u).integrable_comp_of_norm_rpow_le (G := fun _ ↦ G) (by simp) (by simp)
    (hcont.measurable.comp measurable_snd) (integrable_const (|G 0| + C))
  exact ae_of_all μ fun _ s ↦ by
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofNat, Real.rpow_two] using
      PDE.Analysis.norm_le_quadratic_of_deriv_growth hC hd hg s

/-- The `L²` integral potential is continuous under a linear derivative-growth
bound. In particular, its level and sublevel sets in `L²` are closed. -/
theorem continuous_integral_L2_of_deriv_growth
    (hC : 0 ≤ C) (hd : ∀ s, HasDerivAt G (g s) s)
    (hg : ∀ s, |g s| ≤ C * (1 + |s|)) :
    Continuous (fun u : Lp ℝ 2 μ ↦ ∫ x, G (u x) ∂μ) := by
  have hcont : Continuous G := continuous_iff_continuousAt.mpr fun s ↦ (hd s).continuousAt
  apply continuous_integral_L2_of_quadratic_growth (G := fun _ ↦ G)
    (hcont.measurable.comp measurable_snd) (ae_of_all μ fun _ ↦ hcont)
    (integrable_const (|G 0| + C))
  exact ae_of_all μ fun _ s ↦
    PDE.Analysis.norm_le_quadratic_of_deriv_growth hC hd hg s

/-- The derivative of an integral potential on `L²` is its actual integral
pairing with `g(u)`. Continuity of the linearly growing derivative gives strict
Fréchet differentiability, without any uniform bound on its own derivative. -/
theorem hasStrictFDerivAt_integral_L2_of_deriv_growth
    (hC : 0 ≤ C) (hd : ∀ s, HasDerivAt G (g s) s) (hc : Continuous g)
    (hg : ∀ s, |g s| ≤ C * (1 + |s|)) (u : Lp ℝ 2 μ) :
    HasStrictFDerivAt (fun w : Lp ℝ 2 μ ↦ ∫ x, G (w x) ∂μ)
      (innerSL ℝ (Lp.superposition (fun _ ↦ g)
        (memLp_comp_of_linear_growth hc hg) u)) u := by
  have hG : ∀ s, |G s| ≤ |G 0| + C + (2 * C) * |s| ^ (2 : ℝ≥0∞).toReal := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      PDE.Analysis.norm_le_quadratic_of_deriv_growth hC hd hg
  have hg' : ∀ s, |g s| ≤ C * (1 + |s| ^ ((2 : ℝ≥0∞).toReal - 1)) := by
    simpa only [ENNReal.toReal_ofNat, show (2 : ℝ) - 1 = 1 by norm_num,
      Real.rpow_one] using hg
  convert hasStrictFDerivAt_integral_Lp_of_deriv_growth
    (q := 2) (by norm_num : 1 < (2 : ℝ≥0∞)) (by simp) hd hc hG hg' u using 1
  ext v
  rw [innerSL_apply_apply, L2.inner_def, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_superposition (fun _ : α ↦ g)
      (memLp_comp_of_linear_growth (μ := μ) hc hg) u] with x hx
  simp [hx, RCLike.inner_apply, ContinuousLinearMap.mul_apply', mul_comm]

end MeasureTheory
