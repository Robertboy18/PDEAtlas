/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import CAS.ExactTactic

/-!
# The localized KdV profile

The square of the hyperbolic secant is represented using exponentials for the
checked scalar derivative calculation. The cosine-hyperbolic identity, positivity,
crest value and decay identify it as a localized solitary-wave profile.
-/

@[expose] public section

noncomputable section

namespace KdVEquation

open Filter
open scoped Topology ContDiff

/-- The squared hyperbolic secant, in exponential form for exact calculation. -/
def sechSq (z : ℝ) : ℝ :=
  4 * Real.exp (2 * z) / (1 + Real.exp (2 * z)) ^ 2

/-- The exponential denominator of the solitary-wave profile never vanishes. -/
theorem sechSq_denominator_ne_zero (z : ℝ) : 1 + Real.exp (2 * z) ≠ 0 :=
  ne_of_gt (by positivity)

/-- The exponential profile is the square of the hyperbolic secant. -/
theorem sechSq_eq_inv_cosh_sq (z : ℝ) : sechSq z = 1 / Real.cosh z ^ 2 := by
  rw [Real.cosh_eq]
  unfold sechSq
  cas

/-- The normalized solitary-wave profile is smooth everywhere. -/
theorem contDiff_sechSq : ContDiff ℝ ∞ sechSq := by
  unfold sechSq
  exact (by fun_prop : ContDiff ℝ ∞ (fun z : ℝ ↦ 4 * Real.exp (2 * z))).div
    (by fun_prop) (fun z ↦ pow_ne_zero _ (sechSq_denominator_ne_zero z))

/-- The normalized profile solves its second-order nonlinear ODE. -/
theorem sechSq_second_derivative (z : ℝ) :
    deriv (deriv sechSq) z = 4 * sechSq z - 6 * sechSq z ^ 2 := by
  cas using sechSq_denominator_ne_zero z

/-- A solitary-wave profile with arbitrary amplitude, inverse width and center. -/
def solitonProfile (amplitude scale center x : ℝ) : ℝ :=
  amplitude * sechSq (scale * (x - center))

/-- Every member of the profile family is smooth, including degenerate parameter choices. -/
theorem contDiff_solitonProfile (amplitude scale center : ℝ) :
    ContDiff ℝ ∞ (solitonProfile amplitude scale center) := by
  unfold solitonProfile
  exact contDiff_const.mul (contDiff_sechSq.comp (by fun_prop))

/-- The scaled profile equation, without dividing by the amplitude.
This identity remains valid even for zero amplitude or zero scale. -/
theorem solitonProfile_second_derivative (amplitude scale center z : ℝ) :
    deriv (deriv (solitonProfile amplitude scale center)) z =
      4 * scale ^ 2 * solitonProfile amplitude scale center z -
        6 * amplitude * scale ^ 2 * sechSq (scale * (z - center)) ^ 2 := by
  cas using sechSq_denominator_ne_zero (scale * (z - center))

/-- The normalized profile is positive at every finite point. -/
theorem sechSq_pos (z : ℝ) : 0 < sechSq z := by
  rw [sechSq_eq_inv_cosh_sq]
  positivity

/-- The normalized solitary wave has unit crest at the origin. -/
@[simp]
theorem sechSq_zero : sechSq 0 = 1 := by
  norm_num [sechSq]

/-- The normalized profile is even. -/
theorem sechSq_neg (z : ℝ) : sechSq (-z) = sechSq z := by
  simp only [sechSq_eq_inv_cosh_sq, Real.cosh_neg]

/-- The normalized profile never exceeds its crest. -/
theorem sechSq_le_one (z : ℝ) : sechSq z ≤ 1 := by
  rw [sechSq_eq_inv_cosh_sq]
  apply (div_le_one (by positivity : 0 < Real.cosh z ^ 2)).2
  nlinarith [Real.one_le_cosh z]

/-- The profile decays at the left end of the real line. -/
theorem tendsto_sechSq_atBot : Tendsto sechSq atBot (𝓝 0) := by
  have hexp : Tendsto (fun z : ℝ ↦ Real.exp (2 * z)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot (by norm_num))
  change Tendsto (fun z : ℝ ↦ 4 * Real.exp (2 * z) / (1 + Real.exp (2 * z)) ^ 2) atBot (𝓝 0)
  convert ((tendsto_const_nhds (x := (4 : ℝ))).mul hexp).div
      (((tendsto_const_nhds (x := (1 : ℝ))).add hexp).pow 2) (by norm_num) using 1
  norm_num

/-- Evenness gives decay also at the right end of the real line. -/
theorem tendsto_sechSq_atTop : Tendsto sechSq atTop (𝓝 0) := by
  simpa only [Function.comp_def, sechSq_neg] using tendsto_sechSq_atBot.comp tendsto_neg_atTop_atBot

end KdVEquation
