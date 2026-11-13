/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import PDE.Analysis.Integration.BumpMoments.NormalizedPulse.Transition

import CAS.ExactTactic

/-!
# The two normalized pulses in the scalar gate construction

The normalized glue-product density is translated to the intervals
`(100, 105)` and `(200, 205)`, with width five. Translation and dilation of
Lebesgue measure preserve the normalized masses. The first moment
of the density gives the exact pulse means `205 / 2` and `405 / 2`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PDE.Analysis.NormalizedPulse
open scoped ContDiff

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile

private theorem contDiff_shifted_density (a : ℝ) :
    ContDiff ℝ ∞ (fun y : ℝ ↦ density ((y - a) / 5) / 5) :=
  (contDiff_density.comp ((contDiff_id.sub contDiff_const).div_const 5)).div_const 5

private theorem support_shifted_density (a : ℝ) :
    Function.support (fun y : ℝ ↦ density ((y - a) / 5) / 5) = Ioo a (a + 5) := by
  ext y
  change density ((y - a) / 5) / 5 ≠ 0 ↔ a < y ∧ y < a + 5
  have hdiv : density ((y - a) / 5) / 5 ≠ 0 ↔ density ((y - a) / 5) ≠ 0 :=
    ⟨fun h ↦ (div_ne_zero_iff.mp h).1, fun h ↦ div_ne_zero h (by norm_num)⟩
  rw [hdiv]
  change (y - a) / 5 ∈ Function.support density ↔ a < y ∧ y < a + 5
  rw [support_density, mem_Ioo]
  constructor
  · intro h
    constructor <;> linarith [h.1, h.2]
  · intro h
    constructor <;> linarith [h.1, h.2]

private theorem hasCompactSupport_shifted_density (a : ℝ) :
    HasCompactSupport (fun y : ℝ ↦ density ((y - a) / 5) / 5) := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Icc a (a + 5)) isCompact_Icc
  rw [support_shifted_density]
  exact Ioo_subset_Icc_self

private theorem integral_shifted_density (a : ℝ) :
    (∫ y : ℝ, density ((y - a) / 5) / 5) = 1 := by
  rw [integral_div, integral_sub_right_eq_self (μ := volume) (fun y : ℝ ↦ density (y / 5)) a,
    Measure.integral_comp_div, integral_density]
  norm_num

private theorem integral_mul_shifted_density (a : ℝ) :
    (∫ y : ℝ, y * (density ((y - a) / 5) / 5)) = a + 5 / 2 := by
  have hmoment : (∫ s : ℝ, (5 * s + a) * density s) = 5 * (1 / 2) + a := by
    simp_rw [add_mul, mul_assoc]
    rw [integral_add (integrable_mul_density.const_mul 5) (integrable_density.const_mul a),
      integral_const_mul, integral_const_mul, integral_mul_density, integral_density]
    cas
  calc
    (∫ y : ℝ, y * (density ((y - a) / 5) / 5)) =
        (∫ y : ℝ, (5 * ((y - a) / 5) + a) * density ((y - a) / 5)) / 5 := by
      rw [← integral_div]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y ↦ by cas
    _ = (|(5 : ℝ)| • ∫ s : ℝ, (5 * s + a) * density s) / 5 := by
      rw [integral_sub_right_eq_self (μ := volume)
        (fun y : ℝ ↦ (5 * (y / 5) + a) * density (y / 5)) a,
        Measure.integral_comp_div (fun s : ℝ ↦ (5 * s + a) * density s) 5]
    _ = a + 5 / 2 := by
      rw [hmoment]
      simp only [abs_of_pos (by norm_num : (0 : ℝ) < 5), smul_eq_mul]
      cas

/-- The normalized width-five pulse supported between 100 and 105. -/
def qMinus (y : ℝ) : ℝ := density ((y - 100) / 5) / 5

/-- The normalized width-five pulse supported between 200 and 205. -/
def qPlus (y : ℝ) : ℝ := density ((y - 200) / 5) / 5

/-- The first translated pulse is globally smooth. -/
theorem contDiff_qMinus : ContDiff ℝ ∞ qMinus := contDiff_shifted_density 100

/-- The second translated pulse is globally smooth. -/
theorem contDiff_qPlus : ContDiff ℝ ∞ qPlus := contDiff_shifted_density 200

/-- The first pulse is nonnegative everywhere. -/
theorem qMinus_nonneg (y : ℝ) : 0 ≤ qMinus y :=
  div_nonneg (density_nonneg _) (by norm_num)

/-- The second pulse is nonnegative everywhere. -/
theorem qPlus_nonneg (y : ℝ) : 0 ≤ qPlus y :=
  div_nonneg (density_nonneg _) (by norm_num)

/-- The nonzero set of the first pulse is exactly the open interval `(100, 105)`. -/
theorem support_qMinus : Function.support qMinus = Ioo 100 105 := by
  change Function.support (fun y : ℝ ↦ density ((y - 100) / 5) / 5) = _
  convert support_shifted_density 100 using 1
  norm_num

/-- The nonzero set of the second pulse is exactly the open interval `(200, 205)`. -/
theorem support_qPlus : Function.support qPlus = Ioo 200 205 := by
  change Function.support (fun y : ℝ ↦ density ((y - 200) / 5) / 5) = _
  convert support_shifted_density 200 using 1
  norm_num

/-- The first pulse has compact support. -/
theorem hasCompactSupport_qMinus : HasCompactSupport qMinus :=
  hasCompactSupport_shifted_density 100

/-- The second pulse has compact support. -/
theorem hasCompactSupport_qPlus : HasCompactSupport qPlus :=
  hasCompactSupport_shifted_density 200

/-- The first pulse is Lebesgue integrable. -/
theorem integrable_qMinus : Integrable qMinus :=
  contDiff_qMinus.continuous.integrable_of_hasCompactSupport hasCompactSupport_qMinus

/-- The second pulse is Lebesgue integrable. -/
theorem integrable_qPlus : Integrable qPlus :=
  contDiff_qPlus.continuous.integrable_of_hasCompactSupport hasCompactSupport_qPlus

/-- The first pulse has unit mass. -/
theorem integral_qMinus : (∫ y : ℝ, qMinus y) = 1 := integral_shifted_density 100

/-- The second pulse has unit mass. -/
theorem integral_qPlus : (∫ y : ℝ, qPlus y) = 1 := integral_shifted_density 200

/-- Multiplication of the first pulse by the coordinate remains integrable. -/
theorem integrable_mul_qMinus : Integrable (fun y : ℝ ↦ y * qMinus y) :=
  (continuous_id.mul contDiff_qMinus.continuous).integrable_of_hasCompactSupport
    (hasCompactSupport_qMinus.mul_left (f := fun y : ℝ ↦ y))

/-- Multiplication of the second pulse by the coordinate remains integrable. -/
theorem integrable_mul_qPlus : Integrable (fun y : ℝ ↦ y * qPlus y) :=
  (continuous_id.mul contDiff_qPlus.continuous).integrable_of_hasCompactSupport
    (hasCompactSupport_qPlus.mul_left (f := fun y : ℝ ↦ y))

/-- The mean of the first normalized pulse is exactly 102.5. -/
theorem integral_mul_qMinus : (∫ y : ℝ, y * qMinus y) = 205 / 2 := by
  change (∫ y : ℝ, y * (density ((y - 100) / 5) / 5)) = _
  rw [integral_mul_shifted_density]
  norm_num

/-- The mean of the second normalized pulse is exactly 202.5. -/
theorem integral_mul_qPlus : (∫ y : ℝ, y * qPlus y) = 405 / 2 := by
  change (∫ y : ℝ, y * (density ((y - 200) / 5) / 5)) = _
  rw [integral_mul_shifted_density]
  norm_num

end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
