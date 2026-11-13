/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.RadialPower
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Square integrability from near-origin and far-field radial bounds

An inverse-radius bound near zero and a bound by `C / ‖x‖ ^ b` at infinity give square
integrability when the real dimension exceeds two and is less than `2 * b`. The
origin's assigned value is immaterial, and the estimates may use distinct constants
in the two regions. The cases `b = 2` and `b = 3` cover dimensions three, and three
through five.
-/

@[expose] public noncomputable section

namespace MeasureTheory

open Metric Set Filter
open scoped ENNReal

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup G] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Near-origin inverse-radius and far-field inverse-power bounds give finite energy
when the real dimension exceeds two and is less than twice the far-field exponent. -/
theorem integrable_norm_sq_of_near_inv_radius_far_inv_pow {f : E → G} {b : ℕ}
    (hmeas : AEStronglyMeasurable f μ)
    (hnearDim : (2 : ℝ) < Module.finrank ℝ E) (hfarDim : (Module.finrank ℝ E : ℝ) < 2 * b)
    {A C : ℝ} (hC : 0 ≤ C)
    (hnearBound : ∀ x : E, x ≠ 0 → ‖x‖ ≤ 1 → ‖f x‖ ≤ A / ‖x‖)
    (hfarBound : ∀ x : E, x ≠ 0 → 1 ≤ ‖x‖ → ‖f x‖ ≤ C / ‖x‖ ^ b) :
    Integrable (fun x ↦ ‖f x‖ ^ 2) μ := by
  have hdim : 2 < Module.finrank ℝ E := by exact_mod_cast hnearDim
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hmeas2 : AEStronglyMeasurable (fun x ↦ ‖f x‖ ^ 2) μ := hmeas.norm.pow 2
  have hnear : IntegrableOn (fun x ↦ ‖f x‖ ^ 2) (ball 0 1) μ := by
    apply integrableOn_ball_of_norm_le_rpow (C := A ^ 2) (α := 2)
      (by omega) hnearDim ?_ hmeas2
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet,
      ae_restrict_of_ae (μ.ae_ne (0 : E))] with x hx hzero
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hzero
    have hsmall : ‖x‖ ≤ 1 := (by simpa only [mem_ball, dist_zero_right] using hx :
      ‖x‖ < 1).le
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.rpow_neg (by positivity),
      Real.rpow_two]
    calc
      _ ≤ (A / ‖x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hnearBound x hzero hsmall) 2
      _ = A ^ 2 * (‖x‖ ^ 2)⁻¹ := by ring
  have hfar : IntegrableOn (fun x ↦ ‖f x‖ ^ 2) (ball (0 : E) 1)ᶜ μ := by
    apply (((integrable_one_add_norm (μ := μ) hfarDim).const_mul
      ((2 ^ b * C) ^ 2)).integrableOn).mono' hmeas2.restrict
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet.compl,
      ae_restrict_of_ae (μ.ae_ne (0 : E))] with x hx hzero
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hzero
    have hlarge : 1 ≤ ‖x‖ := by
      simpa only [mem_compl_iff, mem_ball, dist_zero_right, not_lt] using hx
    have hpos : 0 < 1 + ‖x‖ := by positivity
    have hbound : ‖f x‖ ≤ (2 ^ b * C) / (1 + ‖x‖) ^ b := by
      refine (hfarBound x hzero hlarge).trans ?_
      apply (div_le_div_iff₀ (pow_pos hr b) (pow_pos hpos b)).mpr
      calc
        C * (1 + ‖x‖) ^ b ≤ C * (2 * ‖x‖) ^ b :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hpos.le (by linarith) b) hC
        _ = 2 ^ b * C * ‖x‖ ^ b := by rw [mul_pow]; ring
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ ((2 ^ b * C) / (1 + ‖x‖) ^ b) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hbound 2
      _ = (2 ^ b * C) ^ 2 * (1 + ‖x‖) ^ (-(2 * b : ℝ)) := by
        rw [Real.rpow_neg hpos.le, show (2 * b : ℝ) = (b : ℝ) * 2 by ring,
          Real.rpow_mul hpos.le, Real.rpow_natCast, Real.rpow_two, div_pow, div_eq_mul_inv]
  simpa only [union_compl_self, integrableOn_univ] using hnear.union hfar

/-- The two radial bounds give a whole-space `L²` class, including through the origin. -/
theorem memLp_two_of_near_inv_radius_far_inv_pow {f : E → G} {b : ℕ}
    (hmeas : AEStronglyMeasurable f μ)
    (hnearDim : (2 : ℝ) < Module.finrank ℝ E) (hfarDim : (Module.finrank ℝ E : ℝ) < 2 * b)
    {A C : ℝ} (hC : 0 ≤ C)
    (hnearBound : ∀ x : E, x ≠ 0 → ‖x‖ ≤ 1 → ‖f x‖ ≤ A / ‖x‖)
    (hfarBound : ∀ x : E, x ≠ 0 → 1 ≤ ‖x‖ → ‖f x‖ ≤ C / ‖x‖ ^ b) :
    MemLp f 2 μ := by
  apply (integrable_norm_rpow_iff hmeas
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).mp
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    integrable_norm_sq_of_near_inv_radius_far_inv_pow hmeas hnearDim hfarDim hC
      hnearBound hfarBound

/-- Inverse-square decay at infinity suffices in dimension three. -/
theorem memLp_two_of_near_inv_radius_far_inv_sq {f : E → G}
    (hmeas : AEStronglyMeasurable f μ)
    (hnearDim : (2 : ℝ) < Module.finrank ℝ E) (hfarDim : (Module.finrank ℝ E : ℝ) < 4)
    {A C : ℝ} (hC : 0 ≤ C)
    (hnearBound : ∀ x : E, x ≠ 0 → ‖x‖ ≤ 1 → ‖f x‖ ≤ A / ‖x‖)
    (hfarBound : ∀ x : E, x ≠ 0 → 1 ≤ ‖x‖ → ‖f x‖ ≤ C / ‖x‖ ^ 2) :
    MemLp f 2 μ :=
  memLp_two_of_near_inv_radius_far_inv_pow hmeas hnearDim (by push_cast; linarith) hC
    hnearBound hfarBound

/-- Inverse-cubic decay at infinity suffices in dimensions three through five. -/
theorem memLp_two_of_near_inv_radius_far_inv_cube {f : E → G}
    (hmeas : AEStronglyMeasurable f μ)
    (hnearDim : (2 : ℝ) < Module.finrank ℝ E) (hfarDim : (Module.finrank ℝ E : ℝ) < 6)
    {A C : ℝ} (hC : 0 ≤ C)
    (hnearBound : ∀ x : E, x ≠ 0 → ‖x‖ ≤ 1 → ‖f x‖ ≤ A / ‖x‖)
    (hfarBound : ∀ x : E, x ≠ 0 → 1 ≤ ‖x‖ → ‖f x‖ ≤ C / ‖x‖ ^ 3) :
    MemLp f 2 μ :=
  memLp_two_of_near_inv_radius_far_inv_pow hmeas hnearDim (by push_cast; linarith) hC
    hnearBound hfarBound

end MeasureTheory
