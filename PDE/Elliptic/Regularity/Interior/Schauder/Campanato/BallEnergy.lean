/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Campanato.Quadratic
public import PDE.Common.Euclidean
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Restriction of mean energy to smaller balls

Nonnegativity bounds the integral on a smaller ball by the outer integral.
The normalization costs precisely the volume ratio `(R/r)^n`. The minimizing
property of the average gives the same bound for quadratic mean oscillation.

The comparison step of Campanato's method is proved once, for arbitrary centers
(`setAverage_norm_sub_sq_le_of_comparison_decay`) and for oscillations
(`setAverage_oscillation_sq_le_of_comparison_decay`): a decay estimate for a
comparison field `e` passes to a field `d` up to the mean-square error of `d - e`
on the outer ball.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

namespace PDE.Elliptic.Regularity.Campanato

variable {n : ℕ} [Fact (0 < n)]

/-- Restricting mean-square energy to a smaller concentric ball costs the
volume ratio. There is no continuity assumption on the field. -/
theorem setAverage_norm_sq_le_of_radius_le
    {z : ℝ^n} {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    {f : ℝ^n → ℝ} (hf : MemLp f 2 (volume.restrict (ball z R))) :
    (⨍ x in ball z r, ‖f x‖ ^ 2) ≤ (R / r) ^ n * ⨍ x in ball z R, ‖f x‖ ^ 2 := by
  let : NeZero n := ⟨(Fact.out : 0 < n).ne'⟩
  have hR := hr.trans_le hrR
  have hv : 0 < volume.real (ball z r) :=
    ENNReal.toReal_pos (measure_ball_pos volume z hr).ne' measure_ball_lt_top.ne
  have hvol : volume.real (ball z R) = (R / r) ^ n * volume.real (ball z r) := by
    simp only [measureReal_def, Measure.addHaar_ball volume z hR.le,
      Measure.addHaar_ball volume z hr.le, finrank_euclideanSpace_fin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hR.le n),
      ENNReal.toReal_ofReal (pow_nonneg hr.le n), div_pow]
    field_simp
  have hmono : (∫ x in ball z r, ‖f x‖ ^ 2) ≤ ∫ x in ball z R, ‖f x‖ ^ 2 :=
    setIntegral_mono_set hf.norm.integrable_sq
      (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)
      (Filter.Eventually.of_forall (ball_subset_ball hrR))
  simp only [setAverage_eq, smul_eq_mul]
  calc
    _ ≤ (volume.real (ball z r))⁻¹ * ∫ x in ball z R, ‖f x‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr hv.le)
    _ = _ := by rw [hvol]; field_simp

/-- Mean-square oscillation obeys the volume-ratio restriction bound, because
the inner average improves on the outer average as a centering constant. -/
theorem setAverage_oscillation_sq_le_of_radius_le
    {z : ℝ^n} {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    {f : ℝ^n → ℝ} (hf : MemLp f 2 (volume.restrict (ball z R))) :
    (⨍ x in ball z r, ‖f x - ⨍ y in ball z r, f y‖ ^ 2) ≤
      (R / r) ^ n * ⨍ x in ball z R, ‖f x - ⨍ y in ball z R, f y‖ ^ 2 := by
  have : IsFiniteMeasure (volume.restrict (ball z R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  refine (setAverage_norm_sub_average_sq_le
    (hf.mono_measure (Measure.restrict_mono (ball_subset_ball hrR) le_rfl))
    (⨍ y in ball z R, f y)).trans ?_
  exact setAverage_norm_sq_le_of_radius_le hr hrR (hf.sub (memLp_const _))

/-- **Comparison step for mean-square decay.** Let `0 < r ≤ R`, `κ ≥ 0`, and let `d`
and `e` be square integrable on `ball z R` with mean-square error
`⨍_{B_R} |d - e|² ≤ E`. If the mean-square deviation of `e` from `c'` on `ball z r`
is at most `κ` times its deviation from `c` on `ball z R`, then the deviation of
`d` from `c'` on `ball z r` is at most `4 κ` times its deviation from `c` on
`ball z R`, plus `(2 (R / r) ^ n + 4 κ) E`. The centers `c` and `c'` are arbitrary
real numbers. -/
theorem setAverage_norm_sub_sq_le_of_comparison_decay
    {z : ℝ^n} {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    {d e : ℝ^n → ℝ} (hd : MemLp d 2 (volume.restrict (ball z R)))
    (he : MemLp e 2 (volume.restrict (ball z R)))
    {κ E : ℝ} (hκ : 0 ≤ κ) {c c' : ℝ}
    (herror : (⨍ x in ball z R, ‖d x - e x‖ ^ 2) ≤ E)
    (hdecay : (⨍ x in ball z r, ‖e x - c'‖ ^ 2) ≤
      κ * ⨍ x in ball z R, ‖e x - c‖ ^ 2) :
    (⨍ x in ball z r, ‖d x - c'‖ ^ 2) ≤
      4 * κ * (⨍ x in ball z R, ‖d x - c‖ ^ 2) + (2 * (R / r) ^ n + 4 * κ) * E := by
  have hsmall := (setAverage_norm_sq_le_of_radius_le hr hrR (hd.sub he)).trans
    (mul_le_mul_of_nonneg_left herror
      (pow_nonneg (div_nonneg (hr.trans_le hrR).le hr.le) n))
  have hinner := setAverage_norm_sub_sq_le
    (hd.mono_measure (Measure.restrict_mono (ball_subset_ball hrR) le_rfl))
    (he.mono_measure (Measure.restrict_mono (ball_subset_ball hrR) le_rfl)) c'
  have houter := setAverage_norm_sub_sq_le he hd c
  simp only [norm_sub_rev (e _) (d _)] at houter
  have hscaled := mul_le_mul_of_nonneg_left houter hκ
  have hscaledError := mul_le_mul_of_nonneg_left herror hκ
  simp only [Pi.sub_apply] at hsmall
  nlinarith only [hsmall, hinner, hscaled, hdecay, hscaledError]

/-- **Comparison step for quadratic oscillation decay.** Let `0 < r ≤ R`, `κ ≥ 0`,
and let `d` and `e` be square integrable on `ball z R` with
`⨍_{B_R} |d - e|² ≤ E`. If the mean-square oscillation of `e` on `ball z r` is at
most `κ` times its mean-square deviation on `ball z R` from the average of `d`
there, then the oscillation of `d` on `ball z r` is at most `4 κ` times its
oscillation on `ball z R`, plus `(2 (R / r) ^ n + 4 κ) E`. -/
theorem setAverage_oscillation_sq_le_of_comparison_decay
    {z : ℝ^n} {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    {d e : ℝ^n → ℝ} (hd : MemLp d 2 (volume.restrict (ball z R)))
    (he : MemLp e 2 (volume.restrict (ball z R)))
    {κ E : ℝ} (hκ : 0 ≤ κ)
    (herror : (⨍ x in ball z R, ‖d x - e x‖ ^ 2) ≤ E)
    (hdecay : (⨍ x in ball z r, ‖e x - ⨍ y in ball z r, e y‖ ^ 2) ≤
      κ * ⨍ x in ball z R, ‖e x - ⨍ y in ball z R, d y‖ ^ 2) :
    (⨍ x in ball z r, ‖d x - ⨍ y in ball z r, d y‖ ^ 2) ≤
      4 * κ * (⨍ x in ball z R, ‖d x - ⨍ y in ball z R, d y‖ ^ 2) +
        (2 * (R / r) ^ n + 4 * κ) * E :=
  (setAverage_norm_sub_average_sq_le
    (hd.mono_measure (Measure.restrict_mono (ball_subset_ball hrR) le_rfl)) _).trans
    (setAverage_norm_sub_sq_le_of_comparison_decay hr hrR hd he hκ herror hdecay)

end PDE.Elliptic.Regularity.Campanato
