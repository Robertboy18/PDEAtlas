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

end PDE.Elliptic.Regularity.Campanato
