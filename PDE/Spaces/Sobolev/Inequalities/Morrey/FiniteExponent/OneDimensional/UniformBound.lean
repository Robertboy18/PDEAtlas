/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Morrey.FiniteExponent.OneDimensional.Estimate
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# A uniform bound from one-dimensional first-order Sobolev norms

A unit interval contains a point where the function is bounded by its global
`Lᵖ` norm. The one-dimensional Morrey estimate controls the oscillation
between that point and the endpoint. Consequently
`|f(x)| ≤ ‖f‖ₚ + ‖f'‖ₚ` for `1 < p ≤ ∞`.

The function need not have compact support. The finite-norm statement applies
to a `C¹` representative with the function and its derivative in `Lᵖ`.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace

open MeasureTheory Set
open scoped ENNReal

/-- A unit interval contains a point controlled by the global `Lᵖ` seminorm. -/
theorem exists_Icc_enorm_le_eLpNorm {f : ℝ → ℝ} (hf : Continuous f)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (x : ℝ) :
    ∃ y ∈ Icc x (x + 1), ‖f y‖ₑ ≤ eLpNorm f p volume := by
  have hvolume : volume (Icc x (x + 1)) = 1 := by
    simp [Real.volume_Icc]
  have hmeas : AEStronglyMeasurable f (volume.restrict (Icc x (x + 1))) :=
    hf.aestronglyMeasurable
  obtain ⟨y, hy, hmean⟩ := exists_le_setLAverage
    (by rw [hvolume]; exact one_ne_zero)
    (by rw [hvolume]; exact ENNReal.one_ne_top) hf.enorm.aemeasurable
  refine ⟨y, hy, hmean.trans ?_⟩
  rw [setLAverage_eq, ← eLpNorm_one_eq_lintegral_enorm hmeas, hvolume, div_one]
  have hcompare := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hmeas
  rw [Measure.restrict_apply_univ, hvolume, ENNReal.one_rpow, mul_one] at hcompare
  exact hcompare.trans (eLpNorm_mono_measure _ Measure.restrict_le_self)

/-- The global first-order Sobolev bound on the line, without a compact-support
assumption and with extended `Lᵖ` seminorms. -/
theorem enorm_apply_le_eLpNorm_add_eLpNorm_deriv {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) {p : ℝ≥0∞} (hp : 1 < p) (x : ℝ) :
    ‖f x‖ₑ ≤ eLpNorm f p volume + eLpNorm (deriv f) p volume := by
  obtain ⟨y, hy, hbase⟩ := exists_Icc_enorm_le_eLpNorm hf.continuous hp.le x
  have hdist : |y - x| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hy.1)]
    exact sub_le_iff_le_add.mpr (by simpa only [add_comm] using hy.2)
  have hosc := enorm_sub_le_eLpNorm_deriv_mul_rpow f hf hp x y
  have hpow : ENNReal.ofReal |y - x| ^ morreyExponent 1 p ≤ 1 := by
    simpa using ENNReal.rpow_le_rpow (ENNReal.ofReal_le_one.mpr hdist)
      (morreyExponent_one_pos hp).le
  have hosc' : ‖f x - f y‖ₑ ≤ eLpNorm (deriv f) p volume := by
    rw [enorm_sub_rev]
    calc
      _ ≤ _ := hosc
      _ ≤ eLpNorm (deriv f) p volume * 1 := by gcongr
      _ = _ := mul_one _
  calc
    ‖f x‖ₑ = ‖f y + (f x - f y)‖ₑ := by rw [add_sub_cancel]
    _ ≤ ‖f y‖ₑ + ‖f x - f y‖ₑ := enorm_add_le _ _
    _ ≤ _ := add_le_add hbase hosc'

/-- A `C¹` function and its derivative in `Lᵖ(ℝ)`, `p > 1`, control its value
at every point, including when the function has noncompact support. -/
theorem norm_apply_le_eLpNorm_toReal_add_deriv {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) {p : ℝ≥0∞} (hp : 1 < p)
    (hbase : MemLp f p volume) (hderiv : MemLp (deriv f) p volume) (x : ℝ) :
    ‖f x‖ ≤ (eLpNorm f p volume).toReal + (eLpNorm (deriv f) p volume).toReal := by
  have h := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hbase.eLpNorm_ne_top, hderiv.eLpNorm_ne_top⟩)
    (enorm_apply_le_eLpNorm_add_eLpNorm_deriv hf hp x)
  simpa only [ENNReal.toReal_add hbase.eLpNorm_ne_top hderiv.eLpNorm_ne_top,
    toReal_enorm] using h

end SobolevSpace
