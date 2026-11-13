/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.WeakDerivative.Euclidean
public import PDE.Spaces.Sobolev.Calculus.Slicing.FundamentalTheorem
public import PDE.Spaces.Sobolev.Inequalities.Morrey.FiniteExponent.OneDimensional.UniformBound
public import PDE.Spaces.Sobolev.Calculus.Slicing.LineRepresentative.WeakDerivative

/-!
# Pointwise bounds from weak derivatives on the line

The local weak fundamental theorem gives the interval integral identity for
a continuous representative with a locally integrable weak derivative.
No global `L¹` assumption on the derivative is needed.

Hölder's inequality then controls the oscillation by the weak derivative's
`Lᵖ` seminorm. A unit-interval average gives the global pointwise bound
`|f(x)| ≤ ‖f‖ₚ + ‖g‖ₚ` for `1 < p ≤ ∞` and weak derivative `g`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Common
open scoped ENNReal

namespace PDE.Analysis.Evolution.HasWeakTimeDerivativeOn

/-- Morrey's oscillation bound for a continuous representative and its weak
derivative, without classical differentiability. -/
theorem enorm_sub_le_eLpNorm_mul_rpow {f g : ℝ → ℝ}
    (hweak : HasWeakTimeDerivativeOn univ f g) (hf : Continuous f)
    {p : ℝ≥0∞} (hp : 1 < p) (x y : ℝ) :
    ‖f y - f x‖ₑ ≤ eLpNorm g p volume *
      ENNReal.ofReal |y - x| ^ SobolevSpace.morreyExponent 1 p := by
  wlog hxy : x ≤ y generalizing x y with h
  · simpa only [enorm_sub_rev, abs_sub_comm] using h y x (le_of_not_ge hxy)
  have hmeas : AEStronglyMeasurable g (volume.restrict (Ioc x y)) :=
    (locallyIntegrableOn_univ.mp hweak.locallyIntegrable_g).aestronglyMeasurable.restrict
  have hrestrict : eLpNorm g p (volume.restrict (Ioc x y)) ≤ eLpNorm g p volume :=
    eLpNorm_mono_measure _ Measure.restrict_le_self
  calc
    ‖f y - f x‖ₑ = ‖∫ t in Ioc x y, g t‖ₑ := by
      rw [← hweak.intervalIntegral_eq_sub hf x y, intervalIntegral.integral_of_le hxy]
    _ ≤ ∫⁻ t in Ioc x y, ‖g t‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm g 1 (volume.restrict (Ioc x y)) :=
      (eLpNorm_one_eq_lintegral_enorm hmeas).symm
    _ ≤ eLpNorm g p (volume.restrict (Ioc x y)) *
        (volume.restrict (Ioc x y)) univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal) :=
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp.le hmeas
    _ ≤ eLpNorm g p volume *
        (volume.restrict (Ioc x y)) univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal) := by
      gcongr
    _ = eLpNorm g p volume *
        ENNReal.ofReal |y - x| ^ SobolevSpace.morreyExponent 1 p := by
      simp [Real.volume_Ioc, SobolevSpace.morreyExponent,
        abs_of_nonneg (sub_nonneg.mpr hxy)]

/-- A continuous representative with a weak derivative obeys the global
first-order Sobolev bound, expressed using extended `Lᵖ` seminorms. -/
theorem enorm_apply_le_eLpNorm_add {f g : ℝ → ℝ}
    (hweak : HasWeakTimeDerivativeOn univ f g) (hf : Continuous f)
    {p : ℝ≥0∞} (hp : 1 < p) (x : ℝ) :
    ‖f x‖ₑ ≤ eLpNorm f p volume + eLpNorm g p volume := by
  obtain ⟨y, hy, hbase⟩ := SobolevSpace.exists_Icc_enorm_le_eLpNorm hf hp.le x
  have hdist : |y - x| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hy.1)]
    exact sub_le_iff_le_add.mpr (by simpa only [add_comm] using hy.2)
  have hosc := hweak.enorm_sub_le_eLpNorm_mul_rpow hf hp x y
  have hpow : ENNReal.ofReal |y - x| ^ SobolevSpace.morreyExponent 1 p ≤ 1 := by
    simpa using ENNReal.rpow_le_rpow (ENNReal.ofReal_le_one.mpr hdist)
      (SobolevSpace.morreyExponent_one_pos hp).le
  have hosc' : ‖f x - f y‖ₑ ≤ eLpNorm g p volume := by
    rw [enorm_sub_rev]
    calc
      _ ≤ _ := hosc
      _ ≤ eLpNorm g p volume * 1 := by gcongr
      _ = _ := mul_one _
  calc
    ‖f x‖ₑ = ‖f y + (f x - f y)‖ₑ := by rw [add_sub_cancel]
    _ ≤ ‖f y‖ₑ + ‖f x - f y‖ₑ := enorm_add_le _ _
    _ ≤ _ := add_le_add hbase hosc'

/-- Finite `Lᵖ` norms of a continuous function and its weak derivative control
every pointwise value, with no compact-support assumption. -/
theorem norm_apply_le_eLpNorm_toReal_add {f g : ℝ → ℝ}
    (hweak : HasWeakTimeDerivativeOn univ f g) (hf : Continuous f)
    {p : ℝ≥0∞} (hp : 1 < p) (hbase : MemLp f p volume)
    (hderiv : MemLp g p volume) (x : ℝ) :
    ‖f x‖ ≤ (eLpNorm f p volume).toReal + (eLpNorm g p volume).toReal := by
  have h := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hbase.eLpNorm_ne_top, hderiv.eLpNorm_ne_top⟩)
    (hweak.enorm_apply_le_eLpNorm_add hf hp x)
  simpa only [ENNReal.toReal_add hbase.eLpNorm_ne_top hderiv.eLpNorm_ne_top,
    toReal_enorm] using h

end PDE.Analysis.Evolution.HasWeakTimeDerivativeOn
