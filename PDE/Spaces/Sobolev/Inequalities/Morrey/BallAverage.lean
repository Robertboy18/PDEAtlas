/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.LebesguePoints
public import PDE.Spaces.Sobolev.Inequalities.Morrey.LocalOscillation
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import CAS.ExactTactic

/-!
# Ball averages in the local Morrey estimate

The dilation factor in the local oscillation estimate combines with the `Lᵖ` norm to
give a normalized integral average. Lebesgue differentiation then makes this factor
vanish for the oscillation of a locally `Lᵖ` field about its value at almost every point.
-/

@[expose] public noncomputable section

open Filter MeasureTheory MeasureTheory.Measure Metric Set
open scoped ENNReal Topology

namespace SobolevSpace.GraphSpace.MeanScaling

/-- The scaled `Lᵖ` norm on a ball equals its normalized power mean, times the fixed
unit-ball volume factor. -/
theorem normFactor_mul_eLpNorm_eq_average
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}
    (hp₀ : p ≠ 0) (hp_top : p ≠ ∞) (x : ℝ^n) {r : ℝ} (hr : 0 < r)
    {f : ℝ^n → E} (hf : AEStronglyMeasurable f (volume.restrict (ball x r))) :
    normFactor n r p * (eLpNorm f p (volume.restrict (ball x r))).toReal =
      volume.real (ball (0 : ℝ^n) 1) ^ p.toReal⁻¹ *
        (⨍ y in ball x r, ‖f y‖ ^ p.toReal) ^ p.toReal⁻¹ := by
  have hvol : 0 < volume.real (ball (0 : ℝ^n) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume _ zero_lt_one).ne' measure_ball_lt_top.ne
  have hscale : volume.real (ball x r) =
      r ^ n * volume.real (ball (0 : ℝ^n) 1) := by
    simp only [measureReal_def, addHaar_ball_of_pos volume x hr,
      finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le n)]
  rw [toReal_eLpNorm, lpNorm_eq_integral_norm_rpow_toReal hp₀ hp_top hf, setAverage_eq,
    hscale, smul_eq_mul]
  simp only [normFactor, ← ENNReal.toReal_rpow, ENNReal.toReal_inv, one_div,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg hr.le n))]
  rw [← Real.mul_rpow (by positivity) (integral_nonneg (fun _ ↦ by positivity)),
    ← Real.mul_rpow hvol.le (by positivity)]
  congr 1
  have hne : volume.real (ball (0 : ℝ^n) 1) ≠ 0 ∧ r ^ n ≠ 0 :=
    ⟨hvol.ne', (pow_pos hr n).ne'⟩
  cas using hne

/-- At almost every point of a locally `Lᵖ` field, its scaled `Lᵖ` oscillation on
shrinking balls tends to zero. The exponent is finite and strictly positive. -/
theorem ae_tendsto_normFactor_mul_eLpNorm_sub
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [SecondCountableTopology E]
    {p : ℝ≥0∞} (hp₀ : p ≠ 0) (hp_top : p ≠ ∞) {f : ℝ^n → E}
    (hf : ∀ K : Set (ℝ^n), IsCompact K → MemLp f p (volume.restrict K)) :
    ∀ᵐ x ∂volume, Tendsto
      (fun r : ℝ ↦ normFactor n r p *
        (eLpNorm (fun y ↦ f y - f x) p (volume.restrict (ball x r))).toReal)
      (𝓝[>] 0) (𝓝 0) := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp₀ hp_top
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub_rpow
    volume hp₀ hp_top hf] with x hx
  have hlim := (hx.rpow_const (p := p.toReal⁻¹) (Or.inr (by positivity))).const_mul
    (volume.real (ball (0 : ℝ^n) 1) ^ p.toReal⁻¹)
  simp only [Real.zero_rpow (inv_pos.mpr hp).ne', mul_zero] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hset : ball x r =ᵐ[volume] closedBall x r := by
    apply ae_eq_of_subset_of_measure_ge ball_subset_closedBall
      (by rw [addHaar_closedBall volume x hr.le, addHaar_ball_of_pos volume x hr])
      measurableSet_ball.nullMeasurableSet measure_closedBall_lt_top.ne
  have : IsFiniteMeasure (volume.restrict (ball x r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hmem : MemLp (fun y ↦ f y - f x) p (volume.restrict (ball x r)) :=
    ((hf (closedBall x r) (isCompact_closedBall x r)).mono_measure
      (Measure.restrict_mono ball_subset_closedBall le_rfl)).sub (memLp_const (f x))
  rw [normFactor_mul_eLpNorm_eq_average hp₀ hp_top x hr hmem.aestronglyMeasurable]
  rw [Measure.restrict_congr_set hset]

/-- The scaled oscillation limit holds locally inside an open domain for an `Lᵖ`
field on that domain. Zero extension is used only to apply Lebesgue differentiation. -/
theorem ae_tendsto_normFactor_mul_eLpNorm_sub_on
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [SecondCountableTopology E]
    {p : ℝ≥0∞} (hp₀ : p ≠ 0) (hp_top : p ≠ ∞) {Ω : Set (ℝ^n)}
    (hΩ : IsOpen Ω) {f : ℝ^n → E} (hf : MemLp f p (volume.restrict Ω)) :
    ∀ᵐ x ∂volume.restrict Ω, Tendsto
      (fun r : ℝ ↦ normFactor n r p *
        (eLpNorm (fun y ↦ f y - f x) p (volume.restrict (ball x r))).toReal)
      (𝓝[>] 0) (𝓝 0) := by
  classical
  have hzero : MemLp (Ω.indicator f) p volume :=
    (memLp_indicator_iff_restrict hΩ.measurableSet.nullMeasurableSet).mpr hf
  have hlim := ae_tendsto_normFactor_mul_eLpNorm_sub hp₀ hp_top
    (fun K _ ↦ hzero.mono_measure Measure.restrict_le_self)
  filter_upwards [ae_restrict_of_ae hlim, ae_restrict_mem hΩ.measurableSet] with x hx hxΩ
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hΩ x hxΩ
  apply hx.congr'
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, r < δ :=
    nhdsWithin_le_nhds (eventually_lt_nhds hδ)
  filter_upwards [hsmall] with r hr
  congr 2
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
  rw [indicator_of_mem hxΩ, indicator_of_mem (hball ((ball_subset_ball hr.le) hy))]

end SobolevSpace.GraphSpace.MeanScaling
