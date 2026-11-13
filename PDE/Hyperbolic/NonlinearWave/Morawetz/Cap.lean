/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Morawetz.Slices
public import PDE.Analysis.MeasureTheory.Lp.WeightedL2
import PDE.FDeriv.SpaceTime
import CAS.ExactTactic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Energy control of the scaling-current cap

A shrinking ball contributes a radius times the energy and one L² pairing.
This bound uses only the current time slice; the future tip need not be a
regular point of the solution.
-/

@[expose] public noncomputable section

open PDE.Common MeasureTheory Metric Set
open scoped BigOperators

namespace WaveEquation

variable {n : ℕ}

/-- On a backward ball, the absolute scaling density is bounded by twice the
radius times physical energy, plus its amplitude pairing. -/
theorem abs_scalingCurrentDensity_le {u : ℝ^(n + 1) → ℝ} (V : ℝ → ℝ) (a T t : ℝ) (c x : ℝ^n)
    (ht : t ≤ T) (hx : ‖x - c‖ ≤ T - t) (hV : 0 ≤ V (u (timeSpaceCons t x)))
    (hu : DifferentiableAt ℝ u (timeSpaceCons t x)) :
    |scalingCurrentDensity V a (timeSpaceCons T c) u (timeSpaceCons t x)| ≤
      2 * (T - t) * semilinearWaveEnergyDensity V u (timeSpaceCons t x) +
        |a * u (timeSpaceCons t x) * (∂[0] u) (timeSpaceCons t x)| := by
  let D := fderiv ℝ (fun y ↦ u (timeSpaceCons t y)) x
  let v := (∂[0] u) (timeSpaceCons t x)
  let W := V (u (timeSpaceCons t x))
  let r := T - t
  let e := (v ^ 2 + ‖D‖ ^ 2) / 2 + W
  have hr : 0 ≤ r := sub_nonneg.mpr ht
  have he : 0 ≤ e := by dsimp [e, W]; positivity
  have hs : DifferentiableAt ℝ (fun y ↦ u (timeSpaceCons t y)) x :=
    hu.comp x (hasFDerivAt_timeSpaceCons_spatial n t x).differentiableAt
  have hnorm := PDE.norm_fderiv_sq_eq_sum_partialDeriv_sq hs
  simp_rw [PDE.partialDeriv_timeSpaceCons_spatial _ _ _ _ hu] at hnorm
  have heq : semilinearWaveEnergyDensity V u (timeSpaceCons t x) = e := by
    simp only [semilinearWaveEnergyDensity, classicalWaveEnergyDensity,
      EuclideanSpace.real_norm_sq_eq, classicalWaveSpatialGradient_apply]
    rw [← hnorm]
    dsimp [e, D, v, W]
    cas
  have hD : |D (x - c)| ≤ r * ‖D‖ := by
    calc
      _ ≤ ‖D‖ * ‖x - c‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖D‖ * r := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
      _ = _ := mul_comm _ _
  have hpair : |D (x - c) * v| ≤ r * (v ^ 2 + ‖D‖ ^ 2) / 2 := by
    rw [abs_mul]
    calc
      _ ≤ (r * ‖D‖) * |v| := mul_le_mul_of_nonneg_right hD (abs_nonneg _)
      _ ≤ _ := by nlinarith [mul_nonneg hr (sq_nonneg (‖D‖ - |v|)), sq_abs v]
  rw [heq, scalingCurrentDensity_timeSlice V a T t c x hu]
  change |(t - T) * e + (D (x - c) + a * u (timeSpaceCons t x)) * v| ≤ _
  rw [show t - T = -r by dsimp [r]; cas, add_mul]
  calc
    _ ≤ |-r * e| + (|D (x - c) * v| + |a * u (timeSpaceCons t x) * v|) :=
      by
        have h₁ := abs_add_le (-r * e) (D (x - c) * v + a * u (timeSpaceCons t x) * v)
        have h₂ := abs_add_le (D (x - c) * v) (a * u (timeSpaceCons t x) * v)
        linarith
    _ ≤ r * e + (r * (v ^ 2 + ‖D‖ ^ 2) / 2 + |a * u (timeSpaceCons t x) * v|) := by
      rw [abs_mul, abs_neg, abs_of_nonneg hr, abs_of_nonneg he]
      linarith [hpair]
    _ ≤ _ := by
      change _ ≤ 2 * r * e + |a * u (timeSpaceCons t x) * v|
      dsimp [e]
      nlinarith [mul_nonneg hr hV]

/-- The cap integral is controlled by local physical energy and the L² norms
of displacement and velocity. -/
theorem abs_ballIntegral_scalingCurrentDensity_le
    {u : ℝ^(n + 1) → ℝ} {V : ℝ → ℝ} (hV : ContDiff ℝ 1 V) (T t : ℝ) (c : ℝ^n)
    (ht : t < T) (hu : ∀ x, ContDiffAt ℝ 2 u (timeSpaceCons t x))
    (hpos : ∀ x ∈ ball c (T - t), 0 ≤ V (u (timeSpaceCons t x))) :
    |PDE.Analysis.ballIntegral n
        (fun x ↦ scalingCurrentDensity V 1 (timeSpaceCons T c) u (timeSpaceCons t x))
        c (T - t)| ≤
      2 * (T - t) * PDE.Analysis.ballIntegral n
          (fun x ↦ semilinearWaveEnergyDensity V u (timeSpaceCons t x)) c (T - t) +
        lpNorm (fun x ↦ u (timeSpaceCons t x)) 2 (volume.restrict (ball c (T - t))) *
          lpNorm (fun x ↦ (∂[0] u) (timeSpaceCons t x)) 2
            (volume.restrict (ball c (T - t))) := by
  let U : ℝ^n → ℝ := fun x ↦ u (timeSpaceCons t x)
  let v : ℝ^n → ℝ := fun x ↦ (∂[0] u) (timeSpaceCons t x)
  let P : ℝ^n → ℝ := fun x ↦ scalingCurrentDensity V 1 (timeSpaceCons T c) u (timeSpaceCons t x)
  let E : ℝ^n → ℝ := fun x ↦ semilinearWaveEnergyDensity V u (timeSpaceCons t x)
  let μ := volume.restrict (ball c (T - t))
  have hs := (contDiff_timeSpaceCons_spatial n t (m := 1)).continuous
  have hU : Continuous U := continuous_iff_continuousAt.mpr fun x ↦
    (hu x).continuousAt.comp hs.continuousAt
  have hv : Continuous v := continuous_iff_continuousAt.mpr fun x ↦
    (PDE.contDiffAt_partialDeriv 1 (hu x) 0).continuousAt.comp hs.continuousAt
  have hP : Continuous P := continuous_iff_continuousAt.mpr fun x ↦
    (contDiffAt_scalingCurrentDensity 1 (timeSpaceCons T c) hV.contDiffAt
      (hu x)).continuousAt.comp hs.continuousAt
  have hE : Continuous E := continuous_iff_continuousAt.mpr fun x ↦
    (contDiffAt_semilinearWaveEnergyDensity (m := 1) hV.contDiffAt
      (hu x)).continuousAt.comp hs.continuousAt
  have hint {f : ℝ^n → ℝ} (hf : Continuous f) : Integrable f μ :=
    (hf.continuousOn.integrableOn_compact (isCompact_closedBall c (T - t))).mono_set
      ball_subset_closedBall
  have hUm : MemLp U 2 μ :=
    (memLp_two_iff_integrable_sq hU.aestronglyMeasurable).2 (hint (hU.pow 2))
  have hvm : MemLp v 2 μ :=
    (memLp_two_iff_integrable_sq hv.aestronglyMeasurable).2 (hint (hv.pow 2))
  have hpoint : ∀ᵐ x ∂μ, |P x| ≤ 2 * (T - t) * E x + |U x * v x| := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hxc : ‖x - c‖ ≤ T - t := le_of_lt (by
      simpa only [mem_ball, dist_eq_norm] using hx)
    simpa only [P, E, U, v, one_mul] using
      abs_scalingCurrentDensity_le V 1 T t c x ht.le hxc (hpos x hx)
        ((hu x).differentiableAt (by norm_num))
  have hcs : (∫ x, |U x * v x| ∂μ) ≤ lpNorm U 2 μ * lpNorm v 2 μ := by
    have h := abs_integral_mul_le_lpNorm_two_mul_lpNorm_two hUm.norm hvm.norm
    have hnonneg : 0 ≤ ∫ x, ‖U x‖ * ‖v x‖ ∂μ :=
      integral_nonneg (fun x ↦ mul_nonneg (norm_nonneg (U x)) (norm_nonneg (v x)))
    rw [abs_of_nonneg hnonneg, lpNorm_norm hUm.aestronglyMeasurable,
      lpNorm_norm hvm.aestronglyMeasurable] at h
    simpa only [abs_mul, Real.norm_eq_abs] using h
  change |∫ x, P x ∂μ| ≤ 2 * (T - t) * (∫ x, E x ∂μ) + lpNorm U 2 μ * lpNorm v 2 μ
  calc
    _ ≤ ∫ x, |P x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, 2 * (T - t) * E x + |U x * v x| ∂μ := integral_mono_ae (hint hP.abs)
        (hint ((continuous_const.mul hE).add (hU.mul hv).abs)) hpoint
    _ = 2 * (T - t) * (∫ x, E x ∂μ) + ∫ x, |U x * v x| ∂μ := by
      have hscaled : Integrable (fun x ↦ 2 * (T - t) * E x) μ := hint (continuous_const.mul hE)
      have hproduct : Integrable (fun x ↦ |U x * v x|) μ := hint (hU.mul hv).abs
      rw [integral_add hscaled hproduct, integral_const_mul]
    _ ≤ _ := by linarith [hcs]

end WaveEquation
