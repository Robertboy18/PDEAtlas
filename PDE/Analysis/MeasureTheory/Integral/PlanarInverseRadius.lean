/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Geometry.EuclideanBall
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import CAS.ExactTactic

/-!
# Planar inverse-radius integrals

A local bound on an integrable density controls its inverse-radius integral
near the pole. The complement retains its distance weight and also admits
the coarser estimate by inverse radius times source mass.

## Main results

* `integral_ball_norm_inv_two`: `∫_{|z|<ρ} |z|⁻¹ dz = 2πρ` in the plane.
* `integrable_norm_div_norm_two`: an integrable planar density `h` bounded near the pole has
  `|h(z)|/|z|` integrable.
* `integral_norm_div_norm_ball_two_le`: a bound `|h| ≤ M` on the disc of radius `ρ` contributes
  at most `2πMρ` to `∫ |h(z)|/|z| dz`.
* `integral_norm_div_norm_compl_ball_two_le`: the integral of `|h(z)|/|z|` outside the disc is
  at most the mass of `|h|` outside the disc divided by `ρ`.
* `integral_norm_div_norm_two_le_near_add_far`:
  `∫ |h(z)|/|z| dz ≤ 2πMρ + ∫_{|z|≥ρ} |h(z)|/|z| dz`.
* `integral_norm_div_norm_two_le`: `∫ |h(z)|/|z| dz ≤ 2πMρ + (∫ |h|)/ρ`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace MeasureTheory

/-- The inverse-radius singularity has mass `2πρ` on a planar disk. -/
theorem integral_ball_norm_inv_two (ρ : ℝ) (hρ : 0 < ρ) :
    (∫ z in Metric.ball (0 : ℝ^2) ρ, ‖z‖⁻¹) = 2 * Real.pi * ρ := by
  let f : ℝ → ℝ := (Iio ρ).indicator (fun r ↦ r⁻¹)
  have hpolar := integral_fun_norm_addHaar (E := ℝ^2) (volume : Measure (ℝ^2)) f
  have hleft : (∫ z : ℝ^2, f ‖z‖) =
      ∫ z in Metric.ball (0 : ℝ^2) ρ, ‖z‖⁻¹ := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [f, Set.indicator, mem_Iio, Metric.mem_ball, dist_zero_right]
  have hrad :
      (∫ r in Ioi (0 : ℝ), r ^ (Module.finrank ℝ (ℝ^2) - 1) • f r) = ρ := by
    calc
      _ = ∫ r in Ioi (0 : ℝ), (Iio ρ).indicator (fun _ ↦ (1 : ℝ)) r := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        by_cases hrρ : r < ρ
        · simp [f, hrρ, ne_of_gt hr]
        · simp [f, hrρ]
      _ = ∫ _r in Ioo (0 : ℝ) ρ, (1 : ℝ) := by
        rw [setIntegral_indicator measurableSet_Iio]
        rfl
      _ = ρ := by simp [measureReal_def, hρ.le]
  have hvol : (volume : Measure (ℝ^2)).real (Metric.ball (0 : ℝ^2) 1) =
      Real.pi := by
    simpa only [PDE.Analysis.ballVolume, measureReal_def, one_pow, mul_one,
      PDE.Analysis.unitBallVolume_two] using
      PDE.Analysis.ballVolume_eq_unitBallVolume_mul_pow 2 1 zero_le_one
  rw [hleft, hrad, hvol] at hpolar
  simpa only [finrank_euclideanSpace_fin, nsmul_eq_mul, smul_eq_mul,
    Nat.cast_ofNat, mul_assoc] using hpolar

/-- Inverse radius is integrable on every planar disk centered at its pole. -/
theorem integrableOn_ball_norm_inv_two (ρ : ℝ) :
    IntegrableOn (fun z : ℝ^2 ↦ ‖z‖⁻¹) (Metric.ball 0 ρ) := by
  apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := (1 : ℝ))
    (by norm_num) (by norm_num)
  · filter_upwards [] with z
    simp [Real.rpow_neg_one]
  · exact measurable_norm.inv.aestronglyMeasurable

/-- A local bound on a measurable density makes its inverse-radius integral finite
on a planar disk. The bound is needed only almost everywhere on that disk. -/
theorem integrableOn_norm_div_norm_ball_two
    {h : ℝ^2 → ℝ} (hh : AEStronglyMeasurable h) {ρ M : ℝ}
    (hbound : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℝ^2) ρ), ‖h z‖ ≤ M) :
    IntegrableOn (fun z ↦ ‖h z‖ / ‖z‖) (Metric.ball 0 ρ) := by
  apply ((integrableOn_ball_norm_inv_two ρ).const_mul M).mono'
    (hh.norm.div₀ measurable_norm.aestronglyMeasurable).restrict
  filter_upwards [hbound] with z hz
  change ‖‖h z‖ / ‖z‖‖ ≤ M * ‖z‖⁻¹
  rw [norm_div, norm_norm, norm_norm, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hz (inv_nonneg.mpr (norm_nonneg z))

/-- Outside a positive-radius disk, inverse radius preserves integrability
of the absolute value of an integrable density. -/
theorem integrableOn_norm_div_norm_compl_ball_two
    {h : ℝ^2 → ℝ} (hh : Integrable h) {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn (fun z ↦ ‖h z‖ / ‖z‖) (Metric.ball (0 : ℝ^2) ρ)ᶜ := by
  apply (hh.norm.div_const ρ).integrableOn.mono'
    (hh.aestronglyMeasurable.norm.div₀ measurable_norm.aestronglyMeasurable).restrict
  filter_upwards [ae_restrict_mem measurableSet_ball.compl] with z hz
  have hdist : ρ ≤ ‖z‖ := by
    simpa only [mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hz
  change ‖‖h z‖ / ‖z‖‖ ≤ ‖h z‖ / ρ
  simpa only [norm_div, norm_norm] using
    div_le_div_of_nonneg_left (norm_nonneg (h z)) hρ hdist

/-- An integrable planar density that is locally bounded near the pole has
an absolutely integrable inverse-radius weight. -/
theorem integrable_norm_div_norm_two
    {h : ℝ^2 → ℝ} (hh : Integrable h) {ρ M : ℝ} (hρ : 0 < ρ)
    (hbound : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℝ^2) ρ), ‖h z‖ ≤ M) :
    Integrable (fun z ↦ ‖h z‖ / ‖z‖) := by
  rw [← integrableOn_univ, ← union_compl_self (Metric.ball (0 : ℝ^2) ρ),
    integrableOn_union]
  exact ⟨integrableOn_norm_div_norm_ball_two hh.aestronglyMeasurable hbound,
    integrableOn_norm_div_norm_compl_ball_two hh hρ⟩

/-- The local source bound contributes at most `2πMρ` to the planar
inverse-radius integral. -/
theorem integral_norm_div_norm_ball_two_le
    {h : ℝ^2 → ℝ} (hh : AEStronglyMeasurable h) {ρ M : ℝ} (hρ : 0 < ρ)
    (hbound : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℝ^2) ρ), ‖h z‖ ≤ M) :
    (∫ z in Metric.ball (0 : ℝ^2) ρ, ‖h z‖ / ‖z‖) ≤ 2 * Real.pi * M * ρ := by
  calc
    _ ≤ ∫ z in Metric.ball (0 : ℝ^2) ρ, M * ‖z‖⁻¹ := by
      apply integral_mono_ae (integrableOn_norm_div_norm_ball_two hh hbound)
        ((integrableOn_ball_norm_inv_two ρ).const_mul M)
      filter_upwards [hbound] with z hz
      simpa only [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_right hz (inv_nonneg.mpr (norm_nonneg z))
    _ = _ := by rw [integral_const_mul, integral_ball_norm_inv_two ρ hρ]; cas

/-- The far part of an inverse-radius integral is bounded by the mass
outside the disk divided by its radius. -/
theorem integral_norm_div_norm_compl_ball_two_le
    {h : ℝ^2 → ℝ} (hh : Integrable h) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ z in (Metric.ball (0 : ℝ^2) ρ)ᶜ, ‖h z‖ / ‖z‖) ≤
      (∫ z in (Metric.ball (0 : ℝ^2) ρ)ᶜ, ‖h z‖) / ρ := by
  calc
    _ ≤ ∫ z in (Metric.ball (0 : ℝ^2) ρ)ᶜ, ‖h z‖ / ρ := by
      apply integral_mono_ae (integrableOn_norm_div_norm_compl_ball_two hh hρ)
        (hh.norm.div_const ρ).integrableOn
      filter_upwards [ae_restrict_mem measurableSet_ball.compl] with z hz
      apply div_le_div_of_nonneg_left (norm_nonneg _) hρ
      simpa only [mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hz
    _ = _ := integral_div ρ _

/-- Splitting off the singular disk leaves the distance-weighted complement
integral available for sharper numerical bounds. -/
theorem integral_norm_div_norm_two_le_near_add_far
    {h : ℝ^2 → ℝ} (hh : Integrable h) {ρ M : ℝ} (hρ : 0 < ρ)
    (hbound : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℝ^2) ρ), ‖h z‖ ≤ M) :
    (∫ z, ‖h z‖ / ‖z‖) ≤ 2 * Real.pi * M * ρ +
      ∫ z in (Metric.ball (0 : ℝ^2) ρ)ᶜ, ‖h z‖ / ‖z‖ := by
  rw [← integral_add_compl (s := Metric.ball (0 : ℝ^2) ρ) measurableSet_ball
    (integrable_norm_div_norm_two hh hρ hbound)]
  exact add_le_add (integral_norm_div_norm_ball_two_le hh.aestronglyMeasurable
    hρ hbound) le_rfl

/-- A coarse global bound uses the local source bound and total source mass. -/
theorem integral_norm_div_norm_two_le
    {h : ℝ^2 → ℝ} (hh : Integrable h) {ρ M : ℝ} (hρ : 0 < ρ)
    (hbound : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℝ^2) ρ), ‖h z‖ ≤ M) :
    (∫ z, ‖h z‖ / ‖z‖) ≤ 2 * Real.pi * M * ρ + (∫ z, ‖h z‖) / ρ := by
  apply (integral_norm_div_norm_two_le_near_add_far hh hρ hbound).trans
  apply add_le_add le_rfl
  apply (integral_norm_div_norm_compl_ball_two_le hh hρ).trans
  apply div_le_div_of_nonneg_right _ hρ.le
  exact integral_mono_measure Measure.restrict_le_self
    (Eventually.of_forall fun z ↦ norm_nonneg (h z)) hh.norm

end MeasureTheory
