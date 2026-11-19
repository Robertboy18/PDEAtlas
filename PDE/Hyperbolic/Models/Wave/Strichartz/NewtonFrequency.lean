/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Distribution.Schwartz.RadialPower
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import PDE.Common.Euclidean
import CAS.ExactTactic

/-!
# Frequency data for the three-dimensional Newton potential

The inverse-Laplacian multiplier sends Schwartz data to an integrable function
with two integrable frequency moments. The inverse-frequency datum is in L².
All membership statements follow from the general radial-weighted Schwartz estimates;
the zero frequency is removed only by an explicit almost-everywhere equality.
-/

@[expose] public section

open MeasureTheory FourierTransform
open scoped ENNReal SchwartzMap

namespace WaveEquation.Strichartz

/-- The inverse-Laplacian frequency datum with the `exp(2πi x·ξ)` convention. -/
noncomputable def newtonFrequency (F : 𝓢(ℝ^3, ℂ)) (ξ : ℝ^3) : ℂ :=
  (2 * Real.pi)⁻¹ ^ 2 • (‖ξ‖ ^ (-2 : ℝ) • F ξ)

/-- The inverse-Laplacian datum is integrable in dimension three. -/
theorem integrable_newtonFrequency (F : 𝓢(ℝ^3, ℂ)) : Integrable (newtonFrequency F) := by
  have h := F.memLp_norm_sub_rpow_smul (μ := volume) (by simp)
    (p := 1) (by norm_num) (by norm_num) (a := -2) (by norm_num) (by norm_num) 0
  have hi : Integrable (fun ξ ↦ ‖ξ‖ ^ (-2 : ℝ) • F ξ) :=
    memLp_one_iff_integrable.mp (by simpa only [sub_zero] using h)
  exact hi.smul ((2 * Real.pi)⁻¹ ^ 2 : ℝ)

/-- Dividing a Schwartz frequency datum by frequency gives an L² function. -/
theorem memLp_inverse_frequency (F : 𝓢(ℝ^3, ℂ)) :
    MemLp (fun ξ ↦ (2 * Real.pi)⁻¹ • (‖ξ‖ ^ (-1 : ℝ) • F ξ)) 2 volume := by
  have h := F.memLp_norm_sub_rpow_smul (μ := volume) (by simp)
    (p := 2) (by norm_num) (by norm_num) (a := -1) (by norm_num) (by norm_num) 0
  exact (show MemLp (fun ξ ↦ ‖ξ‖ ^ (-1 : ℝ) • F ξ) 2 volume by
    simpa only [sub_zero] using h).const_smul ((2 * Real.pi)⁻¹ : ℝ)

private theorem norm_pow_mul_norm_newtonFrequency (F : 𝓢(ℝ^3, ℂ)) (k : ℕ) {ξ : ℝ^3} (hξ : ξ ≠ 0) :
    ‖ξ‖ ^ k * ‖newtonFrequency F ξ‖ = (2 * Real.pi)⁻¹ ^ 2 * ‖‖ξ‖ ^ ((k : ℝ) - 2) • F ξ‖ := by
  have hpos := norm_pos_iff.mpr hξ
  rw [newtonFrequency, norm_smul, norm_smul, norm_smul]
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ((2 * Real.pi)⁻¹)),
    abs_of_nonneg (Real.rpow_nonneg hpos.le _)]
  rw [← Real.rpow_natCast]
  calc
    ‖ξ‖ ^ (k : ℝ) * ((2 * Real.pi)⁻¹ ^ 2 * (‖ξ‖ ^ (-2 : ℝ) * ‖F ξ‖)) =
        (2 * Real.pi)⁻¹ ^ 2 * ((‖ξ‖ ^ (k : ℝ) * ‖ξ‖ ^ (-2 : ℝ)) * ‖F ξ‖) := by ring
    _ = _ := by rw [← Real.rpow_add hpos, ← sub_eq_add_neg]

/-- The first spatial moment of the Newton frequency datum is integrable. -/
theorem integrable_norm_mul_newtonFrequency (F : 𝓢(ℝ^3, ℂ)) :
    Integrable (fun ξ ↦ ‖ξ‖ * ‖newtonFrequency F ξ‖) := by
  have h := F.memLp_norm_sub_rpow_smul (μ := volume) (by simp)
    (p := 1) (by norm_num) (by norm_num) (a := -1) (by norm_num) (by norm_num) 0
  have hi : Integrable (fun ξ ↦ ‖ξ‖ ^ (-1 : ℝ) • F ξ) :=
    memLp_one_iff_integrable.mp (by simpa only [sub_zero] using h)
  apply (hi.norm.const_mul ((2 * Real.pi)⁻¹ ^ 2)).congr
  filter_upwards [volume.ae_ne (0 : ℝ^3)] with ξ hξ
  simpa only [Nat.cast_one, pow_one, show (1 : ℝ) - 2 = -1 by norm_num] using
    (norm_pow_mul_norm_newtonFrequency F 1 hξ).symm

/-- The second spatial moment of the Newton frequency datum is integrable. -/
theorem integrable_norm_sq_mul_newtonFrequency (F : 𝓢(ℝ^3, ℂ)) :
    Integrable (fun ξ ↦ ‖ξ‖ ^ 2 * ‖newtonFrequency F ξ‖) := by
  apply (F.integrable.norm.const_mul ((2 * Real.pi)⁻¹ ^ 2)).congr
  filter_upwards [volume.ae_ne (0 : ℝ^3)] with ξ hξ
  simpa only [Nat.cast_ofNat, sub_self, Real.rpow_zero, one_smul] using
    (norm_pow_mul_norm_newtonFrequency F 2 hξ).symm

/-- Away from the null zero frequency, the Laplacian multiplier cancels its inverse. -/
theorem angularFrequency_sq_smul_newtonFrequency (F : 𝓢(ℝ^3, ℂ)) {ξ : ℝ^3} (hξ : ξ ≠ 0) :
    (2 * Real.pi * ‖ξ‖) ^ 2 • newtonFrequency F ξ = F ξ := by
  have hr : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hc (r : ℝ) (hr : 0 < r) :
      (2 * Real.pi * r) ^ 2 * (2 * Real.pi)⁻¹ ^ 2 * (r ^ 2)⁻¹ = 1 := by
    cas using [hr, Real.pi_pos]
  rw [newtonFrequency, smul_smul, smul_smul,
    Real.rpow_neg (norm_nonneg ξ), Real.rpow_two, hc ‖ξ‖ hr, one_smul]

end WaveEquation.Strichartz
