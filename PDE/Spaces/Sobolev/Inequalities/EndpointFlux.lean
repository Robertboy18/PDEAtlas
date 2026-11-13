/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.WeightedL2
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import PDE.Analysis.MeasureTheory.Lp.Continuous
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Vanishing endpoint flux from square-integrable derivatives

Cauchy–Schwarz bounds a squared endpoint difference by the interval length
times the derivative energy on that interval. The latter tends to zero as the
interval shrinks. Thus the flux with a simple pole vanishes without assuming
a finite endpoint derivative or a Lipschitz bound.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace SobolevSpace.WeightedEndpoint

/-- A squared difference divided by the distance to the right endpoint is
bounded by the derivative energy on the remaining interval. -/
theorem sub_sq_div_le_integral_right
    {f f' : ℝ → ℝ} {a b x : ℝ}
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ y ∈ Ioo a b, HasDerivAt f (f' y) y)
    (hmem : MemLp f' 2 (volume.restrict (Ioo a b)))
    (hx : x ∈ Ioo a b) :
    (f x - f b) ^ 2 / (b - x) ≤ ∫ y in Ioo x b, f' y ^ 2 := by
  have hs : Ioo x b ⊆ Ioo a b := Ioo_subset_Ioo hx.1.le le_rfl
  have hq : MemLp f' 2 (volume.restrict (Ioo x b)) :=
    hmem.mono_measure (Measure.restrict_mono hs le_rfl)
  have hone : MemLp (fun _ : ℝ ↦ (1 : ℝ)) 2 (volume.restrict (Ioo x b)) :=
    memLp_const 1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.2.le
    (hc.mono (Icc_subset_Icc hx.1.le le_rfl)) (fun y hy ↦ hd y (hs hy))
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hx.2.le).mpr
      (hq.integrable (by norm_num)))
  rw [intervalIntegral.integral_of_le hx.2.le, integral_Ioc_eq_integral_Ioo] at hFTC
  have hlength : (∫ _ in Ioo x b, (1 : ℝ) ^ 2) = b - x := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx.2.le]
    simp
  have hcs := (abs_integral_le_integral_abs
    (f := fun y ↦ f' y * 1) (μ := volume.restrict (Ioo x b))).trans
    (integral_abs_mul_le_sqrt_integral_sq hq hone)
  simp only [mul_one, hFTC, hlength] at hcs
  have hsq := (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr hcs
  rw [sq_abs, mul_pow, Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _),
    Real.sq_sqrt (sub_nonneg.mpr hx.2.le), sub_sq_comm] at hsq
  exact (div_le_iff₀ (sub_pos.mpr hx.2)).mpr hsq

/-- Finite derivative energy makes the simple-pole endpoint flux vanish.
The derivative need only exist in the open interval. -/
theorem tendsto_sub_sq_div_right
    {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ y ∈ Ioo a b, HasDerivAt f (f' y) y)
    (hmem : MemLp f' 2 (volume.restrict (Ioo a b))) :
    Tendsto (fun x ↦ (f x - f b) ^ 2 / (b - x)) (𝓝[<] b) (𝓝 0) := by
  have hsq : IntegrableOn (fun y ↦ f' y ^ 2) (Ioo a b) :=
    MemLp.integrable_sq hmem
  have hint : IntegrableOn (fun y ↦ f' y ^ 2) (uIcc a b) := by
    rw [uIcc_of_le hab.le]
    exact (integrableOn_Icc_iff_integrableOn_Ioo).mpr hsq
  have hcont := intervalIntegral.continuousOn_primitive_interval_left hint
  have ht := hcont b right_mem_uIcc
  have hleft : Icc a b ∈ 𝓝[<] b := by
    exact mem_of_superset (Ioo_mem_nhdsLT hab) Ioo_subset_Icc_self
  have hmass : Tendsto (fun x ↦ ∫ y in Ioo x b, f' y ^ 2) (𝓝[<] b) (𝓝 0) := by
    have h := ht.tendsto.mono_left (nhdsWithin_le_of_mem
      (by simpa only [uIcc_of_le hab.le] using hleft))
    simp only [intervalIntegral.integral_same] at h
    apply h.congr'
    filter_upwards [Ioo_mem_nhdsLT hab] with x hx
    rw [intervalIntegral.integral_of_le hx.2.le, integral_Ioc_eq_integral_Ioo]
  apply squeeze_zero' _ _ hmass
  · filter_upwards [Ioo_mem_nhdsLT hab] with x hx
    exact div_nonneg (sq_nonneg _) (sub_nonneg.mpr hx.2.le)
  · filter_upwards [Ioo_mem_nhdsLT hab] with x hx
    exact sub_sq_div_le_integral_right hc hd hmem hx

/-- An inverse-coordinate derivative energy controls the cubic-pole flux.
The factor `1/3` is the integral of the squared coordinate on the unit interval. -/
theorem sub_sq_div_cube_le_integral_left
    {f f' : ℝ → ℝ} {b x : ℝ}
    (hc : ContinuousOn f (Icc 0 b))
    (hd : ∀ y ∈ Ioo 0 b, HasDerivAt f (f' y) y)
    (hmem : MemLp (fun y ↦ f' y / y) 2 (volume.restrict (Ioo 0 b)))
    (hx : x ∈ Ioo 0 b) :
    (f x - f 0) ^ 2 / x ^ 3 ≤ (1 / 3) * ∫ y in Ioo 0 x, (f' y / y) ^ 2 := by
  have hs : Ioo 0 x ⊆ Ioo 0 b := Ioo_subset_Ioo le_rfl hx.2.le
  have hq : MemLp (fun y ↦ f' y / y) 2 (volume.restrict (Ioo 0 x)) :=
    hmem.mono_measure (Measure.restrict_mono hs le_rfl)
  have hid : MemLp (fun y : ℝ ↦ y) 2 (volume.restrict (Ioo 0 x)) :=
    continuousOn_id.memLp_of_subset_isCompact isCompact_Icc measurableSet_Ioo
      Ioo_subset_Icc_self
  have hcancel : (fun y ↦ f' y / y * y) =ᵐ[volume.restrict (Ioo 0 x)] f' := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact div_mul_cancel₀ _ hy.1.ne'
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1.le
    (hc.mono (Icc_subset_Icc le_rfl hx.2.le)) (fun y hy ↦ hd y (hs hy))
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hx.1.le).mpr
      ((hq.integrable_mul hid).congr hcancel))
  rw [intervalIntegral.integral_of_le hx.1.le, integral_Ioc_eq_integral_Ioo] at hFTC
  have hmass : (∫ y in Ioo 0 x, y ^ 2) = x ^ 3 / 3 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx.1.le,
      integral_pow]
    norm_num
  have hcs := (abs_integral_le_integral_abs
    (f := fun y ↦ f' y / y * y) (μ := volume.restrict (Ioo 0 x))).trans
    (integral_abs_mul_le_sqrt_integral_sq hq hid)
  rw [integral_congr_ae hcancel, hFTC, hmass] at hcs
  have hsq := (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr hcs
  rw [sq_abs, mul_pow, Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _),
    Real.sq_sqrt (div_nonneg (pow_nonneg hx.1.le 3) (by norm_num))] at hsq
  exact (div_le_iff₀ (pow_pos hx.1 3)).mpr (by linarith)

/-- The cubic-pole flux vanishes when the inverse-coordinate derivative has
finite square integral. No second derivative or Taylor expansion is required. -/
theorem tendsto_sub_sq_div_cube_left
    {f f' : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hc : ContinuousOn f (Icc 0 b))
    (hd : ∀ y ∈ Ioo 0 b, HasDerivAt f (f' y) y)
    (hmem : MemLp (fun y ↦ f' y / y) 2 (volume.restrict (Ioo 0 b))) :
    Tendsto (fun x ↦ (f x - f 0) ^ 2 / x ^ 3) (𝓝[>] 0) (𝓝 0) := by
  have hint : IntegrableOn (fun y ↦ (f' y / y) ^ 2) (uIcc 0 b) := by
    rw [uIcc_of_le hb.le]
    exact (integrableOn_Icc_iff_integrableOn_Ioo).mpr (MemLp.integrable_sq hmem)
  have hcont := intervalIntegral.continuousOn_primitive_interval hint
  have ht := hcont 0 left_mem_uIcc
  have hright : Icc 0 b ∈ 𝓝[>] (0 : ℝ) := by
    exact mem_of_superset (Ioo_mem_nhdsGT hb) Ioo_subset_Icc_self
  have hmass : Tendsto (fun x ↦ ∫ y in Ioo 0 x, (f' y / y) ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have h := ht.tendsto.mono_left (nhdsWithin_le_of_mem
      (by simpa only [uIcc_of_le hb.le] using hright))
    simp only [intervalIntegral.integral_same] at h
    apply h.congr'
    filter_upwards [Ioo_mem_nhdsGT hb] with x hx
    rw [intervalIntegral.integral_of_le hx.1.le, integral_Ioc_eq_integral_Ioo]
  have hmass' := hmass.const_mul (1 / 3 : ℝ)
  rw [mul_zero] at hmass'
  apply squeeze_zero' _ _ hmass'
  · filter_upwards [Ioo_mem_nhdsGT hb] with x hx
    exact div_nonneg (sq_nonneg _) (pow_nonneg hx.1.le _)
  · filter_upwards [Ioo_mem_nhdsGT hb] with x hx
    exact sub_sq_div_cube_le_integral_left hc hd hmem hx

end SobolevSpace.WeightedEndpoint
