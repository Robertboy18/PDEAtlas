/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Spaces.Sobolev.Calculus.Slicing.Normal
public import PDE.Spaces.Sobolev.Calculus.Slicing.NormalIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Height averages of smooth functions and their boundary values

The fundamental theorem of calculus bounds the difference between a normal
height average and the boundary value by the normal derivative integral.
Jensen's inequality yields the factor `ε ^ (p - 1)` in the p-energy estimate.
The normal coordinate is the final coordinate, also in boundary dimension zero.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Trace.HalfSpace

open MeasureTheory Set
open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
/-- The p-energy form of Hölder's inequality on a positive interval. -/
theorem integral_norm_rpow_le_length_mul {g : ℝ → F} (hg : Continuous g)
    {p ε : ℝ} (hp : 1 ≤ p) (hε : 0 < ε) :
    (∫ t in (0 : ℝ)..ε, ‖g t‖) ^ p ≤
      ε ^ (p - 1) * ∫ t in (0 : ℝ)..ε, ‖g t‖ ^ p := by
  have hp₀ : 0 ≤ p := zero_le_one.trans hp
  have hc : Continuous fun t ↦ ‖g t‖ ^ p :=
    hg.norm.rpow_const (fun _ ↦ Or.inr hp₀)
  have hj := (convexOn_rpow hp).map_set_average_le
    (μ := (volume : Measure ℝ)) (t := Ioc (0 : ℝ) ε) (f := fun t ↦ ‖g t‖)
    (continuousOn_id.rpow_const (fun _ _ ↦ Or.inr hp₀)) isClosed_Ici
    (by simp [Real.volume_Ioc, hε]) (by simp)
    (Filter.Eventually.of_forall fun t ↦ norm_nonneg (g t))
    (hg.norm.intervalIntegrable 0 ε).1 (hc.intervalIntegrable 0 ε).1
  rw [setAverage_eq, setAverage_eq, Real.volume_real_Ioc_of_le hε.le] at hj
  simp only [sub_zero, smul_eq_mul] at hj
  rw [← intervalIntegral.integral_of_le hε.le,
    ← intervalIntegral.integral_of_le hε.le] at hj
  have hI : 0 ≤ ∫ t in (0 : ℝ)..ε, ‖g t‖ :=
    intervalIntegral.integral_nonneg hε.le (fun _ _ ↦ norm_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hj (Real.rpow_nonneg hε.le p)
  rw [Real.mul_rpow (inv_nonneg.mpr hε.le) hI, Real.inv_rpow hε.le] at hmul
  have he : ε ^ p ≠ 0 := (Real.rpow_pos_of_pos hε p).ne'
  calc
    (∫ t in (0 : ℝ)..ε, ‖g t‖) ^ p =
        ε ^ p * ((ε ^ p)⁻¹ * (∫ t in (0 : ℝ)..ε, ‖g t‖) ^ p) := by
      rw [← mul_assoc, mul_inv_cancel₀ he, one_mul]
    _ ≤ ε ^ p * (ε⁻¹ * ∫ t in (0 : ℝ)..ε, ‖g t‖ ^ p) := hmul
    _ = ε ^ (p - 1) * ∫ t in (0 : ℝ)..ε, ‖g t‖ ^ p := by
      rw [← mul_assoc, Real.rpow_sub hε, Real.rpow_one, div_eq_mul_inv]

/-- A normal height average approaches the endpoint with an error controlled
by the derivative p-energy on the averaging interval. -/
theorem norm_height_average_sub_rpow_le [CompleteSpace F] {g : ℝ → F} (hg : ContDiff ℝ 1 g)
    {p ε : ℝ} (hp : 1 ≤ p) (hε : 0 < ε) :
    ‖ε⁻¹ • (∫ t in (0 : ℝ)..ε, g t) - g 0‖ ^ p ≤
      ε ^ (p - 1) * ∫ t in (0 : ℝ)..ε, ‖deriv g t‖ ^ p := by
  have hd : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  let B := ∫ t in (0 : ℝ)..ε, ‖deriv g t‖
  have hpoint (t : ℝ) (ht : t ∈ uIoc (0 : ℝ) ε) : ‖g t - g 0‖ ≤ B := by
    rw [uIoc_of_le hε.le] at ht
    have hFTC := intervalIntegral.integral_deriv_eq_sub
      (fun x _ ↦ hg.differentiable (by norm_num) x) (hd.intervalIntegrable 0 t)
    calc
      ‖g t - g 0‖ = ‖∫ s in (0 : ℝ)..t, deriv g s‖ := congrArg norm hFTC.symm
      _ ≤ ∫ s in (0 : ℝ)..t, ‖deriv g s‖ :=
        intervalIntegral.norm_integral_le_integral_norm (f := deriv g) ht.1.le
      _ ≤ B := intervalIntegral.integral_mono_interval le_rfl ht.1.le ht.2
        (Filter.Eventually.of_forall fun s ↦ norm_nonneg (deriv g s))
        (hd.norm.intervalIntegrable 0 ε)
  have heq :
      ε⁻¹ • (∫ t in (0 : ℝ)..ε, g t) - g 0 =
        ε⁻¹ • ∫ t in (0 : ℝ)..ε, g t - g 0 := by
    rw [intervalIntegral.integral_sub (hg.continuous.intervalIntegrable 0 ε)
      (continuous_const.intervalIntegrable 0 ε), intervalIntegral.integral_const,
      sub_zero, smul_sub, smul_smul, inv_mul_cancel₀ hε.ne', one_smul]
  have hmean : ‖ε⁻¹ • (∫ t in (0 : ℝ)..ε, g t) - g 0‖ ≤ B := by
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε)]
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun t ↦ g t - g 0) (fun t ht ↦ hpoint t ht)
    simp only [sub_zero, abs_of_pos hε] at hbound
    calc
      ε⁻¹ * ‖∫ t in (0 : ℝ)..ε, g t - g 0‖ ≤ ε⁻¹ * (B * ε) :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hε.le)
      _ = B := by rw [mul_comm B, ← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul]
  exact (Real.rpow_le_rpow (norm_nonneg _) hmean (zero_le_one.trans hp)).trans
    (integral_norm_rpow_le_length_mul hd hp hε)

/-- The height-average error is bounded by the derivative energy on the
positive half-line, with coefficient one. -/
theorem norm_height_average_sub_rpow_le_integral_Ioi [CompleteSpace F]
    {g : ℝ → F}
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) {p ε : ℝ}
    (hp : 1 ≤ p) (hε : 0 < ε) :
    ‖ε⁻¹ • (∫ t in Ioc (0 : ℝ) ε, g t) - g 0‖ ^ p ≤
      ε ^ (p - 1) * ∫ t in Ioi (0 : ℝ), ‖deriv g t‖ ^ p := by
  have hp₀ : 0 < p := zero_lt_one.trans_le hp
  have hi : IntegrableOn (fun t ↦ ‖deriv g t‖ ^ p) (Ioi (0 : ℝ)) :=
    ((hg.continuous_deriv (by norm_num)).norm.rpow_const
      (fun _ ↦ Or.inr hp₀.le)).integrable_of_hasCompactSupport
        (hgc.deriv.norm.rpow_const hp₀.ne') |>.integrableOn
  have h := norm_height_average_sub_rpow_le hg hp hε
  rw [intervalIntegral.integral_of_le hε.le,
    intervalIntegral.integral_of_le hε.le] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hε.le _))
  exact setIntegral_mono_set hi
    (Filter.Eventually.of_forall fun t ↦ Real.rpow_nonneg (norm_nonneg _) _)
    (Filter.Eventually.of_forall fun _ ht ↦ ht.1)

/-- Integrating smooth height-average errors over the boundary gives the
normal partial-derivative energy on the upper half-space. -/
theorem lintegral_height_average_sub_le [CompleteSpace F]
    {n : ℕ} {f : ℝ^(n + 1) → F}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) {p ε : ℝ}
    (hp : 1 ≤ p) (hε : 0 < ε) :
    (∫⁻ y : ℝ^n, ENNReal.ofReal
      (‖ε⁻¹ • (∫ t in Ioc (0 : ℝ) ε, normalSlice f y t) - normalSlice f y 0‖ ^ p)) ≤
        ENNReal.ofReal (ε ^ (p - 1) *
          ∫ z in ℝ^(n+1)₊, ‖(∂[Fin.last n] f) z‖ ^ p) := by
  have hp₀ : 0 < p := zero_lt_one.trans_le hp
  have henergy : Integrable (fun z : ℝ^n × ℝ ↦ ‖normalDerivativeInSplit f z‖ ^ p)
      ((volume : Measure (ℝ^n)).prod positiveNormalMeasure) :=
    (normalDerivativeInSplit_continuous hf).norm.rpow_const
      (fun _ ↦ Or.inr hp₀.le)
      |>.integrable_of_hasCompactSupport
        ((normalDerivativeInSplit_hasCompactSupport hfc).norm.rpow_const hp₀.ne')
  have hslice (y : ℝ^n) :
      ‖ε⁻¹ • (∫ t in Ioc (0 : ℝ) ε, normalSlice f y t) - normalSlice f y 0‖ ^ p ≤
        ε ^ (p - 1) * ∫ t, ‖normalDerivativeInSplit f (y, t)‖ ^ p
          ∂positiveNormalMeasure := by
    simpa only [deriv_normalSlice hf y] using
      norm_height_average_sub_rpow_le_integral_Ioi (normalSlice_contDiff hf y)
        (normalSlice_hasCompactSupport hfc y) hp hε
  calc
    _ ≤ ∫⁻ y : ℝ^n, ENNReal.ofReal
        (ε ^ (p - 1) * ∫ t, ‖normalDerivativeInSplit f (y, t)‖ ^ p
          ∂positiveNormalMeasure) :=
      lintegral_mono fun y ↦ ENNReal.ofReal_le_ofReal (hslice y)
    _ = ENNReal.ofReal (∫ y : ℝ^n,
        ε ^ (p - 1) * ∫ t, ‖normalDerivativeInSplit f (y, t)‖ ^ p
          ∂positiveNormalMeasure) :=
      (ofReal_integral_eq_lintegral_ofReal
        (henergy.integral_prod_left.const_mul _) (Filter.Eventually.of_forall fun y ↦
          mul_nonneg (Real.rpow_nonneg hε.le _)
            (integral_nonneg fun t ↦ Real.rpow_nonneg (norm_nonneg _) _))).symm
    _ = ENNReal.ofReal (ε ^ (p - 1) * ∫ z, ‖normalDerivativeInSplit f z‖ ^ p
        ∂((volume : Measure (ℝ^n)).prod positiveNormalMeasure)) := by
      rw [integral_const_mul, ← integral_prod _ henergy]
    _ = _ := by
      congr 1
      congr 1
      exact integral_joinTangentialNormal_eq_integral_upper
        (fun z ↦ ‖(∂[Fin.last n] f) z‖ ^ p)

end SobolevSpace.Trace.HalfSpace
