/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.SineSeries.SmoothData

/-!
# Odd reflection of interval Dirichlet data

A continuous function on `[0, 1]` with zero endpoint values defines a continuous
function on the circle of length two by odd reflection. This construction uses only
the interval values; no differentiability of the reflected function is required.
-/

@[expose] public section

namespace PDE.Analysis.Fourier.SineSeries

open MeasureTheory Set

/-- Odd reflection across zero, used on `[-1, 1]`. -/
noncomputable def oddReflection (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ≤ 0 then -g (-x) else g x

/-- Odd reflection preserves continuity across zero when the initial value is zero. -/
theorem continuousOn_oddReflection {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 0 1)) (hzero : g 0 = 0) :
    ContinuousOn (oddReflection g) (Icc (-1) 1) := by
  apply ContinuousOn.if
  · intro x hx
    have hfront : x ∈ frontier (Iic (0 : ℝ)) := hx.2
    have hx0 : x = 0 := by simpa only [frontier_Iic, mem_singleton_iff] using hfront
    simp [hx0, hzero]
  · apply (hg.comp continuous_neg.continuousOn ?_).neg
    intro x hx
    change x ∈ Icc (-1) 1 ∩ closure (Iic (0 : ℝ)) at hx
    simp only [mem_inter_iff, mem_Icc, closure_Iic, mem_Iic] at hx
    change 0 ≤ -x ∧ -x ≤ 1
    constructor <;> linarith [hx.1.1, hx.2]
  · apply hg.mono
    intro x hx
    simp only [not_le] at hx
    change x ∈ Icc (-1) 1 ∩ closure (Ioi (0 : ℝ)) at hx
    simp only [closure_Ioi, mem_inter_iff, mem_Icc, mem_Ici] at hx
    exact ⟨hx.2, hx.1.2⟩

/-- The odd reflected interval data as a continuous complex function on the circle. -/
noncomputable def oddIntervalMap (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 1))
    (hzero : g 0 = 0) (hone : g 1 = 0) : C(AddCircle (2 : ℝ), ℂ) where
  toFun := AddCircle.liftIoc 2 (-1) (fun x ↦ (oddReflection g x : ℂ))
  continuous_toFun := AddCircle.liftIoc_continuous
    (by norm_num [oddReflection, hone])
    (by
      norm_num only [show (-1 : ℝ) + 2 = 1 by norm_num]
      exact Complex.continuous_ofReal.comp_continuousOn (continuousOn_oddReflection hg hzero))

/-- Real representatives in the closed fundamental interval evaluate to the reflection. -/
theorem oddIntervalMap_coe {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 1))
    (hzero : g 0 = 0) (hone : g 1 = 0) {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    oddIntervalMap g hg hzero hone (x : AddCircle (2 : ℝ)) = (oddReflection g x : ℂ) := by
  change AddCircle.liftIoc (2 : ℝ) (-1) (fun y ↦ (oddReflection g y : ℂ))
    (x : AddCircle (2 : ℝ)) = _
  by_cases hleft : x = -1
  · subst x
    rw [← AddCircle.coe_add_period, AddCircle.liftIoc_coe_apply (by norm_num)]
    norm_num [oddReflection, hone]
  · exact AddCircle.liftIoc_coe_apply ⟨lt_of_le_of_ne hx.1 (Ne.symm hleft),
      by linarith [hx.2]⟩

/-- Reflection does not change the original data on the unit interval. -/
theorem oddReflection_of_nonneg {g : ℝ → ℝ} (hzero : g 0 = 0) {x : ℝ} (hx : 0 ≤ x) :
    oddReflection g x = g x := by
  by_cases h : x = 0
  · simp [h, oddReflection, hzero]
  · simp [oddReflection, not_le.mpr (lt_of_le_of_ne hx (Ne.symm h))]

/-- The reflected values at negative arguments have the expected sign. -/
theorem oddReflection_neg_of_nonneg (g : ℝ → ℝ) {x : ℝ} (hx : 0 ≤ x) :
    oddReflection g (-x) = -g x := by
  simp [oddReflection, neg_nonpos.mpr hx]

/-- The odd real part of the circle function reconstructs the interval data. -/
theorem oddRealPart_oddIntervalMap {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 1))
    (hzero : g 0 = 0) (hone : g 1 = 0) {x : ℝ} (hx : x ∈ Icc 0 1) :
    oddRealPart (oddIntervalMap g hg hzero hone) x = g x := by
  rw [oddRealPart, oddIntervalMap_coe hg hzero hone (by constructor <;> linarith [hx.1, hx.2]),
    oddIntervalMap_coe hg hzero hone (by constructor <;> linarith [hx.1, hx.2]),
    oddReflection_of_nonneg hzero hx.1, oddReflection_neg_of_nonneg g hx.1]
  simp only [Complex.ofReal_re]
  ring

private theorem integral_mul_oddIntervalMap {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 0 1)) (hzero : g 0 = 0) (hone : g 1 = 0)
    (K : ℝ → ℂ) (hK : Continuous K) :
    (∫ x in (-1 : ℝ)..1,
      K x * oddIntervalMap g hg hzero hone (x : AddCircle (2 : ℝ))) =
      ∫ x in (0 : ℝ)..1, (K x - K (-x)) * (g x : ℂ) := by
  let F : ℝ → ℂ := fun x ↦ oddIntervalMap g hg hzero hone (x : AddCircle (2 : ℝ))
  have hF : Continuous F := (oddIntervalMap g hg hzero hone).continuous.comp
    (AddCircle.continuous_mk' _)
  have hp (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : F x = (g x : ℂ) := by
    dsimp only [F]
    rw [oddIntervalMap_coe hg hzero hone (by constructor <;> linarith [hx.1, hx.2]),
      oddReflection_of_nonneg hzero hx.1]
  have hn (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : F (-x) = -(g x : ℂ) := by
    dsimp only [F]
    rw [oddIntervalMap_coe hg hzero hone (by constructor <;> linarith [hx.1, hx.2]),
      oddReflection_neg_of_nonneg g hx.1, Complex.ofReal_neg]
  have hpos : (∫ x in (0 : ℝ)..1, K x * F x) =
      ∫ x in (0 : ℝ)..1, K x * (g x : ℂ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [hp x (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx)]
  have hneg : (∫ x in (-1 : ℝ)..0, K x * F x) =
      ∫ x in (0 : ℝ)..1, -(K (-x) * (g x : ℂ)) := by
    rw [← show (∫ x in (0 : ℝ)..1, K (-x) * F (-x)) =
      ∫ x in (-1 : ℝ)..0, K x * F x from by
        simpa only [neg_zero] using
          (intervalIntegral.integral_comp_neg (f := fun x ↦ K x * F x)
            (a := (0 : ℝ)) (b := 1))]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [hn x (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx), mul_neg]
  change (∫ x in (-1 : ℝ)..1, K x * F x) = _
  have hKF : Continuous (fun x ↦ K x * F x) := hK.mul hF
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hKF.intervalIntegrable (-1) 0) (hKF.intervalIntegrable 0 1),
    hneg, hpos, intervalIntegral.integral_neg]
  have hg' := Complex.continuous_ofReal.comp_continuousOn hg
  have hi : IntervalIntegrable (fun x ↦ K x * (g x : ℂ)) volume 0 1 :=
    (hK.continuousOn.mul (show ContinuousOn (fun x ↦ (g x : ℂ)) (uIcc 0 1) from by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Function.comp_def]
        using hg')).intervalIntegrable
  have hj : IntervalIntegrable (fun x ↦ K (-x) * (g x : ℂ)) volume 0 1 :=
    ((hK.comp continuous_neg).continuousOn.mul
      (show ContinuousOn (fun x ↦ (g x : ℂ)) (uIcc 0 1) from by
        simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Function.comp_def]
          using hg')).intervalIntegrable
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub hi hj]
  ring

/-- The odd part of a Fourier character is its sine component. -/
theorem fourier_sub_reflection (k : ℤ) (x : ℝ) :
    fourier (-k) (x : AddCircle (2 : ℝ)) -
      fourier (-k) ((-x : ℝ) : AddCircle (2 : ℝ)) =
    -2 * Complex.I * (Real.sin ((k : ℝ) * Real.pi * x) : ℂ) := by
  have he (y : ℝ) : fourier (-k) (y : AddCircle (2 : ℝ)) =
      Complex.exp (((-(k : ℝ) * Real.pi * y : ℝ) : ℂ) * Complex.I) := by
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  rw [he, he]
  apply Complex.ext <;>
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.exp_re, Complex.exp_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
      mul_zero, sub_zero, zero_sub, add_zero, zero_add,
      mul_one, one_mul, Real.exp_zero, mul_neg, neg_mul, neg_neg,
      Real.sin_neg, Real.cos_neg] <;> norm_num
  ring

/-- Fourier coefficients of odd interval reflection are imaginary sine integrals.
The normalization uses Haar measure of total mass one on the circle of length two. -/
theorem fourierCoeff_oddIntervalMap {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 1))
    (hzero : g 0 = 0) (hone : g 1 = 0) (k : ℤ) :
    fourierCoeff (oddIntervalMap g hg hzero hone) k =
      -Complex.I * (∫ x in (0 : ℝ)..1, g x * Real.sin ((k : ℝ) * Real.pi * x) : ℝ) := by
  rw [fourierCoeff_eq_intervalIntegral _ _ (-1)]
  simp only [show (-1 : ℝ) + 2 = 1 by norm_num, smul_eq_mul]
  rw [integral_mul_oddIntervalMap hg hzero hone
    (fun x ↦ fourier (-k) (x : AddCircle (2 : ℝ))) (by fun_prop)]
  simp_rw [fourier_sub_reflection]
  have hmul (x : ℝ) :
      -2 * Complex.I * (Real.sin ((k : ℝ) * Real.pi * x) : ℂ) * (g x : ℂ) =
        (-2 * Complex.I) * ((g x * Real.sin ((k : ℝ) * Real.pi * x) : ℝ) : ℂ) := by
    push_cast
    ring
  simp_rw [hmul]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
  simp only [Complex.real_smul]
  push_cast
  ring

/-- The usual unnormalized unit-interval sine coefficient. -/
noncomputable def intervalCoefficient (g : ℝ → ℝ) (n : ℕ) : ℝ :=
  2 * ∫ x in (0 : ℝ)..1, g x * PDE.Representations.intervalDirichletSineMode n x

/-- The Fourier and interval-integral constructions give the same sine coefficients. -/
theorem coefficient_oddIntervalMap {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 1))
    (hzero : g 0 = 0) (hone : g 1 = 0) (n : ℕ) :
    coefficient (oddIntervalMap g hg hzero hone) n = intervalCoefficient g n := by
  rw [coefficient, fourierCoeff_oddIntervalMap hg hzero hone,
    fourierCoeff_oddIntervalMap hg hzero hone]
  simp only [Int.cast_neg, Int.cast_natCast, neg_mul, Real.sin_neg, mul_neg,
    intervalIntegral.integral_neg, Complex.ofReal_neg, Complex.mul_im,
    Complex.neg_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, neg_mul, neg_neg,
    intervalCoefficient, PDE.Representations.intervalDirichletSineMode]
  ring

end PDE.Analysis.Fourier.SineSeries
