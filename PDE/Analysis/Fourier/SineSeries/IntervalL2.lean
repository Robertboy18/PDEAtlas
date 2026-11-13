/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.SineSeries.IntervalLp

/-!
# Sine reconstruction of square-integrable interval data

Pairing the positive and negative vectors of the Fourier Hilbert basis gives sine
reconstruction in `L²`. The coefficients are computed from the interval data.
The norm topology here is that of the odd extension on the circle with normalized
Haar measure.
-/

@[expose] public section

namespace PDE.Analysis.Fourier.SineSeries

open MeasureTheory Set AddCircle PDE.Representations
open scoped ENNReal

/-- The sine mode as a continuous function on the circle of length two. -/
noncomputable def sineCircleMode (n : ℕ) : C(AddCircle (2 : ℝ), ℂ) :=
  (-Complex.I / 2) • (fourier (n.succ : ℤ) - fourier (-(n.succ : ℤ)))

/-- Circle sine modes evaluate to the standard real interval sine modes. -/
theorem sineCircleMode_coe (n : ℕ) (x : ℝ) :
    sineCircleMode n (x : AddCircle (2 : ℝ)) = (intervalDirichletSineMode n x : ℂ) := by
  have h := fourier_sub_reflection (n.succ : ℤ) x
  have hn : fourier (-(n.succ : ℤ)) ((-x : ℝ) : AddCircle (2 : ℝ)) =
      fourier (n.succ : ℤ) (x : AddCircle (2 : ℝ)) := by
    simp only [fourier_apply, QuotientAddGroup.mk_neg, smul_neg, neg_smul, neg_neg]
  rw [hn] at h
  change (-Complex.I / 2) *
    (fourier (n.succ : ℤ) (x : AddCircle (2 : ℝ)) -
      fourier (-(n.succ : ℤ)) (x : AddCircle (2 : ℝ))) = _
  rw [← neg_sub, h]
  simp only [intervalDirichletSineMode, Int.cast_natCast]
  calc
    _ = -(Complex.I * Complex.I) *
        (Real.sin ((n.succ : ℝ) * Real.pi * x) : ℂ) := by ring
    _ = _ := by simp [Complex.I_mul_I]

/-- Circle sine modes have sup norm at most one. -/
theorem norm_sineCircleMode_le (n : ℕ) : ‖sineCircleMode n‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ (by norm_num)).mpr
  intro x
  induction x using QuotientAddGroup.induction_on
  rw [sineCircleMode_coe, Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_sin_le_one _

/-- The sine mode as a vector in circle `L²`. -/
noncomputable def sineL2Mode (n : ℕ) : Lp ℂ 2 (haarAddCircle (T := (2 : ℝ))) :=
  ContinuousMap.toLp 2 haarAddCircle ℂ (sineCircleMode n)

/-- Each sine vector is the corresponding pair of Fourier basis vectors. -/
theorem sineL2Mode_eq (n : ℕ) :
    sineL2Mode n = (-Complex.I / 2) •
      (fourierBasis (n.succ : ℤ) - fourierBasis (-(n.succ : ℤ))) := by
  rw [sineL2Mode, sineCircleMode, map_smul, map_sub, coe_fourierBasis]

/-- Positive Fourier coefficients of odd interval data are the sine coefficients
multiplied by `-i/2`. -/
theorem fourierCoeff_oddIntervalL2_pos {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc 0 1))) (n : ℕ) :
    fourierCoeff (oddIntervalL2 g hg) (n.succ : ℤ) =
      (-Complex.I / 2) * (intervalCoefficient g n : ℂ) := by
  rw [fourierCoeff_oddIntervalL2, intervalCoefficient]
  simp only [intervalDirichletSineMode, Int.cast_natCast]
  push_cast
  ring

/-- Negative Fourier coefficients have the opposite sign. -/
theorem fourierCoeff_oddIntervalL2_neg {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc 0 1))) (n : ℕ) :
    fourierCoeff (oddIntervalL2 g hg) (-(n.succ : ℤ)) =
      (Complex.I / 2) * (intervalCoefficient g n : ℂ) := by
  rw [fourierCoeff_oddIntervalL2, intervalCoefficient]
  simp only [intervalDirichletSineMode, Int.cast_neg, Int.cast_natCast,
    neg_mul, Real.sin_neg, mul_neg, intervalIntegral.integral_neg, Complex.ofReal_neg]
  push_cast
  ring

/-- Square integrability gives a uniform bound on the sine coefficients. -/
theorem norm_intervalCoefficient_le {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc 0 1))) (n : ℕ) :
    ‖intervalCoefficient g n‖ ≤ 2 * ‖oddIntervalL2 g hg‖ := by
  have h := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (fourierBasis.repr (oddIntervalL2 g hg)) (n.succ : ℤ)
  rw [fourierBasis_repr, fourierCoeff_oddIntervalL2_pos hg, norm_mul, norm_div,
    norm_neg, Complex.norm_I, Complex.norm_two, Complex.norm_real,
    fourierBasis.repr.norm_map] at h
  linarith

/-- The computed sine coefficients reconstruct the odd interval extension in `L²`.
This uses Fourier completeness, without assuming an expansion of the initial data. -/
theorem hasSum_intervalCoefficient_sineL2Mode {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc 0 1))) :
    HasSum (fun n ↦ (intervalCoefficient g n : ℂ) • sineL2Mode n) (oddIntervalL2 g hg) := by
  have h := (hasSum_nat_add_iff' 1).mpr
    (HilbertBasis.hasSum_repr fourierBasis (oddIntervalL2 g hg)).nat_add_neg
  have hz : fourierCoeff (oddIntervalL2 g hg) 0 = 0 := by
    rw [fourierCoeff_oddIntervalL2]
    simp
  simp only [fourierBasis_repr, Finset.sum_range_one, Nat.cast_zero, neg_zero,
    hz, zero_smul, add_zero, sub_zero] at h
  convert h using 1
  funext n
  rw [fourierCoeff_oddIntervalL2_pos hg, fourierCoeff_oddIntervalL2_neg hg]
  rw [sineL2Mode_eq, smul_smul, smul_sub]
  simp only [Nat.succ_eq_add_one, neg_div, neg_mul, neg_smul,
    sub_neg_eq_add, mul_comm]

end PDE.Analysis.Fourier.SineSeries
