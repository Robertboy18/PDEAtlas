/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.SineSeries.IntervalL2
public import PDE.Parabolic.Heat.Spectral.HilbertEvolution
public import PDE.Parabolic.Heat.Spectral.Regularity

/-!
# The interval heat series for square-integrable initial data

The odd extension of interval `L²` data evolves in the Fourier Hilbert basis.
At positive time its paired sine series converges in the sup norm, and its
continuous representative is exactly the classical interval heat series.
At zero the Hilbert evolution attains the initial extension in `L²`.
-/

@[expose] public section

namespace HeatEquation

open MeasureTheory Set AddCircle PDE.Representations PDE.Analysis.Fourier.SineSeries
open scoped ENNReal NNReal Topology

/-- Fourier heat evolution of the odd extension of interval `L²` data. -/
noncomputable def intervalHeatL2 (g : ℝ → ℝ)
    (hg : MemLp g 2 (volume.restrict (Ioc 0 1))) (t : ℝ≥0) :
    Lp ℂ 2 (haarAddCircle (T := (2 : ℝ))) :=
  spectralHeatEvolution fourierBasis (fun k : ℤ ↦ ((k : ℝ) * Real.pi) ^ 2)
    (fun _ ↦ sq_nonneg _) (oddIntervalL2 g hg) t

/-- The `L²` evolution is the sine series with the computed interval coefficients.
This norm convergence holds at time zero as well as at positive time. -/
theorem hasSum_intervalHeatL2 {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc 0 1))) (t : ℝ≥0) :
    HasSum (fun n ↦ ((intervalCoefficient g n * intervalHeatTimeMode n t : ℝ) : ℂ) •
      sineL2Mode n) (intervalHeatL2 g hg t) := by
  have h := (hasSum_nat_add_iff' 1).mpr
    (hasSum_spectralHeatEvolution fourierBasis
      (fun k : ℤ ↦ ((k : ℝ) * Real.pi) ^ 2)
      (fun _ ↦ sq_nonneg _) (oddIntervalL2 g hg) t).nat_add_neg
  have hz : fourierCoeff (oddIntervalL2 g hg) 0 = 0 := by
    rw [fourierCoeff_oddIntervalL2]
    simp
  simp only [fourierBasis_repr, Finset.sum_range_one, Nat.cast_zero, neg_zero,
    hz, mul_zero, zero_smul, add_zero, sub_zero] at h
  unfold intervalHeatL2
  convert h using 1
  funext n
  rw [fourierCoeff_oddIntervalL2_pos hg, fourierCoeff_oddIntervalL2_neg hg,
    sineL2Mode_eq, smul_smul, smul_sub]
  simp only [intervalHeatTimeMode, intervalDirichletEigenvalue, Int.cast_neg,
    Int.cast_natCast, neg_mul, neg_sq, Nat.succ_eq_add_one, Complex.ofReal_mul,
    neg_div, mul_neg, neg_smul, sub_neg_eq_add]
  simp only [RCLike.ofReal_eq_complex_ofReal, mul_left_comm, mul_comm]

/-- The `L²` evolution is strongly continuous, including at the initial time. -/
theorem continuous_intervalHeatL2 {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc 0 1))) :
    Continuous (intervalHeatL2 g hg) :=
  continuous_spectralHeatEvolution _ _ _ _

/-- The initial `L²` vector is the odd extension of the supplied interval data. -/
@[simp] theorem intervalHeatL2_zero {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc 0 1))) :
    intervalHeatL2 g hg 0 = oddIntervalL2 g hg :=
  spectralHeatEvolution_zero _ _ _ _

/-- The heat series on the Fourier circle, as a continuous function. At positive time
the defining series is absolutely summable in the sup norm. -/
noncomputable def intervalHeatCircle (g : ℝ → ℝ) (t : ℝ) : C(AddCircle (2 : ℝ), ℂ) :=
  ∑' n, ((intervalCoefficient g n * intervalHeatTimeMode n t : ℝ) : ℂ) • sineCircleMode n

/-- Heat damping makes the continuous sine series absolutely summable for interval
`L²` data at every positive time. -/
theorem summable_intervalHeatCircle {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc 0 1))) {t : ℝ} (ht : 0 < t) :
    Summable (fun n ↦
      ((intervalCoefficient g n * intervalHeatTimeMode n t : ℝ) : ℂ) • sineCircleMode n) := by
  apply ((summable_intervalHeatMajorant 0 ht).mul_left
    (2 * ‖oddIntervalL2 g hg‖)).of_norm_bounded
  intro n
  rw [norm_smul, Complex.norm_real, norm_mul,
    Real.norm_of_nonneg (intervalHeatTimeMode_pos n t).le]
  calc
    _ ≤ ‖intervalCoefficient g n‖ * intervalHeatTimeMode n t * 1 :=
      mul_le_mul_of_nonneg_left (norm_sineCircleMode_le n)
        (mul_nonneg (norm_nonneg _) (intervalHeatTimeMode_pos n t).le)
    _ ≤ _ := by
      simpa only [mul_one, intervalHeatMajorant, pow_zero, one_mul] using
        mul_le_mul_of_nonneg_right (norm_intervalCoefficient_le hg n)
          (intervalHeatTimeMode_pos n t).le

/-- The continuous representative is the same pointwise sine series used in the
classical heat equation proofs. -/
theorem intervalHeatCircle_coe {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc 0 1))) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    intervalHeatCircle g t (x : AddCircle (2 : ℝ)) =
      (intervalHeatSeries (intervalCoefficient g) t x : ℂ) := by
  have h := (ContinuousMap.evalCLM ℂ (x : AddCircle (2 : ℝ))).hasSum
    (summable_intervalHeatCircle hg ht).hasSum
  have hs := Complex.ofRealCLM.hasSum
    (summable_intervalHeatSeries (norm_intervalCoefficient_le hg) ht x).hasSum
  simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply, smul_eq_mul,
    sineCircleMode_coe] at h
  simp only [Complex.ofRealCLM_apply, intervalHeatMode, Complex.ofReal_mul] at hs
  have hs' : HasSum
      (fun n ↦ (intervalCoefficient g n * intervalHeatTimeMode n t : ℂ) *
        (intervalDirichletSineMode n x : ℂ))
      (intervalHeatSeries (intervalCoefficient g) t x : ℂ) := by
    convert hs using 1
    · funext n
      ring
    · rfl
  exact h.unique (by simpa only [Complex.ofReal_mul] using hs')

/-- The positive-time continuous solution represents the Hilbert evolution. Thus the
classical series and the norm-continuous initial-value construction are one solution. -/
theorem toLp_intervalHeatCircle {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc 0 1))) {t : ℝ≥0} (ht : 0 < (t : ℝ)) :
    ContinuousMap.toLp 2 haarAddCircle ℂ (intervalHeatCircle g t) = intervalHeatL2 g hg t := by
  have h := (ContinuousMap.toLp 2 haarAddCircle ℂ).hasSum
    (summable_intervalHeatCircle hg ht).hasSum
  simp only [map_smul] at h
  exact h.unique (hasSum_intervalHeatL2 hg t)

end HeatEquation
