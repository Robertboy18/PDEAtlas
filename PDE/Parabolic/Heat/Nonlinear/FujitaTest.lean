/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.PolynomialBump.Basic
public import PDE.FDeriv.Calculus.SecondDirectionalDerivative
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral
import CAS.ExactTactic

/-!
# Expanding compact tests for Fujita blowup

The cubic positive part of `1 - ‖(x-z)/R‖²` is a nonnegative compact C² test.
Its mass scales as `Rⁿ` and its Laplacian is bounded below by `-C/R²` times
itself. Compact tests avoid any decay assumptions when testing a smooth
whole-space solution.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open PDE (laplacian)
open PDE.Analysis

namespace HeatEquation.Nonlinear

variable {n : ℕ}

/-- A nonnegative compact C² test at spatial scale `R`, centered at `z`. -/
def fujitaCutoff (z : ℝ^n) (R : ℝ) (x : ℝ^n) : ℝ :=
  polynomialBallBump (0 : ℝ^n) 1 (R⁻¹ • (x - z))

/-- The expanding test is globally C², including its support sphere. -/
theorem contDiff_fujitaCutoff (z : ℝ^n) (R : ℝ) :
    ContDiff ℝ 2 (fujitaCutoff z R) :=
  (contDiff_polynomialBallBump 0 1).comp
    ((contDiff_id.sub contDiff_const).const_smul R⁻¹)

/-- Rescaling the fixed test is the same as multiplying the radius-`R`
polynomial bump by `R⁻⁶`. -/
theorem fujitaCutoff_eq_scaled_bump (z : ℝ^n) {R : ℝ} (hR : 0 < R) :
    fujitaCutoff z R = fun x ↦ R⁻¹ ^ 6 * polynomialBallBump z R x := by
  funext x
  simp only [fujitaCutoff, polynomialBallBump, sub_zero, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hR), one_pow]
  have hsq : 0 < R ^ 2 := sq_pos_of_pos hR
  have heq : 1 - (R⁻¹ * ‖x - z‖) ^ 2 = (R ^ 2 - ‖x - z‖ ^ 2) / R ^ 2 := by
    cas using [hR]
  rw [heq]
  by_cases h : 0 ≤ R ^ 2 - ‖x - z‖ ^ 2
  · rw [posPart_eq_self.mpr h, posPart_eq_self.mpr (div_nonneg h hsq.le)]
    cas using [hR]
  · rw [posPart_eq_zero.mpr (le_of_not_ge h),
      posPart_eq_zero.mpr (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) hsq.le)]
    simp

/-- The expanding test has compact support in the closed ball of radius `R`. -/
theorem hasCompactSupport_fujitaCutoff (z : ℝ^n) {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (fujitaCutoff z R) := by
  apply HasCompactSupport.intro (isCompact_closedBall z R)
  intro x hx
  rw [fujitaCutoff_eq_scaled_bump z hR]
  dsimp only
  rw [polynomialBallBump_eq_zero hR.le, mul_zero]
  exact (not_le.mp (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx)).le

/-- The test is nonnegative everywhere. -/
theorem fujitaCutoff_nonneg (z : ℝ^n) (R : ℝ) (x : ℝ^n) :
    0 ≤ fujitaCutoff z R x := polynomialBallBump_nonneg _ _ _

/-- The test equals one at its center, at every scale. -/
@[simp]
theorem fujitaCutoff_self (z : ℝ^n) (R : ℝ) : fujitaCutoff z R z = 1 := by
  simp [fujitaCutoff]

/-- The test has a finite positive mass. -/
theorem integral_fujitaCutoff_pos (z : ℝ^n) {R : ℝ} (hR : 0 < R) :
    0 < ∫ x, fujitaCutoff z R x :=
  integral_pos_of_integrable_nonneg_nonzero (contDiff_fujitaCutoff z R).continuous
    ((contDiff_fujitaCutoff z R).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_fujitaCutoff z hR)) (fujitaCutoff_nonneg z R)
    (by simp : fujitaCutoff z R z ≠ 0)

/-- The whole-space integral of the test scales with spatial dimension. -/
theorem integral_fujitaCutoff (z : ℝ^n) {R : ℝ} (hR : 0 < R) :
    (∫ x, fujitaCutoff z R x) = R ^ n * ∫ x, fujitaCutoff (0 : ℝ^n) 1 x := by
  unfold fujitaCutoff
  simp only [sub_zero, inv_one, one_smul]
  have htranslate := integral_sub_right_eq_self
    (μ := (volume : Measure (ℝ^n)))
    (fun x : ℝ^n ↦ polynomialBallBump (0 : ℝ^n) 1 (R⁻¹ • x)) z
  rw [htranslate]
  simpa only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] using
    Measure.integral_comp_inv_smul_of_nonneg volume
      (polynomialBallBump (0 : ℝ^n) 1) hR.le

/-- Enlarging the scale from one only increases the test. -/
theorem fujitaCutoff_one_le (z x : ℝ^n) {R : ℝ} (hR : 1 ≤ R) :
    fujitaCutoff z 1 x ≤ fujitaCutoff z R x := by
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  simp only [fujitaCutoff, polynomialBallBump, sub_zero, inv_one, one_smul, one_pow,
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRpos)]
  apply pow_le_pow_left₀ (posPart_nonneg _) _ 3
  apply sup_le_sup_right
  apply sub_le_sub_left
  apply (sq_le_sq₀ (mul_nonneg (inv_nonneg.mpr hRpos.le) (norm_nonneg _))
    (norm_nonneg _)).mpr
  exact mul_le_of_le_one_left (norm_nonneg _) ((inv_le_one₀ hRpos).mpr hR)

/-- The Laplacian of the cubic ball bump, including its support sphere. -/
theorem laplacian_polynomialBallBump (z : ℝ^n) (R : ℝ) (x : ℝ^n) :
    laplacian (polynomialBallBump z R) x =
      24 * (R ^ 2 - ‖x - z‖ ^ 2)⁺ * ‖x - z‖ ^ 2 -
        6 * (n : ℝ) * (R ^ 2 - ‖x - z‖ ^ 2)⁺ ^ 2 := by
  have heq : laplacian (polynomialBallBump z R) x =
      ∑ i : Fin n, secondDirectionalDerivative (polynomialBallBump z R) x
        (EuclideanSpace.single i (1 : ℝ)) := by
    simp [secondDirectionalDerivative_eq_sum (contDiff_polynomialBallBump z R).contDiffAt,
      laplacian]
  rw [heq]
  simp only [secondDirectionalDerivative_polynomialBallBump,
    EuclideanSpace.inner_single_right, starRingEnd_apply, star_trivial, mul_one, one_mul,
    PiLp.norm_single,
    norm_one, one_pow, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hs : (∑ i : Fin n, (x - z).ofLp i ^ 2) = ‖x - z‖ ^ 2 :=
    (EuclideanSpace.real_norm_sq_eq (x - z)).symm
  rw [hs]
  cas

/-- A scale-invariant Laplacian lower bound for the compact test. -/
theorem neg_mul_fujitaCutoff_le_laplacian (z : ℝ^n) {R : ℝ} (hR : 0 < R) (x : ℝ^n) :
    -(((n : ℝ) + 4) ^ 2 / R ^ 2) * fujitaCutoff z R x ≤
      laplacian (fujitaCutoff z R) x := by
  rw [fujitaCutoff_eq_scaled_bump z hR, PDE.laplacian_const_smul,
    laplacian_polynomialBallBump]
  have hbase : -(((n : ℝ) + 4) ^ 2 / R ^ 2) * polynomialBallBump z R x ≤
      24 * (R ^ 2 - ‖x - z‖ ^ 2)⁺ * ‖x - z‖ ^ 2 -
        6 * (n : ℝ) * (R ^ 2 - ‖x - z‖ ^ 2)⁺ ^ 2 := by
    unfold polynomialBallBump
    by_cases hgap : 0 ≤ R ^ 2 - ‖x - z‖ ^ 2
    · rw [posPart_eq_self.mpr hgap]
      have heq : R ^ 2 *
          (24 * (R ^ 2 - ‖x - z‖ ^ 2) * ‖x - z‖ ^ 2 -
            6 * (n : ℝ) * (R ^ 2 - ‖x - z‖ ^ 2) ^ 2) +
          ((n : ℝ) + 4) ^ 2 * (R ^ 2 - ‖x - z‖ ^ 2) ^ 3 =
          (R ^ 2 - ‖x - z‖ ^ 2) *
            ((((n : ℝ) + 4) * (R ^ 2 - ‖x - z‖ ^ 2) - 3 * R ^ 2) ^ 2 +
              15 * R ^ 4) := by cas
      have hn : 0 ≤ (R ^ 2 - ‖x - z‖ ^ 2) *
          ((((n : ℝ) + 4) * (R ^ 2 - ‖x - z‖ ^ 2) - 3 * R ^ 2) ^ 2 +
            15 * R ^ 4) := mul_nonneg hgap (by positivity)
      rw [← heq] at hn
      apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hR)).mp
      have hc : -(((n : ℝ) + 4) ^ 2 / R ^ 2) *
          (R ^ 2 - ‖x - z‖ ^ 2) ^ 3 * R ^ 2 =
          -((n : ℝ) + 4) ^ 2 * (R ^ 2 - ‖x - z‖ ^ 2) ^ 3 := by cas using [hR]
      rw [mul_comm (R ^ 2) (-(((n : ℝ) + 4) ^ 2 / R ^ 2) *
        (R ^ 2 - ‖x - z‖ ^ 2) ^ 3), hc]
      nlinarith
    · simp [posPart_eq_zero.mpr (le_of_not_ge hgap)]
  simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left hbase
    (pow_nonneg (inv_nonneg.mpr hR.le) 6)

end HeatEquation.Nonlinear
