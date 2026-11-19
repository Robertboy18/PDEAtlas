/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Harmonic.Definitions
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import PDE.Elliptic.Classical.Harmonic.DerivativeEstimates.Integral
import PDE.Spaces.Sobolev.Compactness.Rellich.CellAverages

/-!
# Quadratic decay of harmonic mean oscillation

The interior derivative estimate and Cauchy–Schwarz bound harmonic oscillation
on a smaller ball by its radius squared times the mean-square deviation on the
larger ball. The constant depends only on the dimension. Only harmonicity and
square integrability on the open outer ball are required; no boundary bound is
assumed. This is the constant-coefficient decay step of the Campanato argument.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open PDE.Analysis
open scoped ENNReal

namespace LaplacianEquation

private theorem norm_sub_average_le_of_pairwise_bound
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {s : Set X}
    (hs : MeasurableSet s) (hs0 : μ s ≠ 0) (hsfin : μ s ≠ ∞)
    {f : X → ℝ} (hf : IntegrableOn f s μ) {x : X} {D : ℝ}
    (hD : ∀ y ∈ s, ‖f x - f y‖ ≤ D) :
    ‖f x - ⨍ y in s, f y ∂μ‖ ≤ D := by
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hsfin
  have hvol : 0 < μ.real s := ENNReal.toReal_pos hs0 hsfin
  have hav : f x - ⨍ y in s, f y ∂μ = ⨍ y in s, f x - f y ∂μ := by
    rw [average_fun_sub (integrable_const (f x)) hf, setAverage_const hs0 hsfin]
  rw [hav, setAverage_eq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvol)]
  calc
    _ ≤ (μ.real s)⁻¹ * (D * μ.real s) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hvol.le)
      simpa [measureReal_def] using
        (norm_integral_le_of_norm_le_const (μ := μ.restrict s)
          ((ae_restrict_mem hs).mono fun y hy ↦ hD y hy))
    _ = D := by field_simp

variable {n : ℕ} [Fact (0 < n)]

/-- The derivative throughout the half ball is controlled by the mean absolute
value on the outer ball. The function may be unbounded at the outer boundary. -/
theorem IsHarmonicPDE.norm_fderiv_le_average_abs
    {u : ℝ^n → ℝ} {z : ℝ^n} {R : ℝ}
    (hu : IsHarmonicPDE n u (ball z R)) (hR : 0 < R)
    (hint : IntegrableOn u (ball z R)) {x : ℝ^n} (hx : x ∈ ball z (R / 2)) :
    ‖fderiv ℝ u x‖ ≤ ((2 : ℝ) ^ (2 * n + 2) * n / R) *
      ⨍ y in ball z R, |u y| := by
  have hsub : ball x (R / 2) ⊆ ball z R := by
    apply ball_subset_ball'
    have := (mem_ball.mp hx).le
    linarith
  have hderiv := hu.norm_iteratedFDeriv_le_integral_abs (k := 1)
    (half_pos hR) hsub (hint.mono_set hsub)
  rw [norm_iteratedFDeriv_one] at hderiv
  have hI : (∫ y in ball x (R / 2), |u y|) ≤ ∫ y in ball z R, |u y| :=
    setIntegral_mono_set hint.abs (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _)
      (Filter.Eventually.of_forall hsub)
  have hbound := hderiv.trans (mul_le_mul_of_nonneg_left hI
    (div_nonneg (interiorDerivativeConstant_pos n 1).le (by positivity)))
  have hvol : volume.real (ball z R) = unitBallVolume n * R ^ n := by
    rw [measureReal_def, Measure.addHaar_ball_center volume z]
    exact ballVolume_eq_unitBallVolume_mul_pow n R hR.le
  refine hbound.trans_eq ?_
  rw [setAverage_eq, hvol, smul_eq_mul]
  simp only [interiorDerivativeConstant, one_ne_zero, ↓reduceIte, Nat.cast_one,
    mul_one, pow_one, div_pow, pow_add, pow_mul]
  field_simp
  ring_nf
  rw [show 2 ^ (n * 2) = (4 : ℝ) ^ n by
    rw [mul_comm n 2, pow_mul]; norm_num]

/-- Harmonic mean-square oscillation decays quadratically with the ratio of
radii. The outer deviation may be measured from any constant, in particular
the outer average. No regularity on the boundary of the outer ball is needed. -/
theorem IsHarmonicPDE.meanSquare_oscillation_le
    {u : ℝ^n → ℝ} {z : ℝ^n} {R r : ℝ}
    (hu : IsHarmonicPDE n u (ball z R))
    (hint : MemLp u 2 (volume.restrict (ball z R)))
    (hr : 0 < r) (hrR : r ≤ R / 2) (c : ℝ) :
    (⨍ x in ball z r, ‖u x - ⨍ y in ball z r, u y‖ ^ 2) ≤
      (((2 : ℝ) ^ (2 * n + 3) * n) * (r / R)) ^ 2 *
        ⨍ x in ball z R, ‖u x - c‖ ^ 2 := by
  have hR : 0 < R := by linarith
  have : IsFiniteMeasure (volume.restrict (ball z R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have : IsFiniteMeasure (volume.restrict (ball z r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hsub : ball z r ⊆ ball z R := ball_subset_ball (hrR.trans (by linarith))
  have hsmall : ball z r ⊆ ball z (R / 2) := ball_subset_ball hrR
  have huc : MemLp (fun x ↦ u x - c) 2 (volume.restrict (ball z R)) :=
    hint.sub (memLp_const c)
  have hucInt := huc.integrable (by norm_num)
  have huInt : IntegrableOn u (ball z R) := hint.integrable (by norm_num)
  let A : ℝ := ⨍ y in ball z R, |u y - c|
  let D : ℝ := ((2 : ℝ) ^ (2 * n + 2) * n / R) * A
  have hD : 0 ≤ D := by
    dsimp [D, A, average]
    positivity
  have hgrad (x : ℝ^n) (hx : x ∈ ball z (R / 2)) : ‖fderiv ℝ u x‖ ≤ D := by
    have hc := hu.sub (isHarmonicPDE_const c (ball z R)) isOpen_ball
    change IsHarmonicPDE n (fun y ↦ u y - c) (ball z R) at hc
    simpa only [fderiv_sub_const] using
      hc.norm_fderiv_le_average_abs hR hucInt hx
  have hpair (x : ℝ^n) (hx : x ∈ ball z r) (y : ℝ^n) (hy : y ∈ ball z r) :
      ‖u x - u y‖ ≤ D * (2 * r) := by
    have hd : ‖x - y‖ ≤ 2 * r := by
      rw [← dist_eq_norm]
      linarith [dist_triangle_right x y z, mem_ball.mp hx, mem_ball.mp hy]
    exact ((convex_ball z (R / 2)).norm_image_sub_le_of_norm_fderiv_le
      (fun w hw ↦ (hu.contDiffAt_of_isOpen isOpen_ball
        (ball_subset_ball (by linarith : R / 2 ≤ R) hw)).differentiableAt (by norm_num))
      hgrad (hsmall hy) (hsmall hx)).trans (mul_le_mul_of_nonneg_left hd hD)
  have hpt (x : ℝ^n) (hx : x ∈ ball z r) :
      ‖u x - ⨍ y in ball z r, u y‖ ^ 2 ≤ (D * (2 * r)) ^ 2 := by
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    exact norm_sub_average_le_of_pairwise_bound isOpen_ball.measurableSet
      (measure_ball_pos volume z hr).ne' measure_ball_lt_top.ne
      (huInt.mono_set hsub) (hpair x hx)
  have hosc : (⨍ x in ball z r, ‖u x - ⨍ y in ball z r, u y‖ ^ 2) ≤
      (D * (2 * r)) ^ 2 := calc
    _ ≤ ⨍ _x in ball z r, (D * (2 * r)) ^ 2 :=
      integral_mono_ae (((hint.mono_measure (Measure.restrict_mono hsub le_rfl)).sub
        (memLp_const _)).norm.integrable_sq).to_average (integrable_const _).to_average
        (((ae_restrict_mem isOpen_ball.measurableSet).mono fun x hx ↦ hpt x hx).filter_mono
          (Measure.ae_smul_measure_le _))
    _ = _ := setAverage_const (measure_ball_pos volume z hr).ne' measure_ball_lt_top.ne _
  have hJ : A ^ 2 ≤ ⨍ y in ball z R, ‖u y - c‖ ^ 2 := by
    simpa only [Real.norm_eq_abs] using
      SobolevSpace.GraphSpace.Rellich.sq_setAverage_le_setAverage_sq
        (ball z R) (measure_ball_pos volume z hR).ne' measure_ball_lt_top.ne
        (fun y ↦ |u y - c|) hucInt.abs huc.norm.integrable_sq
  calc
    _ ≤ (D * (2 * r)) ^ 2 := hosc
    _ = (((2 : ℝ) ^ (2 * n + 3) * n) * (r / R)) ^ 2 * A ^ 2 := by
      dsimp [D]
      rw [show 2 * n + 3 = (2 * n + 2) + 1 by omega, pow_succ]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hJ (sq_nonneg _)

end LaplacianEquation
