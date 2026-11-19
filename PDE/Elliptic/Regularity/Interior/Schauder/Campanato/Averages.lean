/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Comparing averages on nested balls

The difference between averages on two nested balls is controlled by the mean
oscillation on the larger ball and their volume ratio. In Euclidean space,
doubling the radius gives the factor `2^n`. No pointwise regularity is required.
-/

@[expose] public noncomputable section

open MeasureTheory MeasureTheory.Measure Metric Set
open scoped ENNReal

namespace PDE.Elliptic.Regularity.Campanato

private theorem norm_setAverage_sub_le_integral
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {s t : Set X}
    (hs : 0 < μ.real s) (ht : μ t ≠ ∞) (hst : s ⊆ t)
    {f : X → ℝ} (hf : IntegrableOn f t μ) (c : ℝ) :
    μ.real s * ‖(⨍ x in s, f x ∂μ) - c‖ ≤ ∫ x in t, ‖f x - c‖ ∂μ := by
  have hsfinite : μ s ≠ ∞ := (lt_of_le_of_lt (measure_mono hst) ht.lt_top).ne
  have hsnonzero : μ s ≠ 0 := by
    intro h
    simp [measureReal_def, h] at hs
  have hint : IntegrableOn (fun x ↦ f x - c) t μ :=
    hf.sub (integrableOn_const ht)
  have hav : (⨍ x in s, f x ∂μ) - c = ⨍ x in s, f x - c ∂μ := by
    rw [average_fun_sub (hf.mono_set hst) (integrableOn_const hsfinite),
      setAverage_const hsnonzero hsfinite]
  rw [hav, setAverage_eq, smul_eq_mul, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hs.le), ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
  exact (norm_integral_le_integral_norm _).trans
    (setIntegral_mono_set hint.norm (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
      (Filter.Eventually.of_forall hst))

variable {n : ℕ}

/-- A ball average differs from a constant by at most `2^n` times the mean
deviation from that constant on any containing ball of twice the radius. -/
theorem norm_average_sub_le_double
    {x y : ℝ^n} {r : ℝ} (hr : 0 < r)
    (hsub : closedBall y r ⊆ closedBall x (2 * r))
    {f : ℝ^n → ℝ} (hf : IntegrableOn f (closedBall x (2 * r))) (c : ℝ) :
    ‖(⨍ z in closedBall y r, f z) - c‖ ≤
      (2 : ℝ) ^ n * ⨍ z in closedBall x (2 * r), ‖f z - c‖ := by
  have hs : 0 < volume.real (closedBall y r) :=
    ENNReal.toReal_pos (measure_closedBall_pos volume y hr).ne' measure_closedBall_lt_top.ne
  have hscale : volume.real (closedBall x (2 * r)) =
      (2 : ℝ) ^ n * volume.real (closedBall y r) := by
    simp only [measureReal_def, addHaar_closedBall volume x (by positivity : 0 ≤ 2 * r),
      addHaar_closedBall volume y hr.le, finrank_euclideanSpace_fin, ENNReal.toReal_mul]
    rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity),
      mul_pow, mul_assoc]
  have h := norm_setAverage_sub_le_integral volume hs measure_closedBall_lt_top.ne hsub hf c
  have hav : (∫ z in closedBall x (2 * r), ‖f z - c‖) =
      volume.real (closedBall x (2 * r)) *
        ⨍ z in closedBall x (2 * r), ‖f z - c‖ := by
    rw [setAverage_eq, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀, one_mul]
    exact (by rw [hscale]; positivity : 0 < volume.real (closedBall x (2 * r))).ne'
  rw [hav, hscale] at h
  exact (mul_le_mul_iff_right₀ hs).mp
    (by simpa only [mul_comm, mul_left_comm, mul_assoc] using h)

end PDE.Elliptic.Regularity.Campanato
