/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Measure.Haar.Unique
import CAS.ExactTactic

/-!
# Semiconcavity from an almost-everywhere derivative slope bound

For a Lipschitz real function, the fundamental theorem of calculus applies to
each difference of translates. Integrating an almost-everywhere one-sided
bound for its derivative proves the second-difference bound. Continuity then
removes the exceptional increments. The derivative and its slope inequality
need only hold almost everywhere.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped NNReal

namespace PDE.Analysis.Scalar

/-- A one-sided bound on the almost-everywhere derivative of a Lipschitz
function gives its pointwise spatial semiconcavity bound. The increment in the
slope hypothesis is itself only quantified almost everywhere. -/
theorem secondDifference_le_of_lipschitz_ae_deriv_slope
    {v q : ℝ → ℝ} {L : ℝ≥0} (hv : LipschitzWith L v)
    (hderiv : ∀ᵐ x ∂volume, HasDerivAt v (q x) x)
    {K : ℝ}
    (hslope : ∀ᵐ z ∂volume, 0 < z → ∀ᵐ x ∂volume, q (x + z) - q x ≤ K * z) :
    ∀ x z, v (x + z) - 2 * v x + v (x - z) ≤ K * z ^ 2 := by
  have hpositive : ∀ᵐ z ∂volume, 0 < z →
      ∀ x, v (x + z) - 2 * v x + v (x - z) ≤ K * z ^ 2 := by
    filter_upwards [hslope] with z hz hzpos
    have hshift : ∀ᵐ x ∂volume, HasDerivAt v (q (x + z)) (x + z) :=
      (measurePreserving_add_right volume z).quasiMeasurePreserving.ae hderiv
    let d : ℝ → ℝ := fun x ↦ v (x + z) - v x
    have hd : LipschitzWith (L + L) d := by
      simpa only [mul_one, d, Function.comp_apply] using
        (hv.comp (isometry_add_right z).lipschitzWith).sub hv
    have hbound : ∀ᵐ x ∂volume, deriv d x ≤ K * z := by
      filter_upwards [hderiv, hshift, hz hzpos] with x hx hxz hs
      have hdx : HasDerivAt d (q (x + z) - q x) x := by
        simpa only [Function.comp_def, id_eq, Pi.sub_apply, mul_one, d] using
          (hxz.comp x ((hasDerivAt_id x).add_const z)).fun_sub hx
      simpa only [hdx.deriv] using hs
    intro x
    have hAC : AbsolutelyContinuousOnInterval d (x - z) x :=
      hd.lipschitzOnWith.absolutelyContinuousOnInterval
    calc
      v (x + z) - 2 * v x + v (x - z) = d x - d (x - z) := by
        dsimp only [d]
        rw [sub_add_cancel]
        cas
      _ = ∫ y in (x - z)..x, deriv d y := hAC.integral_deriv_eq_sub.symm
      _ ≤ ∫ _y in (x - z)..x, K * z :=
        intervalIntegral.integral_mono_ae (sub_le_self x hzpos.le)
          hAC.intervalIntegrable_deriv intervalIntegrable_const hbound
      _ = K * z ^ 2 := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        cas
  have hnegative := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
    hpositive
  have hall : ∀ᵐ z ∂volume,
      ∀ x, v (x + z) - 2 * v x + v (x - z) ≤ K * z ^ 2 := by
    filter_upwards [hpositive, hnegative] with z hz hneg
    intro x
    rcases lt_trichotomy 0 z with hpos | hzero | hnegz
    · exact hz hpos x
    · simp only [← hzero, add_zero, sub_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
      cas
    · calc
        v (x + z) - 2 * v x + v (x - z) =
            v (x + -z) - 2 * v x + v (x - -z) := by
          simp only [← sub_eq_add_neg, sub_neg_eq_add]
          cas
        _ ≤ K * (-z) ^ 2 := hneg (neg_pos.mpr hnegz) x
        _ = K * z ^ 2 := by rw [neg_sq]
  intro x z
  have hae : ∀ᵐ z ∂volume,
      v (x + z) - 2 * v x + v (x - z) ≤ K * z ^ 2 := by
    filter_upwards [hall] with z hz using hz x
  exact (isClosed_le
    (((hv.continuous.comp (continuous_const.add continuous_id)).sub continuous_const).add
      (hv.continuous.comp (continuous_const.sub continuous_id)))
    (continuous_const.mul (continuous_id.pow 2))).closure_subset
      ((volume : Measure ℝ).dense_of_ae hae z)

end PDE.Analysis.Scalar
