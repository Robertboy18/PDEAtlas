/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.EuclideanBall.Dilation
import CAS.ExactTactic

/-!
# Initial-ball bound for the wave scaling current

The radial moment in the scaling multiplier can be integrated without a
singular weight at the center. Young's inequality leaves exactly the moment
computed by the square-trace dilation identity. This gives the potential term
and boundary trace needed at the bottom of a backward wave cone.

This is the bound (14) in step 3 of the proof of Evans, §12.4, Theorem 2.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, proof of Theorem 2, step 3, equation (14).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set

namespace WaveEquation

variable {n : ℕ}

/-- Young's inequality for the initial scaling density, with the radial
moment left explicit. Its ball integral is given by the dilation identity. -/
theorem scalingInitialDensity_le {r : ℝ} (hr : 0 < r) (a v W : ℝ)
    (D : ℝ^n →L[ℝ] ℝ) {x : ℝ^n} (hx : ‖x‖ ≤ r) :
    -r * ((v ^ 2 + ‖D‖ ^ 2) / 2 + W) + (D x + a) * v ≤
      -r * W + (a ^ 2 + 2 * a * D x) / (2 * r) := by
  have hd : |D x| ≤ r * ‖D‖ := by
    calc
      _ ≤ ‖D‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖D‖ * r := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
      _ = _ := mul_comm _ _
  have hd2 : (D x) ^ 2 ≤ r ^ 2 * ‖D‖ ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (D x)) hd 2
    simpa only [sq_abs, mul_pow] using h
  have hmul : (-r * ((v ^ 2 + ‖D‖ ^ 2) / 2 + W) + (D x + a) * v + r * W) *
        (2 * r) ≤ a ^ 2 + 2 * a * D x := by
    nlinarith only [sq_nonneg (r * v - D x - a), hd2]
  have h := (le_div_iff₀ (show 0 < 2 * r by positivity)).mpr hmul
  linarith

/-- The initial scaling density is bounded by its potential integral and the
square trace. The exact dimensional correction is retained; it is nonpositive
in every positive spatial dimension. In dimension zero the radial moment vanishes. -/
theorem ballIntegral_scalingInitialDensity_le {u v W : ℝ^n → ℝ} (hu : ContDiff ℝ 1 u)
    (hv : Continuous v) (hW : Continuous W) (c : ℝ^n) {r : ℝ} (hr : 0 < r) :
    PDE.Analysis.ballIntegral n (fun y ↦
        -r * ((v y ^ 2 + ‖fderiv ℝ u y‖ ^ 2) / 2 + W y) +
          (fderiv ℝ u y (y - c) + u y) * v y) c r ≤
      -r * PDE.Analysis.ballIntegral n W c r +
        PDE.Analysis.sphereIntegral n (fun y ↦ u y ^ 2) c r / 2 -
          ((n : ℝ) - 1) / (2 * r) * PDE.Analysis.ballIntegral n (fun y ↦ u y ^ 2) c r := by
  have hD : Continuous (fun y ↦ fderiv ℝ u y (y - c)) :=
    (hu.continuous_fderiv one_ne_zero).clm_apply (continuous_id.sub continuous_const)
  have hN : Continuous (fun y ↦ ‖fderiv ℝ u y‖ ^ 2) := (hu.continuous_fderiv one_ne_zero).norm.pow 2
  have hint {f : ℝ^n → ℝ} (hf : Continuous f) : IntegrableOn f (ball c r) :=
    (hf.continuousOn.integrableOn_compact (isCompact_closedBall c r)).mono_set
      ball_subset_closedBall
  have hiu : IntegrableOn (fun y ↦ u y ^ 2) (ball c r) := hint (hu.continuous.pow 2)
  have him : IntegrableOn (fun y ↦ u y * fderiv ℝ u y (y - c)) (ball c r) :=
    hint (hu.continuous.mul hD)
  have hiW : IntegrableOn W (ball c r) := hint hW
  have hleft : IntegrableOn (fun y ↦ -r * ((v y ^ 2 + ‖fderiv ℝ u y‖ ^ 2) / 2 + W y) +
        (fderiv ℝ u y (y - c) + u y) * v y) (ball c r) :=
    hint ((continuous_const.mul (((hv.pow 2).add hN).div_const 2 |>.add hW)).add
      ((hD.add hu.continuous).mul hv))
  have hisum : IntegrableOn (fun y ↦ u y ^ 2 + 2 * (u y * fderiv ℝ u y (y - c))) (ball c r) :=
    hint ((hu.continuous.pow 2).add (continuous_const.mul (hu.continuous.mul hD)))
  have hright : IntegrableOn (fun y ↦ -r * W y +
      (u y ^ 2 + 2 * (u y * fderiv ℝ u y (y - c))) / (2 * r)) (ball c r) :=
    hint ((continuous_const.mul hW).add
      (((hu.continuous.pow 2).add (continuous_const.mul (hu.continuous.mul hD))).div_const _))
  have hpoint (y : ℝ^n) (hy : y ∈ ball c r) : -r * ((v y ^ 2 + ‖fderiv ℝ u y‖ ^ 2) / 2 + W y) +
          (fderiv ℝ u y (y - c) + u y) * v y ≤
        -r * W y + (u y ^ 2 + 2 * (u y * fderiv ℝ u y (y - c))) / (2 * r) := by
    have hx : ‖y - c‖ ≤ r := le_of_lt (by simpa only [mem_ball, dist_eq_norm] using hy)
    simpa only [mul_assoc] using scalingInitialDensity_le hr (u y) (v y) (W y) (fderiv ℝ u y) hx
  have hbound := integral_mono_ae hleft hright ((ae_restrict_mem measurableSet_ball).mono hpoint)
  rw [integral_add (hiW.const_mul (-r)) (hisum.div_const (2 * r)), integral_const_mul,
    integral_div, integral_add hiu (him.const_mul 2), integral_const_mul] at hbound
  have hm : 2 * (∫ y in ball c r, u y * fderiv ℝ u y (y - c)) ≤
      r * PDE.Analysis.sphereIntegral n (fun y ↦ u y ^ 2) c r -
        (n : ℝ) * (∫ y in ball c r, u y ^ 2) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h0 : (fun y : ℝ^0 ↦ u y * fderiv ℝ u y (y - c)) = fun _ ↦ 0 := by
        funext y
        rw [Subsingleton.elim y c, sub_self, map_zero, mul_zero]
      rw [h0, integral_zero, Nat.cast_zero, zero_mul, sub_zero, mul_zero]
      exact mul_nonneg hr.le (PDE.Analysis.sphereIntegral_nonneg fun y _ ↦ sq_nonneg (u y))
    · have : Fact (0 < n) := ⟨hn⟩
      have hid := PDE.Analysis.ballIntegral_dilation_sq hu c hr
      change (n : ℝ) * (∫ y in ball c r, u y ^ 2) +
        2 * (∫ y in ball c r, u y * fderiv ℝ u y (y - c)) = _ at hid
      linarith
  replace hbound := hbound.trans (add_le_add le_rfl (div_le_div_of_nonneg_right
    (add_le_add le_rfl hm) (by positivity : (0 : ℝ) ≤ 2 * r)))
  change (∫ y in ball c r, _) ≤ -r * (∫ y in ball c r, W y) + _ / 2 - _ * (∫ y in ball c r, u y ^ 2)
  convert hbound using 1
  field_simp [ne_of_gt hr]
  cas

end WaveEquation
