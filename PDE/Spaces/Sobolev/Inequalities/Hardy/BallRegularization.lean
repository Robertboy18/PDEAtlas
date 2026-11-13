/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.EuclideanBall
public import PDE.Analysis.Calculus.Rellich.Field
import CAS.ExactTactic

/-!
# Regularized Hardy multipliers on a ball

The field `x ((‖x‖² + ε)⁻¹ - (r² + ε)⁻¹)` vanishes on the sphere of radius `r`.
Its divergence controls the regularized inverse-square weight, with a lower-order
error proportional to `r⁻²`. The boundary cancellation imposes no condition on the
function being estimated.

Evans proves §5.8.4, Theorem 7 for smooth functions by integrating by parts against `x/|x|²`
and bounding the boundary integral by a trace inequality. The field here vanishes on the sphere,
so the integration by parts has no boundary term; the subtracted constant `(r² + ε)⁻¹` produces
the lower-order error instead.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.4, Theorem 7 and its proof, pp. 296-297.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set PDE PDE.Analysis
open scoped RealInnerProductSpace

namespace SobolevSpace.Hardy

variable {n : ℕ}

/-- A regularized radial multiplier with zero boundary values on the sphere of radius `r`. -/
def regularizedHardyField (r ε : ℝ) (x : ℝ^n) : ℝ^n :=
  ((‖x‖ ^ 2 + ε)⁻¹ - (r ^ 2 + ε)⁻¹) • x

/-- Positive regularization makes the Hardy multiplier smooth even at the origin. -/
theorem contDiff_regularizedHardyField (r : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 1 (regularizedHardyField (n := n) r ε) := by
  exact (((contDiff_norm_sq ℝ).add contDiff_const).inv
    (fun x ↦ (add_pos_of_nonneg_of_pos (sq_nonneg ‖x‖) hε).ne')).sub
      contDiff_const |>.smul contDiff_id

/-- The regularized multiplier vanishes on the sphere without restricting the data. -/
theorem regularizedHardyField_eq_zero {r ε : ℝ} {x : ℝ^n}
    (hx : x ∈ sphere 0 r) : regularizedHardyField r ε x = 0 := by
  simp [regularizedHardyField, mem_sphere_zero_iff_norm.mp hx]

/-- The divergence separates its inverse-square part and its constant boundary correction. -/
theorem divergence_regularizedHardyField (r : ℝ) {ε : ℝ} (hε : 0 < ε) (x : ℝ^n) :
    ∇· (regularizedHardyField r ε) x =
      (n : ℝ) * ((‖x‖ ^ 2 + ε)⁻¹ - (r ^ 2 + ε)⁻¹) -
        2 * ‖x‖ ^ 2 / (‖x‖ ^ 2 + ε) ^ 2 := by
  let a : ℝ^n → ℝ := fun y ↦ (‖y‖ ^ 2 + ε)⁻¹ - (r ^ 2 + ε)⁻¹
  have hd : HasDerivAt (fun s : ℝ ↦ (s + ε)⁻¹ - (r ^ 2 + ε)⁻¹)
      (-(‖x‖ ^ 2 + ε)⁻¹ ^ 2) (‖x‖ ^ 2) := by
    cas using add_pos_of_nonneg_of_pos (sq_nonneg ‖x‖) hε
  have ha := hd.comp_hasFDerivAt x (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  change HasFDerivAt a _ x at ha
  have hid : ∇· (fun y : ℝ^n ↦ y) x = (n : ℝ) := by
    simpa using divergence_sub_const (0 : ℝ^n) x
  change ∇· (fun y ↦ a y • y) x = _
  rw [divergence_smul (F := fun y ↦ y) ha.differentiableAt differentiableAt_id,
    ha.fderiv, hid]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply,
    real_inner_self_eq_norm_sq, a]
  cas

/-- A smooth scalar multiple of the Hardy field has zero integrated divergence on the ball. -/
theorem integral_divergence_mul_regularizedHardyField
    [Fact (0 < n)] {u : ℝ^n → ℝ} (hu : ContDiff ℝ 1 u)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    (∫ x in ball (0 : ℝ^n) r,
      ∇· (fun y ↦ u y ^ 2 • regularizedHardyField r ε y) x) = 0 := by
  have hc := (hu.pow 2).smul (contDiff_regularizedHardyField (n := n) r hε)
  have h := ballIntegral_divergence_eq_sphereIntegral_normal_flux
    (fun i x ↦ (u x ^ 2 • regularizedHardyField r ε x) i)
    (fun i ↦ (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hc) 0 hr
  change (∫ x in ball (0 : ℝ^n) r,
    ∑ i, (∂[i] (fun y ↦ (u y ^ 2 • regularizedHardyField r ε y) i)) x) = 0
  simp only [ballIntegral] at h
  rw [h, sphereIntegral_congr_on_sphere hr (v := fun _ ↦ 0)]
  · simp [sphereIntegral]
  · intro x hx
    simp [regularizedHardyField_eq_zero hx]

/-- Inside the ball, the square of the multiplier is bounded by the regularized weight. -/
theorem norm_regularizedHardyField_sq_le {r ε : ℝ} (hε : 0 < ε)
    {x : ℝ^n} (hx : x ∈ ball 0 r) :
    ‖regularizedHardyField r ε x‖ ^ 2 ≤ (‖x‖ ^ 2 + ε)⁻¹ := by
  have hD : 0 < ‖x‖ ^ 2 + ε := add_pos_of_nonneg_of_pos (sq_nonneg _) hε
  have hR : 0 < r ^ 2 + ε := add_pos_of_nonneg_of_pos (sq_nonneg _) hε
  have hnr : ‖x‖ ^ 2 ≤ r ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (mem_ball_zero_iff.mp hx).le 2
  have hi : (r ^ 2 + ε)⁻¹ ≤ (‖x‖ ^ 2 + ε)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hD (by linarith)
  have ha : 0 ≤ (‖x‖ ^ 2 + ε)⁻¹ - (r ^ 2 + ε)⁻¹ := sub_nonneg.mpr hi
  have hb : (‖x‖ ^ 2 + ε)⁻¹ - (r ^ 2 + ε)⁻¹ ≤ (‖x‖ ^ 2 + ε)⁻¹ :=
    sub_le_self _ (inv_nonneg.mpr hR.le)
  have hs := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ ha hb 2) (sq_nonneg ‖x‖)
  have hcancel : (‖x‖ ^ 2 + ε)⁻¹ ^ 2 * (‖x‖ ^ 2 + ε) = (‖x‖ ^ 2 + ε)⁻¹ := by
    cas using hD.ne'
  have hlast : (‖x‖ ^ 2 + ε)⁻¹ ^ 2 * ‖x‖ ^ 2 ≤ (‖x‖ ^ 2 + ε)⁻¹ := by
    calc
      _ ≤ (‖x‖ ^ 2 + ε)⁻¹ ^ 2 * (‖x‖ ^ 2 + ε) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hε.le) (sq_nonneg _)
      _ = _ := hcancel
  simpa only [regularizedHardyField, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    using hs.trans hlast

/-- The divergence dominates one copy of the regularized weight in dimension at least three. -/
theorem regularizedHardyField_divergence_lower_bound (hn : 3 ≤ n)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (x : ℝ^n) :
    (‖x‖ ^ 2 + ε)⁻¹ - (n : ℝ) / r ^ 2 ≤ ∇· (regularizedHardyField r ε) x := by
  have hD : 0 < ‖x‖ ^ 2 + ε := add_pos_of_nonneg_of_pos (sq_nonneg _) hε
  have hi : (r ^ 2 + ε)⁻¹ ≤ (r ^ 2)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (sq_pos_of_pos hr)
      (le_add_of_nonneg_right hε.le)
  have hx : ‖x‖ ^ 2 / (‖x‖ ^ 2 + ε) ^ 2 ≤ (‖x‖ ^ 2 + ε)⁻¹ := by
    apply (div_le_iff₀ (sq_pos_of_pos hD)).mpr
    have heq : (‖x‖ ^ 2 + ε)⁻¹ * (‖x‖ ^ 2 + ε) ^ 2 = ‖x‖ ^ 2 + ε := by
      cas using hD.ne'
    rw [heq]
    exact le_add_of_nonneg_right hε.le
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hni := mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hdim := mul_nonneg (sub_nonneg.mpr hn') (inv_nonneg.mpr hD.le)
  rw [divergence_regularizedHardyField r hε]
  rw [mul_div_assoc]
  simp only [div_eq_mul_inv] at hx ⊢
  nlinarith

/-- Young's inequality absorbs the derivative of the data into half of the Hardy weight. -/
theorem divergence_mul_regularizedHardyField_lower_bound (hn : 3 ≤ n)
    {u : ℝ^n → ℝ} {x : ℝ^n} (hu : DifferentiableAt ℝ u x)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (hx : x ∈ ball 0 r) :
    u x ^ 2 / (‖x‖ ^ 2 + ε) / 2 - 2 * ‖fderiv ℝ u x‖ ^ 2 -
        (n : ℝ) / r ^ 2 * u x ^ 2 ≤
      ∇· (fun y ↦ u y ^ 2 • regularizedHardyField r ε y) x := by
  let F := regularizedHardyField (n := n) r ε
  have hF := (contDiff_regularizedHardyField (n := n) r hε).differentiable one_ne_zero x
  have hd := divergence_smul (a := fun y ↦ u y ^ 2) (hu.pow 2) hF
  have hsq := hu.hasFDerivAt.pow 2
  rw [hsq.fderiv] at hd
  simp only [Nat.reduceSub, pow_one, smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat] at hd
  have hdiv := mul_le_mul_of_nonneg_left
    (regularizedHardyField_divergence_lower_bound hn hr hε x) (sq_nonneg (u x))
  have hfield := mul_le_mul_of_nonneg_left
    (norm_regularizedHardyField_sq_le hε hx) (sq_nonneg (u x))
  have hcross : |u x * fderiv ℝ u x (F x)| ≤ |u x| * ‖fderiv ℝ u x‖ * ‖F x‖ := by
    rw [abs_mul]
    simpa only [← mul_assoc, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_left ((fderiv ℝ u x).le_opNorm (F x)) (abs_nonneg (u x))
  have hyoung := sq_nonneg (|u x| * ‖F x‖ - 2 * ‖fderiv ℝ u x‖)
  have hneg := neg_abs_le (u x * fderiv ℝ u x (F x))
  simp only [sub_sq, mul_pow, sq_abs] at hyoung
  change _ ≤ ∇· (fun y ↦ u y ^ 2 • F y) x
  change _ ≤ u x ^ 2 * ∇· F x at hdiv
  change u x ^ 2 * ‖F x‖ ^ 2 ≤ _ at hfield
  change ∇· (fun y ↦ u y ^ 2 • F y) x =
    2 * u x * fderiv ℝ u x (F x) + u x ^ 2 * ∇· F x at hd
  rw [hd]
  simp only [div_eq_mul_inv] at hdiv hfield ⊢
  norm_num only at *
  nlinarith

/-- The regularized Hardy bound on a ball is uniform in the positive regularization.
The data need not vanish at either the center or the boundary. -/
theorem integral_regularized_hardy_ball (hn : 3 ≤ n)
    {u : ℝ^n → ℝ} (hu : ContDiff ℝ 1 u)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    (∫ x in ball (0 : ℝ^n) r, u x ^ 2 / (‖x‖ ^ 2 + ε)) ≤
      4 * (∫ x in ball (0 : ℝ^n) r, ‖fderiv ℝ u x‖ ^ 2) +
        2 * (n : ℝ) / r ^ 2 * ∫ x in ball (0 : ℝ^n) r, u x ^ 2 := by
  let : Fact (0 < n) := ⟨by omega⟩
  have hint {f : ℝ^n → ℝ} (hf : Continuous f) : IntegrableOn f (ball 0 r) :=
    (hf.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℝ^n) r)).mono_set
      ball_subset_closedBall
  have hD (x : ℝ^n) : ‖x‖ ^ 2 + ε ≠ 0 :=
    (add_pos_of_nonneg_of_pos (sq_nonneg _) hε).ne'
  have hA : IntegrableOn (fun x ↦ u x ^ 2 / (‖x‖ ^ 2 + ε)) (ball 0 r) :=
    hint ((hu.continuous.pow 2).div ((continuous_norm.pow 2).add continuous_const) hD)
  have hB : IntegrableOn (fun x ↦ ‖fderiv ℝ u x‖ ^ 2) (ball 0 r) :=
    hint ((hu.continuous_fderiv one_ne_zero).norm.pow 2)
  have hU : IntegrableOn (fun x ↦ u x ^ 2) (ball 0 r) := hint (hu.continuous.pow 2)
  have hflux := (hu.pow 2).smul (contDiff_regularizedHardyField (n := n) r hε)
  have hdiv : Continuous (∇· (fun y ↦ u y ^ 2 • regularizedHardyField r ε y)) := by
    apply continuous_finsetSum
    intro i _
    exact (((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hflux).continuous_fderiv
      one_ne_zero).clm_apply continuous_const
  have hineq := integral_mono_ae
    (((hA.div_const 2).sub (hB.const_mul 2)).sub (hU.const_mul ((n : ℝ) / r ^ 2)))
    (hint hdiv) (by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact divergence_mul_regularizedHardyField_lower_bound hn
        (hu.differentiable one_ne_zero x) hr hε hx)
  simp only [Pi.sub_apply] at hineq
  rw [integral_divergence_mul_regularizedHardyField hu hr hε,
    integral_sub (f := fun x ↦ u x ^ 2 / (‖x‖ ^ 2 + ε) / 2 -
      2 * ‖fderiv ℝ u x‖ ^ 2)
      ((hA.div_const 2).sub (hB.const_mul 2)) (hU.const_mul _),
    integral_sub (hA.div_const 2) (hB.const_mul 2), integral_div,
    integral_const_mul, integral_const_mul] at hineq
  simp only [div_eq_mul_inv] at hineq ⊢
  linarith

end SobolevSpace.Hardy
