/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.FDeriv.Calculus
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import CAS.IntegrationTactic

/-!
# First-order Taylor bounds from planar Hessian entries

A bound `M` for each of the four Hessian entries gives the gradient Lipschitz
constant `2M`. Integrating that estimate along the segment from zero to `x`
gives the first-order remainder `M ‖x‖²`. Only `C²` regularity is used.
-/

@[expose] public section

open scoped Gradient

noncomputable section

open MeasureTheory

namespace PDE.FDeriv

private theorem norm_fderiv_le_of_planar_partial_bounds
    {g : ℝ^2 → ℝ} {x : ℝ^2} (hg : DifferentiableAt ℝ g x)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ i : Fin 2, |(∂[i] g) x| ≤ M) :
    ‖fderiv ℝ g x‖ ≤ √2 * M := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hM)).mp
  rw [norm_fderiv_sq_eq_sum_partialDeriv_sq hg, Fin.sum_univ_two]
  have hs (i : Fin 2) : (∂[i] g) x ^ 2 ≤ M ^ 2 := by
    simpa only [sq_abs] using
      (pow_le_pow_left₀ (abs_nonneg _) (hbound i) 2)
  calc
    _ ≤ M ^ 2 + M ^ 2 := add_le_add (hs 0) (hs 1)
    _ = (√2 * M) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      cas

/-- If every planar Hessian entry is bounded by `M`, the gradient is
`2M`-Lipschitz. -/
theorem gradient_sub_le_of_planar_hessian_bound
    {f : ℝ^2 → ℝ} (hf : ContDiff ℝ 2 f) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ (i j : Fin 2) (x : ℝ^2),
      |(∂[i] (∂[j] f)) x| ≤ M) (x y : ℝ^2) :
    ‖∇ f y - ∇ f x‖ ≤ 2 * M * ‖y - x‖ := by
  have hfirst (j : Fin 2) : ContDiff ℝ 1 (∂[j] f) :=
    contDiff_partialDeriv_of_succ (m := 1) hf
  have hrow (j : Fin 2) :
      |(∂[j] f) y - (∂[j] f) x| ≤
        (√2 * M) * ‖y - x‖ := by
    simpa only [Real.norm_eq_abs] using
      (convex_univ : Convex ℝ (Set.univ : Set (ℝ^2))).norm_image_sub_le_of_norm_fderiv_le
        (fun z _ ↦ (hfirst j).differentiable_one z)
        (fun z _ ↦ norm_fderiv_le_of_planar_partial_bounds
          ((hfirst j).differentiable_one z) hM (fun i ↦ hbound i j z))
        (Set.mem_univ x) (Set.mem_univ y)
  have hs (j : Fin 2) :
      ((∂[j] f) y - (∂[j] f) x) ^ 2 ≤
        ((√2 * M) * ‖y - x‖) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hrow j) 2
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2 * M * ‖y - x‖)).mp
  have hnorm : ‖∇ f y - ∇ f x‖ ^ 2 =
      ((∂[0] f) y - (∂[0] f) x) ^ 2 +
        ((∂[1] f) y - (∂[1] f) x) ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  rw [hnorm]
  calc
    _ ≤ ((√2 * M) * ‖y - x‖) ^ 2 +
        ((√2 * M) * ‖y - x‖) ^ 2 := add_le_add (hs 0) (hs 1)
    _ = (2 * M * ‖y - x‖) ^ 2 := by
      simp only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      cas

/-- The first-order Taylor remainder at zero is bounded by `M ‖x‖²`
when every planar Hessian entry is bounded by `M`. The factor one half comes
from integrating the gradient estimate along the segment. -/
theorem first_order_remainder_le_of_planar_hessian_bound
    {f : ℝ^2 → ℝ} (hf : ContDiff ℝ 2 f) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ (i j : Fin 2) (x : ℝ^2),
      |(∂[i] (∂[j] f)) x| ≤ M) (x : ℝ^2) :
    |f x - f 0 - fderiv ℝ f 0 x| ≤ M * ‖x‖ ^ 2 := by
  let D : ℝ → ℝ := fun t ↦ (fderiv ℝ f (t • x) - fderiv ℝ f 0) x
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hD : Continuous D :=
    (((hf.fderiv_right (m := 0) (by norm_num)).continuous.comp
      (continuous_id.smul continuous_const)).sub continuous_const).clm_apply continuous_const
  have hpath (t : ℝ) :
      HasDerivAt (fun t : ℝ ↦ f (t • x) - f 0 - t * fderiv ℝ f 0 x) (D t) t := by
    have hline : HasDerivAt (fun s : ℝ ↦ s • x) x t := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id t).smul_const x
    have hcomp : HasDerivAt (fun s : ℝ ↦ f (s • x))
        (fderiv ℝ f (t • x) x) t :=
      (hdiff (t • x)).hasFDerivAt.comp_hasDerivAt t hline
    have hlinear : HasDerivAt (fun s : ℝ ↦ s * fderiv ℝ f 0 x)
        (fderiv ℝ f 0 x) t := by
      simpa only [id_eq, one_mul] using
        (hasDerivAt_id t).mul_const (fderiv ℝ f 0 x)
    simpa only [D, sub_apply, Pi.sub_apply] using!
      (hcomp.sub_const (f 0)).sub hlinear
  have hDnorm (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ‖D t‖ ≤ 2 * M * ‖x‖ ^ 2 * t := by
    have hdual :
        ‖fderiv ℝ f (t • x) - fderiv ℝ f 0‖ =
          ‖∇ f (t • x) - ∇ f 0‖ := by
      simpa only [map_sub, toDual_gradient] using
        (InnerProductSpace.toDual ℝ (ℝ^2)).norm_map
          (∇ f (t • x) - ∇ f 0)
    calc
      ‖D t‖ ≤ ‖fderiv ℝ f (t • x) - fderiv ℝ f 0‖ * ‖x‖ :=
        (fderiv ℝ f (t • x) - fderiv ℝ f 0).le_opNorm x
      _ = ‖∇ f (t • x) - ∇ f 0‖ * ‖x‖ := by rw [hdual]
      _ ≤ (2 * M * ‖t • x - 0‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right
          (gradient_sub_le_of_planar_hessian_bound hf hM hbound 0 (t • x))
          (norm_nonneg _)
      _ = 2 * M * ‖x‖ ^ 2 * t := by
        rw [sub_zero, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        cas
  have hFTC : f x - f 0 - fderiv ℝ f 0 x = ∫ t in (0 : ℝ)..1, D t := by
    simpa only [one_smul, zero_smul, one_mul, zero_mul, sub_self, sub_zero] using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := (0 : ℝ)) (b := 1) (fun t _ ↦ hpath t)
        (hD.intervalIntegrable 0 1)).symm
  rw [hFTC, ← Real.norm_eq_abs]
  calc
    ‖∫ t in (0 : ℝ)..1, D t‖ ≤ ∫ t in (0 : ℝ)..1, ‖D t‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ t in (0 : ℝ)..1, 2 * M * ‖x‖ ^ 2 * t :=
      intervalIntegral.integral_mono_on (by norm_num) (hD.norm.intervalIntegrable 0 1)
        ((continuous_const.mul continuous_id).intervalIntegrable 0 1) hDnorm
    _ = M * ‖x‖ ^ 2 := by
      have hid : (∫ t in (0 : ℝ)..1, t) = (1 / 2 : ℝ) := by cas
      rw [intervalIntegral.integral_const_mul, hid]
      cas

end PDE.FDeriv
