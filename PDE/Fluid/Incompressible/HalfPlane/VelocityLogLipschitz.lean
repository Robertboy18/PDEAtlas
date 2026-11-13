/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.BiotSavart
public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarSingularIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.GradientBounds
import PDE.Fluid.Incompressible.HalfPlane.OriginTaylor
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Size and log-Lipschitz bounds of the half-plane velocity

For a vorticity `ω` on the upper half-plane with `|ω| ≤ B` and `L = ∫_{ℝ²₊} |ω|`, the
Biot–Savart velocity `u = halfPlaneVelocity ω` is a convolution of the odd extension `W` with the
gradient kernels `gⱼ(z) = -(2π)⁻¹ zⱼ/|z|²`, which satisfy `|gⱼ(z)| ≤ (2π|z|)⁻¹` and
`|gⱼ(z) - gⱼ(w)| ≤ |z - w|/(π|z|²)` when `2|z - w| ≤ |z|` (`abs_gradientKernel_sub_le`). Hence
the velocity is bounded and log-Lipschitz on the whole plane.

Only boundedness and integrability of `W` are used, so the jump of `W` across the boundary does
not matter. The data class is that of `partialDeriv_halfSpaceGreenPotential_eq_integral`
(continuous, compactly supported vorticity).

## Main results

* `abs_gradientKernel_sub_le`: `|gⱼ(z) - gⱼ(w)| ≤ |z - w|/(π|z|²)` when `2|z - w| ≤ |z|`.
* `abs_integral_gradientKernel_mul_sub_le`: for `|W| ≤ B` and `W` integrable,
  `V = ∫ gⱼ(· - y) W(y) dy` satisfies `|V(x) - V(x')| ≤ δ (5B + ‖W‖₁ + 2B log⁺(1/δ))`,
  `δ = |x - x'|`.
* `abs_halfPlaneVelocity_le`: `|uₖ(x)| ≤ B + L/π`.
* `abs_halfPlaneVelocity_sub_le`: `|uₖ(x) - uₖ(x')| ≤ |x - x'| (5B + 2L + 2B log⁺(1/|x - x'|))`,
  the log-Lipschitz bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology
open GreenFunction PotentialTheory.Planar SobolevSpace

namespace PotentialTheory.Planar

local notation "𝔠" => (Complex.orthonormalBasisOneI.repr.symm : ℝ^2 → ℂ)

/-- `|1/w - 1/v| ≤ 2|w - v|/|w|²` when `2|w - v| ≤ |w|`. -/
private theorem norm_inv_sub_inv_le {w v : ℂ} (h : 2 * ‖w - v‖ ≤ ‖w‖) :
    ‖1 / w - 1 / v‖ ≤ 2 * ‖w - v‖ / ‖w‖ ^ 2 := by
  rcases eq_or_ne w 0 with hw | hw
  · subst hw
    have hv : v = 0 := by
      have := norm_nonneg v
      simp only [zero_sub, norm_neg, norm_zero] at h
      exact norm_eq_zero.mp (by linarith)
    simp [hv]
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hv : ‖w‖ / 2 ≤ ‖v‖ := by
    have := norm_sub_norm_le w v
    linarith
  have hvpos : 0 < ‖v‖ := by linarith
  have hv0 : v ≠ 0 := norm_pos_iff.mp hvpos
  rw [div_sub_div _ _ hw hv0, norm_div, norm_mul, one_mul, mul_one, norm_sub_rev v w,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have : ‖w‖ ^ 2 ≤ 2 * (‖w‖ * ‖v‖) := by nlinarith
  nlinarith [norm_nonneg (w - v)]

/-- **Increment bound of the gradient kernels.** `|gⱼ(z) - gⱼ(w)| ≤ |z - w|/(π|z|²)` when
`2|z - w| ≤ |z|`. -/
theorem abs_gradientKernel_sub_le (j : Fin 2) {z w : ℝ^2} (h : 2 * ‖z - w‖ ≤ ‖z‖) :
    |gradientKernel j z - gradientKernel j w| ≤ ‖z - w‖ / (Real.pi * ‖z‖ ^ 2) := by
  rcases eq_or_ne ‖z‖ 0 with hz | hz
  · have hzw : z = w := by
      have : ‖z - w‖ = 0 := by linarith [norm_nonneg (z - w)]
      exact sub_eq_zero.mp (norm_eq_zero.mp this)
    rw [hzw, sub_self, abs_zero]
    positivity
  have hcx : ∀ y : ℝ^2, ‖𝔠 y‖ = ‖y‖ := fun y ↦ Complex.orthonormalBasisOneI.repr.symm.norm_map y
  have h' : 2 * ‖𝔠 z - 𝔠 w‖ ≤ ‖𝔠 z‖ := by rw [← map_sub, hcx, hcx]; exact h
  have hc := norm_inv_sub_inv_le h'
  rw [← map_sub, hcx, hcx] at hc
  have hpi := Real.pi_pos
  have hnorm : |gradientKernel j z - gradientKernel j w| ≤
      1 / (2 * Real.pi) * ‖1 / 𝔠 z - 1 / 𝔠 w‖ := by
    match j with
    | 0 =>
      rw [IncompressibleFlow.gradientKernel_zero_eq_neg_re,
        IncompressibleFlow.gradientKernel_zero_eq_neg_re, ← mul_sub, abs_mul,
        abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi)), ← Complex.sub_re]
      gcongr
      exact Complex.abs_re_le_norm _
    | 1 =>
      rw [IncompressibleFlow.gradientKernel_one_eq_im,
        IncompressibleFlow.gradientKernel_one_eq_im, ← mul_sub, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi)), ← Complex.sub_im]
      gcongr
      exact Complex.abs_im_le_norm _
  refine hnorm.trans ?_
  calc 1 / (2 * Real.pi) * ‖1 / 𝔠 z - 1 / 𝔠 w‖ ≤ 1 / (2 * Real.pi) * (2 * ‖z - w‖ / ‖z‖ ^ 2) := by
        gcongr
    _ = ‖z - w‖ / (Real.pi * ‖z‖ ^ 2) := by field_simp

end PotentialTheory.Planar

namespace IncompressibleFlow

variable {W : ℝ^2 → ℝ} {B : ℝ}

/-- `‖gⱼ(p - y) W(y)‖ ≤ B/(2π) |p - y|^(1-2)` for `|W| ≤ B`. -/
private theorem norm_gradientKernel_mul_le (j : Fin 2) (hB : ∀ y, |W y| ≤ B) (p y : ℝ^2) :
    ‖gradientKernel j (p - y) * W y‖ ≤ B / (2 * Real.pi) * ‖p - y‖ ^ ((1 : ℝ) - 2) := by
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, show (1 : ℝ) - 2 = -1 by norm_num]
  calc |gradientKernel j (p - y)| * |W y| ≤ 1 / (2 * Real.pi) * ‖p - y‖ ^ (-1 : ℝ) * B := by
        gcongr
        · simpa using norm_gradientKernel_le j (p - y)
        · exact hB y
    _ = B / (2 * Real.pi) * ‖p - y‖ ^ (-1 : ℝ) := by ring

/-- Outside `B(x, 1)`, `|gⱼ(x - y)| ≤ 1/(2π)`. -/
private theorem abs_gradientKernel_le_of_mem_compl_ball (j : Fin 2) {x y : ℝ^2}
    (hy : y ∈ (ball x 1)ᶜ) : |gradientKernel j (x - y)| ≤ 1 / (2 * Real.pi) :=
  (abs_gradientKernel_le j (x - y)).trans (one_div_le_one_div_of_le (by positivity)
    (by nlinarith [Real.pi_pos, le_norm_sub_of_mem_compl_ball hy]))

/-- `|∫_S gⱼ(p - y) W(y) dy| ≤ B ρ` for `S ⊆ B(p, ρ)` and `|W| ≤ B`. -/
private theorem abs_setIntegral_gradientKernel_mul_le (j : Fin 2) (hB : ∀ y, |W y| ≤ B)
    {p : ℝ^2} {ρ : ℝ} (hρ : 0 ≤ ρ) {S : Set (ℝ^2)} (hS : MeasurableSet S)
    (hSρ : S ⊆ ball p ρ) : |∫ y in S, gradientKernel j (p - y) * W y| ≤ B * ρ := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hval := lintegral_ball_mul_rpow_sub_two p (by positivity : 0 ≤ B / (2 * Real.pi)) hρ
    one_pos
  have hfin : ∫⁻ y in ball p ρ,
      ENNReal.ofReal (B / (2 * Real.pi) * ‖p - y‖ ^ ((1 : ℝ) - 2)) ≠ ⊤ := by
    rw [hval]; exact ENNReal.ofReal_ne_top
  rw [← Real.norm_eq_abs]
  refine (norm_setIntegral_le_of_norm_le hS (fun y _ ↦ norm_gradientKernel_mul_le j hB p y)
    (ne_top_of_le_ne_top hfin (lintegral_mono_set hSρ))).trans
      ((ENNReal.toReal_mono hfin (lintegral_mono_set hSρ)).trans_eq ?_)
  rw [hval, ENNReal.toReal_ofReal (by positivity), Real.rpow_one]
  field_simp

/-- The gradient-kernel integrand is integrable for a bounded integrable density. -/
private theorem integrable_gradientKernel_mul (j : Fin 2) (hW : Integrable W)
    (hB : ∀ y, |W y| ≤ B) (x : ℝ^2) :
    Integrable fun y ↦ gradientKernel j (x - y) * W y := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hmeas : AEStronglyMeasurable (fun y ↦ gradientKernel j (x - y) * W y) :=
    ((measurable_gradientKernel j).comp
      (measurable_const.sub measurable_id)).aestronglyMeasurable.mul hW.aestronglyMeasurable
  have hnear : IntegrableOn (fun y ↦ gradientKernel j (x - y) * W y) (ball x 1) :=
    integrableOn_of_norm_le_of_lintegral_ne_top measurableSet_ball hmeas.restrict
      (fun y _ ↦ norm_gradientKernel_mul_le j hB x y) (by
        rw [lintegral_ball_mul_rpow_sub_two x (by positivity : 0 ≤ B / (2 * Real.pi))
          zero_le_one one_pos]
        exact ENNReal.ofReal_ne_top)
  have hfar : IntegrableOn (fun y ↦ gradientKernel j (x - y) * W y) (ball x 1)ᶜ := by
    refine Integrable.bdd_mul (c := 1 / (2 * Real.pi)) hW.integrableOn
      ((measurable_gradientKernel j).comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with y hy
    rw [Real.norm_eq_abs]
    exact abs_gradientKernel_le_of_mem_compl_ball j hy
  have := hnear.union hfar
  rwa [union_compl_self, integrableOn_univ] at this

/-- The size bound `|∫ gⱼ(x - y) W(y) dy| ≤ B + ‖W‖₁/(2π)`. -/
private theorem abs_integral_gradientKernel_mul_le (j : Fin 2) (hW : Integrable W)
    (hB : ∀ y, |W y| ≤ B) (x : ℝ^2) :
    |∫ y, gradientKernel j (x - y) * W y| ≤ B + (∫ y, |W y|) / (2 * Real.pi) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hint := integrable_gradientKernel_mul j hW hB x
  rw [← integral_add_compl measurableSet_ball hint (s := ball x 1)]
  have h1 : |∫ y in ball x 1, gradientKernel j (x - y) * W y| ≤ B :=
    (abs_setIntegral_gradientKernel_mul_le j hB zero_le_one measurableSet_ball subset_rfl).trans_eq
      (mul_one B)
  have h2 : |∫ y in (ball x 1)ᶜ, gradientKernel j (x - y) * W y| ≤
      (∫ y, |W y|) / (2 * Real.pi) := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    calc ∫ y in (ball x 1)ᶜ, ‖gradientKernel j (x - y) * W y‖
        ≤ ∫ y in (ball x 1)ᶜ, 1 / (2 * Real.pi) * |W y| := by
          refine setIntegral_mono_on hint.integrableOn.norm (hW.abs.const_mul _).integrableOn
            measurableSet_ball.compl fun y hy ↦ ?_
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (abs_gradientKernel_le_of_mem_compl_ball j hy)
            (abs_nonneg _)
      _ ≤ ∫ y, 1 / (2 * Real.pi) * |W y| :=
          setIntegral_le_integral (hW.abs.const_mul _)
            (Eventually.of_forall fun y ↦ by positivity)
      _ = (∫ y, |W y|) / (2 * Real.pi) := by rw [integral_const_mul]; ring
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- **Log-Lipschitz bound of gradient-kernel integrals.** For `|W| ≤ B` and `W` integrable,
`|V(x) - V(x')| ≤ δ (5B + ‖W‖₁ + 2B log⁺(1/δ))` with `V = ∫ gⱼ(· - y) W(y) dy`, `δ = |x - x'|`. -/
theorem abs_integral_gradientKernel_mul_sub_le (j : Fin 2) (hW : Integrable W)
    (hB : ∀ y, |W y| ≤ B) (x x' : ℝ^2) :
    |(∫ y, gradientKernel j (x - y) * W y) - ∫ y, gradientKernel j (x' - y) * W y| ≤
      ‖x - x'‖ * (5 * B + (∫ y, |W y|) + 2 * B * Real.posLog (1 / ‖x - x'‖)) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hL0 : 0 ≤ ∫ y, |W y| := integral_nonneg fun y ↦ abs_nonneg _
  have hpi := Real.pi_gt_three
  have hpi0 := Real.pi_pos
  rcases eq_or_ne x x' with rfl | hxx'
  · simp
  set δ := ‖x - x'‖ with hδdef
  have hδ : 0 < δ := norm_pos_iff.mpr (sub_ne_zero.mpr hxx')
  have hlogpos : 0 ≤ Real.posLog (1 / δ) := Real.posLog_nonneg
  rcases lt_or_ge (1 / 2) δ with hδ2 | hδ2
  · -- far apart: twice the size bound
    have h1 := abs_integral_gradientKernel_mul_le j hW hB x
    have h2 := abs_integral_gradientKernel_mul_le j hW hB x'
    refine (abs_sub _ _).trans ((add_le_add h1 h2).trans ?_)
    have hL : (∫ y, |W y|) / (2 * Real.pi) ≤ (∫ y, |W y|) / 6 := by
      gcongr; linarith
    nlinarith [mul_nonneg hδ.le hlogpos, mul_nonneg hB0 (mul_nonneg hδ.le hlogpos)]
  -- close: near and far pieces
  have hint := integrable_gradientKernel_mul j hW hB x
  have hint' := integrable_gradientKernel_mul j hW hB x'
  set N := ball x (2 * δ) with hNdef
  have hNm : MeasurableSet N := measurableSet_ball
  have hN3 : N ⊆ ball x' (3 * δ) := fun y hy ↦ by
    rw [mem_ball, dist_eq_norm] at hy ⊢
    linarith [norm_sub_le_norm_sub_add_norm_sub y x x']
  have hsplit : ∀ g : ℝ^2 → ℝ, Integrable g → ∫ y, g y = (∫ y in N, g y) +
      (∫ y in ball x 1 \ N, g y) + ∫ y in (ball x 1)ᶜ, g y := by
    intro g hg
    have hN1 : N ⊆ ball x 1 := ball_subset_ball (by linarith)
    rw [← integral_add_compl measurableSet_ball hg (s := ball x 1),
      ← setIntegral_union disjoint_sdiff_right (measurableSet_ball.diff hNm) hg.integrableOn
        hg.integrableOn, union_sdiff_cancel hN1]
  have hdiff : (∫ y, gradientKernel j (x - y) * W y) - ∫ y, gradientKernel j (x' - y) * W y =
      ∫ y, (gradientKernel j (x - y) - gradientKernel j (x' - y)) * W y := by
    rw [← integral_sub hint hint']
    congr 1; funext y; ring
  have hint2 : Integrable fun y ↦ (gradientKernel j (x - y) - gradientKernel j (x' - y)) * W y := by
    have := hint.sub hint'
    refine this.congr (Eventually.of_forall fun y ↦ ?_)
    simp only [Pi.sub_apply]; ring
  rw [hdiff, hsplit _ hint2]
  -- near piece
  have hnear : |∫ y in N, (gradientKernel j (x - y) - gradientKernel j (x' - y)) * W y| ≤
      5 * B * δ := by
    have hsub : (fun y ↦ (gradientKernel j (x - y) - gradientKernel j (x' - y)) * W y) =
        fun y ↦ gradientKernel j (x - y) * W y - gradientKernel j (x' - y) * W y := by
      funext y; ring
    rw [hsub, integral_sub hint.integrableOn hint'.integrableOn]
    have h1 := abs_setIntegral_gradientKernel_mul_le j hB (by linarith) hNm subset_rfl
    have h2 := abs_setIntegral_gradientKernel_mul_le j hB (by linarith) hNm hN3
    calc _ ≤ |∫ y in N, gradientKernel j (x - y) * W y| +
          |∫ y in N, gradientKernel j (x' - y) * W y| := abs_sub _ _
      _ ≤ B * (2 * δ) + B * (3 * δ) := add_le_add h1 h2
      _ = 5 * B * δ := by ring
  -- the kernel increment on the far pieces
  have hinc : ∀ y, 2 * δ ≤ ‖x - y‖ →
      ‖(gradientKernel j (x - y) - gradientKernel j (x' - y)) * W y‖ ≤
        δ / Real.pi * ((‖x - y‖ ^ 2)⁻¹ * |W y|) := by
    intro y hy
    have h' : (x - y) - (x' - y) = x - x' := by abel
    have hk := abs_gradientKernel_sub_le j (z := x - y) (w := x' - y) (by rw [h']; exact hy)
    rw [h'] at hk
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc _ ≤ δ / (Real.pi * ‖x - y‖ ^ 2) * |W y| := by gcongr
      _ = δ / Real.pi * ((‖x - y‖ ^ 2)⁻¹ * |W y|) := by field_simp
  -- the middle annulus
  have hmid : |∫ y in ball x 1 \ N, (gradientKernel j (x - y) - gradientKernel j (x' - y)) * W y| ≤
      2 * B * δ * Real.log (1 / (2 * δ)) := by
    have hval := lintegral_annulus_mul_inv_sq x (by positivity : 0 ≤ δ / Real.pi * B)
      (by linarith : (0 : ℝ) < 2 * δ) (by linarith : 2 * δ ≤ 1)
    have hle : ∀ y ∈ ball x 1 \ N,
        ‖(gradientKernel j (x - y) - gradientKernel j (x' - y)) * W y‖ ≤
          δ / Real.pi * B * (‖x - y‖ ^ 2)⁻¹ := by
      intro y hy
      refine (hinc y (le_norm_sub_of_mem_compl_ball hy.2)).trans ?_
      rw [mul_comm ((‖x - y‖ ^ 2)⁻¹), ← mul_assoc]
      gcongr
      exact hB y
    rw [← Real.norm_eq_abs]
    refine (norm_setIntegral_le_of_norm_le (measurableSet_ball.diff hNm) hle
      (by rw [hval]; exact ENNReal.ofReal_ne_top)).trans ?_
    rw [hval, ENNReal.toReal_ofReal (by
      have : 0 ≤ Real.log (1 / (2 * δ)) := Real.log_nonneg (by
        rw [le_div_iff₀ (by linarith)]; linarith)
      positivity)]
    refine le_of_eq ?_
    field_simp
  -- the far piece
  have hfar : |∫ y in (ball x 1)ᶜ, (gradientKernel j (x - y) - gradientKernel j (x' - y)) * W y| ≤
      δ / Real.pi * ∫ y, |W y| := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    calc ∫ y in (ball x 1)ᶜ, ‖(gradientKernel j (x - y) - gradientKernel j (x' - y)) * W y‖
        ≤ ∫ y in (ball x 1)ᶜ, δ / Real.pi * |W y| := by
          refine setIntegral_mono_on hint2.integrableOn.norm (hW.abs.const_mul _).integrableOn
            measurableSet_ball.compl fun y hy ↦ ?_
          have h1 := le_norm_sub_of_mem_compl_ball hy
          refine (hinc y (by linarith)).trans ?_
          gcongr
          rw [inv_mul_le_iff₀ (by positivity)]
          have h2 : 1 ≤ ‖x - y‖ ^ 2 := one_le_pow₀ h1
          nlinarith [abs_nonneg (W y)]
      _ ≤ ∫ y, δ / Real.pi * |W y| :=
          setIntegral_le_integral (hW.abs.const_mul _)
            (Eventually.of_forall fun y ↦ by positivity)
      _ = δ / Real.pi * ∫ y, |W y| := integral_const_mul _ _
  have hlog : Real.log (1 / (2 * δ)) ≤ Real.posLog (1 / δ) := by
    refine (Real.log_le_log (x := 1 / (2 * δ)) (y := 1 / δ) (by positivity) (by
      rw [div_le_div_iff₀ (by positivity) hδ]; linarith)).trans (by
        rw [Real.posLog_apply]; exact le_max_right _ _)
  refine (abs_add_le _ _).trans ((add_le_add ((abs_add_le _ _).trans (add_le_add hnear hmid))
    hfar).trans ?_)
  have hL : δ / Real.pi * ∫ y, |W y| ≤ δ * ∫ y, |W y| := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hpi0]
    nlinarith [mul_nonneg hδ.le hL0]
  nlinarith [mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ 2 * B * δ)]

variable {ω : ℝ^2 → ℝ}

/-- The horizontal velocity `u₀ = -∫ g₁(x - y) W(y) dy`. -/
theorem halfPlaneVelocity_zero_eq_integral (hω : Continuous ω) (hc : HasCompactSupport ω)
    (x : ℝ^2) :
    halfPlaneVelocity ω x 0 = -∫ y, gradientKernel 1 (x - y) * oddHalfSpaceExtension ω y := by
  have h := congrFun (halfPlaneVelocity_zero ω) x
  simp only [Pi.neg_apply] at h
  rw [h, partialDeriv_halfSpaceGreenPotential_eq_integral hω hc]

/-- The vertical velocity `u₁ = ∫ g₀(x - y) W(y) dy`. -/
theorem halfPlaneVelocity_one_eq_integral (hω : Continuous ω) (hc : HasCompactSupport ω)
    (x : ℝ^2) :
    halfPlaneVelocity ω x 1 = ∫ y, gradientKernel 0 (x - y) * oddHalfSpaceExtension ω y := by
  have h := congrFun (halfPlaneVelocity_one ω) x
  rw [h, partialDeriv_halfSpaceGreenPotential_eq_integral hω hc]

/-- Each velocity component is `±∫ gⱼ(x - y) W(y) dy`. -/
private theorem halfPlaneVelocity_eq_integral (hω : Continuous ω) (hc : HasCompactSupport ω)
    (k : Fin 2) : ∃ j : Fin 2, ∃ s : ℝ, |s| = 1 ∧ ∀ x : ℝ^2,
      halfPlaneVelocity ω x k = s * ∫ y, gradientKernel j (x - y) * oddHalfSpaceExtension ω y := by
  match k with
  | 0 =>
    exact ⟨1, -1, by norm_num, fun x ↦ by
      rw [halfPlaneVelocity_zero_eq_integral hω hc]; ring⟩
  | 1 =>
    exact ⟨0, 1, by norm_num, fun x ↦ by
      rw [halfPlaneVelocity_one_eq_integral hω hc, one_mul]⟩

/-- **Size of the half-plane velocity.** For `|ω| ≤ B` on the open upper half-plane,
`|uₖ(x)| ≤ B + L/π` at every point of the plane, `L = ∫_{ℝ²₊} |ω|`. -/
theorem abs_halfPlaneVelocity_le (hω : Continuous ω) (hc : HasCompactSupport ω)
    (hB : ∀ y ∈ HalfSpace.upper 2, |ω y| ≤ B) (k : Fin 2) (x : ℝ^2) :
    |halfPlaneVelocity ω x k| ≤ B + (∫ y in HalfSpace.upper 2, |ω y|) / Real.pi := by
  have hB0 : 0 ≤ B := by
    have := hB !₂[0, 1] (show (0 : ℝ) < (!₂[0, 1] : ℝ^2) 1 by simp)
    exact (abs_nonneg _).trans this
  obtain ⟨j, s, hs, hrep⟩ := halfPlaneVelocity_eq_integral hω hc k
  have hW := integrable_oddHalfSpaceExtension hω hc
  have hWB : ∀ y, |oddHalfSpaceExtension ω y| ≤ B := fun y ↦ by
    simpa only [Real.norm_eq_abs] using norm_oddHalfSpaceExtension_le hB0
      (fun y hy ↦ by simpa only [Real.norm_eq_abs] using hB y hy) y
  have hL := integral_norm_oddHalfSpaceExtension hω hc
  simp only [Real.norm_eq_abs] at hL
  rw [hrep x, abs_mul, hs, one_mul]
  refine (abs_integral_gradientKernel_mul_le j hW hWB x).trans (le_of_eq ?_)
  rw [hL]
  field_simp

/-- **Log-Lipschitz bound of the half-plane velocity.** For `|ω| ≤ B` on the open upper
half-plane and `L = ∫_{ℝ²₊} |ω|`, at all points of the plane
`|uₖ(x) - uₖ(x')| ≤ |x - x'| (5B + 2L + 2B log⁺(1/|x - x'|))`. -/
theorem abs_halfPlaneVelocity_sub_le (hω : Continuous ω) (hc : HasCompactSupport ω)
    (hB : ∀ y ∈ HalfSpace.upper 2, |ω y| ≤ B) (k : Fin 2) (x x' : ℝ^2) :
    |halfPlaneVelocity ω x k - halfPlaneVelocity ω x' k| ≤
      ‖x - x'‖ * (5 * B + 2 * (∫ y in HalfSpace.upper 2, |ω y|) +
        2 * B * Real.posLog (1 / ‖x - x'‖)) := by
  have hB0 : 0 ≤ B := by
    have := hB !₂[0, 1] (show (0 : ℝ) < (!₂[0, 1] : ℝ^2) 1 by simp)
    exact (abs_nonneg _).trans this
  obtain ⟨j, s, hs, hrep⟩ := halfPlaneVelocity_eq_integral hω hc k
  have hW := integrable_oddHalfSpaceExtension hω hc
  have hWB : ∀ y, |oddHalfSpaceExtension ω y| ≤ B := fun y ↦ by
    simpa only [Real.norm_eq_abs] using norm_oddHalfSpaceExtension_le hB0
      (fun y hy ↦ by simpa only [Real.norm_eq_abs] using hB y hy) y
  have hL := integral_norm_oddHalfSpaceExtension hω hc
  simp only [Real.norm_eq_abs] at hL
  rw [hrep x, hrep x', ← mul_sub, abs_mul, hs, one_mul]
  refine (abs_integral_gradientKernel_mul_sub_le j hW hWB x x').trans (le_of_eq ?_)
  rw [hL]

end IncompressibleFlow
