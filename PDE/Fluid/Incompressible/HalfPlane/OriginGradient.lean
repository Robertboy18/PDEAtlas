/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.OriginTaylor
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.GradientBounds
import PDE.FDeriv.PartialDeriv.Regularity

/-!
# The velocity gradient at the origin

For a compactly supported `C²` vorticity `ω` odd in `x₀` whose tangential derivative satisfies
`|∂₀ω(y)| ≤ M |y|²` on the closed upper half-plane, the second derivatives of the Green stream
`φ = halfSpaceGreenPotential ω` that make up `∇ũ` satisfy

`|∂₁∂₀φ(x) - ∂₁∂₀φ(0)| ≤ (16/π)(2πM + ‖W'‖₁)|x|² + 16 M |x|³` and the same bound for `|∂₀∂₀φ(x)|`,

with `W'` the odd extension of `∂₀ω` (`abs_partialDeriv_one_partialDeriv_zero_sub_le`,
`abs_partialDeriv_zero_partialDeriv_zero_le`). So `ũ_x = u_x - u_x(0)`, `ṽ_x = v_x` and
`ũ_y = v_x + ω` are `O(|x|²)` (Chen and Hou, Part I, Section 4.2, the display after (4.8),
`∇ũ = O(|x|²)`).

## Main results

* `abs_integral_gradientKernel_sub_sub_le`: for `W` integrable, even in `y₀`, odd in `y₁` and
  `|W(y)| ≤ M |y|²`, `|∫ (gⱼ(x - y) - gⱼ(-y)) W(y) dy| ≤ (16/π)(2πM + ‖W‖₁)|x|² + 16 M |x|³`.
* `abs_partialDeriv_one_partialDeriv_zero_sub_le`:
  `|∂₁∂₀φ(x) - ∂₁∂₀φ(0)| ≤ (16/π)(2πM + ‖W'‖₁)|x|² + 16 M |x|³`.
* `abs_partialDeriv_zero_partialDeriv_zero_le`: the same bound for `|∂₀∂₀φ(x)|`.
* `partialDeriv_one_partialDeriv_zero_sub_isBigO`: `ũ_x = O(|x|²)` at the origin.
* `partialDeriv_zero_partialDeriv_zero_isBigO`: `ṽ_x = O(|x|²)` at the origin.

## How it works

We differentiate under the Green integral in the tangential direction: `∂₀φ` is the Green potential
of `∂₀ω` (`partialDeriv_halfSpaceGreenPotential_eq`), so the second derivatives of `φ` are integrals
of the gradient kernels `gⱼ` against the odd extension `W'`
(`partialDeriv_halfSpaceGreenPotential_eq_integral`), which is even in `y₀` and odd in `y₁`. In the
quadratic estimate `abs_integral_gradientKernel_sub_sub_le` we split the plane at `|y| = 2|x|`. On
the far part we fold onto the quadrant (`setIntegral_eq_setIntegral_inter_quadrant`), which gives
the kernel `evenOddKernel gⱼ`; it is even in `x`, so its first-order term vanishes and it moves by
at most `(16/π)|x|²/|y|³` from its value at the origin
(`abs_evenOddKernel_gradientKernel_one_sub_le`, `abs_evenOddKernel_gradientKernel_zero_sub_le`). On
the near part we bound `|gⱼ(z)|` by `1/(2π|z|)` (`abs_gradientKernel_le`) and `|W'(y)|` by `M|y|²`,
and integrate `1/|x - y|` over a ball (`integral_ball_norm_sub_inv`). For `∂₀∂₀φ` the value at the
origin vanishes, since `g₀(-y) W'(y)` is odd under the reflection of `y₀`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 4.2, (4.8) and the display
  after it, pp. 39-40.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open GreenFunction PotentialTheory.Planar

namespace IncompressibleFlow

section Estimate

local notation "𝐑" => PDE.Common.coordinateReflection

/-- **The quadratic estimate.** Let `W` be integrable, even in `y₀` and odd in `y₁`, with
`|W(y)| ≤ M |y|²`, and let the even-odd kernel of `gⱼ` satisfy the far-field bound. Then
`|∫ (gⱼ(x - y) - gⱼ(-y)) W(y) dy| ≤ (16/π)(2πM + ‖W‖₁)|x|² + 16 M |x|³`. -/
theorem abs_integral_gradientKernel_sub_sub_le (j : Fin 2) {W : ℝ^2 → ℝ} (hW : Integrable W)
    (hW₀ : ∀ y, W (𝐑 0 y) = W y) (hW₁ : ∀ y, W (𝐑 1 y) = -W y) {M : ℝ}
    (hM : ∀ y, |W y| ≤ M * ‖y‖ ^ 2) (x : ℝ^2)
    (hker : ∀ y, y ≠ 0 → 2 * ‖x‖ ≤ ‖y‖ →
      |evenOddKernel (gradientKernel j) x y - evenOddKernel (gradientKernel j) 0 y| ≤
        16 / Real.pi * ‖x‖ ^ 2 / ‖y‖ ^ 3)
    (hgint : Integrable fun y ↦ gradientKernel j (x - y) * W y)
    (hg0int : Integrable fun y ↦ gradientKernel j (-y) * W y) :
    |∫ y, (gradientKernel j (x - y) - gradientKernel j (-y)) * W y| ≤
      16 / Real.pi * (2 * Real.pi * M + ∫ y, |W y|) * ‖x‖ ^ 2 + 16 * M * ‖x‖ ^ 3 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hM0 : 0 ≤ M := by simpa using (abs_nonneg _).trans (hM (EuclideanSpace.single 0 1))
  set F : ℝ^2 → ℝ := fun y ↦ (gradientKernel j (x - y) - gradientKernel j (-y)) * W y with hFdef
  have hF : Integrable F :=
    (hgint.sub hg0int).congr (.of_forall fun y ↦ by simp only [hFdef, Pi.sub_apply]; ring)
  have hnm : Measurable fun y : ℝ^2 ↦ ‖y‖ := measurable_norm
  set A : Set (ℝ^2) := {y | 2 * ‖x‖ ≤ ‖y‖}
  have hA : MeasurableSet A := measurableSet_le measurable_const hnm
  rw [← integral_add_compl hA hF]
  -- the far part, folded onto the quadrant
  have hfar : |∫ y in A, F y| ≤ 16 / Real.pi * (2 * Real.pi * M + ∫ y, |W y|) * ‖x‖ ^ 2 := by
    have hAR (i : Fin 2) (y : ℝ^2) : 𝐑 i y ∈ A ↔ y ∈ A := by
      simp only [A, mem_ofPred_eq, PDE.Common.norm_coordinateReflection]
    rw [setIntegral_eq_setIntegral_inter_quadrant hA (hAR 0) (hAR 1) hF.integrableOn]
    have hfold : ∀ y, F y + F (𝐑 0 y) + F (𝐑 1 y) + F (-y) =
        (evenOddKernel (gradientKernel j) x y - evenOddKernel (gradientKernel j) 0 y) * W y := by
      intro y
      have hneg : W (-y) = -W y := by rw [← coordinateReflection_zero_one, hW₀, hW₁]
      simp only [hFdef, hW₀, hW₁, hneg, evenOddKernel, sub_neg_eq_add, zero_sub, zero_add,
        neg_neg]
      ring
    simp_rw [hfold]
    set G : ℝ^2 → ℝ := fun y ↦ 16 / Real.pi * ‖x‖ ^ 2 *
      ((Metric.ball (0 : ℝ^2) 1).indicator (fun y ↦ M * ‖y‖⁻¹) y + |W y|)
    have hind : Integrable ((Metric.ball (0 : ℝ^2) 1).indicator (fun y ↦ M * ‖y‖⁻¹)) :=
      IntegrableOn.integrable_indicator ((integrableOn_ball_norm_inv_two 1).const_mul M)
        measurableSet_ball
    have hGi : Integrable G := (hind.add hW.abs).const_mul _
    have hG0 : 0 ≤ᵐ[volume] G := Eventually.of_forall fun y ↦ by
      have h1 : 0 ≤ (Metric.ball (0 : ℝ^2) 1).indicator (fun y ↦ M * ‖y‖⁻¹) y :=
        indicator_nonneg (fun z _ ↦ by positivity) y
      positivity
    have hGint : ∫ y, G y = 16 / Real.pi * (2 * Real.pi * M + ∫ y, |W y|) * ‖x‖ ^ 2 := by
      simp only [G]
      rw [integral_const_mul, integral_add hind hW.abs,
        integral_indicator measurableSet_ball, integral_const_mul,
        integral_ball_norm_inv_two 1 one_pos]
      ring
    rw [← hGint, ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (hGi.integrableOn) ?_).trans
      (setIntegral_le_integral hGi hG0)
    filter_upwards [ae_restrict_mem (hA.inter measurableSet_quadrant)] with y hy
    have hy0 : y ≠ 0 := by rintro rfl; simpa using hy.2.1
    have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    rw [Real.norm_eq_abs, abs_mul]
    have hk := hker y hy0 hy.1
    simp only [G]
    have hb' : |W y| / ‖y‖ ^ 3 ≤
        (Metric.ball (0 : ℝ^2) 1).indicator (fun y ↦ M * ‖y‖⁻¹) y + |W y| := by
      by_cases hb : y ∈ Metric.ball (0 : ℝ^2) 1
      · rw [indicator_of_mem hb]
        have hWy := hM y
        calc |W y| / ‖y‖ ^ 3 ≤ M * ‖y‖ ^ 2 / ‖y‖ ^ 3 := by gcongr
          _ = M * ‖y‖⁻¹ := by field_simp
          _ ≤ M * ‖y‖⁻¹ + |W y| := le_add_of_nonneg_right (abs_nonneg _)
      · rw [indicator_of_notMem hb, zero_add]
        exact div_le_self (abs_nonneg _) (one_le_pow₀ (by simpa using hb))
    calc _ ≤ 16 / Real.pi * ‖x‖ ^ 2 / ‖y‖ ^ 3 * |W y| :=
          mul_le_mul_of_nonneg_right hk (abs_nonneg _)
      _ = 16 / Real.pi * ‖x‖ ^ 2 * (|W y| / ‖y‖ ^ 3) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb' (by positivity)
  -- the near part
  have hnear : |∫ y in Aᶜ, F y| ≤ 16 * M * ‖x‖ ^ 3 := by
    by_cases hx : x = 0
    · have hempty : Aᶜ = ∅ := by
        ext y; simp [A, hx]
      rw [hempty, Measure.restrict_empty, integral_zero_measure, abs_zero]
      positivity
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    set G : ℝ^2 → ℝ := fun y ↦ 2 * M * ‖x‖ ^ 2 / Real.pi *
      (Metric.ball x (3 * ‖x‖)).indicator (fun y ↦ ‖x - y‖⁻¹) y +
        M * ‖x‖ / Real.pi * (Metric.ball (0 : ℝ^2) (2 * ‖x‖)).indicator (fun _ ↦ (1 : ℝ)) y
    have hG₁ := ((integrableOn_ball_norm_sub_inv x (3 * ‖x‖)).integrable_indicator
      measurableSet_ball).const_mul (2 * M * ‖x‖ ^ 2 / Real.pi)
    have hG₂ := ((integrableOn_const (μ := volume) (C := (1 : ℝ))
      (measure_ball_lt_top (x := (0 : ℝ^2)) (r := 2 * ‖x‖)).ne).integrable_indicator
        measurableSet_ball).const_mul (M * ‖x‖ / Real.pi)
    have hGi : Integrable G := hG₁.add hG₂
    have hG0 : 0 ≤ᵐ[volume] G := Eventually.of_forall fun y ↦ by
      have h1 : 0 ≤ (Metric.ball x (3 * ‖x‖)).indicator (fun y ↦ ‖x - y‖⁻¹) y :=
        indicator_nonneg (fun z _ ↦ by positivity) y
      have h2 : 0 ≤ (Metric.ball (0 : ℝ^2) (2 * ‖x‖)).indicator (fun _ ↦ (1 : ℝ)) y :=
        indicator_nonneg (fun z _ ↦ zero_le_one) y
      positivity
    have hGint : ∫ y, G y = 16 * M * ‖x‖ ^ 3 := by
      simp only [G]
      rw [integral_add hG₁ hG₂, integral_const_mul, integral_const_mul,
        integral_indicator measurableSet_ball,
        integral_ball_norm_sub_inv x (by positivity : (0 : ℝ) < 3 * ‖x‖),
        integral_indicator_const _ measurableSet_ball, smul_eq_mul, mul_one, measureReal_def,
        EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hpi.le]
      field_simp
      ring
    rw [← hGint, ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (hGi.integrableOn) ?_).trans
      (setIntegral_le_integral hGi hG0)
    filter_upwards [ae_restrict_mem hA.compl] with y hy
    have hy' : ‖y‖ < 2 * ‖x‖ := by simpa [A] using hy
    have hball : y ∈ Metric.ball x (3 * ‖x‖) := by
      rw [Metric.mem_ball, dist_eq_norm]
      linarith [norm_sub_le y x]
    have hball' : y ∈ Metric.ball (0 : ℝ^2) (2 * ‖x‖) := by simpa using hy'
    simp only [G, indicator_of_mem hball, indicator_of_mem hball', mul_one]
    have hWy : |W y| ≤ 4 * M * ‖x‖ ^ 2 :=
      (hM y).trans ((by gcongr : M * ‖y‖ ^ 2 ≤ M * (2 * ‖x‖) ^ 2).trans_eq (by ring))
    have hg : |gradientKernel j (x - y) * W y| ≤ 2 * M * ‖x‖ ^ 2 / Real.pi * ‖x - y‖⁻¹ := by
      rw [abs_mul]
      by_cases hxy : x - y = 0
      · rw [hxy, gradientKernel_zero, abs_zero, zero_mul]
        positivity
      calc |gradientKernel j (x - y)| * |W y| ≤
            1 / (2 * Real.pi * ‖x - y‖) * (4 * M * ‖x‖ ^ 2) :=
            mul_le_mul (abs_gradientKernel_le j (x - y)) hWy (abs_nonneg _) (by positivity)
        _ = 2 * M * ‖x‖ ^ 2 / Real.pi * ‖x - y‖⁻¹ := by field_simp; ring
    have hg0 : |gradientKernel j (-y) * W y| ≤ M * ‖x‖ / Real.pi := by
      rw [abs_mul]
      by_cases hy0 : y = 0
      · rw [hy0, neg_zero, gradientKernel_zero, abs_zero, zero_mul]
        positivity
      have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
      calc |gradientKernel j (-y)| * |W y| ≤ 1 / (2 * Real.pi * ‖-y‖) * (M * ‖y‖ ^ 2) :=
            mul_le_mul (abs_gradientKernel_le j (-y)) (hM y) (abs_nonneg _) (by positivity)
        _ = M * ‖y‖ / (2 * Real.pi) := by rw [norm_neg]; field_simp
        _ ≤ M * ‖x‖ / Real.pi := by
          rw [div_le_div_iff₀ (by positivity) hpi]
          have : M * ‖y‖ ≤ M * (2 * ‖x‖) := mul_le_mul_of_nonneg_left hy'.le hM0
          nlinarith
    rw [Real.norm_eq_abs]
    simp only [hFdef]
    rw [sub_mul]
    exact (abs_sub _ _).trans (add_le_add hg hg0)
  exact (abs_add_le _ _).trans (add_le_add hfar hnear)

end Estimate

section Gradient

local notation "𝐑" => PDE.Common.coordinateReflection

variable {ω : ℝ^2 → ℝ} (hω : ContDiff ℝ 2 ω) (hc : HasCompactSupport ω)
  (hodd : ∀ y, 0 ≤ y 1 → ω (𝐑 0 y) = -ω y) {M : ℝ}
  (hM : ∀ y, 0 ≤ y 1 → |(∂[(0 : Fin 2)] ω) y| ≤ M * ‖y‖ ^ 2)
include hω hc hodd hM

omit hc hM in
/-- The tangential derivative of a source odd in `y₀` is even in `y₀` on the open half-plane. -/
private theorem partialDeriv_zero_reflect_zero {y : ℝ^2} (hy : 0 < y 1) :
    (∂[(0 : Fin 2)] ω) (𝐑 0 y) = (∂[(0 : Fin 2)] ω) y := by
  set R : ℝ^2 →L[ℝ] ℝ^2 := (PDE.Common.coordinateReflectionLinearIsometryEquiv
    (0 : Fin 2)).toContinuousLinearEquiv.toContinuousLinearMap
  have hR : ∀ z, R z = 𝐑 0 z := fun z ↦ rfl
  have hdiff : Differentiable ℝ ω := hω.differentiable (by norm_num)
  have h1 : HasFDerivAt (fun z ↦ ω (R z)) ((fderiv ℝ ω (R y)).comp R) y :=
    (hdiff (R y)).hasFDerivAt.comp y R.hasFDerivAt
  have hopen : IsOpen {z : ℝ^2 | 0 < z 1} :=
    isOpen_lt continuous_const (EuclideanSpace.proj (1 : Fin 2)).continuous
  have heq : (fun z ↦ -ω z) =ᶠ[𝓝 y] fun z ↦ ω (R z) := by
    filter_upwards [hopen.mem_nhds hy] with z hz
    rw [hR, hodd z (le_of_lt hz)]
  have h2 : HasFDerivAt (fun z ↦ -ω z) ((fderiv ℝ ω (R y)).comp R) y :=
    h1.congr_of_eventuallyEq heq
  have h3 : HasFDerivAt (fun z ↦ -ω z) (-fderiv ℝ ω y) y := (hdiff y).hasFDerivAt.neg
  have h := congrArg (fun L : ℝ^2 →L[ℝ] ℝ ↦ L (EuclideanSpace.single 0 1)) (h2.unique h3)
  have he : R (EuclideanSpace.single 0 1) = -EuclideanSpace.single 0 1 := by
    rw [hR, PDE.Common.coordinateReflection_single_same]
    ext i; fin_cases i <;> simp
  simp only [ContinuousLinearMap.comp_apply, neg_apply, he, map_neg, neg_inj] at h
  change fderiv ℝ ω (𝐑 0 y) (EuclideanSpace.single 0 1) =
    fderiv ℝ ω y (EuclideanSpace.single 0 1)
  rw [← hR]
  exact h

omit hc hM in
/-- The odd extension of `∂₀ω` is even in `y₀`. -/
private theorem oddExt_partialDeriv_reflect_zero (y : ℝ^2) :
    oddHalfSpaceExtension (∂[(0 : Fin 2)] ω) (𝐑 0 y) =
      oddHalfSpaceExtension (∂[(0 : Fin 2)] ω) y := by
  have h := oddHalfSpaceExtension_reflect_zero_eq_mul (ω := ∂[(0 : Fin 2)] ω) (c := 1)
    (fun y hy ↦ by rw [one_mul]; exact partialDeriv_zero_reflect_zero hω hodd hy) y
  rwa [one_mul] at h

omit hω hodd hM in
/-- For compactly supported vorticity the tangential derivative `∂₀ω` has compact support. -/
private theorem hasCompactSupport_partialDeriv_zero : HasCompactSupport (∂[(0 : Fin 2)] ω) :=
  hc.fderiv_apply ℝ (EuclideanSpace.single 0 (1 : ℝ))

/-- **`ũ_x = O(|x|²)`** with the explicit constant: the mixed derivative of the Green stream
moves from its value at the origin by `O(|x|²)`. -/
theorem abs_partialDeriv_one_partialDeriv_zero_sub_le (x : ℝ^2) :
    |(∂[(1 : Fin 2)] (∂[(0 : Fin 2)] (halfSpaceGreenPotential ω))) x -
        (∂[(1 : Fin 2)] (∂[(0 : Fin 2)] (halfSpaceGreenPotential ω))) 0| ≤
      16 / Real.pi * (2 * Real.pi * M +
        ∫ y, |oddHalfSpaceExtension (∂[(0 : Fin 2)] ω) y|) * ‖x‖ ^ 2 + 16 * M * ‖x‖ ^ 3 := by
  have hd := ContDiff.continuous_partialDeriv (hω.of_le (by norm_num)) (0 : Fin 2)
  have hdc := hasCompactSupport_partialDeriv_zero hc
  rw [partialDeriv_halfSpaceGreenPotential_eq (hω.of_le (by norm_num)) hc,
    partialDeriv_halfSpaceGreenPotential_eq_integral hd hdc 1 x,
    partialDeriv_halfSpaceGreenPotential_eq_integral hd hdc 1 0]
  have hW := integrable_oddHalfSpaceExtension hd hdc
  have hg := integrable_gradientKernel_sub_mul_oddHalfSpaceExtension hd hdc 1 x
  have hg0 := integrable_gradientKernel_sub_mul_oddHalfSpaceExtension hd hdc 1 0
  simp only [zero_sub] at hg0 ⊢
  rw [← integral_sub hg hg0]
  have h := abs_integral_gradientKernel_sub_sub_le 1 hW (oddExt_partialDeriv_reflect_zero hω hodd)
    (oddHalfSpaceExtension_reflect_one _) (abs_oddHalfSpaceExtension_le_mul_pow hM) x
    (fun y hy hxy ↦ abs_evenOddKernel_gradientKernel_one_sub_le hy hxy) hg hg0
  convert h using 3
  funext y
  ring

/-- **`ṽ_x = O(|x|²)`** with the explicit constant. -/
theorem abs_partialDeriv_zero_partialDeriv_zero_le (x : ℝ^2) :
    |(∂[(0 : Fin 2)] (∂[(0 : Fin 2)] (halfSpaceGreenPotential ω))) x| ≤
      16 / Real.pi * (2 * Real.pi * M +
        ∫ y, |oddHalfSpaceExtension (∂[(0 : Fin 2)] ω) y|) * ‖x‖ ^ 2 + 16 * M * ‖x‖ ^ 3 := by
  have hd := ContDiff.continuous_partialDeriv (hω.of_le (by norm_num)) (0 : Fin 2)
  have hdc := hasCompactSupport_partialDeriv_zero hc
  rw [partialDeriv_halfSpaceGreenPotential_eq (hω.of_le (by norm_num)) hc,
    partialDeriv_halfSpaceGreenPotential_eq_integral hd hdc 0 x]
  have hW := integrable_oddHalfSpaceExtension hd hdc
  have hg := integrable_gradientKernel_sub_mul_oddHalfSpaceExtension hd hdc 0 x
  have hg0 := integrable_gradientKernel_sub_mul_oddHalfSpaceExtension hd hdc 0 0
  simp only [zero_sub] at hg0
  -- the value at the origin vanishes by evenness in `y₀`
  have hzero : ∫ y, gradientKernel 0 (-y) * oddHalfSpaceExtension (∂[(0 : Fin 2)] ω) y = 0 := by
    refine integral_eq_zero_of_comp_linearIsometryEquiv_eq_neg
      (PDE.Common.coordinateReflectionLinearIsometryEquiv 0) fun z ↦ ?_
    change gradientKernel 0 (-𝐑 0 z) * oddHalfSpaceExtension (∂[(0 : Fin 2)] ω) (𝐑 0 z) = _
    have hneg : -𝐑 0 z = 𝐑 0 (-z) :=
      ((PDE.Common.coordinateReflectionLinearIsometryEquiv 0).map_neg z).symm
    have hgR : gradientKernel 0 (𝐑 0 (-z)) = -gradientKernel 0 (-z) := by
      rw [gradientKernel_eq_div, gradientKernel_eq_div, PDE.Common.norm_coordinateReflection,
        PDE.Common.coordinateReflection_apply_same]
      ring
    rw [hneg, hgR, oddExt_partialDeriv_reflect_zero hω hodd]
    ring
  have h := abs_integral_gradientKernel_sub_sub_le 0 hW (oddExt_partialDeriv_reflect_zero hω hodd)
    (oddHalfSpaceExtension_reflect_one _) (abs_oddHalfSpaceExtension_le_mul_pow hM) x
    (fun y hy hxy ↦ abs_evenOddKernel_gradientKernel_zero_sub_le hy hxy) hg hg0
  rw [← sub_zero (∫ y, _), ← hzero, ← integral_sub hg hg0]
  convert h using 3
  funext y
  ring

/-- **`ũ_x = O(|x|²)` at the origin.** -/
theorem partialDeriv_one_partialDeriv_zero_sub_isBigO :
    (fun x ↦ (∂[(1 : Fin 2)] (∂[(0 : Fin 2)] (halfSpaceGreenPotential ω))) x -
        (∂[(1 : Fin 2)] (∂[(0 : Fin 2)] (halfSpaceGreenPotential ω))) 0) =O[𝓝 0]
      fun x ↦ ‖x‖ ^ 2 := by
  set C₁ := 16 / Real.pi * (2 * Real.pi * M +
    ∫ y, |oddHalfSpaceExtension (∂[(0 : Fin 2)] ω) y|)
  refine Asymptotics.IsBigO.of_bound (|C₁| + 16 * |M|) ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ^2) one_pos] with x hx
  have hlt : ‖x‖ < 1 := by simpa using hx
  have h := abs_partialDeriv_one_partialDeriv_zero_sub_le hω hc hodd hM x
  rw [Real.norm_eq_abs, norm_pow, norm_norm]
  have h3 : ‖x‖ ^ 3 ≤ ‖x‖ ^ 2 := by
    rw [pow_succ]; exact mul_le_of_le_one_right (by positivity) hlt.le
  calc _ ≤ C₁ * ‖x‖ ^ 2 + 16 * M * ‖x‖ ^ 3 := h
    _ ≤ |C₁| * ‖x‖ ^ 2 + 16 * |M| * ‖x‖ ^ 2 := by
        gcongr
        · exact le_abs_self _
        · nlinarith [abs_nonneg M, le_abs_self M, pow_nonneg (norm_nonneg x) 2,
            pow_nonneg (norm_nonneg x) 3]
    _ = (|C₁| + 16 * |M|) * ‖x‖ ^ 2 := by ring

/-- **`ṽ_x = O(|x|²)` at the origin.** -/
theorem partialDeriv_zero_partialDeriv_zero_isBigO :
    (∂[(0 : Fin 2)] (∂[(0 : Fin 2)] (halfSpaceGreenPotential ω))) =O[𝓝 0]
      fun x ↦ ‖x‖ ^ 2 := by
  set C₁ := 16 / Real.pi * (2 * Real.pi * M +
    ∫ y, |oddHalfSpaceExtension (∂[(0 : Fin 2)] ω) y|)
  refine Asymptotics.IsBigO.of_bound (|C₁| + 16 * |M|) ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ^2) one_pos] with x hx
  have hlt : ‖x‖ < 1 := by simpa using hx
  have h := abs_partialDeriv_zero_partialDeriv_zero_le hω hc hodd hM x
  rw [Real.norm_eq_abs, norm_pow, norm_norm]
  have h3 : ‖x‖ ^ 3 ≤ ‖x‖ ^ 2 := by
    rw [pow_succ]; exact mul_le_of_le_one_right (by positivity) hlt.le
  calc _ ≤ C₁ * ‖x‖ ^ 2 + 16 * M * ‖x‖ ^ 3 := h
    _ ≤ |C₁| * ‖x‖ ^ 2 + 16 * |M| * ‖x‖ ^ 2 := by
        gcongr
        · exact le_abs_self _
        · nlinarith [abs_nonneg M, le_abs_self M, pow_nonneg (norm_nonneg x) 2,
            pow_nonneg (norm_nonneg x) 3]
    _ = (|C₁| + 16 * |M|) * ‖x‖ ^ 2 := by ring

end Gradient

end IncompressibleFlow
