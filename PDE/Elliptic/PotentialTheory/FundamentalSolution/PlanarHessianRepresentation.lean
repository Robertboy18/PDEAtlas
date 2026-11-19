/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarPrincipalValue
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import PDE.Analysis.Calculus.SmoothTransitionGlobalBounds
import PDE.Elliptic.PotentialTheory.FundamentalSolution.Pole
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Second derivatives of planar logarithmic potentials as principal values

Let `gⱼ = ∂ⱼ Φ` be the planar gradient kernel. If `W` has the line derivative `W'` in the
coordinate direction `eᵢ` at every point and is continuous at `x`, then

`∫ gⱼ(x - y) W'(y) dy = π⁻¹ P.V.∫ kᵢⱼ(x - y) W(y) dy - (δᵢⱼ / 2) W(x)`,

with the disc-truncated principal value. This is the distributional identity
`∂ᵢ∂ⱼ Φ = π⁻¹ P.V. kᵢⱼ - (δᵢⱼ/2) δ₀`, tested against a density that is differentiable only in
the direction `eᵢ`. It is behind the localized velocity gradient of Chen and Hou I, Section 3:
with `G = π Φ` their kernels are `K₁ = ∂₁∂₂G` and `K₂ = ∂₁²G` (3.1), and the local terms
`±ω(x)/2` of `u_y` and `v_x` in (3.4) come from its delta part. For the odd extension of a
vorticity across the boundary of the half-plane the direction `eᵢ` is the tangential one, along
which the extension has no jump.

## Main definitions

* `poleCutoff`: the smooth radial cutoff `θ_ε`, zero for `|z| ≤ ε/2` and one for `|z| ≥ ε`.

## Main results

* `hasPrincipalValueAt_hessianKernel_of_hasLineDerivAt`:
  `∫ gⱼ(x - y) W'(y) dy = π⁻¹ P.V.∫ kᵢⱼ(x - y) W(y) dy - (δᵢⱼ / 2) W(x)`.
* `integral_partialDeriv_poleCutoff_mul_gradientKernel`: `∫ (∂ᵢθ_ε) gⱼ = -δᵢⱼ / 2` for every
  `ε > 0`.
* `sum_integral_partialDeriv_poleCutoff_mul_gradientKernel`: the trace of these constants is `-1`.
* `partialDeriv_poleCutoff_mul_gradientKernel`: `∂ᵢ(θ_ε gⱼ) = (∂ᵢθ_ε) gⱼ + θ_ε kᵢⱼ / π`.
* `tendsto_integral_mul_sub_of_continuousAt`: kernels bounded by `C/ε²` and supported in the disc
  of radius `ε` average `W - W(x)` to zero as `ε → 0` when `W` is continuous at `x`.

## How it works

We regularize `gⱼ` with the smooth radial cutoff `θ_ε` (built from Mathlib's
`Real.smoothTransition`), move `∂ᵢ` onto `θ_ε gⱼ` with Mathlib's integration by parts for line
derivatives (`integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable`), and let
`ε → 0`. The cutoff derivative contributes `cᵢⱼ W(x)` with `cᵢⱼ = ∫ (∂ᵢθ_ε) gⱼ = -δᵢⱼ/2`: the
off-diagonal entries and the difference of the diagonal ones vanish by the reflection and swap
symmetries, and the trace is `∫ Φ Δ(1 - θ_ε) = -1` by the distributional identity `-ΔΦ = δ₀`
(`PotentialTheory.integral_fundamentalSolution_mul_laplacian`). Only continuity of `W` at `x` is
used, to evaluate this term and to compare the smooth and the sharp truncations
(`tendsto_integral_mul_sub_of_continuousAt`). The assembly is
`hasPrincipalValueAt_hessianKernel_of_hasLineDerivAt`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 3, (3.1) and (3.4).
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology

namespace PotentialTheory.Planar

open PDE (partialDeriv)

/-- The smooth radial cutoff `θ_ε(z) = S(4|z|²/(3ε²) - 1/3)`, with `S` Mathlib's smooth
transition: it vanishes for `|z| ≤ ε/2` and equals one for `|z| ≥ ε`. -/
def poleCutoff (ε : ℝ) (z : ℝ^2) : ℝ :=
  Real.smoothTransition (4 / (3 * ε ^ 2) * ‖z‖ ^ 2 - 1 / 3)

section Cutoff

variable {ε : ℝ}

/-- For `ε > 0` the cutoff `θ_ε` vanishes on the closed disc `|z| ≤ ε/2`. -/
theorem poleCutoff_eq_zero (hε : 0 < ε) {z : ℝ^2} (hz : ‖z‖ ≤ ε / 2) : poleCutoff ε z = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have h : ‖z‖ ^ 2 ≤ ε ^ 2 / 4 := by nlinarith [norm_nonneg z]
  have : 4 / (3 * ε ^ 2) * ‖z‖ ^ 2 ≤ 1 / 3 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
  linarith

/-- For `ε > 0` the cutoff `θ_ε` equals one where `|z| ≥ ε`. -/
theorem poleCutoff_eq_one (hε : 0 < ε) {z : ℝ^2} (hz : ε ≤ ‖z‖) : poleCutoff ε z = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have h : ε ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith
  have : 4 / 3 ≤ 4 / (3 * ε ^ 2) * ‖z‖ ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; nlinarith
  linarith

/-- The cutoff `θ_ε` is nonnegative. -/
theorem poleCutoff_nonneg (z : ℝ^2) : 0 ≤ poleCutoff ε z := Real.smoothTransition.nonneg _

/-- The cutoff `θ_ε` is at most one. -/
theorem poleCutoff_le_one (z : ℝ^2) : poleCutoff ε z ≤ 1 := Real.smoothTransition.le_one _

/-- The cutoff `θ_ε` is smooth. -/
theorem contDiff_poleCutoff {n : ℕ∞} : ContDiff ℝ n (poleCutoff ε) := by
  unfold poleCutoff
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul (contDiff_norm_sq ℝ)).sub contDiff_const)

/-- The cutoff `θ_ε` is radial: it is invariant under every linear isometry of the plane. -/
theorem poleCutoff_comp_linearIsometryEquiv (e : ℝ^2 ≃ₗᵢ[ℝ] ℝ^2) (z : ℝ^2) :
    poleCutoff ε (e z) = poleCutoff ε z := by
  simp [poleCutoff]

/-- The derivative of the cutoff. -/
theorem hasFDerivAt_poleCutoff (z : ℝ^2) :
    HasFDerivAt (poleCutoff ε)
      ((deriv Real.smoothTransition (4 / (3 * ε ^ 2) * ‖z‖ ^ 2 - 1 / 3) * (8 / (3 * ε ^ 2))) •
        innerSL ℝ z) z := by
  have hn := (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hin := (hn.const_mul (4 / (3 * ε ^ 2))).sub_const (1 / 3)
  have hS := ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero
    (4 / (3 * ε ^ 2) * ‖z‖ ^ 2 - 1 / 3)).hasDerivAt
  have h := hS.comp_hasFDerivAt z hin
  have hL : (deriv Real.smoothTransition (4 / (3 * ε ^ 2) * ‖z‖ ^ 2 - 1 / 3) *
      (8 / (3 * ε ^ 2))) • innerSL ℝ z =
      deriv Real.smoothTransition (4 / (3 * ε ^ 2) * ‖z‖ ^ 2 - 1 / 3) •
        ((4 / (3 * ε ^ 2)) • (2 : ℕ) • innerSL ℝ z) := by
    ext v
    simp only [smul_apply, smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  have hfun : poleCutoff ε = Real.smoothTransition ∘ fun x : ℝ^2 ↦
      4 / (3 * ε ^ 2) * ‖x‖ ^ 2 - 1 / 3 := by
    funext x; simp [poleCutoff]
  rw [hL, hfun]
  exact h

/-- The coordinate derivatives of the cutoff, `∂ᵢθ_ε(z) = S'(t(z)) (8/(3ε²)) zᵢ`. -/
theorem partialDeriv_poleCutoff (i : Fin 2) (z : ℝ^2) :
    (∂[i] (poleCutoff ε)) z =
      deriv Real.smoothTransition (4 / (3 * ε ^ 2) * ‖z‖ ^ 2 - 1 / 3) * (8 / (3 * ε ^ 2)) *
        z i := by
  unfold partialDeriv
  rw [(hasFDerivAt_poleCutoff z).fderiv]
  simp [EuclideanSpace.inner_single_right]

/-- The cutoff derivative vanishes off the annulus `ε/2 < |z| < ε`. -/
theorem partialDeriv_poleCutoff_eq_zero (hε : 0 < ε) (i : Fin 2) {z : ℝ^2}
    (hz : ‖z‖ ≤ ε / 2 ∨ ε ≤ ‖z‖) : (∂[i] (poleCutoff ε)) z = 0 := by
  rw [partialDeriv_poleCutoff]
  rcases hz with hz | hz
  · rw [PDE.Analysis.deriv_smoothTransition_zero_of_nonpos]
    · ring
    have h : ‖z‖ ^ 2 ≤ ε ^ 2 / 4 := by nlinarith [norm_nonneg z]
    have : 4 / (3 * ε ^ 2) * ‖z‖ ^ 2 ≤ 1 / 3 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
    linarith
  · rw [PDE.Analysis.deriv_smoothTransition_zero_of_one_le]
    · ring
    have h : ε ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith
    have : 4 / 3 ≤ 4 / (3 * ε ^ 2) * ‖z‖ ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; nlinarith
    linarith

/-- The cutoff derivative is bounded by `96 / ε`. -/
theorem abs_partialDeriv_poleCutoff_le (hε : 0 < ε) (i : Fin 2) (z : ℝ^2) :
    |(∂[i] (poleCutoff ε)) z| ≤ 96 / ε := by
  by_cases hz : ε ≤ ‖z‖
  · rw [partialDeriv_poleCutoff_eq_zero hε i (Or.inr hz), abs_zero]; positivity
  replace hz := lt_of_not_ge hz
  rw [partialDeriv_poleCutoff, abs_mul, abs_mul]
  have hzi : |z i| ≤ ε := by
    have : |z i| ≤ ‖z‖ := by simpa using PiLp.norm_apply_le z i
    linarith
  have hd := PDE.Analysis.abs_deriv_smoothTransition_le (4 / (3 * ε ^ 2) * ‖z‖ ^ 2 - 1 / 3)
  rw [abs_of_pos (by positivity : (0 : ℝ) < 8 / (3 * ε ^ 2))]
  calc _ ≤ 36 * (8 / (3 * ε ^ 2)) * ε := by gcongr
    _ = 96 / ε := by field_simp; ring

end Cutoff

section Regularized

variable {ε : ℝ}

/-- The gradient kernel `gⱼ` takes the value `0` at the pole. -/
theorem gradientKernel_zero (j : Fin 2) : gradientKernel j 0 = 0 := by
  simp [gradientKernel]

/-- The gradient kernel is bounded by `|gⱼ(z)| ≤ 1 / (2π |z|)`. -/
theorem abs_gradientKernel_le (j : Fin 2) (z : ℝ^2) :
    |gradientKernel j z| ≤ 1 / (2 * Real.pi * ‖z‖) := by
  have h := norm_gradientKernel_le j z
  rw [Real.norm_eq_abs, Real.rpow_neg_one] at h
  calc _ ≤ 1 / (2 * Real.pi) * ‖z‖⁻¹ := h
    _ = 1 / (2 * Real.pi * ‖z‖) := by rw [one_div, one_div]; ring

/-- The regularized gradient kernel vanishes near the pole. -/
theorem poleCutoff_mul_gradientKernel_eventuallyEq_zero (hε : 0 < ε) (j : Fin 2) :
    (fun z ↦ poleCutoff ε z * gradientKernel j z) =ᶠ[𝓝 0] fun _ ↦ 0 := by
  filter_upwards [ball_mem_nhds (0 : ℝ^2) (by positivity : 0 < ε / 2)] with z hz
  rw [mem_ball, dist_zero_right] at hz
  rw [poleCutoff_eq_zero hε hz.le, zero_mul]

/-- The regularized gradient kernel is differentiable everywhere. -/
theorem differentiableAt_poleCutoff_mul_gradientKernel (hε : 0 < ε) (j : Fin 2) (z : ℝ^2) :
    DifferentiableAt ℝ (fun z ↦ poleCutoff ε z * gradientKernel j z) z := by
  by_cases hz : z = 0
  · subst hz
    exact ((poleCutoff_mul_gradientKernel_eventuallyEq_zero hε j).differentiableAt_iff).mpr
      (differentiableAt_const _)
  · exact ((contDiff_poleCutoff (ε := ε) (n := 1)).differentiable one_ne_zero z).mul
      ((contDiffAt_gradientKernel j hz (n := 1)).differentiableAt one_ne_zero)

/-- The coordinate derivatives of the regularized gradient kernel,
`∂ᵢ(θ_ε gⱼ) = (∂ᵢθ_ε) gⱼ + θ_ε kᵢⱼ / π`, at every point including the pole. -/
theorem partialDeriv_poleCutoff_mul_gradientKernel (hε : 0 < ε) (i j : Fin 2) (z : ℝ^2) :
    (∂[i] (fun z ↦ poleCutoff ε z * gradientKernel j z)) z =
      (∂[i] (poleCutoff ε)) z * gradientKernel j z +
        poleCutoff ε z * (hessianKernel i j z / Real.pi) := by
  by_cases hz : z = 0
  · subst hz
    have h0 := (poleCutoff_mul_gradientKernel_eventuallyEq_zero hε j).fderiv_eq (𝕜 := ℝ)
    unfold partialDeriv
    rw [h0, poleCutoff_eq_zero hε (by rw [norm_zero]; positivity), gradientKernel_zero]
    simp
  · have hθ := ((contDiff_poleCutoff (ε := ε) (n := 1)).differentiable one_ne_zero z).hasFDerivAt
    have hg := ((contDiffAt_gradientKernel j hz (n := 1)).differentiableAt one_ne_zero).hasFDerivAt
    have h := hθ.fun_mul hg
    unfold partialDeriv
    rw [h.fderiv]
    have hk := partialDeriv_gradientKernel i j hz
    unfold partialDeriv at hk
    simp only [add_apply, smul_apply, smul_eq_mul, hk]
    ring

/-- The regularized gradient kernel is bounded by `1/(π ε)`. -/
theorem abs_poleCutoff_mul_gradientKernel_le (hε : 0 < ε) (j : Fin 2) (z : ℝ^2) :
    |poleCutoff ε z * gradientKernel j z| ≤ 1 / (Real.pi * ε) := by
  by_cases hz : ‖z‖ ≤ ε / 2
  · rw [poleCutoff_eq_zero hε hz, zero_mul, abs_zero]; positivity
  replace hz := lt_of_not_ge hz
  rw [abs_mul, abs_of_nonneg (poleCutoff_nonneg z)]
  calc _ ≤ 1 * (1 / (2 * Real.pi * ‖z‖)) :=
        mul_le_mul (poleCutoff_le_one z) (abs_gradientKernel_le j z) (abs_nonneg _) zero_le_one
    _ ≤ 1 / (Real.pi * ε) := by
        rw [one_mul]; apply one_div_le_one_div_of_le (by positivity); nlinarith [Real.pi_pos]

/-- The cutoff-derivative term `(∂ᵢθ_ε) gⱼ` is bounded by `96/(π ε²)` and vanishes off the
annulus `ε/2 < |z| < ε`. -/
theorem abs_partialDeriv_poleCutoff_mul_gradientKernel_le (hε : 0 < ε) (i j : Fin 2)
    (z : ℝ^2) : |(∂[i] (poleCutoff ε)) z * gradientKernel j z| ≤ 96 / (Real.pi * ε ^ 2) := by
  by_cases hz : ‖z‖ ≤ ε / 2
  · rw [partialDeriv_poleCutoff_eq_zero hε i (Or.inl hz), zero_mul, abs_zero]; positivity
  replace hz := lt_of_not_ge hz
  rw [abs_mul]
  calc _ ≤ 96 / ε * (1 / (2 * Real.pi * ‖z‖)) :=
        mul_le_mul (abs_partialDeriv_poleCutoff_le hε i z) (abs_gradientKernel_le j z)
          (abs_nonneg _) (by positivity)
    _ ≤ 96 / ε * (1 / (Real.pi * ε)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith [Real.pi_pos]
    _ = 96 / (Real.pi * ε ^ 2) := by field_simp

/-- The derivative of the regularized kernel is bounded by `98/(π ε²)`. -/
theorem abs_partialDeriv_poleCutoff_mul_gradientKernel_le' (hε : 0 < ε) (i j : Fin 2)
    (z : ℝ^2) :
    |(∂[i] (fun z ↦ poleCutoff ε z * gradientKernel j z)) z| ≤ 98 / (Real.pi * ε ^ 2) := by
  rw [partialDeriv_poleCutoff_mul_gradientKernel hε]
  by_cases hz : ‖z‖ ≤ ε / 2
  · rw [partialDeriv_poleCutoff_eq_zero hε i (Or.inl hz), poleCutoff_eq_zero hε hz, zero_mul,
      zero_mul, add_zero, abs_zero]
    positivity
  replace hz := lt_of_not_ge hz
  have h1 := abs_partialDeriv_poleCutoff_mul_gradientKernel_le hε i j z
  have h2 : |poleCutoff ε z * (hessianKernel i j z / Real.pi)| ≤ 2 / (Real.pi * ε ^ 2) := by
    rw [abs_mul, abs_of_nonneg (poleCutoff_nonneg z), abs_div,
      abs_of_pos Real.pi_pos]
    have hk : |hessianKernel i j z| ≤ 2 / ε ^ 2 := by
      have hz0 : 0 < ‖z‖ := by linarith
      refine (abs_hessianKernel_le i j z).trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc _ ≤ 1 * (2 / ε ^ 2 / Real.pi) := by
          gcongr
          · exact poleCutoff_le_one z
      _ = 2 / (Real.pi * ε ^ 2) := by field_simp
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ 96 / (Real.pi * ε ^ 2) + 2 / (Real.pi * ε ^ 2) := add_le_add h1 h2
    _ = 98 / (Real.pi * ε ^ 2) := by ring

/-- The cut-off Hessian kernel is bounded by `2/ε²`. -/
theorem abs_poleCutoff_mul_hessianKernel_le (hε : 0 < ε) (i j : Fin 2) (z : ℝ^2) :
    |poleCutoff ε z * hessianKernel i j z| ≤ 2 / ε ^ 2 := by
  by_cases hz : ‖z‖ ≤ ε / 2
  · rw [poleCutoff_eq_zero hε hz, zero_mul, abs_zero]; positivity
  replace hz := lt_of_not_ge hz
  have hz0 : 0 < ‖z‖ := by linarith
  rw [abs_mul, abs_of_nonneg (poleCutoff_nonneg z)]
  calc _ ≤ 1 * (1 / (2 * ‖z‖ ^ 2)) :=
        mul_le_mul (poleCutoff_le_one z) (abs_hessianKernel_le i j z) (abs_nonneg _) zero_le_one
    _ ≤ 2 / ε ^ 2 := by
        rw [one_mul, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith

end Regularized

section Constant

variable {ε : ℝ}

/-- For `ε > 0` the function `1 - θ_ε` is supported in the closed disc of radius `ε`. -/
theorem hasCompactSupport_one_sub_poleCutoff (hε : 0 < ε) :
    HasCompactSupport (fun z ↦ 1 - poleCutoff ε z) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ^2) ε)
  intro z hz
  rw [mem_closedBall, dist_zero_right, not_le] at hz
  rw [poleCutoff_eq_one hε hz.le, sub_self]

/-- The coordinate derivatives of `1 - θ_ε` are `∂ᵢ(1 - θ_ε) = -∂ᵢθ_ε`. -/
theorem partialDeriv_one_sub_poleCutoff (i : Fin 2) :
    (∂[i] (fun z ↦ 1 - poleCutoff ε z)) = fun z ↦ -(∂[i] (poleCutoff ε)) z := by
  funext z
  unfold partialDeriv
  rw [fderiv_const_sub]
  rfl

/-- The cutoff-derivative constant as a distributional pairing:
`∫ (∂ᵢθ_ε) gⱼ = ∫ Φ ∂ⱼ∂ᵢ(1 - θ_ε)`. -/
theorem integral_partialDeriv_poleCutoff_mul_gradientKernel_eq (hε : 0 < ε) (i j : Fin 2) :
    ∫ z, (∂[i] (poleCutoff ε)) z * gradientKernel j z =
      ∫ z, fundamentalSolution 2 z * (∂[j] (∂[i] (fun z ↦ 1 - poleCutoff ε z))) z := by
  have hβ : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ 1 - poleCutoff ε z) :=
    contDiff_const.sub contDiff_poleCutoff
  have hdi : ContDiff ℝ 1 (∂[i] (fun z ↦ 1 - poleCutoff ε z)) := hβ.partialDeriv i
  have hdc : HasCompactSupport (∂[i] (fun z ↦ 1 - poleCutoff ε z)) :=
    (hasCompactSupport_one_sub_poleCutoff hε).fderiv_apply ℝ (EuclideanSpace.single i (1 : ℝ))
  rw [integral_fundamentalSolution_mul_partialDeriv j hdi hdc, partialDeriv_one_sub_poleCutoff,
    ← integral_neg]
  congr 1
  funext z
  ring

/-- The trace of the cutoff-derivative constants is `-1`, from `∫ Φ Δφ = -φ(0)`. -/
theorem sum_integral_partialDeriv_poleCutoff_mul_gradientKernel (hε : 0 < ε) :
    (∫ z, (∂[0] (poleCutoff ε)) z * gradientKernel 0 z) +
      ∫ z, (∂[1] (poleCutoff ε)) z * gradientKernel 1 z = -1 := by
  have hβ : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ 1 - poleCutoff ε z) :=
    contDiff_const.sub contDiff_poleCutoff
  have hc := hasCompactSupport_one_sub_poleCutoff hε
  have hint (i : Fin 2) : Integrable fun z ↦
      fundamentalSolution 2 z * (∂[i] (∂[i] (fun z ↦ 1 - poleCutoff ε z))) z := by
    have hcont : Continuous (∂[i] (∂[i] (fun z ↦ 1 - poleCutoff ε z))) :=
      ((hβ.partialDeriv i (k := (⊤ : ℕ∞))).partialDeriv i (k := (⊤ : ℕ∞))).continuous
    have hsupp : HasCompactSupport (∂[i] (∂[i] (fun z ↦ 1 - poleCutoff ε z))) :=
      (hc.fderiv_apply ℝ (EuclideanSpace.single i (1 : ℝ))).fderiv_apply ℝ
        (EuclideanSpace.single i (1 : ℝ))
    simpa [smul_eq_mul] using
      (locallyIntegrable_fundamentalSolution 2).integrable_smul_right_of_hasCompactSupport
        hcont hsupp
  rw [integral_partialDeriv_poleCutoff_mul_gradientKernel_eq hε,
    integral_partialDeriv_poleCutoff_mul_gradientKernel_eq hε, ← integral_add (hint 0) (hint 1)]
  have hpole := PotentialTheory.integral_fundamentalSolution_mul_laplacian (n := 2) le_rfl
    (hβ.of_le (by norm_num)) hc
  have hlap : (fun z ↦ fundamentalSolution 2 z * PDE.laplacian (fun z ↦ 1 - poleCutoff ε z) z) =
      fun z ↦ fundamentalSolution 2 z * (∂[0] (∂[0] (fun z ↦ 1 - poleCutoff ε z))) z +
        fundamentalSolution 2 z * (∂[1] (∂[1] (fun z ↦ 1 - poleCutoff ε z))) z := by
    funext z
    simp only [PDE.laplacian, Fin.sum_univ_two]
    ring
  rw [hlap] at hpole
  rw [hpole, poleCutoff_eq_zero hε (by rw [norm_zero]; positivity), sub_zero]

/-- The coordinate derivatives of the cutoff transform like the coordinates. -/
private theorem partialDeriv_poleCutoff_reflect (i : Fin 2) (z : ℝ^2) :
    (∂[i] (poleCutoff ε)) (PDE.Common.coordinateReflection 0 z) =
      (if i = 0 then -1 else 1) * (∂[i] (poleCutoff ε)) z := by
  rw [partialDeriv_poleCutoff, partialDeriv_poleCutoff, PDE.Common.norm_coordinateReflection]
  fin_cases i
  · simp [PDE.Common.coordinateReflection_apply_same]
  · simp

/-- Under the coordinate swap the derivatives of the cutoff exchange: `(∂ᵢθ_ε)(z₁, z₀)` is
`(∂_{1-i}θ_ε)(z)`. -/
private theorem partialDeriv_poleCutoff_swap (i : Fin 2) (z : ℝ^2) :
    (∂[i] (poleCutoff ε)) (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1) z) =
      (∂[1 - i] (poleCutoff ε)) z := by
  rw [partialDeriv_poleCutoff, partialDeriv_poleCutoff, LinearIsometryEquiv.norm_map]
  obtain ⟨h0, h1⟩ := coordinateSwap_apply z
  fin_cases i
  · simp [h0]
  · simp [h1]

/-- Under the reflection `z₀ ↦ -z₀` the kernel `g₀` changes sign and `g₁` is unchanged. -/
private theorem gradientKernel_reflect (j : Fin 2) (z : ℝ^2) :
    gradientKernel j (PDE.Common.coordinateReflection 0 z) =
      (if j = 0 then -1 else 1) * gradientKernel j z := by
  rw [gradientKernel_eq_div, gradientKernel_eq_div, PDE.Common.norm_coordinateReflection]
  fin_cases j
  · simp [PDE.Common.coordinateReflection_apply_same]; ring
  · simp

/-- Under the coordinate swap the gradient kernels exchange: `gⱼ(z₁, z₀) = g_{1-j}(z)`. -/
private theorem gradientKernel_swap (j : Fin 2) (z : ℝ^2) :
    gradientKernel j (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1) z) =
      gradientKernel (1 - j) z := by
  rw [gradientKernel_eq_div, gradientKernel_eq_div, LinearIsometryEquiv.norm_map]
  obtain ⟨h0, h1⟩ := coordinateSwap_apply z
  fin_cases j
  · simp [h0]
  · simp [h1]

/-- **The delta coefficient**: `∫ (∂ᵢθ_ε) gⱼ = -δᵢⱼ / 2` for every `ε > 0`. -/
theorem integral_partialDeriv_poleCutoff_mul_gradientKernel (hε : 0 < ε) (i j : Fin 2) :
    ∫ z, (∂[i] (poleCutoff ε)) z * gradientKernel j z = if i = j then -1 / 2 else 0 := by
  have hoff (i j : Fin 2) (hij : i ≠ j) :
      ∫ z, (∂[i] (poleCutoff ε)) z * gradientKernel j z = 0 := by
    apply integral_eq_zero_of_comp_linearIsometryEquiv_eq_neg
      (PDE.Common.coordinateReflectionLinearIsometryEquiv 0)
    intro z
    change (∂[i] (poleCutoff ε)) (PDE.Common.coordinateReflection 0 z) *
      gradientKernel j (PDE.Common.coordinateReflection 0 z) = _
    rw [partialDeriv_poleCutoff_reflect, gradientKernel_reflect]
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
  have hdiag : ∫ z, (∂[0] (poleCutoff ε)) z * gradientKernel 0 z =
      ∫ z, (∂[1] (poleCutoff ε)) z * gradientKernel 1 z := by
    rw [← MeasureTheory.integral_comp
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1))]
    congr 1
    funext z
    rw [partialDeriv_poleCutoff_swap, gradientKernel_swap]
    rfl
  have hsum := sum_integral_partialDeriv_poleCutoff_mul_gradientKernel hε
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte]; linarith
  · simpa using hoff 0 1 (by decide)
  · simpa using hoff 1 0 (by decide)
  · simp only [Fin.mk_one, Fin.isValue, ↓reduceIte]; linarith

end Constant

section Main

/-- The area of a planar closed disc. -/
theorem measureReal_closedBall_two (x : ℝ^2) {ε : ℝ} (hε : 0 ≤ ε) :
    volume.real (closedBall x ε) = ε ^ 2 * Real.pi := by
  rw [measureReal_def, EuclideanSpace.volume_closedBall_fin_two, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hε, ENNReal.toReal_ofReal Real.pi_pos.le]

/-- Kernels bounded by `C/ε²` and supported in the closed disc of radius `ε` average
`W - W(x)` to zero as `ε → 0` when `W` is continuous at `x`. -/
theorem tendsto_integral_mul_sub_of_continuousAt {Q : ℝ → ℝ^2 → ℝ} {C : ℝ} {W : ℝ^2 → ℝ}
    {x : ℝ^2} (hQb : ∀ ε > 0, ∀ z, |Q ε z| ≤ C / ε ^ 2)
    (hQs : ∀ ε > 0, ∀ z, ε < ‖z‖ → Q ε z = 0) (hx : ContinuousAt W x) :
    Tendsto (fun ε ↦ ∫ y, Q ε (x - y) * (W y - W x)) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  set C' := |C| * Real.pi + 1 with hC'def
  have hC' : 0 < C' := by positivity
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp hx (η / C') (by positivity)
  filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
  have hε0 := hε.1
  rw [dist_zero_right]
  have hbound : ∀ y, ‖Q ε (x - y) * (W y - W x)‖ ≤
      (closedBall x ε).indicator (fun _ ↦ |C| / ε ^ 2 * (η / C')) y := by
    intro y
    by_cases hy : y ∈ closedBall x ε
    · rw [indicator_of_mem hy, Real.norm_eq_abs, abs_mul]
      have hd : dist y x < δ := lt_of_le_of_lt (mem_closedBall.mp hy) hε.2
      have h1 : |W y - W x| ≤ η / C' := by
        have := hcont hd
        rw [Real.dist_eq] at this
        exact this.le
      have h2 : |Q ε (x - y)| ≤ |C| / ε ^ 2 :=
        (hQb ε hε0 _).trans (by gcongr; exact le_abs_self C)
      exact mul_le_mul h2 h1 (abs_nonneg _) (by positivity)
    · rw [indicator_of_notMem hy]
      have hlt : ε < ‖x - y‖ := by
        rw [mem_closedBall, not_le, dist_eq_norm, norm_sub_rev] at hy
        exact hy
      rw [hQs ε hε0 _ hlt, zero_mul, norm_zero]
  have hint : Integrable ((closedBall x ε).indicator fun _ ↦ |C| / ε ^ 2 * (η / C')) :=
    (integrableOn_const (measure_closedBall_lt_top (x := x) (r := ε)).ne).integrable_indicator
      measurableSet_closedBall
  calc ‖∫ y, Q ε (x - y) * (W y - W x)‖
      ≤ ∫ y, (closedBall x ε).indicator (fun _ ↦ |C| / ε ^ 2 * (η / C')) y :=
        norm_integral_le_of_norm_le hint (Eventually.of_forall hbound)
    _ = |C| / ε ^ 2 * (η / C') * (ε ^ 2 * Real.pi) := by
        rw [integral_indicator_const _ measurableSet_closedBall, measureReal_closedBall_two x
          hε0.le, smul_eq_mul, mul_comm]
    _ = |C| * Real.pi * η / C' := by field_simp
    _ < η := by
        rw [div_lt_iff₀ hC']
        nlinarith [abs_nonneg C, Real.pi_pos]

end Main

/-- The gradient kernel `gⱼ` is measurable. -/
theorem measurable_gradientKernel (j : Fin 2) : Measurable (gradientKernel j) := by
  unfold gradientKernel
  have hj : Measurable fun z : ℝ^2 ↦ z j := (EuclideanSpace.proj j).continuous.measurable
  fun_prop

/-- **Second derivatives of planar logarithmic potentials as principal values.**
If `W` is integrable, has the line derivative `W'` along `eᵢ` at every point, `gⱼ(x - ·) W'` is
integrable and `W` is continuous at `x`, then the principal value of
`∫ kᵢⱼ(x - y) W(y) dy` exists and

`P.V.∫ kᵢⱼ(x - y) W(y) dy = π (∫ gⱼ(x - y) W'(y) dy + δᵢⱼ W(x) / 2)`. -/
theorem hasPrincipalValueAt_hessianKernel_of_hasLineDerivAt (i j : Fin 2) {W W' : ℝ^2 → ℝ}
    {x : ℝ^2} (hW : Integrable W) (hW' : Integrable fun y ↦ gradientKernel j (x - y) * W' y)
    (hd : ∀ y, HasLineDerivAt ℝ W (W' y) y (EuclideanSpace.single i (1 : ℝ)))
    (hx : ContinuousAt W x) :
    PDE.Analysis.HasPrincipalValueAt univ (fun x y ↦ hessianKernel i j (x - y)) W x
      (Real.pi * ((∫ y, gradientKernel j (x - y) * W' y) + if i = j then W x / 2 else 0)) := by
  set G := ∫ y, gradientKernel j (x - y) * W' y with hG
  set c : ℝ := if i = j then -1 / 2 else 0 with hc
  have hsubm : Measurable fun y : ℝ^2 ↦ x - y := measurable_const.sub measurable_id
  have hkm : Measurable fun y ↦ hessianKernel i j (x - y) :=
    (measurable_hessianKernel i j).comp hsubm
  have hθm (ε : ℝ) : Measurable fun y ↦ poleCutoff ε (x - y) :=
    (contDiff_poleCutoff (ε := ε) (n := 0)).continuous.measurable.comp hsubm
  have hPm (ε : ℝ) :
      Measurable fun y ↦ (∂[i] (poleCutoff ε)) (x - y) * gradientKernel j (x - y) :=
    (((contDiff_poleCutoff (ε := ε) (n := ⊤)).partialDeriv i (k := (⊤ : ℕ∞))).continuous
      |>.measurable.comp hsubm).mul ((measurable_gradientKernel j).comp hsubm)
  have hbdd {f : ℝ^2 → ℝ} {C : ℝ} (hb : ∀ y, |f y| ≤ C) (hf : Measurable f) :
      Integrable fun y ↦ f y * W y :=
    hW.bdd_mul hf.aestronglyMeasurable (Eventually.of_forall hb)
  -- A bounded kernel supported in a disc averages `W - W(x)` as below.
  have hcpt {Q : ℝ^2 → ℝ} {ε C : ℝ} (hQ : Measurable fun y ↦ Q (x - y)) (hb : ∀ z, |Q z| ≤ C)
      (hs : ∀ z, ε < ‖z‖ → Q z = 0) :
      ∫ y, Q (x - y) * (W y - W x) = (∫ y, Q (x - y) * W y) - (∫ z, Q z) * W x := by
    have hint : Integrable fun y ↦ Q (x - y) :=
      (integrableOn_iff_integrable_of_support_subset fun y hy ↦ by
        by_contra hyb
        rw [mem_closedBall, not_le, dist_eq_norm, norm_sub_rev] at hyb
        exact hy (hs _ hyb)).mp
      (Measure.integrableOn_of_bounded (M := C) (measure_closedBall_lt_top (x := x) (r := ε)).ne
        hQ.aestronglyMeasurable (Eventually.of_forall fun y ↦ hb _))
    simp_rw [mul_sub]
    rw [integral_sub (hbdd (fun y ↦ hb (x - y)) hQ) (hint.mul_const _), integral_mul_const,
      integral_sub_left_eq_self]
  -- Step 1: removing the cutoff from `∫ θ_ε gⱼ W'`.
  have hL1 : Tendsto (fun ε ↦ ∫ y, poleCutoff ε (x - y) * (gradientKernel j (x - y) * W' y))
      (𝓝[>] 0) (𝓝 G) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun y ↦ ‖gradientKernel j (x - y) * W' y‖) ?_ ?_ hW'.norm ?_
    · exact Eventually.of_forall fun ε ↦
        (hθm ε).aestronglyMeasurable.mul hW'.aestronglyMeasurable
    · exact Eventually.of_forall fun ε ↦ Eventually.of_forall fun y ↦ by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (poleCutoff_nonneg _)]
        exact mul_le_of_le_one_left (norm_nonneg _) (poleCutoff_le_one _)
    · filter_upwards [Measure.ae_ne volume x] with y hy
      have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hy))
      apply tendsto_const_nhds.congr'
      filter_upwards [Ioo_mem_nhdsGT hpos] with ε hε
      rw [poleCutoff_eq_one hε.1 hε.2.le, one_mul]
  -- Step 2: integration by parts in the direction `eᵢ`.
  have hIBP : ∀ ε > 0, ∫ y, poleCutoff ε (x - y) * (gradientKernel j (x - y) * W' y) =
      ∫ y, (∂[i] (fun z ↦ poleCutoff ε z * gradientKernel j z)) (x - y) * W y := by
    intro ε hε
    set A : ℝ^2 → ℝ := fun z ↦ poleCutoff ε z * gradientKernel j z
    have hAd := differentiableAt_poleCutoff_mul_gradientKernel hε j
    have hDm : Measurable fun y ↦ (∂[i] A) (x - y) := by
      convert (hPm ε).add ((hθm ε).mul (hkm.div_const Real.pi)) using 1
      funext y
      exact partialDeriv_poleCutoff_mul_gradientKernel hε i j (x - y)
    have hAW' : (fun y ↦ A (x - y) * W' y) =
        fun y ↦ poleCutoff ε (x - y) * (gradientKernel j (x - y) * W' y) := by
      simp only [A, mul_assoc]
    have hfg' : Integrable fun y ↦ A (x - y) * W' y := by
      rw [hAW']
      exact hW'.bdd_mul (c := 1) (hθm ε).aestronglyMeasurable
        (Eventually.of_forall fun y ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (poleCutoff_nonneg _)]; exact poleCutoff_le_one _)
    have hf : ∀ y ∈ tsupport W, HasLineDerivAt ℝ (fun y ↦ A (x - y)) (-(∂[i] A) (x - y)) y
        (EuclideanSpace.single i (1 : ℝ)) := by
      intro y _
      have h2 : HasFDerivAt (fun y : ℝ^2 ↦ x - y) (-ContinuousLinearMap.id ℝ (ℝ^2)) y :=
        (hasFDerivAt_id y).const_sub x
      have h3 := ((hAd (x - y)).hasFDerivAt.comp y h2).hasLineDerivAt
        (EuclideanSpace.single i (1 : ℝ))
      rwa [show ((fderiv ℝ A (x - y)).comp (-ContinuousLinearMap.id ℝ (ℝ^2)))
        (EuclideanSpace.single i (1 : ℝ)) = -(∂[i] A) (x - y) by simp [partialDeriv]] at h3
    have h := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
      (μ := volume) (B := ContinuousLinearMap.mul ℝ ℝ)
      (hbdd (fun y ↦ (abs_neg _).trans_le
        (abs_partialDeriv_poleCutoff_mul_gradientKernel_le' hε i j (x - y))) hDm.neg)
      hfg' (hbdd (fun y ↦ abs_poleCutoff_mul_gradientKernel_le hε j (x - y))
        ((hθm ε).mul ((measurable_gradientKernel j).comp hsubm))) hf fun y _ ↦ hd y
    simp only [ContinuousLinearMap.mul_apply', neg_mul, integral_neg, neg_neg] at h
    rw [← hAW', h]
  -- Step 3: the two parts of the derivative of the regularized kernel.
  have hsplit : ∀ ε > 0, ∫ y, (∂[i] (fun z ↦ poleCutoff ε z * gradientKernel j z)) (x - y) * W y =
      (∫ y, (∂[i] (poleCutoff ε)) (x - y) * gradientKernel j (x - y) * W y) +
        (∫ y, poleCutoff ε (x - y) * hessianKernel i j (x - y) * W y) / Real.pi := by
    intro ε hε
    rw [← integral_div, ← integral_add
      (hbdd (fun y ↦ abs_partialDeriv_poleCutoff_mul_gradientKernel_le hε i j (x - y)) (hPm ε))
      ((hbdd (fun y ↦ abs_poleCutoff_mul_hessianKernel_le hε i j (x - y))
        ((hθm ε).mul hkm)).div_const _)]
    congr 1 with y
    rw [partialDeriv_poleCutoff_mul_gradientKernel hε]
    ring
  -- Step 4: the cutoff-derivative part tends to `cᵢⱼ W(x)`.
  have hL2 : Tendsto (fun ε ↦ ∫ y, (∂[i] (poleCutoff ε)) (x - y) * gradientKernel j (x - y) * W y)
      (𝓝[>] 0) (𝓝 (c * W x)) := by
    have hlim := (tendsto_integral_mul_sub_of_continuousAt (W := W) (x := x) (C := 96 / Real.pi)
      (Q := fun ε z ↦ (∂[i] (poleCutoff ε)) z * gradientKernel j z)
      (fun ε hε z ↦ by
        rw [div_div]; exact abs_partialDeriv_poleCutoff_mul_gradientKernel_le hε i j z)
      (fun ε hε z hz ↦ by
        rw [partialDeriv_poleCutoff_eq_zero hε i (Or.inr hz.le), zero_mul]) hx).add_const
      (c * W x)
    rw [zero_add] at hlim
    refine (tendsto_congr' ?_).mp hlim
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [hcpt (Q := fun z ↦ (∂[i] (poleCutoff ε)) z * gradientKernel j z) (hPm ε)
      (abs_partialDeriv_poleCutoff_mul_gradientKernel_le hε i j) fun z hz ↦ by
        rw [partialDeriv_poleCutoff_eq_zero hε i (Or.inr hz.le), zero_mul],
      integral_partialDeriv_poleCutoff_mul_gradientKernel hε, ← hc]
    ring
  -- Step 5: the regularized principal value.
  have hB : Tendsto (fun ε ↦ ∫ y, poleCutoff ε (x - y) * hessianKernel i j (x - y) * W y)
      (𝓝[>] 0) (𝓝 (Real.pi * (G - c * W x))) := by
    have heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Real.pi *
        ((∫ y, poleCutoff ε (x - y) * (gradientKernel j (x - y) * W' y)) -
          ∫ y, (∂[i] (poleCutoff ε)) (x - y) * gradientKernel j (x - y) * W y) =
        ∫ y, poleCutoff ε (x - y) * hessianKernel i j (x - y) * W y := by
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      rw [hIBP ε hε, hsplit ε hε]
      field_simp
      ring
    exact (tendsto_congr' heq).mp ((hL1.sub hL2).const_mul Real.pi)
  -- Step 6: comparison of the smooth and the sharp truncations.
  have hcomp : Tendsto (fun ε ↦ (∫ y in univ ∩ {y | ε < ‖x - y‖}, hessianKernel i j (x - y) * W y) -
      ∫ y, poleCutoff ε (x - y) * hessianKernel i j (x - y) * W y) (𝓝[>] 0) (𝓝 0) := by
    let Q : ℝ → ℝ^2 → ℝ := fun ε z ↦ ((Ioi ε).indicator (fun _ ↦ (1 : ℝ)) ‖z‖ - poleCutoff ε z) *
      hessianKernel i j z
    have hQs : ∀ ε > 0, ∀ z, ε < ‖z‖ → Q ε z = 0 := by
      intro ε hε z hz
      simp only [Q, indicator_of_mem (show ‖z‖ ∈ Ioi ε from hz), poleCutoff_eq_one hε hz.le,
        sub_self, zero_mul]
    have hQb : ∀ ε > 0, ∀ z, |Q ε z| ≤ 2 / ε ^ 2 := by
      intro ε hε z
      by_cases h : ε < ‖z‖
      · rw [hQs ε hε z h, abs_zero]
        positivity
      simp only [Q, indicator_of_notMem (show ‖z‖ ∉ Ioi ε from h), zero_sub, neg_mul, abs_neg]
      exact abs_poleCutoff_mul_hessianKernel_le hε i j z
    have hQm (ε : ℝ) : Measurable fun y ↦ Q ε (x - y) :=
      ((((measurable_const.indicator measurableSet_Ioi).comp hsubm.norm).sub (hθm ε)).mul hkm)
    apply (tendsto_congr' ?_).mp
      (tendsto_integral_mul_sub_of_continuousAt (W := W) (x := x) (C := 2) hQb hQs hx)
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have hθkW := hbdd (fun y ↦ abs_poleCutoff_mul_hessianKernel_le hε i j (x - y))
      ((hθm ε).mul hkm)
    have hzero : ∫ z, Q ε z = 0 := by
      apply integral_mul_hessianKernel_eq_zero
      · intro z; simp [PDE.Common.norm_coordinateReflection, poleCutoff]
      · intro z; simp [poleCutoff]
    have htrunc : ∫ y in univ ∩ {y | ε < ‖x - y‖}, hessianKernel i j (x - y) * W y =
        ∫ y, (Ioi ε).indicator (fun _ ↦ (1 : ℝ)) ‖x - y‖ * hessianKernel i j (x - y) * W y := by
      rw [univ_inter, ← integral_indicator (measurableSet_lt measurable_const hsubm.norm)]
      congr 1 with y
      by_cases hy : ε < ‖x - y‖ <;> simp [indicator, hy]
    have hdiff : (∫ y, (Ioi ε).indicator (fun _ ↦ (1 : ℝ)) ‖x - y‖ * hessianKernel i j (x - y) *
        W y) - ∫ y, poleCutoff ε (x - y) * hessianKernel i j (x - y) * W y =
          ∫ y, Q ε (x - y) * W y := by
      rw [← integral_sub ((hbdd (fun y ↦ hQb ε hε (x - y)) (hQm ε)).add hθkW |>.congr
        (Eventually.of_forall fun y ↦ by simp only [Q, Pi.add_apply]; ring)) hθkW]
      congr 1; funext y; simp only [Q]; ring
    rw [htrunc, hdiff, hcpt (Q := Q ε) (hQm ε) (hQb ε hε) (hQs ε hε), hzero, zero_mul, sub_zero]
  -- Conclusion.
  refine ⟨?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [univ_inter]
    refine (hW.integrableOn).bdd_mul (c := 1 / (2 * ε ^ 2)) hkm.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem (measurableSet_lt measurable_const hsubm.norm)] with y hy
    rw [Real.norm_eq_abs]
    exact abs_hessianKernel_le_of_lt i j hε hy
  · have hval : Real.pi * (G - c * W x) =
        Real.pi * (G + if i = j then W x / 2 else 0) := by
      rw [hc]; split_ifs <;> ring
    rw [← hval]
    have := hcomp.add hB
    rw [zero_add] at this
    refine (tendsto_congr' (Eventually.of_forall fun ε ↦ ?_)).mp this
    unfold PDE.Analysis.principalValueTruncation
    ring

end PotentialTheory.Planar
