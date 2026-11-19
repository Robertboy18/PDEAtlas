/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.BiotSavart
public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.QuadrantSymmetrization
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.GradientBounds

/-!
# The strain of the half-plane velocity at the origin

For a compactly supported `C²` vorticity `ω` odd in the tangential coordinate, the horizontal
velocity `u` of `halfPlaneVelocity ω` is differentiable at the origin within the closed
half-plane, and its tangential derivative is

`u_x(0) = -(4/π) ∫_{ℝ²₊₊} y₀ y₁ / |y|⁴ ω(y) dy = -(4/π) ⟨ω, f_*⟩`,

the formula for `c_ω` of Chen and Hou, Part I, (5.67). The integral converges absolutely
because oddness gives `|ω(y)| ≤ L |y₀|`. The origin is a boundary point where the odd extension
of `ω` is continuous, so the principal-value identity for `∂₁∂₀φ` applies there; the principal
value is then an absolutely convergent integral, and folding onto the quadrant gives the factor
`4`.

## Main results

* `oddHalfSpaceExtension_reflect_zero`: a source odd in the tangential coordinate has an odd
  extension odd in both coordinates.
* `abs_le_mul_abs_of_odd`: oddness in `y₀` and a `C¹` bound give `|ω(y)| ≤ B |y₀|` on the closed
  upper half-plane.
* `integrableOn_hessianKernel_mul_quadrant`: the strain integral `∫_{ℝ²₊₊} y₀ y₁/|y|⁴ ω(y) dy`
  converges absolutely.
* `pi_mul_partialDeriv_partialDeriv_zero_origin`: `π ∂₁∂₀φ(0) = 4 ∫_{ℝ²₊₊} K₁(y) ω(y) dy`.
* `hasFDerivWithinAt_halfPlaneVelocity_zero`: the horizontal velocity is differentiable at the
  origin within the closed half-plane.
* `cOmega_eq`: (5.67), `u_x(0) = -(4/π) ∫_{ℝ²₊₊} y₀ y₁/|y|⁴ ω(y) dy`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 5.6, (5.67), p. 78.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open GreenFunction PotentialTheory.Planar SobolevSpace

namespace IncompressibleFlow

local notation "𝐑" => PDE.Common.coordinateReflection

variable {ω : ℝ^2 → ℝ}

/-- The boundary reflection of the half-plane is the reflection of coordinate `1`. -/
theorem reflect_two_eq_coordinateReflection_one (y : ℝ^2) : HalfSpace.reflect 2 y = 𝐑 1 y := by
  have h0 : (HalfSpace.reflect 2 y) 0 = (𝐑 1 y) 0 := by
    rw [HalfSpace.reflect_apply_of_ne_last (n := 2) _ (i := 0) (by decide),
      PDE.Common.coordinateReflection_apply_of_ne (1 : Fin 2) 0 (by decide)]
  have h1 : (HalfSpace.reflect 2 y) 1 = (𝐑 1 y) 1 := by
    change HalfSpace.reflect 2 y PDE.Common.lastIndex = _
    rw [HalfSpace.reflect_apply_last, PDE.Common.coordinateReflection_apply_same]
    rfl
  ext k
  fin_cases k
  · exact h0
  · exact h1

/-- The odd extension is odd in the boundary-normal coordinate. -/
theorem oddHalfSpaceExtension_reflect_one (ω : ℝ^2 → ℝ) (y : ℝ^2) :
    oddHalfSpaceExtension ω (𝐑 1 y) = -oddHalfSpaceExtension ω y := by
  rw [← reflect_two_eq_coordinateReflection_one, oddHalfSpaceExtension_reflect]

/-- If `ω ∘ R₀ = c ω` on the open upper half-plane, the odd extension satisfies the same
identity on the whole plane. -/
theorem oddHalfSpaceExtension_reflect_zero_eq_mul {c : ℝ}
    (h : ∀ y, 0 < y 1 → ω (𝐑 0 y) = c * ω y) (y : ℝ^2) :
    oddHalfSpaceExtension ω (𝐑 0 y) = c * oddHalfSpaceExtension ω y := by
  have h1 : (𝐑 0 y) 1 = y 1 :=
    PDE.Common.coordinateReflection_apply_of_ne (0 : Fin 2) 1 (by decide) y
  have hu : 𝐑 0 y ∈ HalfSpace.upper 2 ↔ y ∈ HalfSpace.upper 2 := by
    change 0 < (𝐑 0 y) 1 ↔ 0 < y 1; rw [h1]
  have hl : 𝐑 0 y ∈ HalfSpace.lower 2 ↔ y ∈ HalfSpace.lower 2 := by
    change (𝐑 0 y) 1 < 0 ↔ y 1 < 0; rw [h1]
  have hcomm : HalfSpace.reflect 2 (𝐑 0 y) = 𝐑 0 (HalfSpace.reflect 2 y) := by
    rw [reflect_two_eq_coordinateReflection_one, reflect_two_eq_coordinateReflection_one,
      coordinateReflection_comm]
  rcases lt_trichotomy (y 1) 0 with hy | hy | hy
  · have hyl : y ∈ HalfSpace.lower 2 := hy
    have hyu : y ∉ HalfSpace.upper 2 := fun h ↦ by
      have : (0 : ℝ) < y 1 := h
      linarith
    have hr : 0 < (HalfSpace.reflect 2 y) 1 := by
      have : (0 : ℝ) < (HalfSpace.reflect 2 y) PDE.Common.lastIndex := by
        rw [HalfSpace.reflect_apply_last]; change 0 < -y 1; linarith
      exact this
    simp only [oddHalfSpaceExtension, Pi.sub_apply, indicator_of_mem (hl.mpr hyl),
      indicator_of_notMem (fun h ↦ hyu (hu.mp h)), indicator_of_mem hyl,
      indicator_of_notMem hyu, hcomm, h _ hr]
    ring
  · have hyl : y ∉ HalfSpace.lower 2 := fun h ↦ by
      have : y 1 < 0 := h
      linarith
    have hyu : y ∉ HalfSpace.upper 2 := fun h ↦ by
      have : (0 : ℝ) < y 1 := h
      linarith
    simp only [oddHalfSpaceExtension, Pi.sub_apply,
      indicator_of_notMem (fun h ↦ hyl (hl.mp h)), indicator_of_notMem (fun h ↦ hyu (hu.mp h)),
      indicator_of_notMem hyl, indicator_of_notMem hyu]
    ring
  · have hyu : y ∈ HalfSpace.upper 2 := hy
    have hyl : y ∉ HalfSpace.lower 2 := fun h ↦ by
      have : y 1 < 0 := h
      linarith
    simp only [oddHalfSpaceExtension, Pi.sub_apply, indicator_of_mem (hu.mpr hyu),
      indicator_of_notMem (fun h ↦ hyl (hl.mp h)), indicator_of_mem hyu, indicator_of_notMem hyl,
      h y hy]
    ring

/-- A source odd in the tangential coordinate has an odd extension odd in both coordinates. -/
theorem oddHalfSpaceExtension_reflect_zero (hodd : ∀ y, 0 ≤ y 1 → ω (𝐑 0 y) = -ω y) (y : ℝ^2) :
    oddHalfSpaceExtension ω (𝐑 0 y) = -oddHalfSpaceExtension ω y := by
  have h := oddHalfSpaceExtension_reflect_zero_eq_mul (ω := ω) (c := -1)
    (fun y hy ↦ by rw [hodd y hy.le]; ring) y
  rw [h]; ring

/-- Oddness in `y₀` and a `C¹` bound give `|ω(y)| ≤ B |y₀|` on the closed upper half-plane. -/
theorem abs_le_mul_abs_of_odd (hω : ContDiff ℝ 1 ω) (hc : HasCompactSupport ω)
    (hodd : ∀ y, 0 ≤ y 1 → ω (𝐑 0 y) = -ω y) :
    ∃ B, 0 ≤ B ∧ ∀ y, 0 ≤ y 1 → |ω y| ≤ B * |y 0| := by
  obtain ⟨B, hB⟩ := (hω.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hc.fderiv (𝕜 := ℝ))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine ⟨B, hB0, fun y hy ↦ ?_⟩
  set p : ℝ^2 := y - y 0 • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
  have hp0 : ω p = 0 := by
    have hfix : 𝐑 0 p = p := by
      ext k
      fin_cases k
      · simp [p, PDE.Common.coordinateReflection_apply_same]
      · simp [p, PDE.Common.coordinateReflection_apply_of_ne]
    have hp1 : 0 ≤ p 1 := by simpa [p] using hy
    have := hodd p hp1
    rw [hfix] at this
    linarith
  have hyp : ‖y - p‖ = |y 0| := by
    simp only [p, sub_sub_cancel, norm_smul, Real.norm_eq_abs]
    rw [PiLp.norm_single, norm_one, mul_one]
  have h := convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ ↦ (hω.differentiable one_ne_zero) z) (fun z _ ↦ hB z) (mem_univ p) (mem_univ y)
  rw [hp0, sub_zero, hyp, Real.norm_eq_abs] at h
  exact h

/-- The odd extension inherits the bound `|W(y)| ≤ B |y₀|`. -/
theorem abs_oddHalfSpaceExtension_le {B : ℝ} (hB0' : 0 ≤ B)
    (hB : ∀ y, 0 ≤ y 1 → |ω y| ≤ B * |y 0|) (y : ℝ^2) :
    |oddHalfSpaceExtension ω y| ≤ B * |y 0| := by
  have hB0 : 0 ≤ B * |y 0| := mul_nonneg hB0' (abs_nonneg _)
  have hr : (HalfSpace.reflect 2 y) 0 = y 0 :=
    HalfSpace.reflect_apply_of_ne_last (n := 2) _ (i := 0) (by decide)
  unfold oddHalfSpaceExtension
  simp only [Pi.sub_apply, indicator]
  split_ifs with h1 h2 h2
  · exact absurd h2 (fun h ↦ by
      have a : (0 : ℝ) < y PDE.Common.lastIndex := h1
      have b : y PDE.Common.lastIndex < 0 := h
      linarith)
  · rw [sub_zero]; exact hB y (le_of_lt h1)
  · rw [zero_sub, abs_neg]
    have hrl : 0 ≤ (HalfSpace.reflect 2 y) 1 := by
      have : (0 : ℝ) < (HalfSpace.reflect 2 y) PDE.Common.lastIndex := by
        rw [HalfSpace.reflect_apply_last]; have : y PDE.Common.lastIndex < 0 := h2; linarith
      exact this.le
    have := hB (HalfSpace.reflect 2 y) hrl; rwa [hr] at this
  · rw [sub_zero, abs_zero]; exact hB0

/-- The strain integrand `K₁ W` is integrable for odd `C¹` compact data. -/
theorem integrable_hessianKernel_mul_oddHalfSpaceExtension (hω : ContDiff ℝ 1 ω)
    (hc : HasCompactSupport ω) (hodd : ∀ y, 0 ≤ y 1 → ω (𝐑 0 y) = -ω y) :
    Integrable fun y ↦ hessianKernel 0 1 y * oddHalfSpaceExtension ω y := by
  obtain ⟨B, hB0, hB⟩ := abs_le_mul_abs_of_odd hω hc hodd
  have hWi := integrable_oddHalfSpaceExtension hω.continuous hc
  have hm : AEStronglyMeasurable (fun y ↦ hessianKernel 0 1 y * oddHalfSpaceExtension ω y) :=
    (measurable_hessianKernel 0 1).aestronglyMeasurable.mul hWi.aestronglyMeasurable
  have hnear : IntegrableOn (fun y ↦ hessianKernel 0 1 y * oddHalfSpaceExtension ω y)
      (Metric.ball (0 : ℝ^2) 1) := by
    refine ((integrableOn_ball_norm_inv_two 1).const_mul B).mono' hm.restrict ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hy : y = 0
    · subst hy; simp [hessianKernel]
    have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have h0 : |y 0| ≤ ‖y‖ := by simpa using PiLp.norm_apply_le y 0
    have h1 : |y 1| ≤ ‖y‖ := by simpa using PiLp.norm_apply_le y 1
    rw [hessianKernel_zero_one, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ‖y‖ ^ 4)]
    calc |y 0| * |y 1| / ‖y‖ ^ 4 * |oddHalfSpaceExtension ω y|
        ≤ ‖y‖ * ‖y‖ / ‖y‖ ^ 4 * (B * ‖y‖) := by
          gcongr
          exact (abs_oddHalfSpaceExtension_le hB0 hB y).trans (by gcongr)
      _ = B * ‖y‖⁻¹ := by field_simp
  have hfar : IntegrableOn (fun y ↦ hessianKernel 0 1 y * oddHalfSpaceExtension ω y)
      (Metric.ball (0 : ℝ^2) 1)ᶜ := by
    refine hWi.integrableOn.bdd_mul (c := 1 / 2)
      (measurable_hessianKernel 0 1).aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with y hy
    rw [mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] at hy
    rw [Real.norm_eq_abs]
    refine (abs_hessianKernel_le 0 1 y).trans ?_
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
    nlinarith
  have := hnear.union hfar
  rwa [union_compl_self, integrableOn_univ] at this

/-- `ω(0) = 0` for a source odd in the tangential coordinate. -/
theorem eq_zero_of_odd (hodd : ∀ y, 0 ≤ y 1 → ω (𝐑 0 y) = -ω y) : ω 0 = 0 := by
  have := hodd 0 le_rfl
  rw [(PDE.Common.coordinateReflection_eq_zero_iff 0 0).mpr rfl] at this
  linarith

section Strain

variable (hω : ContDiff ℝ 2 ω) (hc : HasCompactSupport ω) (hodd : ∀ y, 0 ≤ y 1 → ω (𝐑 0 y) = -ω y)
include hω hc hodd

/-- At the origin, `π ∂₁∂₀φ(0) = 4 ∫_{ℝ²₊₊} K₁(y) ω(y) dy`. -/
theorem pi_mul_partialDeriv_partialDeriv_zero_origin :
    Real.pi * (∂[(1 : Fin 2)] (∂[(0 : Fin 2)] (halfSpaceGreenPotential ω))) 0 =
      4 * ∫ y in quadrant, hessianKernel 0 1 y * ω y := by
  have hω1 : ContDiff ℝ 1 ω := hω.of_le (by norm_num)
  have hzero : ω 0 = 0 := eq_zero_of_odd hodd
  have hcont : ContinuousAt (oddHalfSpaceExtension ω) 0 :=
    continuousAt_oddHalfSpaceExtension_of_eq_zero hω.continuous hzero (by
      change (0 : ℝ^2) PDE.Common.lastIndex = 0; rfl)
  have hpv := hasPrincipalValueAt_partialDeriv_partialDeriv_zero 1 hω1 hc hcont
  rw [ite_eq_right (show ¬((0 : Fin 2) = 1) by decide), add_zero] at hpv
  have hint := integrable_hessianKernel_mul_oddHalfSpaceExtension hω1 hc hodd
  have hint' : Integrable fun y ↦ hessianKernel 0 1 (0 - y) * oddHalfSpaceExtension ω y := by
    simpa only [zero_sub, hessianKernel_neg] using hint
  have hpv' := hasPrincipalValueAt_of_integrable (K := fun x y ↦ hessianKernel 0 1 (x - y))
    hint'
  rw [hpv.unique hpv']
  simp only [zero_sub, hessianKernel_neg]
  rw [integral_eq_four_mul_setIntegral_quadrant hint]
  · congr 1
    refine setIntegral_congr_fun measurableSet_quadrant fun y hy ↦ ?_
    rw [oddHalfSpaceExtension_eqOn ω (show y ∈ HalfSpace.upper 2 from hy.2)]
  · intro y
    rw [hessianKernel_zero_one_coordinateReflection, oddHalfSpaceExtension_reflect_zero hodd]
    ring
  · intro y
    rw [hessianKernel_zero_one_coordinateReflection, oddHalfSpaceExtension_reflect_one]
    ring

omit hodd in
/-- The horizontal velocity is differentiable at the origin within the closed half-plane. -/
theorem hasFDerivWithinAt_halfPlaneVelocity_zero :
    HasFDerivWithinAt (fun y ↦ halfPlaneVelocity ω y 0) (-normalDerivativeFDeriv ω 0)
      (closure (HalfSpace.upper 2)) 0 := by
  rw [halfPlaneVelocity_zero]
  exact (hasFDerivWithinAt_partialDeriv_halfSpaceGreenPotential_normal_closure hω hc 0).neg

/-- **Part I (5.67)**: `u_x(0) = -(4/π) ∫_{ℝ²₊₊} y₀ y₁/|y|⁴ ω(y) dy`, with `u_x(0)` the
tangential component of the derivative of `u` at the origin within the closed half-plane. -/
theorem cOmega_eq :
    (-normalDerivativeFDeriv ω 0) (EuclideanSpace.single 0 1) =
      -(4 / Real.pi) * ∫ y in quadrant, hessianKernel 0 1 y * ω y := by
  have h := pi_mul_partialDeriv_partialDeriv_zero_origin hω hc hodd
  have hval : (normalDerivativeFDeriv ω 0) (EuclideanSpace.single 0 1) =
      (∂[(1 : Fin 2)] (∂[(0 : Fin 2)] (halfSpaceGreenPotential ω))) 0 := by
    simp [normalDerivativeFDeriv]
  rw [neg_apply, hval]
  field_simp
  linarith

end Strain

/-- The strain integral `⟨ω, f_*⟩ = ∫_{ℝ²₊₊} y₀ y₁/|y|⁴ ω(y) dy` converges absolutely. -/
theorem integrableOn_hessianKernel_mul_quadrant (hω : ContDiff ℝ 1 ω) (hc : HasCompactSupport ω)
    (hodd : ∀ y, 0 ≤ y 1 → ω (𝐑 0 y) = -ω y) :
    IntegrableOn (fun y ↦ hessianKernel 0 1 y * ω y) quadrant := by
  have h := (integrable_hessianKernel_mul_oddHalfSpaceExtension hω hc hodd).integrableOn
    (s := quadrant)
  refine h.congr_fun (fun y hy ↦ ?_) measurableSet_quadrant
  change hessianKernel 0 1 y * oddHalfSpaceExtension ω y = _
  rw [oddHalfSpaceExtension_eqOn ω (show y ∈ HalfSpace.upper 2 from hy.2)]

end IncompressibleFlow
