/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.VelocityLogLipschitz
public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.OddSingularIntegral
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.GradientBounds
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The velocity gradient for Hölder vorticity on the half-plane

For a continuous compactly supported vorticity `ω` that is `α`-Hölder on the closed upper
half-plane, the Biot–Savart velocity `u = halfPlaneVelocity ω` is differentiable at every point
of the open upper half-plane, with

`∂ᵢuₖ(x) = halfPlaneVelocityGradient ω i k x`:
`∂₀u₀ = -π⁻¹ H₁`, `∂₁u₀ = π⁻¹ H₂ + ω/2`, `∂₀u₁ = π⁻¹ H₂ - ω/2`, `∂₁u₁ = π⁻¹ H₁`,

where `H₁, H₂` are the half-plane singular integrals of `K₁ = k₀₁` and `K₂ = k₀₀`
(`GreenFunction.halfPlaneSingularIntegral`), the principal values of Chen and Hou, Part I,
(3.1)-(3.4) (`hasFDerivAt_halfPlaneVelocity`, `partialDeriv_halfPlaneVelocity`).

## Main definitions

* `halfPlaneVelocityGradient`: the principal value formulas (3.1)-(3.4) for `∂ᵢuₖ` at interior
  points.

## Main results

* `abs_halfPlaneVelocityGradient_sub_le`: for `0 < α < 1` and `x, x'` in the open upper
  half-plane, the formulas satisfy `|∂ᵢuₖ(x) - ∂ᵢuₖ(x')| ≤ 211/(α(1-α)) · M |x - x'|^α`.
* `abs_halfPlaneVelocityGradient_le`: with `|f| ≤ B`, `|∂ᵢuₖ(x)| ≤ 50M/α + 8B + 5‖E‖₁`.
* `abs_halfPlaneVelocityGradient_le_log`: the Kato-type bound
  `|∂ᵢuₖ(x)| ≤ (50/α)(1 + B log(2 + M)) + 8B + 5‖E‖₁`.
* `partialDeriv_halfPlaneVelocity_of_contDiff`: the velocity gradient for compactly supported `C²`
  vorticity at every point of the open upper half-plane.
* `exists_smooth_approximation`: Hölder vorticity is approximated by compactly supported `C²`
  functions with the same Hölder constant.
* `hasFDerivAt_halfPlaneVelocity`: for `α`-Hölder vorticity, `0 < α ≤ 1`, each velocity component
  is differentiable at every point of the open upper half-plane.
* `partialDeriv_halfPlaneVelocity`: there `∂ᵢuₖ(x) = halfPlaneVelocityGradient ω i k x`.

## How it works

Each entry of the formulas is `a H + b ω` with `|a| ≤ π⁻¹` and `|b| ≤ 1/2`
(`halfPlaneVelocityGradient_eq_combination`), so the three estimates follow from the Hölder, size
and Kato-type bounds of the half-plane singular integrals (`abs_halfPlaneSingularIntegral_sub_le`,
`abs_halfPlaneSingularIntegral_le`, `abs_halfPlaneSingularIntegral_le_log`). For compactly supported
`C²` vorticity the formulas are `halfPlaneVelocity_dx_eq` and its companions, once the principal
values over the plane are identified with the half-plane singular integrals
(`hasPrincipalValueAt_halfPlaneSingularIntegral`). For Hölder vorticity we approximate:
`ωₙ = φₙ ⋆ E`, a normed bump of radius `1/(n+1)` convolved with the even extension `E`, is smooth,
compactly supported, Hölder with the constant of `ω`, and satisfies `|ωₙ - E| ≤ M (n+1)^(-α)`
(`exists_smooth_approximation`). Interpolating this bound with the Hölder bounds makes `ωₙ - ω`
Hölder of exponent `α/2` with constant `2√(M (n+1)^(-α) M)`, so linearity
(`halfPlaneVelocityGradient_sub`) and the size bound `abs_halfPlaneVelocityGradient_le` at exponent
`α/2` make the gradients of `u(ωₙ)` converge uniformly on the open half-plane. The velocities
converge uniformly by `abs_halfPlaneVelocity_le`, and the uniform limit theorem for derivatives from
Mathlib (`hasFDerivAt_of_tendstoUniformlyOn`) identifies the limit.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 3, (3.1)-(3.4), p. 27.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology Convolution
open GreenFunction PotentialTheory.Planar SobolevSpace
open PDE.Analysis (evenReflection evenReflection_of_nonneg continuous_evenReflection
  evenReflection_eq_zero hasCompactSupport_evenReflection abs_evenReflection_sub_le)

namespace IncompressibleFlow

variable {ω : ℝ^2 → ℝ}

/-- The velocity gradient of the half-plane Biot–Savart law at interior points: the principal
value formulas (3.1)-(3.4) for `∂ᵢuₖ`. -/
def halfPlaneVelocityGradient (ω : ℝ^2 → ℝ) (i k : Fin 2) (x : ℝ^2) : ℝ :=
  match i, k with
  | 0, 0 => -(1 / Real.pi) * halfPlaneSingularIntegral (hessianKernel 0 1) ω x
  | 1, 0 => 1 / Real.pi * halfPlaneSingularIntegral (hessianKernel 0 0) ω x + ω x / 2
  | 0, 1 => 1 / Real.pi * halfPlaneSingularIntegral (hessianKernel 0 0) ω x - ω x / 2
  | 1, 1 => 1 / Real.pi * halfPlaneSingularIntegral (hessianKernel 0 1) ω x

/-- Every entry of the velocity gradient is `a H + b ω` with `|a| ≤ π⁻¹`, `|b| ≤ 1/2` and `H`
one of the two half-plane singular integrals; the coefficients do not depend on `ω`. -/
theorem halfPlaneVelocityGradient_eq_combination (i k : Fin 2) :
    ∃ j : Fin 2, ∃ a b : ℝ, |a| ≤ 1 / Real.pi ∧ |b| ≤ 1 / 2 ∧
      ∀ (ω : ℝ^2 → ℝ) (x : ℝ^2), halfPlaneVelocityGradient ω i k x =
        a * halfPlaneSingularIntegral (hessianKernel 0 j) ω x + b * ω x := by
  have hpi : 0 < 1 / Real.pi := by positivity
  match i, k with
  | 0, 0 =>
    exact ⟨1, -(1 / Real.pi), 0, by rw [abs_neg, abs_of_pos hpi], by norm_num, fun ω x ↦ by
      simp only [halfPlaneVelocityGradient]; ring⟩
  | 1, 0 =>
    exact ⟨0, 1 / Real.pi, 1 / 2, (abs_of_pos hpi).le, by norm_num, fun ω x ↦ by
      simp only [halfPlaneVelocityGradient]; ring⟩
  | 0, 1 =>
    exact ⟨0, 1 / Real.pi, -(1 / 2), (abs_of_pos hpi).le, by norm_num, fun ω x ↦ by
      simp only [halfPlaneVelocityGradient]; ring⟩
  | 1, 1 =>
    exact ⟨1, 1 / Real.pi, 0, (abs_of_pos hpi).le, by norm_num, fun ω x ↦ by
      simp only [halfPlaneVelocityGradient]; ring⟩

section Estimates

variable {f : ℝ^2 → ℝ} {M α B : ℝ}

/-- A Hölder bound on the closed upper half-plane has a nonnegative constant. -/
private theorem nonneg_of_holder_le
    (hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |f y - f z| ≤ M * ‖y - z‖ ^ α) : 0 ≤ M := by
  have h := hM !₂[1, 0] 0 (by simp) (by simp)
  rw [sub_zero, ← Real.sqrt_sq (norm_nonneg _), norm_sq_vec] at h
  norm_num at h
  exact (abs_nonneg _).trans h

/-- **Hölder estimate of the gradient formulas.** For `f` Hölder on the closed upper half-plane
with integrable even extension, `0 < α < 1`, and `x, x'` in the open upper half-plane,
`|∂ᵢuₖ(x) - ∂ᵢuₖ(x')| ≤ 211/(α(1-α)) · M |x - x'|^α` for the formulas `∂ᵢuₖ`. -/
theorem abs_halfPlaneVelocityGradient_sub_le (hα : 0 < α) (hα1 : α < 1)
    (hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |f y - f z| ≤ M * ‖y - z‖ ^ α)
    (hE : Integrable (evenReflection f)) (i k : Fin 2) {x x' : ℝ^2}
    (hx : x ∈ HalfSpace.upper 2) (hx' : x' ∈ HalfSpace.upper 2) :
    |halfPlaneVelocityGradient f i k x - halfPlaneVelocityGradient f i k x'| ≤
      211 / (α * (1 - α)) * M * ‖x - x'‖ ^ α := by
  obtain ⟨j, a, b, ha, hb, hrep⟩ := halfPlaneVelocityGradient_eq_combination i k
  have hH := abs_halfPlaneSingularIntegral_sub_le (isSingularKernel_hessianKernel 0 j)
    (hasLineCancellation_hessianKernel 0 j) hα hα1 hM hE hx hx'
  have hM0 : 0 ≤ M := nonneg_of_holder_le hM
  have hf' := hM x x' hx.le hx'.le
  have h1α : 0 < 1 - α := by linarith
  have hαα : 0 < α * (1 - α) := mul_pos hα h1α
  have hδ : 0 ≤ ‖x - x'‖ ^ α := by positivity
  rw [hrep f x, hrep f x']
  have hpi := Real.pi_pos
  calc |a * halfPlaneSingularIntegral (hessianKernel 0 j) f x + b * f x -
        (a * halfPlaneSingularIntegral (hessianKernel 0 j) f x' + b * f x')|
      = |a * (halfPlaneSingularIntegral (hessianKernel 0 j) f x -
          halfPlaneSingularIntegral (hessianKernel 0 j) f x') + b * (f x - f x')| := by ring_nf
    _ ≤ |a| * |halfPlaneSingularIntegral (hessianKernel 0 j) f x -
          halfPlaneSingularIntegral (hessianKernel 0 j) f x'| + |b| * |f x - f x'| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ 1 / Real.pi * (42 * Real.pi / (α * (1 - α)) * 5 * M * ‖x - x'‖ ^ α) +
          1 / 2 * (M * ‖x - x'‖ ^ α) := by gcongr
    _ = (210 / (α * (1 - α)) + 1 / 2) * (M * ‖x - x'‖ ^ α) := by
        field_simp
        ring
    _ ≤ 211 / (α * (1 - α)) * (M * ‖x - x'‖ ^ α) := by
        gcongr
        rw [show (211 : ℝ) / (α * (1 - α)) = 210 / (α * (1 - α)) + 1 / (α * (1 - α)) by ring]
        gcongr
        · nlinarith [sq_nonneg (α - 1 / 2)]
    _ = 211 / (α * (1 - α)) * M * ‖x - x'‖ ^ α := by ring

/-- **Size of the gradient formulas.** With `|f| ≤ B` on the closed upper half-plane,
`|∂ᵢuₖ(x)| ≤ 50M/α + 8B + 5‖E‖₁` in the open upper half-plane. -/
theorem abs_halfPlaneVelocityGradient_le (hα : 0 < α) (hα1 : α ≤ 1)
    (hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |f y - f z| ≤ M * ‖y - z‖ ^ α)
    (hE : Integrable (evenReflection f)) (hB : ∀ y, 0 ≤ y 1 → |f y| ≤ B)
    (i k : Fin 2) {x : ℝ^2} (hx : x ∈ HalfSpace.upper 2) :
    |halfPlaneVelocityGradient f i k x| ≤
      50 * M / α + 8 * B + 5 * ∫ y, |evenReflection f y| := by
  obtain ⟨j, a, b, ha, hb, hrep⟩ := halfPlaneVelocityGradient_eq_combination i k
  have hH := abs_halfPlaneSingularIntegral_le (isSingularKernel_hessianKernel 0 j)
    (hasLineCancellation_hessianKernel 0 j) hα hα1 hM hE hB hx
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 le_rfl)
  have hL0 : 0 ≤ ∫ y, |evenReflection f y| := integral_nonneg fun y ↦ abs_nonneg _
  have hfx := hB x hx.le
  rw [hrep f x]
  have hpi := Real.pi_gt_three
  have hpi0 := Real.pi_pos
  calc |a * halfPlaneSingularIntegral (hessianKernel 0 j) f x + b * f x|
      ≤ |a| * |halfPlaneSingularIntegral (hessianKernel 0 j) f x| + |b| * |f x| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ 1 / Real.pi * (5 * (10 * Real.pi * M / α + 4 * B +
          3 * ∫ y, |evenReflection f y|)) + 1 / 2 * B := by gcongr
    _ = 50 * M / α + (20 / Real.pi + 1 / 2) * B +
          15 / Real.pi * ∫ y, |evenReflection f y| := by
        field_simp
        ring
    _ ≤ 50 * M / α + 8 * B + 5 * ∫ y, |evenReflection f y| := by
        gcongr
        · rw [div_add' _ _ _ hpi0.ne', div_le_iff₀ hpi0]; linarith
        · rw [div_le_iff₀ hpi0]; linarith

/-- **Kato-type bound of the gradient formulas.** With `|f| ≤ B` on the closed upper
half-plane, `|∂ᵢuₖ(x)| ≤ (50/α)(1 + B log(2 + M)) + 8B + 5‖E‖₁` in the open upper half-plane. -/
theorem abs_halfPlaneVelocityGradient_le_log (hα : 0 < α) (hα1 : α ≤ 1)
    (hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |f y - f z| ≤ M * ‖y - z‖ ^ α)
    (hE : Integrable (evenReflection f)) (hB : ∀ y, 0 ≤ y 1 → |f y| ≤ B)
    (i k : Fin 2) {x : ℝ^2} (hx : x ∈ HalfSpace.upper 2) :
    |halfPlaneVelocityGradient f i k x| ≤
      50 / α * (1 + B * Real.log (2 + M)) + 8 * B + 5 * ∫ y, |evenReflection f y| := by
  obtain ⟨j, a, b, ha, hb, hrep⟩ := halfPlaneVelocityGradient_eq_combination i k
  have hH := abs_halfPlaneSingularIntegral_le_log (isSingularKernel_hessianKernel 0 j)
    (hasLineCancellation_hessianKernel 0 j) hα hα1 hM hE hB hx
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 le_rfl)
  have hL0 : 0 ≤ ∫ y, |evenReflection f y| := integral_nonneg fun y ↦ abs_nonneg _
  have hfx := hB x hx.le
  rw [hrep f x]
  have hpi := Real.pi_gt_three
  have hpi0 := Real.pi_pos
  calc |a * halfPlaneSingularIntegral (hessianKernel 0 j) f x + b * f x|
      ≤ |a| * |halfPlaneSingularIntegral (hessianKernel 0 j) f x| + |b| * |f x| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ 1 / Real.pi * (10 * Real.pi * 5 / α * (1 + B * Real.log (2 + M)) + 4 * 5 * B +
          3 * 5 * ∫ y, |evenReflection f y|) + 1 / 2 * B := by gcongr
    _ = 50 / α * (1 + B * Real.log (2 + M)) + (20 / Real.pi + 1 / 2) * B +
          15 / Real.pi * ∫ y, |evenReflection f y| := by
        field_simp
        ring
    _ ≤ 50 / α * (1 + B * Real.log (2 + M)) + 8 * B +
          5 * ∫ y, |evenReflection f y| := by
        gcongr
        · rw [div_add' _ _ _ hpi0.ne', div_le_iff₀ hpi0]; linarith
        · rw [div_le_iff₀ hpi0]; linarith

end Estimates

section Linearity

/-- The odd extension is linear. -/
theorem oddHalfSpaceExtension_sub (f g : ℝ^2 → ℝ) :
    oddHalfSpaceExtension (f - g) = oddHalfSpaceExtension f - oddHalfSpaceExtension g := by
  funext y
  by_cases hu : y ∈ HalfSpace.upper 2 <;> by_cases hl : y ∈ HalfSpace.lower 2 <;>
    simp [oddHalfSpaceExtension, hu, hl] <;> ring

/-- The half-plane velocity is linear on continuous compactly supported vorticities. -/
theorem halfPlaneVelocity_sub {f g : ℝ^2 → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (x : ℝ^2) (k : Fin 2) :
    halfPlaneVelocity (f - g) x k = halfPlaneVelocity f x k - halfPlaneVelocity g x k := by
  have hfg := hf.sub hg
  have hfgc := hfc.sub hgc
  match k with
  | 0 =>
    rw [halfPlaneVelocity_zero_eq_integral hfg hfgc, halfPlaneVelocity_zero_eq_integral hf hfc,
      halfPlaneVelocity_zero_eq_integral hg hgc, oddHalfSpaceExtension_sub]
    simp only [Pi.sub_apply, mul_sub]
    rw [integral_sub (integrable_gradientKernel_sub_mul_oddHalfSpaceExtension hf hfc 1 x)
      (integrable_gradientKernel_sub_mul_oddHalfSpaceExtension hg hgc 1 x)]
    ring
  | 1 =>
    rw [halfPlaneVelocity_one_eq_integral hfg hfgc, halfPlaneVelocity_one_eq_integral hf hfc,
      halfPlaneVelocity_one_eq_integral hg hgc, oddHalfSpaceExtension_sub]
    simp only [Pi.sub_apply, mul_sub]
    rw [integral_sub (integrable_gradientKernel_sub_mul_oddHalfSpaceExtension hf hfc 0 x)
      (integrable_gradientKernel_sub_mul_oddHalfSpaceExtension hg hgc 0 x)]

variable {f g : ℝ^2 → ℝ} {Mf Mg α : ℝ}

/-- The gradient formulas are linear on Hölder data with integrable even extensions. -/
theorem halfPlaneVelocityGradient_sub (hα : 0 < α)
    (hMf : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |f y - f z| ≤ Mf * ‖y - z‖ ^ α)
    (hMg : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |g y - g z| ≤ Mg * ‖y - z‖ ^ α)
    (hEf : Integrable (evenReflection f)) (hEg : Integrable (evenReflection g))
    (i k : Fin 2) {x : ℝ^2} (hx : 0 < x 1) :
    halfPlaneVelocityGradient (f - g) i k x =
      halfPlaneVelocityGradient f i k x - halfPlaneVelocityGradient g i k x := by
  obtain ⟨j, a, b, -, -, hrep⟩ := halfPlaneVelocityGradient_eq_combination i k
  rw [hrep, hrep, hrep, halfPlaneSingularIntegral_sub (isSingularKernel_hessianKernel 0 j) hα
    hMf hMg hEf hEg hx]
  simp only [Pi.sub_apply]
  ring

end Linearity

/-- The velocity depends only on the vorticity in the open upper half-plane, so it does not
change when `ω` is replaced by its even extension; data given on the closed half-plane enter the
theorems below through `evenReflection`, which is continuous and compactly supported when
`ω` is continuous on the closed half-plane and vanishes there outside a disc. -/
theorem halfPlaneVelocity_evenReflection (ω : ℝ^2 → ℝ) :
    halfPlaneVelocity (evenReflection ω) = halfPlaneVelocity ω := by
  unfold halfPlaneVelocity
  rw [halfSpaceGreenPotential_congr fun y hy ↦ evenReflection_of_nonneg (le_of_lt hy)]

section Data

variable (hω : Continuous ω) (hc : HasCompactSupport ω)
include hω hc

/-- The even extension of a compactly supported continuous vorticity is integrable. -/
theorem integrable_evenReflection : Integrable (evenReflection ω) :=
  (continuous_evenReflection hω.continuousOn).integrable_of_hasCompactSupport
    (hasCompactSupport_evenReflection hc)

/-- `‖E‖₁ = 2 ‖ω‖_{L¹(ℝ²₊)}`. -/
theorem integral_abs_evenReflection :
    ∫ y, |evenReflection ω y| = 2 * ∫ y in HalfSpace.upper 2, |ω y| := by
  have h := integral_norm_oddHalfSpaceExtension hω hc
  simp only [Real.norm_eq_abs] at h
  rw [← h]
  exact integral_congr_ae (abs_oddHalfSpaceExtension_ae_eq ω).symm

end Data

section Smooth

variable (hω : ContDiff ℝ 2 ω) (hc : HasCompactSupport ω)
include hω hc

/-- The principal value of `k₀ⱼ` against the odd extension at an interior point is the
half-plane singular integral. -/
private theorem principalValue_eq (j : Fin 2) {x : ℝ^2} (hx : x ∈ HalfSpace.upper 2) :
    PDE.Analysis.principalValue univ (fun x y ↦ hessianKernel 0 j (x - y))
      (oddHalfSpaceExtension ω) x = halfPlaneSingularIntegral (hessianKernel 0 j) ω x := by
  obtain ⟨C, hC⟩ := hω.lipschitzWith_of_hasCompactSupport hc (by norm_num)
  have hC' : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → |ω y - ω z| ≤ C * ‖y - z‖ ^ (1 : ℝ) :=
    fun y z _ _ ↦ by
      rw [Real.rpow_one, ← Real.dist_eq, ← dist_eq_norm]
      exact hC.dist_le_mul y z
  exact (hasPrincipalValueAt_halfPlaneSingularIntegral 0 j one_pos hC'
    (integrable_evenReflection hω.continuous hc) hx).principalValue_eq

/-- **The velocity gradient for compactly supported `C²` vorticity**, at every point of the open
upper half-plane. -/
theorem partialDeriv_halfPlaneVelocity_of_contDiff (i k : Fin 2) {x : ℝ^2}
    (hx : x ∈ HalfSpace.upper 2) :
    (∂[i] (fun y ↦ halfPlaneVelocity ω y k)) x = halfPlaneVelocityGradient ω i k x := by
  match i, k with
  | 0, 0 =>
    rw [halfPlaneVelocity_dx_eq hω hc hx, principalValue_eq hω hc 1 hx]
    rfl
  | 1, 0 =>
    rw [halfPlaneVelocity_dy_eq hω hc hx, principalValue_eq hω hc 0 hx]
    rfl
  | 0, 1 =>
    rw [halfPlaneVelocity_vertical_dx_eq hω hc hx, principalValue_eq hω hc 0 hx]
    rfl
  | 1, 1 =>
    have h := (hasPrincipalValueAt_halfPlaneVelocity_one_dy hω hc hx).principalValue_eq
    rw [principalValue_eq hω hc 1 hx] at h
    change _ = 1 / Real.pi * halfPlaneSingularIntegral (hessianKernel 0 1) ω x
    rw [h]
    field_simp

/-- For compactly supported `C²` vorticity the velocity is `C¹` at interior points. -/
theorem contDiffAt_halfPlaneVelocity {x : ℝ^2} (hx : x ∈ HalfSpace.upper 2) :
    ContDiffAt ℝ 1 (halfPlaneVelocity ω) x := by
  have hreg := (halfSpaceGreenPotential_local_poisson hω.continuous hc hx hω.contDiffAt).1
  refine contDiffAt_piLp' 2 fun k ↦ ?_
  match k with
  | 0 =>
    rw [halfPlaneVelocity_zero]
    exact (hreg.partialDeriv 1 (by norm_num)).neg
  | 1 =>
    rw [halfPlaneVelocity_one]
    exact hreg.partialDeriv 0 (by norm_num)

end Smooth

section Approximation

variable {M α : ℝ}

/-- **Smooth approximation of Hölder vorticity.** For `ω` continuous, compactly supported and
`α`-Hölder with constant `M` on the closed upper half-plane there are compactly supported `C²`
functions `ωₙ`, Hölder on the plane with the same constant, with `|ωₙ - E| ≤ M (n+1)^(-α)` for
the even extension `E`, all vanishing outside a common disc. (`ωₙ = φₙ ⋆ E` for normed bumps
`φₙ` of radius `1/(n+1)`.) -/
theorem exists_smooth_approximation (hω : Continuous ω) (hc : HasCompactSupport ω) (hα : 0 < α)
    (hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |ω y - ω z| ≤ M * ‖y - z‖ ^ α) :
    ∃ (ωn : ℕ → ℝ^2 → ℝ) (R : ℝ), (∀ n, ContDiff ℝ 2 (ωn n)) ∧
      (∀ n, HasCompactSupport (ωn n)) ∧ (∀ n y z, |ωn n y - ωn n z| ≤ M * ‖y - z‖ ^ α) ∧
      (∀ n y, |ωn n y - evenReflection ω y| ≤ M * (1 / ((n : ℝ) + 1)) ^ α) ∧
      (∀ n y, R < ‖y‖ → ωn n y = 0) ∧ (∀ y, R < ‖y‖ → ω y = 0) := by
  set E := evenReflection ω with hEdef
  have hEc : Continuous E := continuous_evenReflection hω.continuousOn
  have hEcs : HasCompactSupport E := hasCompactSupport_evenReflection hc
  have hEM : ∀ y z, |E y - E z| ≤ M * ‖y - z‖ ^ α := abs_evenReflection_sub_le hα.le hM
  have hM0 : 0 ≤ M := nonneg_of_holder_le hM
  obtain ⟨R0, hR0⟩ := hc.isCompact.isBounded.subset_closedBall 0
  have hω0 : ∀ y : ℝ^2, R0 < ‖y‖ → ω y = 0 := fun y hy ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ by
      have := hR0 h
      rw [mem_closedBall, dist_zero_right] at this
      linarith
  have hE0 : ∀ y : ℝ^2, R0 < ‖y‖ → E y = 0 := fun _ hy ↦
    evenReflection_eq_zero (fun y _ ↦ hω0 y) hy
  obtain ⟨C, hC⟩ := hEc.bounded_above_of_compact_support hEcs
  let φ : ℕ → ContDiffBump (0 : ℝ^2) := fun n ↦
    ⟨1 / (2 * ((n : ℝ) + 1)), 1 / ((n : ℝ) + 1), by positivity, by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith⟩
  have hrOut : ∀ n, (φ n).rOut = 1 / ((n : ℝ) + 1) := fun n ↦ rfl
  have hrOut1 : ∀ n, (φ n).rOut ≤ 1 := fun n ↦ by
    rw [hrOut, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hint : ∀ n p, Integrable (fun t ↦ (φ n).normed volume t • E (p - t)) := fun n p ↦
    (φ n).integrable_normed.smul_of_top_left (memLp_top_of_bound
      (hEc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable C
      (Eventually.of_forall fun t ↦ hC _))
  refine ⟨fun n ↦ ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] E : ℝ^2 → ℝ),
    R0 + 1, fun n ↦ ?_, fun n ↦ ?_, fun n y z ↦ ?_, fun n y ↦ ?_, fun n y hy ↦ ?_,
    fun y hy ↦ hω0 y (by linarith)⟩
  · exact (φ n).hasCompactSupport_normed.contDiff_convolution_left _ (φ n).contDiff_normed
      hEc.locallyIntegrable
  · exact (φ n).hasCompactSupport_normed.convolution _ hEcs
  · simp only [convolution_lsmul]
    rw [← integral_sub (hint n y) (hint n z)]
    calc |∫ t, ((φ n).normed volume t • E (y - t) - (φ n).normed volume t • E (z - t))|
        ≤ ∫ t, |(φ n).normed volume t • E (y - t) - (φ n).normed volume t • E (z - t)| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ t, (φ n).normed volume t * (M * ‖y - z‖ ^ α) := by
          refine integral_mono ((hint n y).sub (hint n z)).abs
            ((φ n).integrable_normed.mul_const _) fun t ↦ ?_
          simp only [smul_eq_mul]
          rw [← mul_sub, abs_mul, abs_of_nonneg ((φ n).nonneg_normed t)]
          gcongr
          · exact (φ n).nonneg_normed t
          · simpa using hEM (y - t) (z - t)
      _ = M * ‖y - z‖ ^ α := by
          rw [integral_mul_const, (φ n).integral_normed, one_mul]
  · have h := (φ n).dist_normed_convolution_le (μ := volume) (g := E) (x₀ := y)
      (ε := M * (1 / ((n : ℝ) + 1)) ^ α) hEc.aestronglyMeasurable fun x hx ↦ by
        rw [Real.dist_eq]
        refine (hEM x y).trans ?_
        rw [mem_ball, dist_eq_norm, hrOut] at hx
        gcongr
    rwa [Real.dist_eq] at h
  · simp only [convolution_lsmul]
    have hzero : ∀ t, (φ n).normed volume t • E (y - t) = 0 := by
      intro t
      by_cases ht : ‖t‖ < (φ n).rOut
      · rw [hE0 _ (by linarith [norm_sub_norm_le y t, hrOut1 n]), smul_zero]
      · have hsupp := (φ n).support_normed_eq (μ := volume)
        have : t ∉ Function.support ((φ n).normed volume) := by
          rw [hsupp, mem_ball, dist_zero_right]; exact ht
        rw [Function.notMem_support.mp this, zero_smul]
    exact (integral_congr_ae (Eventually.of_forall hzero)).trans (integral_zero _ _)

end Approximation

section Holder

variable {M α : ℝ}

/-- The linear map with the gradient formulas as entries. -/
private theorem gradientMap_apply_single (ω : ℝ^2 → ℝ) (k i : Fin 2) (x : ℝ^2) :
    (∑ j : Fin 2, halfPlaneVelocityGradient ω j k x • (EuclideanSpace.proj j : ℝ^2 →L[ℝ] ℝ))
      (EuclideanSpace.single i 1) = halfPlaneVelocityGradient ω i k x := by
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  fin_cases i <;> simp

/-- **Differentiability of the velocity for Hölder vorticity.** For `ω` continuous, compactly
supported and `α`-Hölder (`0 < α ≤ 1`) on the closed upper half-plane, each velocity component is
differentiable at every point of the open upper half-plane, with partial derivatives the
principal-value formulas `halfPlaneVelocityGradient`. -/
theorem hasFDerivAt_halfPlaneVelocity (hω : Continuous ω) (hc : HasCompactSupport ω)
    (hα : 0 < α) (hα1 : α ≤ 1) (hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |ω y - ω z| ≤ M * ‖y - z‖ ^ α)
    (k : Fin 2) {x : ℝ^2} (hx : x ∈ HalfSpace.upper 2) :
    HasFDerivAt (fun y ↦ halfPlaneVelocity ω y k)
      (∑ i : Fin 2, halfPlaneVelocityGradient ω i k x • (EuclideanSpace.proj i : ℝ^2 →L[ℝ] ℝ))
      x := by
  obtain ⟨ωn, R, hsmooth, hcs, hhol, hclose, hsuppn, hsupp⟩ :=
    exists_smooth_approximation hω hc hα hM
  have hM0 : 0 ≤ M := nonneg_of_holder_le hM
  set η : ℕ → ℝ := fun n ↦ M * (1 / ((n : ℝ) + 1)) ^ α with hηdef
  have hη0 : ∀ n, 0 ≤ η n := fun n ↦ by positivity
  have hηlim : Tendsto η atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat.rpow_const (Or.inr hα.le)).const_mul M
    rwa [Real.zero_rpow hα.ne', mul_zero] at h
  set V := volume.real (closedBall (0 : ℝ^2) R) with hVdef
  have hV0 : 0 ≤ V := measureReal_nonneg
  set h : ℕ → ℝ^2 → ℝ := fun n ↦ ωn n - ω with hhdef
  have hhc : ∀ n, Continuous (h n) := fun n ↦ (hsmooth n).continuous.sub hω
  have hhcs : ∀ n, HasCompactSupport (h n) := fun n ↦ (hcs n).sub hc
  have hEω := integrable_evenReflection hω hc
  have hEn : ∀ n, Integrable (evenReflection (ωn n)) := fun n ↦
    integrable_evenReflection (hsmooth n).continuous (hcs n)
  have hhB : ∀ n y, 0 ≤ y 1 → |h n y| ≤ η n := fun n y hy ↦ by
    have := hclose n y
    rwa [evenReflection_of_nonneg hy] at this
  have hhol' : ∀ n, ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |ωn n y - ωn n z| ≤ M * ‖y - z‖ ^ α :=
    fun n y z _ _ ↦ hhol n y z
  have hhH : ∀ n, ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 →
      |h n y - h n z| ≤ 2 * Real.sqrt (η n * M) * ‖y - z‖ ^ (α / 2) := by
    intro n y z hy hz
    have h1 : |h n y - h n z| ≤ 2 * η n := by
      linarith [abs_sub (h n y) (h n z), hhB n y hy, hhB n z hz]
    have h2 : |h n y - h n z| ≤ 2 * (M * ‖y - z‖ ^ α) := by
      have e : h n y - h n z = (ωn n y - ωn n z) - (ω y - ω z) := by
        simp only [hhdef, Pi.sub_apply]; ring
      rw [e]
      linarith [abs_sub (ωn n y - ωn n z) (ω y - ω z), hhol n y z, hM y z hy hz]
    have hsq : |h n y - h n z| ^ 2 ≤ (2 * η n) * (2 * (M * ‖y - z‖ ^ α)) := by
      rw [sq]; exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    have hrt : ‖y - z‖ ^ α = (‖y - z‖ ^ (α / 2)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]; norm_num
    rw [← Real.sqrt_sq (abs_nonneg _)]
    calc Real.sqrt (|h n y - h n z| ^ 2) ≤
          Real.sqrt ((2 * η n) * (2 * (M * ‖y - z‖ ^ α))) := Real.sqrt_le_sqrt hsq
      _ = 2 * Real.sqrt (η n * M) * ‖y - z‖ ^ (α / 2) := by
          rw [hrt, show 2 * η n * (2 * (M * (‖y - z‖ ^ (α / 2)) ^ 2)) =
            (2 * ‖y - z‖ ^ (α / 2)) ^ 2 * (η n * M) by ring, Real.sqrt_mul (by positivity),
            Real.sqrt_sq (by positivity)]
          ring
  have hhEh : ∀ n, Integrable (evenReflection (h n)) := fun n ↦
    integrable_evenReflection (hhc n) (hhcs n)
  have hL : ∀ n, ∫ y in HalfSpace.upper 2, |h n y| ≤ η n * V := by
    intro n
    have hle : ∀ y ∈ HalfSpace.upper 2, |h n y| ≤ (closedBall (0 : ℝ^2) R).indicator
        (fun _ ↦ η n) y := by
      intro y hy
      by_cases hyR : y ∈ closedBall (0 : ℝ^2) R
      · rw [indicator_of_mem hyR]; exact hhB n y (le_of_lt hy)
      · rw [indicator_of_notMem hyR]
        rw [mem_closedBall, dist_zero_right, not_le] at hyR
        simp [hhdef, hsuppn n y hyR, hsupp y hyR]
    have hind : Integrable ((closedBall (0 : ℝ^2) R).indicator fun _ ↦ η n) :=
      (integrableOn_const (C := η n) measure_closedBall_lt_top.ne).integrable_indicator
        measurableSet_closedBall
    calc ∫ y in HalfSpace.upper 2, |h n y|
        ≤ ∫ y in HalfSpace.upper 2, (closedBall (0 : ℝ^2) R).indicator (fun _ ↦ η n) y :=
          setIntegral_mono_on ((hhc n).integrable_of_hasCompactSupport (hhcs n)).abs.integrableOn
            hind.integrableOn (HalfSpace.measurableSet_upper (n := 2)) hle
      _ ≤ ∫ y, (closedBall (0 : ℝ^2) R).indicator (fun _ ↦ η n) y :=
          setIntegral_le_integral hind (Eventually.of_forall fun y ↦ by
            by_cases hy : y ∈ closedBall (0 : ℝ^2) R <;> simp [hy, hη0 n])
      _ = η n * V := by
          rw [integral_indicator measurableSet_closedBall, setIntegral_const, smul_eq_mul,
            mul_comm]
  -- the gradient formulas converge uniformly on the open half-plane
  set c : ℕ → ℝ := fun n ↦ 50 * (2 * Real.sqrt (η n * M)) / (α / 2) + 8 * η n +
    5 * (2 * (η n * V)) with hcdef
  have hclim : Tendsto c atTop (𝓝 0) := by
    have hs : Tendsto (fun n ↦ Real.sqrt (η n * M)) atTop (𝓝 0) := by
      have := ((hηlim.mul_const M).sqrt)
      rwa [zero_mul, Real.sqrt_zero] at this
    have := ((((hs.const_mul 2).const_mul 50).div_const (α / 2)).add
      (hηlim.const_mul 8)).add (((hηlim.mul_const V).const_mul 2).const_mul 5)
    simpa using this
  have hgrad : ∀ n i, ∀ y ∈ HalfSpace.upper 2,
      |halfPlaneVelocityGradient (ωn n) i k y - halfPlaneVelocityGradient ω i k y| ≤ c n := by
    intro n i y hy
    rw [← halfPlaneVelocityGradient_sub hα (hhol' n) hM (hEn n) hEω i k hy]
    refine (abs_halfPlaneVelocityGradient_le (half_pos hα) (by linarith) (hhH n) (hhEh n)
      (hhB n) i k hy).trans ?_
    rw [integral_abs_evenReflection (hhc n) (hhcs n)]
    have := hL n
    simp only [hcdef]
    gcongr
  -- the velocities converge
  have hvel : ∀ n y, |halfPlaneVelocity (ωn n) y k - halfPlaneVelocity ω y k| ≤
      η n + η n * V / Real.pi := by
    intro n y
    rw [← halfPlaneVelocity_sub (hsmooth n).continuous (hcs n) hω hc]
    refine (abs_halfPlaneVelocity_le (hhc n) (hhcs n) (fun z hz ↦ hhB n z (le_of_lt hz)) k
      y).trans ?_
    gcongr
    exact hL n
  -- the uniform limit theorem for derivatives
  refine hasFDerivAt_of_tendstoUniformlyOn (l := atTop) (HalfSpace.isOpen_upper 2)
    (f := fun n y ↦ halfPlaneVelocity (ωn n) y k)
    (f' := fun n y ↦ fderiv ℝ (fun z ↦ halfPlaneVelocity (ωn n) z k) y)
    (g' := fun y ↦
      ∑ i : Fin 2, halfPlaneVelocityGradient ω i k y • (EuclideanSpace.proj i : ℝ^2 →L[ℝ] ℝ))
    ?_ ?_ ?_ hx
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [(tendsto_order.1 hclim).2 (ε / 2) (by positivity)] with n hn
    intro y hy
    rw [dist_eq_norm]
    refine (ContinuousLinearMap.norm_le_sum_norm_apply_single _).trans_lt ?_
    have he : ∀ i : Fin 2,
        (∑ j : Fin 2, halfPlaneVelocityGradient ω j k y •
            (EuclideanSpace.proj j : ℝ^2 →L[ℝ] ℝ) -
          fderiv ℝ (fun z ↦ halfPlaneVelocity (ωn n) z k) y) (EuclideanSpace.single i 1) =
        halfPlaneVelocityGradient ω i k y - halfPlaneVelocityGradient (ωn n) i k y := by
      intro i
      rw [sub_apply, gradientMap_apply_single,
        ← partialDeriv_halfPlaneVelocity_of_contDiff (hsmooth n) (hcs n) i k hy]
      rfl
    rw [Fin.sum_univ_two, he 0, he 1, Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm,
      abs_sub_comm (halfPlaneVelocityGradient ω 1 k y)]
    linarith [hgrad n 0 y hy, hgrad n 1 y hy]
  · intro n y hy
    have hd := ((contDiffAt_halfPlaneVelocity (hsmooth n) (hcs n) hy).differentiableAt
      (by norm_num))
    exact ((EuclideanSpace.proj k : ℝ^2 →L[ℝ] ℝ).differentiableAt.comp y hd).hasFDerivAt
  · intro y _
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ (Real.norm_eq_abs _).trans_le (hvel n y))
      (by simpa using hηlim.add ((hηlim.mul_const V).div_const Real.pi))

/-- **The velocity gradient for Hölder vorticity.** Under the hypotheses of
`hasFDerivAt_halfPlaneVelocity`, `∂ᵢuₖ(x) = halfPlaneVelocityGradient ω i k x` at every point of
the open upper half-plane. -/
theorem partialDeriv_halfPlaneVelocity (hω : Continuous ω) (hc : HasCompactSupport ω)
    (hα : 0 < α) (hα1 : α ≤ 1) (hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |ω y - ω z| ≤ M * ‖y - z‖ ^ α)
    (i k : Fin 2) {x : ℝ^2} (hx : x ∈ HalfSpace.upper 2) :
    (∂[i] (fun y ↦ halfPlaneVelocity ω y k)) x = halfPlaneVelocityGradient ω i k x := by
  change fderiv ℝ (fun y ↦ halfPlaneVelocity ω y k) x (EuclideanSpace.single i 1) = _
  rw [(hasFDerivAt_halfPlaneVelocity hω hc hα hα1 hM k hx).fderiv, gradientMap_apply_single]

/-- For Hölder vorticity the velocity is differentiable at every point of the open upper
half-plane. -/
theorem differentiableAt_halfPlaneVelocity (hω : Continuous ω) (hc : HasCompactSupport ω)
    (hα : 0 < α) (hα1 : α ≤ 1) (hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |ω y - ω z| ≤ M * ‖y - z‖ ^ α)
    {x : ℝ^2} (hx : x ∈ HalfSpace.upper 2) :
    DifferentiableAt ℝ (halfPlaneVelocity ω) x :=
  (differentiableAt_piLp 2).2 fun k ↦
    (hasFDerivAt_halfPlaneVelocity hω hc hα hα1 hM k hx).differentiableAt

end Holder

end IncompressibleFlow
