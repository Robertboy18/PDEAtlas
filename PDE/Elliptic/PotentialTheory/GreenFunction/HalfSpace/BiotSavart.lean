/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.ClosureRegularity
public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarHessianRepresentation
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.GradientBounds

/-!
# Second derivatives of planar Green potentials as principal values

Let `φ` be the half-space Green potential of a compactly supported `C¹` source `f` and `W` the
odd extension of `f` across the boundary, which may jump there. The tangential derivative
`∂₀φ` is the Green potential of `∂₀ f`, and `W` is differentiable along the boundary direction
`e₀` at every point (on the boundary line it vanishes identically), with derivative the odd
extension of `∂₀ f`. The principal-value representation of
`PotentialTheory.Planar.hasPrincipalValueAt_hessianKernel_of_hasLineDerivAt` therefore applies
with `i = 0` and gives, at every point where `W` is continuous,

`∂₀∂₀φ(x) = π⁻¹ P.V.∫ K₂(x - y) W(y) dy - W(x)/2`,
`∂₁∂₀φ(x) = π⁻¹ P.V.∫ K₁(x - y) W(y) dy`,

with `K₁ = hessianKernel 0 1`, `K₂ = hessianKernel 0 0`. These are the formulas of Chen and
Hou I, Section 3, for `v_x = ∂₀∂₀φ` and `v_y = -u_x = ∂₁∂₀φ`: the integral for `u_x` that follows
(3.3), and `v_x` in (3.4), with the same local term `-ω(x)/2` (there over a box). The points of
continuity of `W` are the off-boundary points and the boundary points where `f` vanishes.

## Main results

* `hasLineDerivAt_oddHalfSpaceExtension_tangential`: the odd extension is differentiable along
  `e₀` at every point, with derivative the odd extension of `∂₀ f`.
* `partialDeriv_halfSpaceGreenPotential_eq_integral`: `∂ⱼφ(x) = ∫ gⱼ(x - y) W(y) dy`, an
  absolutely convergent integral against the odd extension.
* `hasPrincipalValueAt_partialDeriv_partialDeriv_zero`: the two displayed principal-value
  formulas, at every point where `W` is continuous.
* `continuousAt_oddHalfSpaceExtension_of_eq_zero`: the odd extension of a continuous source is
  continuous at boundary points where the source vanishes.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 3, (3.3)-(3.4).
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

namespace GreenFunction

open MeasureTheory Filter Topology Set SobolevSpace PotentialTheory.Planar
open scoped Convolution

/-- The canonical odd extension is differentiable along the boundary direction `e₀` at every
point of the plane, with derivative the odd extension of `∂₀ f`. On the boundary line both
vanish. -/
theorem hasLineDerivAt_oddHalfSpaceExtension_tangential {f : ℝ^2 → ℝ} (hf : ContDiff ℝ 1 f)
    (y : ℝ^2) :
    HasLineDerivAt ℝ (oddHalfSpaceExtension f) (oddHalfSpaceExtension (∂[(0 : Fin 2)] f) y) y
      (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) := by
  have hfd (z : ℝ^2) : HasFDerivAt f (fderiv ℝ f z) z :=
    (hf.differentiable one_ne_zero z).hasFDerivAt
  have hzero (g : ℝ^2 → ℝ) {z : ℝ^2} (hz : z 1 = 0) : oddHalfSpaceExtension g z = 0 := by
    have hu : z ∉ HalfSpace.upper 2 := fun h ↦ (show (0 : ℝ) < z 1 from h).ne' hz
    have hl : z ∉ HalfSpace.lower 2 := fun h ↦ (show z 1 < 0 from h).ne hz
    simp [oddHalfSpaceExtension, hu, hl]
  rcases lt_trichotomy (y 1) 0 with hy | hy | hy
  · -- lower half-plane: the extension is `-f ∘ reflect` near `y`
    have hmem : y ∈ HalfSpace.lower 2 := hy
    have heq : oddHalfSpaceExtension f =ᶠ[𝓝 y] fun z ↦ -f (HalfSpace.reflect 2 z) := by
      filter_upwards [(HalfSpace.isOpen_lower 2).mem_nhds hmem] with z hz
      rw [← neg_neg (oddHalfSpaceExtension f z), ← oddHalfSpaceExtension_reflect,
        oddHalfSpaceExtension_eqOn f ((HalfSpace.mem_upper_reflect_iff (n := 2) z).2 hz)]
    have hRe : HalfSpace.reflect 2 (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) =
        EuclideanSpace.single 0 1 := by
      ext k
      fin_cases k <;> simp [HalfSpace.reflect, PDE.Common.lastIndex]
    have h := ((hfd (HalfSpace.reflect 2 y)).comp y ((HalfSpace.reflectLinearIsometryEquiv 2
      ).toContinuousLinearEquiv : ℝ^2 →L[ℝ] ℝ^2).hasFDerivAt).neg.hasLineDerivAt
        (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
    rw [← neg_neg (oddHalfSpaceExtension _ y), ← oddHalfSpaceExtension_reflect,
      oddHalfSpaceExtension_eqOn _ ((HalfSpace.mem_upper_reflect_iff (n := 2) y).2 hmem)]
    convert h.congr_of_eventuallyEq heq using 2
    change -(fderiv ℝ f _ (EuclideanSpace.single 0 1)) = -(fderiv ℝ f _ (HalfSpace.reflect 2 _))
    rw [hRe]
  · -- boundary line: the extension vanishes along it
    rw [hzero _ hy]
    have hline : (fun t : ℝ ↦ oddHalfSpaceExtension f (y + t • EuclideanSpace.single 0 1)) =
        fun _ ↦ 0 := funext fun t ↦ hzero f (by simp [hy])
    unfold HasLineDerivAt
    rw [hline]
    exact hasDerivAt_const 0 0
  · -- upper half-plane: the extension is `f` near `y`
    have hmem : y ∈ HalfSpace.upper 2 := hy
    rw [oddHalfSpaceExtension_eqOn _ hmem]
    exact ((hfd y).hasLineDerivAt _).congr_of_eventuallyEq
      (eventually_of_mem ((HalfSpace.isOpen_upper 2).mem_nhds hmem) (oddHalfSpaceExtension_eqOn f))

/-- The first derivatives of the Green potential as absolutely convergent integrals against the
odd extension: `∂ⱼφ(x) = ∫ gⱼ(x - y) W(y) dy`. -/
theorem partialDeriv_halfSpaceGreenPotential_eq_integral {f : ℝ^2 → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) (j : Fin 2) (x : ℝ^2) :
    (∂[j] (halfSpaceGreenPotential f)) x =
      ∫ y, gradientKernel j (x - y) * oddHalfSpaceExtension f y := by
  unfold PDE.partialDeriv
  rw [(hasFDerivAt_halfSpaceGreenPotential hf hc x).fderiv]
  simp only [innerSL_apply_apply, EuclideanSpace.inner_single_right, starRingEnd_apply,
    star_trivial, one_mul, halfSpaceGreenPotentialGradient]
  change (gradientKernel j ⋆[ContinuousLinearMap.mul ℝ ℝ] oddHalfSpaceExtension f) x = _
  rw [convolution_def]
  simp only [ContinuousLinearMap.mul_apply']
  rw [← integral_sub_left_eq_self (fun t ↦ gradientKernel j t * oddHalfSpaceExtension f (x - t))
    volume x]
  simp only [sub_sub_cancel]

/-- The integrand `gⱼ(x - ·) W` of a first derivative is integrable. -/
theorem integrable_gradientKernel_sub_mul_oddHalfSpaceExtension {f : ℝ^2 → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) (j : Fin 2) (x : ℝ^2) :
    Integrable fun y ↦ gradientKernel j (x - y) * oddHalfSpaceExtension f y := by
  have hvec := integrable_oddHalfSpaceExtension_smul_gradientKernelVector hf hc x
  have hj := (EuclideanSpace.proj j : ℝ^2 →L[ℝ] ℝ).integrable_comp hvec
  have hj' := hj.comp_sub_left x
  refine hj'.congr (Eventually.of_forall fun y ↦ ?_)
  simp only [map_smul, smul_eq_mul, sub_sub_cancel]
  rw [PiLp.proj_apply, gradientKernelVector_apply, mul_comm]

/-- **The tangential second derivatives of the Green potential as principal values.** For a
compactly supported `C¹` source, at every point where the odd extension `W` is continuous,

`P.V.∫ k₀ⱼ(x - y) W(y) dy = π (∂ⱼ∂₀φ(x) + δ₀ⱼ W(x)/2)`,

that is `∂₀∂₀φ = π⁻¹ P.V. K₂ * W - W/2` and `∂₁∂₀φ = π⁻¹ P.V. K₁ * W`. -/
theorem hasPrincipalValueAt_partialDeriv_partialDeriv_zero (j : Fin 2) {f : ℝ^2 → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) {x : ℝ^2}
    (hx : ContinuousAt (oddHalfSpaceExtension f) x) :
    PDE.Analysis.HasPrincipalValueAt univ (fun x y ↦ hessianKernel 0 j (x - y))
      (oddHalfSpaceExtension f) x
      (Real.pi * ((∂[j] (∂[(0 : Fin 2)] (halfSpaceGreenPotential f))) x +
        if (0 : Fin 2) = j then oddHalfSpaceExtension f x / 2 else 0)) := by
  have hd : Continuous (∂[(0 : Fin 2)] f) := by
    change Continuous (fun x ↦ fderiv ℝ f x (EuclideanSpace.single 0 (1 : ℝ)))
    exact (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdc : HasCompactSupport (∂[(0 : Fin 2)] f) :=
    hc.fderiv_apply ℝ (EuclideanSpace.single 0 (1 : ℝ))
  have h := hasPrincipalValueAt_hessianKernel_of_hasLineDerivAt 0 j
    (W := oddHalfSpaceExtension f) (W' := oddHalfSpaceExtension (∂[(0 : Fin 2)] f))
    (integrable_oddHalfSpaceExtension hf.continuous hc)
    (integrable_gradientKernel_sub_mul_oddHalfSpaceExtension hd hdc j x)
    (hasLineDerivAt_oddHalfSpaceExtension_tangential hf) hx
  rwa [partialDeriv_halfSpaceGreenPotential_eq hf hc,
    partialDeriv_halfSpaceGreenPotential_eq_integral hd hdc]

/-- The odd extension of a continuous source is continuous at boundary points where the source
vanishes. -/
theorem continuousAt_oddHalfSpaceExtension_of_eq_zero {f : ℝ^2 → ℝ} (hf : Continuous f)
    {y : ℝ^2} (hy : f y = 0) (hyb : y ∈ HalfSpace.boundary 2) :
    ContinuousAt (oddHalfSpaceExtension f) y := by
  have hb : y 1 = 0 := hyb
  have hyr : HalfSpace.reflect 2 y = y := by
    ext k
    fin_cases k <;> simp [HalfSpace.reflect, PDE.Common.lastIndex, hb]
  have hval : oddHalfSpaceExtension f y = 0 := by
    have hu : y ∉ HalfSpace.upper 2 := fun h ↦ (show (0 : ℝ) < y 1 from h).ne' hb
    have hl : y ∉ HalfSpace.lower 2 := fun h ↦ (show y 1 < 0 from h).ne hb
    simp [oddHalfSpaceExtension, hu, hl]
  rw [ContinuousAt, hval]
  have h1 : Tendsto ((HalfSpace.upper 2).indicator f) (𝓝 y) (𝓝 0) :=
    squeeze_zero_norm (fun z ↦ norm_indicator_le_norm_self f z)
      (by simpa [hy] using (hf.tendsto y).norm)
  have h2 : Tendsto ((HalfSpace.lower 2).indicator fun z ↦ f (HalfSpace.reflect 2 z)) (𝓝 y)
      (𝓝 0) := squeeze_zero_norm (fun z ↦ norm_indicator_le_norm_self _ z) (by simpa [hyr, hy]
        using ((hf.comp (HalfSpace.reflectLinearIsometryEquiv 2).continuous).tendsto y).norm)
  have h := h1.sub h2
  rwa [sub_zero] at h

end GreenFunction
