/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.BoundaryRegularity
public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarGradient
import PDE.Analysis.Convolution.WeakDerivative
import PDE.Spaces.Sobolev.Calculus.Differentiation.WeakToClassical
import PDE.FDeriv.Reflection.Coordinate

/-!
# First derivatives of planar half-space Green potentials

A continuous compact source has a globally `C¹` Green potential, including when
the source is nonzero on the horizontal boundary. Its first derivatives are
convolutions of the locally integrable inverse-radius kernel with the canonical
odd source extension. Continuous weak derivatives give classical derivatives;
no derivative of the discontinuous source extension is taken.

## Main definitions

* `halfSpaceGreenPotentialGradient`: the gradient-kernel convolution with the odd source
  extension, the candidate first derivative.

## Main results

* `continuous_halfSpaceGreenPotentialGradient`: the gradient-kernel potential is continuous across
  the horizontal boundary.
* `hasFDerivAt_halfSpaceGreenPotential`: the Green potential has this classical derivative at
  every point of the plane.
* `contDiff_one_halfSpaceGreenPotential`: continuous compact sources give globally `C¹` Green
  potentials, without vanishing at the boundary.
* `partialDeriv_halfSpaceGreenPotential_boundary`: the tangential derivative vanishes on the
  horizontal boundary.
* `tendsto_fderiv_halfSpaceGreenPotential_within_upper`: from the upper half-plane the first
  derivative tends to its kernel formula, also at boundary points.
-/

@[expose] public section

noncomputable section

namespace GreenFunction

open MeasureTheory Filter Topology Set SobolevSpace
open scoped Convolution

/-- The continuous vector field representing the Green potential's first derivative.
Each coordinate is the absolutely convergent planar gradient-kernel convolution. -/
def halfSpaceGreenPotentialGradient (f : ℝ^2 → ℝ) (x : ℝ^2) : ℝ^2 :=
  WithLp.toLp 2 fun i ↦
    (PotentialTheory.Planar.gradientKernel i ⋆[ContinuousLinearMap.mul ℝ ℝ]
      oddHalfSpaceExtension f) x

/-- The planar gradient-kernel potential is continuous across the horizontal boundary,
even when the odd source extension has a jump there. -/
theorem continuous_halfSpaceGreenPotentialGradient
    {f : ℝ^2 → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Continuous (halfSpaceGreenPotentialGradient f) := by
  have hg (i : Fin 2) : Continuous
      (PotentialTheory.Planar.gradientKernel i ⋆[ContinuousLinearMap.mul ℝ ℝ]
        oddHalfSpaceExtension f) :=
    continuous_convolution_oddHalfSpaceExtension
      (PotentialTheory.Planar.locallyIntegrable_gradientKernel i) hf hc
  unfold halfSpaceGreenPotentialGradient
  fun_prop

/-- The Green potential has the classical derivative represented by its continuous
inverse-radius kernel potential at every point of the plane. -/
theorem hasFDerivAt_halfSpaceGreenPotential
    {f : ℝ^2 → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) (x : ℝ^2) :
    HasFDerivAt (halfSpaceGreenPotential f)
      (innerSL ℝ (halfSpaceGreenPotentialGradient f x)) x := by
  have hFc := hasCompactSupport_oddHalfSpaceExtension hc
  have hFi : Integrable (oddHalfSpaceExtension f) volume :=
    (integrableOn_iff_integrable_of_support_subset
      (subset_tsupport (oddHalfSpaceExtension f))).mp
        ((locallyIntegrable_oddHalfSpaceExtension hf).integrableOn_isCompact hFc)
  have hP : Continuous (PotentialTheory.fundamentalSolution 2 ⋆[ContinuousLinearMap.mul ℝ ℝ]
      oddHalfSpaceExtension f) :=
    continuous_convolution_oddHalfSpaceExtension
      (PotentialTheory.locallyIntegrable_fundamentalSolution 2) hf hc
  have hg (i : Fin 2) : Continuous
      (PotentialTheory.Planar.gradientKernel i ⋆[ContinuousLinearMap.mul ℝ ℝ]
        oddHalfSpaceExtension f) :=
    continuous_convolution_oddHalfSpaceExtension
      (PotentialTheory.Planar.locallyIntegrable_gradientKernel i) hf hc
  have hweak (i : Fin 2) := PDE.Analysis.hasWeakDerivativeOn_convolution i
    (PotentialTheory.Planar.hasWeakDerivativeOn_fundamentalSolution_two i) hFi hFc hP (hg i)
  rw [halfSpaceGreenPotential_eq_convolution_oddHalfSpaceExtension hf hc]
  exact Approximation.hasFDerivAt_of_continuous_weakPartialDerivatives hP hg hweak x

/-- Continuous compact planar sources give globally `C¹` Green potentials.
This conclusion does not require the source to vanish at the boundary. -/
theorem contDiff_one_halfSpaceGreenPotential
    {f : ℝ^2 → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    ContDiff ℝ 1 (halfSpaceGreenPotential f) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  exact ⟨fun x ↦ innerSL ℝ (halfSpaceGreenPotentialGradient f x),
    (innerSL ℝ).continuous.comp (continuous_halfSpaceGreenPotentialGradient hf hc),
    hasFDerivAt_halfSpaceGreenPotential hf hc⟩

/-- The tangential Cartesian derivative vanishes on the horizontal boundary.
The potential is differentiable there even if the source has nonzero boundary values. -/
theorem partialDeriv_halfSpaceGreenPotential_boundary
    {f : ℝ^2 → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    {x : ℝ^2} (hx : x ∈ HalfSpace.boundary 2) :
    (∂[(0 : Fin 2)] (halfSpaceGreenPotential f)) x = 0 := by
  have hzero : PDE.Common.VanishesOnCoordinateHyperplane (1 : Fin 2)
      (halfSpaceGreenPotential f) := by
    intro y hy
    exact halfSpaceGreenPotential_boundary f hy
  exact hzero.partialDeriv_eq_zero_of_ne (by decide) hx
    (hasFDerivAt_halfSpaceGreenPotential hf hc x).differentiableAt

/-- Approaching a point from the upper half-plane, the classical first derivative
tends to its kernel formula. This includes every horizontal boundary point. -/
theorem tendsto_fderiv_halfSpaceGreenPotential_within_upper
    {f : ℝ^2 → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    (x : ℝ^2) :
    Tendsto (fderiv ℝ (halfSpaceGreenPotential f)) (𝓝[HalfSpace.upper 2] x)
      (𝓝 (innerSL ℝ (halfSpaceGreenPotentialGradient f x))) := by
  have hlim := ((contDiff_one_halfSpaceGreenPotential hf hc).continuous_fderiv
    one_ne_zero).tendsto x
  rw [(hasFDerivAt_halfSpaceGreenPotential hf hc x).fderiv] at hlim
  exact hlim.mono_left nhdsWithin_le_nhds

/-- A function vanishing outside the closed disc of radius `R` has compact support. -/
theorem hasCompactSupport_of_eq_zero_of_lt_norm {f : ℝ^2 → ℝ} {R : ℝ}
    (hR : ∀ y, R < ‖y‖ → f y = 0) : HasCompactSupport f :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℝ^2) R) fun y hy ↦
    hR y (by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hy)

end GreenFunction
