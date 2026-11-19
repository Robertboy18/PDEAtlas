/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convolution.AlmostEverywhereContinuous
public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.GreenPotential
import PDE.Elliptic.PotentialTheory.FundamentalSolution.LocalIntegrability

/-!
# Continuity of planar half-space Green potentials at the boundary

Continuous compact sources have continuous Green potentials on the entire plane,
including when the source is nonzero on the horizontal boundary. Their canonical
odd extensions may jump there, but are bounded and continuous almost everywhere.
Convolution with the locally integrable logarithmic kernel removes these jumps
at the level of the potential. The prescribed zero boundary values therefore
are also limits from the upper half-plane.

## Main results

* `halfSpaceGreenPotential_eq_convolution_oddHalfSpaceExtension`: the Green potential is the
  logarithmic convolution with the canonical odd extension of the source.
* `continuous_convolution_oddHalfSpaceExtension`: a locally integrable kernel has a continuous
  convolution with the odd extension of a continuous compact source, despite its jumps.
* `continuous_halfSpaceGreenPotential`: a continuous compact source has a continuous Green
  potential on the whole plane.
* `tendsto_halfSpaceGreenPotential_boundary`: the Green potential tends to zero at every
  horizontal boundary point, with no boundary condition on the source.
-/

@[expose] public section

noncomputable section

namespace GreenFunction

open MeasureTheory Filter Topology Set SobolevSpace
open scoped Convolution

/-- The boundary reflection of the half-plane is the reflection of the coordinate `1`. -/
theorem reflect_two_eq_coordinateReflection :
    HalfSpace.reflect 2 = PDE.Common.coordinateReflection (1 : Fin 2) := by
  funext y
  ext i
  fin_cases i <;>
    simp [HalfSpace.reflect, PDE.Common.lastIndex, PDE.Common.coordinateReflection_apply_of_ne]

/-- Away from the horizontal boundary, the canonical odd extension of a continuous
source is continuous. -/
theorem continuousAt_oddHalfSpaceExtension
    {f : ℝ^2 → ℝ} (hf : Continuous f) {y : ℝ^2}
    (hy : y ∉ HalfSpace.boundary 2) : ContinuousAt (oddHalfSpaceExtension f) y := by
  have hycoord : y 1 ≠ 0 := hy
  rcases lt_or_gt_of_ne hycoord with hyl | hyu
  · have hmem : y ∈ HalfSpace.lower 2 := hyl
    have heq : oddHalfSpaceExtension f =ᶠ[𝓝 y] fun z ↦ -f (HalfSpace.reflect 2 z) := by
      filter_upwards [(HalfSpace.isOpen_lower 2).mem_nhds hmem] with z hz
      have hupper : HalfSpace.reflect 2 z ∈ HalfSpace.upper 2 :=
        (HalfSpace.mem_upper_reflect_iff (n := 2) z).2 hz
      calc
        oddHalfSpaceExtension f z = -oddHalfSpaceExtension f (HalfSpace.reflect 2 z) := by
          rw [oddHalfSpaceExtension_reflect, neg_neg]
        _ = -f (HalfSpace.reflect 2 z) := by rw [oddHalfSpaceExtension_eqOn f hupper]
    have href : ContinuousAt (fun z ↦ -f (HalfSpace.reflect 2 z)) y :=
      (hf.comp (HalfSpace.reflectLinearIsometryEquiv 2).continuous).neg.continuousAt
    exact href.congr_of_eventuallyEq heq
  · have hmem : y ∈ HalfSpace.upper 2 := hyu
    have heq : oddHalfSpaceExtension f =ᶠ[𝓝 y] f := by
      filter_upwards [(HalfSpace.isOpen_upper 2).mem_nhds hmem] with z hz
      exact oddHalfSpaceExtension_eqOn f hz
    exact hf.continuousAt.congr_of_eventuallyEq heq

/-- The Green potential is the logarithmic convolution with the canonical odd extension.
The boundary source need not vanish. -/
theorem halfSpaceGreenPotential_eq_convolution_oddHalfSpaceExtension
    {f : ℝ^2 → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    halfSpaceGreenPotential f =
      PotentialTheory.fundamentalSolution 2 ⋆[ContinuousLinearMap.mul ℝ ℝ]
        oddHalfSpaceExtension f := by
  funext x
  calc
    halfSpaceGreenPotential f x = halfSpaceGreenPotential (oddHalfSpaceExtension f) x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (HalfSpace.measurableSet_upper (n := 2))] with y hy
      rw [oddHalfSpaceExtension_eqOn f hy]
    _ = _ := halfSpaceGreenPotential_eq_convolution_of_odd_of_integrable
      (oddHalfSpaceExtension f) (oddHalfSpaceExtension_reflect f) x
      (integrable_fundamentalSolution_mul_oddHalfSpaceExtension hf hc x)

/-- A locally integrable scalar kernel has a continuous convolution with the canonical
odd extension of a continuous compact source. Jumps of the extension are allowed. -/
theorem continuous_convolution_oddHalfSpaceExtension
    {K f : ℝ^2 → ℝ} (hK : LocallyIntegrable K volume)
    (hf : Continuous f) (hc : HasCompactSupport f) :
    Continuous (K ⋆[ContinuousLinearMap.mul ℝ ℝ] oddHalfSpaceExtension f) := by
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hc
  have hbound : ∀ y, ‖oddHalfSpaceExtension f y‖ ≤ M + M := by
    intro y
    calc
      ‖oddHalfSpaceExtension f y‖ ≤ ‖(HalfSpace.upper 2).indicator f y‖ +
          ‖(HalfSpace.lower 2).indicator (fun z ↦ f (HalfSpace.reflect 2 z)) y‖ :=
        norm_sub_le _ _
      _ ≤ M + M := add_le_add
        ((norm_indicator_le_norm_self f y).trans (hM y))
        ((norm_indicator_le_norm_self (fun z ↦ f (HalfSpace.reflect 2 z)) y).trans (hM _))
  apply PDE.Analysis.continuous_convolution_of_ae_continuousAt
    hK (locallyIntegrable_oddHalfSpaceExtension hf).aestronglyMeasurable
    (hasCompactSupport_oddHalfSpaceExtension hc) hbound
  filter_upwards [compl_mem_ae_iff.mpr (HalfSpace.volume_boundary (n := 2))] with y hy
  exact continuousAt_oddHalfSpaceExtension hf hy

/-- A continuous compact source has a continuous planar Green potential, including
at boundary points with nonzero source value. -/
theorem continuous_halfSpaceGreenPotential
    {f : ℝ^2 → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Continuous (halfSpaceGreenPotential f) := by
  rw [halfSpaceGreenPotential_eq_convolution_oddHalfSpaceExtension hf hc]
  exact continuous_convolution_oddHalfSpaceExtension
    (PotentialTheory.locallyIntegrable_fundamentalSolution 2) hf hc

/-- The Green potential tends to zero on approaching any horizontal boundary point.
No zero boundary condition on the source is required. -/
theorem tendsto_halfSpaceGreenPotential_boundary
    {f : ℝ^2 → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    {x : ℝ^2} (hx : x ∈ HalfSpace.boundary 2) :
    Tendsto (halfSpaceGreenPotential f) (𝓝 x) (𝓝 0) := by
  simpa only [halfSpaceGreenPotential_boundary f hx] using
    (continuous_halfSpaceGreenPotential hf hc).tendsto x

end GreenFunction
