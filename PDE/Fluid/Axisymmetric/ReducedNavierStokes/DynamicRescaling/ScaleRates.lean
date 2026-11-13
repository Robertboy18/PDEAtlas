/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Axisymmetric.ReducedNavierStokes.DynamicRescaling.Basic
public import PDE.Representations.Similarity.ScaleRates

/-!
# Rate compatibility from the scale laws

The physical amplitudes satisfy `sᵤ = sω sᵣ`, with derivatives
`sᵤ' = -cᵤ sᵤ`, `sω' = -cω sω`, and `sᵣ' = -λ sᵣ`. Differentiating the product and
cancelling its nonzero value gives `cω = cᵤ - λ`.

In the forward-pullback convention of `DynamicRescalingData`, the amplitudes are
`A = 1/sᵤ`, `Aω = 1/sω`, and `L = sᵣ`. Thus compatibility is `Aω = AL`, and the
same rate identity follows from `A' = cᵤ A`, `Aω' = cω Aω`, and `L' = -λ L`.
`satisfiesDynamicRescalingLawsAt_of_scale_compatibility` derives the rate field of
`SatisfiesDynamicRescalingLawsAt` from these differential laws and scale compatibility on a
neighborhood.
-/

@[expose] public section

namespace AxisymmetricFlow

open PDE.Representations.Similarity
open scoped Topology

/-- Differentiating the physical-amplitude identity `sᵤ = sω sᵣ` derives the vorticity rate.
Only nonvanishing of `sᵤ` is needed for cancellation. -/
theorem vorticityRate_eq_sub_of_physicalScale_compatibility
    {swirlScale vorticityScale spatialScale : ℝ → ℝ}
    {swirlRate vorticityRate spatialRate τ : ℝ}
    (hswirl : HasDerivAt swirlScale (-swirlRate * swirlScale τ) τ)
    (hvorticity : HasDerivAt vorticityScale (-vorticityRate * vorticityScale τ) τ)
    (hspatial : HasDerivAt spatialScale (-spatialRate * spatialScale τ) τ)
    (hswirl_ne : swirlScale τ ≠ 0)
    (hcompat : swirlScale =ᶠ[𝓝 τ] fun t ↦ vorticityScale t * spatialScale t) :
    vorticityRate = swirlRate - spatialRate := by
  have hrate := logarithmicRate_eq_add_of_eventuallyEq_mul
    hvorticity hspatial hswirl hswirl_ne hcompat
  have hsum : swirlRate = vorticityRate + spatialRate :=
    neg_inj.mp (by simpa only [neg_add] using hrate)
  exact eq_sub_iff_add_eq.mpr hsum.symm

/-- In the reciprocal-amplitude convention, differentiating `Aω = AL` determines `cω`.
No rate compatibility is assumed in `SatisfiesDynamicScaleODEsAt`. -/
theorem SatisfiesDynamicScaleODEsAt.vorticityRate_eq_of_scale_compatibility
    {data : DynamicRescalingData} {τ : ℝ}
    (hlaws : SatisfiesDynamicScaleODEsAt data τ)
    (hswirl_ne : data.swirlScale τ ≠ 0)
    (hspatial_ne : data.spatialScale τ ≠ 0)
    (hcompat : data.vorticityScale =ᶠ[𝓝 τ]
      fun t ↦ data.swirlScale t * data.spatialScale t) :
    data.vorticityRate τ = data.swirlRate τ - data.spatialRate τ := by
  have hvorticity_ne : data.vorticityScale τ ≠ 0 := by
    rw [hcompat.eq_of_nhds]
    exact mul_ne_zero hswirl_ne hspatial_ne
  simpa only [sub_eq_add_neg] using logarithmicRate_eq_add_of_eventuallyEq_mul
    hlaws.swirlScale_hasDerivAt hlaws.spatialScale_hasDerivAt
    hlaws.vorticityScale_hasDerivAt hvorticity_ne hcompat

/-- Assemble the full rescaling laws from the differential laws, positive scales,
viscosity compatibility, and local amplitude compatibility. The vorticity rate is derived. -/
theorem satisfiesDynamicRescalingLawsAt_of_scale_compatibility
    {data : DynamicRescalingData} {physicalViscosity τ : ℝ}
    (hlaws : SatisfiesDynamicScaleODEsAt data τ)
    (hswirl : 0 < data.swirlScale τ)
    (hspatial : 0 < data.spatialScale τ)
    (hcompat : data.vorticityScale =ᶠ[𝓝 τ]
      fun t ↦ data.swirlScale t * data.spatialScale t)
    (hviscosity : data.rescaledViscosity τ =
      physicalViscosity * data.swirlScale τ / data.spatialScale τ ^ 2) :
    SatisfiesDynamicRescalingLawsAt data physicalViscosity τ where
  toSatisfiesDynamicScaleODEsAt := hlaws
  swirlScale_pos := hswirl
  spatialScale_pos := hspatial
  vorticityScale_eq := hcompat.eq_of_nhds
  rescaledViscosity_eq := hviscosity
  vorticityRate_eq :=
    hlaws.vorticityRate_eq_of_scale_compatibility hswirl.ne' hspatial.ne' hcompat

end AxisymmetricFlow
