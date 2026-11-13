/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.VorticityStream.DynamicRescaling.Equations
import PDE.Fluid.Boussinesq.VorticityStream.DynamicRescaling.Calculus

/-!
# Dynamic rescaling of the vorticity–streamfunction model

The pointwise change-of-variables results of `DynamicRescaling.Basic`,
`DynamicRescaling.Calculus` and `DynamicRescaling.Equations` combine into the full
rescaled system on a set of times (`dynamicallyRescaledFields_satisfySystemOn`).

For rescaled time `τ`, the fields are

```text
ω̃(x,τ) = Cω(τ) ω(Cl(τ)x, t(τ)),
θ̃(x,τ) = Cθ(τ) θ(Cl(τ)x, t(τ)),
φ̃(x,τ) = Cω(τ) Cl(τ)⁻² φ(Cl(τ)x, t(τ)).
```

The streamfunction scaling gives `ũ = Cω Cl⁻¹ u` and preserves
`-Δφ = ω`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 2.1, (2.4)-(2.8).
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

namespace Boussinesq

open IncompressibleFlow
open PDE.Representations.Similarity

set_option linter.missingDocs true

noncomputable section

/-- A classical physical solution transforms into the complete dynamically
rescaled equation system on every rescaled time where the scale laws hold.

The physical time set is assumed open so that the joint `C¹` hypotheses
provide ordinary, rather than merely relative, derivatives. This is the
forward change-of-variables implication. -/
theorem dynamicallyRescaledFields_satisfySystemOn
    (data : DynamicRescalingData)
    (fields : VorticityStreamFields)
    (physicalTimes rescaledTimes : Set ℝ)
    (hphysicalOpen : IsOpen physicalTimes)
    (hsolution :
      IsClassicalVorticityStreamSolutionOn fields physicalTimes)
    (hlaws : ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
      SatisfiesDynamicRescalingLawsAt data τ)
    (hphysicalTime : ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
      data.physicalTime τ ∈ physicalTimes) :
    SatisfiesDynamicRescaledSystemOn data fields rescaledTimes := by
  have hregularity := hsolution.regularity
  have hvorticity := hsolution.vorticity_equation
  have htemperature := hsolution.temperature_equation
  have hstream := hsolution.streamFunction_equation
  have hboundary := hsolution.zero_streamFunction_boundary
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro τ hτ x hx
    have hτphysical := hphysicalTime hτ
    have hτlaws := hlaws hτ
    have hxphysical :
        dynamicSimilarityPoint data x τ ∈ upperHalfPlane :=
      dynamicSimilarityPoint_mem_upperHalfPlane data
        hτlaws.spatialScale_pos hx
    have hvorticityJoint : DifferentiableAt ℝ
        (Function.uncurry fields.vorticity)
        (dynamicSimilarityPoint data x τ, data.physicalTime τ) := by
      have hwithin := hregularity.vorticity_contDiffOn
        (dynamicSimilarityPoint data x τ, data.physicalTime τ)
        ⟨Set.mem_univ _, hτphysical⟩
      have hat := hwithin.contDiffAt
        ((isOpen_univ.prod hphysicalOpen).mem_nhds
          ⟨Set.mem_univ _, hτphysical⟩)
      exact hat.differentiableAt (by norm_num)
    have htemperatureSpatial : DifferentiableAt ℝ
        (fun y ↦ fields.temperature y (data.physicalTime τ))
        (dynamicSimilarityPoint data x τ) :=
      ((hregularity.temperature_spatial_contDiff hτphysical).differentiable
        (by norm_num)).differentiableAt
    exact vorticityEquation_dynamicallyRescaledFields
      data fields x τ hτlaws.toSatisfiesDynamicScaleODEsAt
      (ne_of_gt hτlaws.spatialScale_pos) hτlaws.sourceScale_eq
      hvorticityJoint
      htemperatureSpatial
      ((hregularity.streamFunction_spatial_contDiff hτphysical).of_le (by norm_num))
      (hvorticity hxphysical hτphysical)
  · intro τ hτ x hx
    have hτphysical := hphysicalTime hτ
    have hτlaws := hlaws hτ
    have hxphysical :
        dynamicSimilarityPoint data x τ ∈ upperHalfPlane :=
      dynamicSimilarityPoint_mem_upperHalfPlane data
        hτlaws.spatialScale_pos hx
    have htemperatureJoint : DifferentiableAt ℝ
        (Function.uncurry fields.temperature)
        (dynamicSimilarityPoint data x τ, data.physicalTime τ) := by
      have hwithin := hregularity.temperature_contDiffOn
        (dynamicSimilarityPoint data x τ, data.physicalTime τ)
        ⟨Set.mem_univ _, hτphysical⟩
      have hat := hwithin.contDiffAt
        ((isOpen_univ.prod hphysicalOpen).mem_nhds
          ⟨Set.mem_univ _, hτphysical⟩)
      exact hat.differentiableAt (by norm_num)
    exact temperatureEquation_dynamicallyRescaledFields
      data fields x τ hτlaws.toSatisfiesDynamicScaleODEsAt
      (ne_of_gt hτlaws.spatialScale_pos) htemperatureJoint
      ((hregularity.streamFunction_spatial_contDiff hτphysical).of_le (by norm_num))
      (htemperature hxphysical hτphysical)
  · intro x τ hx hτ
    have hτphysical := hphysicalTime hτ
    have hτlaws := hlaws hτ
    have hxphysical :
        dynamicSimilarityPoint data x τ ∈ upperHalfPlane :=
      dynamicSimilarityPoint_mem_upperHalfPlane data
        hτlaws.spatialScale_pos hx
    exact streamFunctionEquation_dynamicallyRescaledFields
      data fields x τ (ne_of_gt hτlaws.spatialScale_pos)
      (hstream hxphysical hτphysical)
  · intro x₁ τ hτ
    exact zeroStreamFunctionBoundary_dynamicallyRescaledFields
      data fields x₁ τ
      (hboundary (data.spatialScale τ * x₁) (hphysicalTime hτ))

end

end Boussinesq
