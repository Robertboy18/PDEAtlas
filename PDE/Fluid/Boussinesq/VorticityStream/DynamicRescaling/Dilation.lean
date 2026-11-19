/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.VorticityStream.DynamicRescaling.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# A dynamic rescaling with a prescribed initial spatial scale

For `l₀ > 0`, `D.dilate l₀` is the dynamic rescaling `D` with the spatial scale multiplied by `l₀`
and the temperature scale divided by `l₀`; the clock, the vorticity scale and the rates are those
of `D`. The scale laws are linear in the scales and the source compatibility `C_θ C_l = C_ω²` sees
only the product `C_θ C_l`, so `D.dilate l₀` satisfies the scale laws wherever `D` does
(`SatisfiesDynamicRescalingLawsAt.dilate`). A rescaling built from rates in physical time starts
with the spatial scale `1`; its dilation by `l₀` starts with the spatial scale `l₀`, as the Euler
wall rescaling with a small initial scale `C_l(0)` requires.

## Main definitions

* `Boussinesq.DynamicRescalingData.dilate`.

## Main results

* `Boussinesq.SatisfiesDynamicRescalingLawsAt.dilate`.
-/

@[expose] public section

noncomputable section

namespace Boussinesq

set_option linter.missingDocs true

/-- The dynamic rescaling `D` with the spatial scale multiplied by `l₀` and the temperature scale
divided by `l₀`. -/
def DynamicRescalingData.dilate (D : DynamicRescalingData) (l₀ : ℝ) : DynamicRescalingData where
  vorticityScale := D.vorticityScale
  spatialScale τ := l₀ * D.spatialScale τ
  temperatureScale τ := D.temperatureScale τ / l₀
  physicalTime := D.physicalTime
  vorticityRate := D.vorticityRate
  spatialRate := D.spatialRate
  temperatureRate := D.temperatureRate

namespace DynamicRescalingData

variable (D : DynamicRescalingData) (l₀ : ℝ)

/-- Dilating leaves the vorticity scale unchanged. -/
@[simp]
theorem dilate_vorticityScale : (D.dilate l₀).vorticityScale = D.vorticityScale := rfl

/-- Dilating by `l₀` multiplies the spatial scale by `l₀`. -/
@[simp]
theorem dilate_spatialScale (τ : ℝ) : (D.dilate l₀).spatialScale τ = l₀ * D.spatialScale τ := rfl

/-- Dilating by `l₀` divides the temperature scale by `l₀`. -/
@[simp]
theorem dilate_temperatureScale (τ : ℝ) :
    (D.dilate l₀).temperatureScale τ = D.temperatureScale τ / l₀ := rfl

/-- Dilating leaves the clock unchanged. -/
@[simp]
theorem dilate_physicalTime : (D.dilate l₀).physicalTime = D.physicalTime := rfl

/-- Dilating leaves the vorticity rate unchanged. -/
@[simp]
theorem dilate_vorticityRate : (D.dilate l₀).vorticityRate = D.vorticityRate := rfl

/-- Dilating leaves the spatial rate unchanged. -/
@[simp]
theorem dilate_spatialRate : (D.dilate l₀).spatialRate = D.spatialRate := rfl

/-- Dilating leaves the temperature rate unchanged. -/
@[simp]
theorem dilate_temperatureRate : (D.dilate l₀).temperatureRate = D.temperatureRate := rfl

end DynamicRescalingData

/-- **The scale laws of a dilated rescaling.** If `D` satisfies the scale laws at `τ` and
`l₀ > 0`, so does `D.dilate l₀`. -/
theorem SatisfiesDynamicRescalingLawsAt.dilate {D : DynamicRescalingData} {τ : ℝ}
    (h : SatisfiesDynamicRescalingLawsAt D τ) {l₀ : ℝ} (hl₀ : 0 < l₀) :
    SatisfiesDynamicRescalingLawsAt (D.dilate l₀) τ where
  vorticityScale_hasDerivAt := h.vorticityScale_hasDerivAt
  spatialScale_hasDerivAt := (HasDerivAt.const_mul l₀ h.spatialScale_hasDerivAt).congr_deriv
    (by change l₀ * (-D.spatialRate τ * D.spatialScale τ) =
          -D.spatialRate τ * (l₀ * D.spatialScale τ)
        ring)
  temperatureScale_hasDerivAt :=
    (HasDerivAt.div_const h.temperatureScale_hasDerivAt l₀).congr_deriv
      (by change D.temperatureRate τ * D.temperatureScale τ / l₀ =
            D.temperatureRate τ * (D.temperatureScale τ / l₀)
          ring)
  physicalTime_hasDerivAt := h.physicalTime_hasDerivAt
  spatialScale_pos := mul_pos hl₀ h.spatialScale_pos
  sourceScale_eq := by
    simp only [DynamicRescalingData.dilate_temperatureScale,
      DynamicRescalingData.dilate_spatialScale, DynamicRescalingData.dilate_vorticityScale]
    rw [← h.sourceScale_eq]
    field_simp
  temperatureRate_eq := h.temperatureRate_eq

end Boussinesq
