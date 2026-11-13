/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.DynamicRescaling

/-!
# Constructing the scales from the normalization rates

Once the rescaled trajectory determines `cl` and `cw`, we recover the scales by
integrating these rates. Both scales start at one; physical time starts at zero
and advances at the vorticity scale. The fundamental theorem of calculus proves
the three scale laws, so these laws need not be supplied as separate assumptions.

For the normalization `cw = cl`, the length scale is the reciprocal of the
vorticity scale. A decaying vorticity scale therefore means expanding spatial
coordinates.
-/

@[expose] public noncomputable section

namespace DeGregorio.DynamicRescalingData

/-- Unit initial scales and zero initial physical time, recovered by integrating
the two normalization rates. Continuity is only needed to prove the scale laws. -/
def ofRates (cl cw : ℝ → ℝ) : DynamicRescalingData where
  vorticityScale τ := Real.exp (∫ s in (0 : ℝ)..τ, cw s)
  spatialScale τ := Real.exp (-(∫ s in (0 : ℝ)..τ, cl s))
  physicalTime τ := ∫ s in (0 : ℝ)..τ, Real.exp (∫ r in (0 : ℝ)..s, cw r)
  vorticityRate := cw
  spatialRate := cl

/-- The constructed vorticity scale stays strictly positive at every time. -/
theorem vorticityScale_ofRates_pos (cl cw : ℝ → ℝ) (τ : ℝ) :
    0 < (ofRates cl cw).vorticityScale τ :=
  Real.exp_pos _

/-- The constructed spatial scale stays strictly positive at every time. -/
theorem spatialScale_ofRates_pos (cl cw : ℝ → ℝ) (τ : ℝ) :
    0 < (ofRates cl cw).spatialScale τ :=
  Real.exp_pos _

/-- The rescaling initially leaves vorticity unchanged. -/
@[simp]
theorem vorticityScale_ofRates_zero (cl cw : ℝ → ℝ) :
    (ofRates cl cw).vorticityScale 0 = 1 := by
  simp [ofRates]

/-- The rescaling initially leaves the spatial coordinate unchanged. -/
@[simp]
theorem spatialScale_ofRates_zero (cl cw : ℝ → ℝ) :
    (ofRates cl cw).spatialScale 0 = 1 := by
  simp [ofRates]

/-- Physical time and rescaled time share their initial origin. -/
@[simp]
theorem physicalTime_ofRates_zero (cl cw : ℝ → ℝ) :
    (ofRates cl cw).physicalTime 0 = 0 := by
  simp [ofRates]

/-- The clock has strict derivative `Cω(τ)` at every `τ`. This is the form used by the
inverse function theorem in `ClockInverse`. -/
theorem physicalTime_ofRates_hasStrictDerivAt
    (cl : ℝ → ℝ) {cw : ℝ → ℝ} (hcw : Continuous cw) (τ : ℝ) :
    HasStrictDerivAt (ofRates cl cw).physicalTime
      ((ofRates cl cw).vorticityScale τ) τ := by
  have hscale : Continuous (fun s ↦ Real.exp (∫ r in (0 : ℝ)..s, cw r)) :=
    Real.continuous_exp.comp
      (intervalIntegral.differentiable_integral_of_continuous hcw).continuous
  exact intervalIntegral.integral_hasStrictDerivAt_right
    (hscale.intervalIntegrable 0 τ)
    hscale.aestronglyMeasurable.stronglyMeasurableAtFilter hscale.continuousAt

/-- Continuous normalization rates give all three differential scale laws. -/
theorem satisfiesDynamicScaleODEsAt_ofRates
    {cl cw : ℝ → ℝ} (hcl : Continuous cl) (hcw : Continuous cw) (τ : ℝ) :
    SatisfiesDynamicScaleODEsAt (ofRates cl cw) τ := by
  have hspatial := intervalIntegral.integral_hasDerivAt_right
    (hcl.intervalIntegrable 0 τ)
    hcl.aestronglyMeasurable.stronglyMeasurableAtFilter hcl.continuousAt
  have hvorticity := intervalIntegral.integral_hasDerivAt_right
    (hcw.intervalIntegrable 0 τ)
    hcw.aestronglyMeasurable.stronglyMeasurableAtFilter hcw.continuousAt
  refine ⟨?_, ?_, ?_⟩
  · simpa only [ofRates, mul_comm] using hvorticity.exp
  · simpa only [ofRates, Pi.neg_apply, mul_comm] using hspatial.neg.exp
  · exact (physicalTime_ofRates_hasStrictDerivAt cl hcw τ).hasDerivAt

/-- Equal normalization rates give reciprocal scales, directly from their
integral formulas. -/
theorem spatialScale_ofRates_eq_inv (c : ℝ → ℝ) (τ : ℝ) :
    (ofRates c c).spatialScale τ = ((ofRates c c).vorticityScale τ)⁻¹ := by
  exact Real.exp_neg _

end DeGregorio.DynamicRescalingData
