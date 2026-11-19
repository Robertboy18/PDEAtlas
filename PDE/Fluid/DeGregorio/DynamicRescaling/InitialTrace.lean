/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.DynamicRescaling.Reconstruction

/-!
# The initial trace under physical reconstruction

The scales and the inverse clock are continuous at zero and equal one, one,
and zero there. Thus a joint right-continuous initial vorticity remains
right-continuous after reconstruction. This uses the forward clock image,
where every physical point has a nonnegative rescaled time.

Together with the exact initial-slice identity, physical reconstruction therefore
preserves an initial-value problem whose classical equation holds only at positive
times.
-/

@[expose] public noncomputable section

open Set

namespace DeGregorio

open DynamicRescalingData

/-- Physical reconstruction preserves joint right continuity of the vorticity at time zero,
relative to the forward clock image. -/
theorem continuousWithinAt_physicallyReconstructedFields_vorticity_zero
    {fields : Fields} {cl cw : ℝ → ℝ} {x : ℝ}
    (hcl : Continuous cl) (hcw : Continuous cw)
    (hinitial : ContinuousWithinAt (Function.uncurry fields.vorticity)
      (univ ×ˢ Ici 0) (x, 0)) :
    ContinuousWithinAt
      (Function.uncurry (physicallyReconstructedFields (ofRates cl cw) fields).vorticity)
      (univ ×ˢ ((ofRates cl cw).physicalTime '' Ici 0)) (x, 0) := by
  let data := ofRates cl cw
  have htime : ContinuousAt data.rescaledTime 0 := by
    simpa only [data, physicalTime_ofRates_zero] using
      (rescaledTime_ofRates_hasStrictDerivAt cl hcw 0).hasDerivAt.continuousAt
  have htime' : ContinuousAt (fun p : ℝ × ℝ ↦ data.rescaledTime p.2) (x, 0) :=
    htime.comp (f := fun p : ℝ × ℝ ↦ p.2) continuousAt_snd
  have hzero : data.rescaledTime 0 = 0 := rescaledTime_ofRates_zero cl hcw
  have hA : ContinuousAt
      (fun p : ℝ × ℝ ↦ data.vorticityScale (data.rescaledTime p.2)) (x, 0) := by
    apply ContinuousAt.comp _ htime'
    rw [hzero]
    exact (satisfiesDynamicScaleODEsAt_ofRates hcl hcw 0).vorticityScale_hasDerivAt.continuousAt
  have hL : ContinuousAt
      (fun p : ℝ × ℝ ↦ data.spatialScale (data.rescaledTime p.2)) (x, 0) := by
    apply ContinuousAt.comp _ htime'
    rw [hzero]
    exact (satisfiesDynamicScaleODEsAt_ofRates hcl hcw 0).spatialScale_hasDerivAt.continuousAt
  have hpath : ContinuousAt
      (fun p : ℝ × ℝ ↦ (p.1 / data.spatialScale (data.rescaledTime p.2),
        data.rescaledTime p.2)) (x, 0) :=
    (continuousAt_fst.div hL (spatialScale_ofRates_pos cl cw _).ne').prodMk htime'
  have hmaps : MapsTo
      (fun p : ℝ × ℝ ↦ (p.1 / data.spatialScale (data.rescaledTime p.2),
        data.rescaledTime p.2))
      (univ ×ˢ (data.physicalTime '' Ici 0)) (univ ×ˢ Ici 0) := by
    rintro ⟨y, t⟩ ⟨_, τ, hτ, rfl⟩
    exact ⟨mem_univ _, by simpa only [data, rescaledTime_ofRates_physicalTime cl hcw]⟩
  have hcomposed : ContinuousWithinAt
      (fun p : ℝ × ℝ ↦ fields.vorticity
        (p.1 / data.spatialScale (data.rescaledTime p.2)) (data.rescaledTime p.2))
      (univ ×ˢ (data.physicalTime '' Ici 0)) (x, 0) := by
    exact hinitial.comp_of_eq hpath.continuousWithinAt hmaps (by
      simp only [data, rescaledTime_ofRates_zero cl hcw, spatialScale_ofRates_zero, div_one])
  exact (hA.inv₀ (vorticityScale_ofRates_pos cl cw _).ne').continuousWithinAt.mul hcomposed

end DeGregorio
