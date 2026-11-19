/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Lifting.Formula
public import PDE.Spaces.Sobolev.Approximation.Mollification.ScaleDerivative.Regularity

/-!
# Interior regularity of the mollified extension

Locally integrable boundary data give a smooth extension at every positive
height. The coordinate split and the height cutoff preserve the joint
regularity of mollification in scale and position.
-/

@[expose] public section

open MeasureTheory Set

namespace SobolevSpace.Trace.HalfSpace

open SobolevSpace.Approximation

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Mollifying at the current height gives a smooth function in the open
upper half-space, even when the boundary data are only locally integrable. -/
theorem contDiffOn_mollifiedExtension (μ : Mollifier n) {g : ℝ^n → F}
    (hg : LocallyIntegrable g volume) :
    ContDiffOn ℝ (⊤ : ℕ∞) (mollifiedExtension μ g) ℝ^(n + 1)₊ := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (@splitTangentialNormal n) :=
    tangentialNormalContinuousLinearEquiv.contDiff
  have hm := (contDiffOn_mollifyVector_scale μ hg).comp
    (hs.snd.prodMk hs.fst).contDiffOn (show MapsTo
      (fun z : ℝ^(n + 1) ↦ ((splitTangentialNormal z).2, (splitTangentialNormal z).1))
      ℝ^(n + 1)₊ (Ioi 0 ×ˢ univ) from fun z hz ↦ by
        rw [upper_eq_preimage_split_snd_Ioi] at hz
        exact ⟨hz.2, mem_univ _⟩)
  exact (contDiff_heightCutoff.comp hs.snd).contDiffOn.smul hm

/-- The mollified extension is measurable for volume restricted to the upper half-space. -/
theorem aestronglyMeasurable_mollifiedExtension
    (μ : Mollifier n) {g : ℝ^n → F} (hg : LocallyIntegrable g volume) :
    AEStronglyMeasurable (mollifiedExtension μ g) (volume.restrict ℝ^(n + 1)₊) :=
  (contDiffOn_mollifiedExtension μ hg).continuousOn.aestronglyMeasurable
    (HalfSpace.measurableSet_upper (n + 1))

end SobolevSpace.Trace.HalfSpace
