/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.RealPair.VelocityIdentification
public import PDE.Fluid.DeGregorio.DynamicRescaling

/-!
# Principal-value velocity for a classical rescaled solution

The equation uses the spectral Hilbert relation so that it also makes sense
for rough data. On a compact C¹ slice, fixing the velocity at the origin
identifies it with the principal-value primitive pointwise.
-/

@[expose] public noncomputable section

open Set PDE.Analysis

namespace DeGregorio

/-- The normalized velocity of a compact C¹ classical slice agrees pointwise
with the principal-value velocity used in the energy estimates. -/
theorem IsClassicalRescaledSolutionOn.velocity_eq_hilbertPVVelocity
    {a : ℝ} {fields : Fields} {cl cw : ℝ → ℝ} {times : Set ℝ}
    (hsol : IsClassicalRescaledSolutionOn a fields cl cw times)
    {t : ℝ} (ht : t ∈ times)
    (hregular : ContDiff ℝ 1 (fun x ↦ fields.vorticity x t))
    (hcompact : HasCompactSupport (fun x ↦ fields.vorticity x t))
    (hnormalized : fields.velocity 0 t = 0) :
    (fun x ↦ fields.velocity x t) = hilbertPVVelocity (fun x ↦ fields.vorticity x t) := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcompact hregular one_ne_zero
  exact (hsol.biotSavart ht).eq_hilbertPVVelocity_of_normalized
    (fun _ ↦ hsol.regularity.velocity_differentiableAt ht) hK hcompact hnormalized

end DeGregorio
