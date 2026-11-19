/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.Coordinates
public import PDE.Hyperbolic.ConservationLaw.InitialBoundary.TimeCutoff

/-!
# Volume transport in scalar spacetime

The scalar spacetime equivalence only reorders the time and space
coordinates. It preserves volume in both directions, allowing joint
almost-everywhere identities and integrals to use the same coordinate map.
-/

@[expose] public noncomputable section

open MeasureTheory PDE.Common PDE.Hyperbolic.ConservationLaw

namespace HamiltonJacobi1D

/-- Putting time first in scalar Euclidean spacetime preserves volume. -/
theorem measurePreserving_scalarSpaceTimeEquiv_symm :
    MeasurePreserving scalarSpaceTimeEquiv.symm volume volume := by
  have hs : MeasurePreserving Prod.swap (volume : Measure (ℝ × ℝ)) volume := by
    simpa only [Measure.volume_eq_prod] using
      (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume))
  have he : (scalarSpaceTimeEquiv.symm : (ℝ × ℝ) → ℝ^2) =
      spaceTimePair ∘ Prod.swap := by
    funext p
    simp [spaceTimePair_apply]
  rw [he]
  exact measurePreserving_spaceTimePair.comp hs

/-- The scalar coordinate map preserves volume from Euclidean
spacetime to space × time. -/
theorem measurePreserving_scalarSpaceTimeEquiv :
    MeasurePreserving scalarSpaceTimeEquiv volume volume :=
  MeasurePreserving.symm scalarSpaceTimeEquiv.symm.toHomeomorph.toMeasurableEquiv
    measurePreserving_scalarSpaceTimeEquiv_symm

end HamiltonJacobi1D
