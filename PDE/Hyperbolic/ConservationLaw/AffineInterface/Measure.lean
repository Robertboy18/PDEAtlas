/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.AffineInterface.Geometry
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Null affine interfaces in spacetime

An affine front has one spatial point in each time slice. Fubini and the
canonical volume-preserving coordinate maps show that it has zero spacetime
volume, so pointwise equations away from finitely many fronts hold almost everywhere.
-/

@[expose] public noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.AffineInterface

open MeasureTheory

/-- Almost every spacetime point avoids any prescribed affine front. -/
theorem ae_ne_interface (s : ℝ) :
    ∀ᵐ p : ℝ^2, p 1 ≠ s * p 0 := by
  have hprod : ∀ᵐ p : ℝ × ℝ, p.2 ≠ s * p.1 := by
    rw [Measure.volume_eq_prod]
    apply (Measure.ae_prod_iff_ae_ae
      (isClosed_eq continuous_snd (continuous_const.mul continuous_fst)).measurableSet.compl).mpr
    exact Filter.Eventually.of_forall fun t ↦ volume.ae_ne (s * t)
  have hpi := (volume_preserving_finTwoArrow ℝ).quasiMeasurePreserving.ae hprod
  exact (PiLp.volume_preserving_ofLp (Fin 2)).quasiMeasurePreserving.ae hpi

end PDE.Hyperbolic.ConservationLaw.AffineInterface
