/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Data.SobolevTimeJet

/-!
# Spatial restriction of Sobolev-valued time curves

Lowering the stored spatial order preserves the underlying function and
therefore its Dirichlet load. These identities allow spatial recovery and
weak time differentiation to use the same forcing and acceleration.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set

namespace Hyperbolic.HigherRegularity

open SobolevSpace SobolevSpace.GraphSpace

variable {n m : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- Spatial order restriction preserves the base-coordinate time class. -/
@[simp]
theorem baseCoordinateTimeLp_lowerOrderTimeLp
    (f : Lp (W^{(m + 1),2}(Ω)) 2 (volume.restrict (Ioc a b))) :
    baseCoordinateTimeLp (lowerOrderTimeLp f) = baseCoordinateTimeLp f := by
  apply Lp.ext
  filter_upwards [baseCoordinateTimeLp_apply_ae (lowerOrderTimeLp f),
    lowerOrderTimeLp_apply_ae f, baseCoordinateTimeLp_apply_ae f] with t h₁ h₂ h₃
  rw [h₁, h₂, h₃]
  rfl

/-- Spatial order restriction preserves the full Dirichlet load. -/
@[simp]
theorem dirichletLoadTimeLp_lowerOrderTimeLp (hopen : IsOpen Ω)
    (f : Lp (W^{(m + 1),2}(Ω)) 2 (volume.restrict (Ioc a b))) :
    dirichletLoadTimeLp hopen (lowerOrderTimeLp f) = dirichletLoadTimeLp hopen f := by
  simp only [dirichletLoadTimeLp, baseCoordinateTimeLp_lowerOrderTimeLp]

end Hyperbolic.HigherRegularity
