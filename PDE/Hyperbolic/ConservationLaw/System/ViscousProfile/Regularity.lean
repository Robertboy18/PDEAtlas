/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.FirstIntegral
import PDE.Analysis.Evolution.ODE.Regularity

/-!
# Smoothness of viscous profiles

The first integral turns the second-order profile equation into an autonomous
ODE with the same regularity as the flux. The regularity theorem for integral curves
therefore upgrades a classical profile to a smooth one.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace PDE.Hyperbolic.ConservationLaw.System

/-- Every classical profile of a smooth flux is smooth on the entire real line.
The higher derivatives are derived from its first integral. -/
theorem IsViscousProfile.contDiff_infty {m : ℕ} {flux : ℝ^m → ℝ^m} {uL uR : ℝ^m} {speed : ℝ}
    {v : ℝ → ℝ^m} (hv : IsViscousProfile flux uL uR speed v) (hflux : ContDiff ℝ ∞ flux) :
    ContDiff ℝ ∞ v := by
  have hf : ContDiff ℝ ∞ (fun p : ℝ × ℝ^m ↦ flux p.2 - flux uL - speed • (p.2 - uL)) :=
    ((hflux.comp contDiff_snd).sub contDiff_const).sub
      ((contDiff_snd.sub contDiff_const).const_smul speed)
  apply contDiffOn_univ.mp
  apply PDE.Analysis.Evolution.contDiffOn_of_hasDerivAt
    (f := fun _ x ↦ flux x - flux uL - speed • (x - uL)) isOpen_univ hf.contDiffOn
  intro t _
  simpa only [hv.first_integral (hflux.differentiable (by simp)) t] using
    (hv.contDiff.differentiable (by norm_num) t).hasDerivAt

end PDE.Hyperbolic.ConservationLaw.System
