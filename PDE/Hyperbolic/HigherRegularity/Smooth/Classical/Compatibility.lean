/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Smooth.Classical.WeakSolution.Construction
public import PDE.Hyperbolic.HigherRegularity.Smooth.Representative.InitialTraces

/-!
# Necessity of the wave compatibility conditions

A classical solution determines its original weak wave. The full equation then
identifies all its initial derivatives with the pointwise recurrence. Their
zero lateral values prove every compatibility condition. This also provides a
way to verify compatible manufactured data from an explicit classical formula.
-/

@[expose] public noncomputable section

open PDE (SpaceTime)

namespace Hyperbolic.HigherRegularity.SmoothWave

open Filter MeasureTheory Set PDE.Common SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity SobolevSpace.Evolution.Classical

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- Smoothness of a classical wave forces all the recursively computed
initial values to vanish on the boundary. No ellipticity is needed. -/
theorem IsClassicalSolution.hasCompatibleBoundaryValues {P : SmoothFullCoefficients n Ω}
    (hn : 0 < n) {hopen : IsOpen Ω} (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) (hab : a < b) {f U : SpaceTime n → ℝ} {g h : ℝ^n → ℝ}
    {hf : ∀ k, ContDiffUpToBoundary k f (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b))}
    {hg : ∀ k, ContDiffUpToBoundary k g Ω} {hh : ∀ k, ContDiffUpToBoundary k h Ω}
    (hU : IsClassicalSolution P hopen hf hg hh U) :
    HasCompatibleBoundaryValues P hopen hbounded hab hf hg hh := by
  obtain ⟨u, v, w, q₀, p₀, hw, hu, hq, hp⟩ := hU.exists_weakWave hn hbounded hgraph hab
  have hq₀ : baseCoordCLM q₀ =
      wkpBaseCoordinateCLM (initialSobolevValue P hopen hbounded hab hf hg hh 1 0) :=
    Lp.ext (hq.trans ((hg 1).toWkpSpaceOn_base_ae hopen hbounded 2).symm)
  have hp₀ : p₀ = wkpBaseCoordinateCLM (initialSobolevValue P hopen hbounded hab hf hg hh 0 1) :=
    Lp.ext (hp.trans ((hh 0).toWkpSpaceOn_base_ae hopen hbounded 2).symm)
  intro j x hx
  rw [← initial_derivativeSlice_eq P hopen hbounded hab hf hg hh hU.smooth hU.continuous
    hw hq₀ hp₀ hu j (frontier_subset_closure hx)]
  exact derivativeSlice_eq_zero_on_frontier hopen hab hU.smooth hU.continuous
    hU.boundary j a ⟨le_rfl, hab.le⟩ x hx

end Hyperbolic.HigherRegularity.SmoothWave
