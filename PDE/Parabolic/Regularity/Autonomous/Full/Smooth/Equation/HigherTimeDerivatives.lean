/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Regularity.Autonomous.Full.Smooth.Equation.Sobolev

/-!
# Higher time derivatives of the parabolic equation

The Sobolev curves are differentiable at every time, with one-sided
derivatives within the interval at the endpoints. Since the autonomous full
load is a bounded linear map, the equation can be differentiated to every
finite order without constructing a new solution.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.Smooth

open Set PDE.Common SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity SobolevSpace.Evolution.Classical

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

local notation "Q" => splitSpaceTime ⁻¹' Set.prod Ω (Ioo a b)

/-- Differentiating the closed-interval Sobolev equation gives every
higher full equation, including its continuous initial and terminal values. -/
theorem sobolev_equation_derivatives (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    {f U : SpaceTime n → ℝ}
    (hf : ∀ k, ContDiffUpToBoundary k f Q)
    (hU : ∀ k, ContDiffUpToBoundary k U Q)
    (heq : ∀ t ∈ Icc a b,
      wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU 0 1 t) +
          wkpBaseCoordinateCLM
            (P.load hopen hbounded 0 (sobolevCurve hopen hbounded hab hU 2 0 t)) =
        wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hf 0 0 t))
    (j : ℕ) :
    ∀ t ∈ Icc a b,
      wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU 0 (j + 1) t) +
          wkpBaseCoordinateCLM
            (P.load hopen hbounded 0 (sobolevCurve hopen hbounded hab hU 2 j t)) =
        wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hf 0 j t) := by
  induction j with
  | zero => exact heq
  | succ j ih =>
    intro t ht
    let B : W^{0,2}(Ω) →L[ℝ] DerivLp n 2 Ω := wkpBaseCoordinateCLM
    let L : W^{2,2}(Ω) →L[ℝ] DerivLp n 2 Ω :=
      wkpBaseCoordinateCLM.comp (P.load hopen hbounded 0)
    have hdt := B.hasFDerivAt.comp_hasDerivWithinAt t
      (hasDerivWithinAt_sobolevCurve hopen hbounded hab hU 0 (j + 1) ht)
    have hload := L.hasFDerivAt.comp_hasDerivWithinAt t
      (hasDerivWithinAt_sobolevCurve hopen hbounded hab hU 2 j ht)
    have hforcing := B.hasFDerivAt.comp_hasDerivWithinAt t
      (hasDerivWithinAt_sobolevCurve hopen hbounded hab hf 0 j ht)
    have hright := hforcing.congr_of_mem ih ht
    exact ((hdt.add hload).derivWithin (uniqueDiffOn_Icc hab t ht)).symm.trans
      (hright.derivWithin (uniqueDiffOn_Icc hab t ht))

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.Smooth
