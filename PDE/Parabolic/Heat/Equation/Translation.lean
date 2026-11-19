/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Equation

/-!
# Time translation of the heat operator

Translation commutes with `fderiv` at every point, whether or not the function is
differentiable there. A pure time translation also leaves the spatial variable
unchanged, so it commutes with `heatOperator` with no regularity hypothesis.
-/

@[expose] public section

open PDE (SpaceTime partialDeriv)

namespace HeatEquation

open PDE.Common

/-- Backward time translation commutes with `heatOperator`. -/
theorem heatOperator_comp_sub_time {n : ℕ} (u : SpaceTime n → ℝ)
    (δ : ℝ) (p : SpaceTime n) :
    heatOperator (fun q ↦ u (q - timeSpaceCons δ 0)) p =
      heatOperator u (p - timeSpaceCons δ 0) := by
  have hslice (s : ℝ) (y : ℝ^n) :
      timeSpaceCons s y - timeSpaceCons δ 0 = timeSpaceCons (s - δ) y := by
    ext i
    cases i using Fin.cases <;> simp
  simp only [heatOperator, partialDeriv, fderiv_comp_sub, hslice,
    PiLp.sub_apply, timeSpaceCons_zero, map_sub, spatialPartCLM_timeSpaceCons, sub_zero]

end HeatEquation
