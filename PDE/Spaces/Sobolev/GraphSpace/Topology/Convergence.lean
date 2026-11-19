/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.OrderRestriction

/-!
# Coordinate convergence in Sobolev graph spaces

The graph topology is the subspace topology of the finite product of
its derivative coordinates. Convergence therefore reduces to convergence
in each coordinate, with no assumption on the domain or dimension.
-/

@[expose] public section

namespace SobolevSpace.GraphSpace

open Filter MeasureTheory
open scoped ENNReal Topology Sobolev

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set ℝ^n}

/-- Coordinate convergence in `Lᵖ` implies convergence in the Sobolev graph norm. -/
theorem tendsto_wkp_of_coordinate_eLpNorm
    {U : ℕ → W^{k,p}(Ω)} {V : W^{k,p}(Ω)}
    (h : ∀ a : DerivIndex n k,
      Tendsto (fun j ↦ eLpNorm
        ((wkpCoordinateCLM a (U j) : ℝ^n → ℝ) -
          (wkpCoordinateCLM a V : ℝ^n → ℝ)) p (domainMeasure n Ω))
        atTop (𝓝 0)) :
    Tendsto U atTop (𝓝 V) := by
  apply tendsto_subtype_rng.mpr
  apply (PiLp.homeomorph p (fun _ : DerivIndex n k ↦ DerivLp n p Ω)).symm.continuous.tendsto _
    |>.comp
  apply tendsto_pi_nhds.mpr
  intro a
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
    (fun j ↦ wkpCoordinateCLM a (U j)) (wkpCoordinateCLM a V)).2 (h a)

end SobolevSpace.GraphSpace
