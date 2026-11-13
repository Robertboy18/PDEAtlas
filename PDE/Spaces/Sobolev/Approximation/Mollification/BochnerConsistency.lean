/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.H1Operator
public import PDE.Analysis.Evolution.Compactness.Lp.Basic

/-!
# Strong convergence of row mollifiers on Bochner L²

The whole-space row isometry transports the L² approximate identity to Sobolev
coordinates. Contractivity then lifts strong convergence to Bochner L² on an
arbitrary measure space. The time representative needs no continuity.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology

namespace SobolevSpace.Approximation

open GraphSpace PDE.Analysis.Evolution

variable {n : ℕ}

/-- The row mollifiers tend strongly to the identity, by the L²
approximate identity transported through the whole-space row isometry. -/
theorem tendsto_mollifierRowCLM
    (μ : Mollifier n) (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k)
    (hε0 : Tendsto ε atTop (𝓝 0)) (u : DerivLp n 2 univ) :
    Tendsto (fun k ↦ mollifierRowCLM μ (hε k) u) atTop (𝓝 u) := by
  have hraw := tendsto_mollifierL2CLM (E := ℝ) μ ε hε hε0 (wholeSpaceL2Equiv u)
  have h := wholeSpaceL2Equiv.symm.continuous.continuousAt.tendsto.comp hraw
  simpa only [Function.comp_def, ← wholeSpaceL2Equiv_mollifierRowCLM,
    LinearIsometryEquiv.symm_apply_apply] using h

/-- Spatial row mollification converges strongly on Bochner L² classes without
any time regularity of the representative. -/
theorem tendsto_mollifierRowCLM_compLpL
    {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (μ : Mollifier n) (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k)
    (hε0 : Tendsto ε atTop (𝓝 0)) (u : Lp (DerivLp n 2 univ) 2 ν) :
    Tendsto (fun k ↦ (mollifierRowCLM μ (hε k)).compLpL 2 ν u)
      atTop (𝓝 u) := by
  apply tendsto_compLpL_of_tendsto_strongly
    (fun k ↦ mollifierRowCLM μ (hε k)) 1 zero_le_one
  · intro k v
    simpa only [one_mul] using norm_mollifierRowCLM_apply_le μ (hε k) v
  · exact tendsto_mollifierRowCLM μ ε hε hε0

end SobolevSpace.Approximation
