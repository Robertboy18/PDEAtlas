/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Basic
import PDE.Analysis.Calculus.StrongOperator

/-!
# Joint continuity of a strongly continuous semigroup

Strong continuity concerns each fixed vector. Uniform boundedness on compact time
intervals upgrades it to joint continuity of `(t, x) ↦ T(t)x`. This is the continuity
needed for the Duhamel integral; continuity in the operator norm is not required.
-/

@[expose] public section

noncomputable section

open Filter Set Topology

namespace PDE.Analysis.Evolution.StronglyContinuousSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The action of a strongly continuous semigroup on a Banach space is jointly
continuous in time and the initial vector. -/
theorem continuous_apply (T : StronglyContinuousSemigroup E) :
    Continuous (fun p : NNReal × E ↦ T p.1 p.2) := by
  refine PDE.Analysis.continuous_apply_prod_of_eventually_norm_le T.continuous_orbit
    fun t₀ ↦ ?_
  obtain ⟨C, _, hbound⟩ := T.exists_norm_le_on_Icc (t₀ + 1)
  exact ⟨C, (gt_mem_nhds (lt_add_one t₀)).mono fun t ht ↦ hbound t ⟨zero_le, ht.le⟩⟩

end PDE.Analysis.Evolution.StronglyContinuousSemigroup
