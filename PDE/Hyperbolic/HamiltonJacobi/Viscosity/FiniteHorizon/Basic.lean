/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.InitialValue

/-!
# Open and closed finite time slabs

The viscosity equation on a finite horizon is tested only for `0 < t < T`.
Continuity extends an interior comparison to both faces of the closed slab.
This uses Mathlib's order closure theorem and requires no terminal viscosity test.
-/

@[expose] public section

namespace HamiltonJacobi

open Set

variable {E : Type*} [NormedAddCommGroup E]

/-- The open spacetime slab on which a finite-horizon equation is tested. -/
def openTimeSlab (T : ℝ) : Set (E × ℝ) :=
  {z | 0 < z.2 ∧ z.2 < T}

/-- Both strict time inequalities define open sets. -/
theorem isOpen_openTimeSlab (T : ℝ) : IsOpen (openTimeSlab (E := E) T) :=
  (isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const)

/-- For a positive horizon, the open slab is dense in the closed slab. -/
theorem closure_openTimeSlab {T : ℝ} (hT : 0 < T) :
    closure (openTimeSlab (E := E) T) = closedTimeSlab T := by
  have hopen : openTimeSlab (E := E) T = univ ×ˢ Ioo 0 T := by
    ext z
    simp only [openTimeSlab, mem_ofPred_eq, mem_prod, mem_univ, true_and, mem_Ioo]
  rw [hopen, closure_prod_eq, closure_univ, closure_Ioo hT.ne]
  ext z
  simp only [mem_prod, mem_univ, true_and, mem_Icc, closedTimeSlab, mem_ofPred_eq]

/-- Comparison on the open slab extends to both time endpoints by continuity. -/
theorem le_on_closedTimeSlab {u v : E × ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hu : ContinuousOn u (closedTimeSlab T)) (hv : ContinuousOn v (closedTimeSlab T))
    (hle : ∀ z ∈ openTimeSlab T, u z ≤ v z) :
    ∀ z ∈ closedTimeSlab T, u z ≤ v z := by
  rw [← closure_openTimeSlab hT] at hu hv ⊢
  exact fun _ hz ↦ le_on_closure hle hu hv hz

end HamiltonJacobi
