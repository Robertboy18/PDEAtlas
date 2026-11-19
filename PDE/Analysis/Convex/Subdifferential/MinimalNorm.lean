/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convex.Subdifferential.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-!
# Attainment of the minimal subgradient norm

Projection of zero onto a nonempty closed convex subdifferential fiber produces a
supporting vector of least norm. This justifies the minimum in the Yosida estimate.
-/

@[expose] public section

namespace PDE.Analysis.Convex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- At each point in the subdifferential domain, the subgradient norm attains its minimum. -/
theorem exists_minimal_norm_subgradient {I : H → EReal} (hI : IsProper I)
    {u : H} (hu : u ∈ subdifferentialDomain I) :
    ∃ v ∈ subdifferential I u, ∀ w ∈ subdifferential I u, ‖v‖ ≤ ‖w‖ := by
  obtain ⟨v, hv, hnorm⟩ := exists_norm_eq_iInf_of_complete_convex hu
    (isClosed_subdifferential hI u).isComplete (convex_subdifferential hI u) 0
  refine ⟨v, hv, fun w hw ↦ ?_⟩
  simp only [zero_sub, norm_neg] at hnorm
  rw [hnorm]
  exact ciInf_le ⟨0, Set.forall_mem_range.2 fun _ ↦ norm_nonneg _⟩
    (⟨w, hw⟩ : subdifferential I u)

end PDE.Analysis.Convex
