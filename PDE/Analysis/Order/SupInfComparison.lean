/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Supremum and infimum from pairwise comparison

A uniform positive multiplicative comparison gives the corresponding real
supremum/infimum inequality. It supplies the boundedness needed for both
conditionally complete lattice operations, even without compactness.
-/

@[expose] public section

namespace PDE.Analysis

open Set

/-- Cross comparisons between two fields give a supremum/infimum comparison,
including the common empty-set convention for the real numbers. -/
theorem sSup_image_le_mul_sInf_image_of_pairwise
    {X : Type*} {V : Set X} {u v : X → ℝ} {C : ℝ}
    (hC : 0 < C) (hcompare : ∀ x ∈ V, ∀ y ∈ V, u x ≤ C * v y) :
    sSup (u '' V) ≤ C * sInf (v '' V) := by
  rcases V.eq_empty_or_nonempty with rfl | ⟨z, hz⟩
  · simp
  have hne : (u '' V).Nonempty := ⟨u z, mem_image_of_mem u hz⟩
  apply csSup_le hne
  rintro _ ⟨x, hx, rfl⟩
  rw [← div_le_iff₀' hC]
  apply le_csInf ⟨v z, mem_image_of_mem v hz⟩
  rintro _ ⟨y, hy, rfl⟩
  exact (div_le_iff₀' hC).mpr (hcompare x hx y hy)

end PDE.Analysis
