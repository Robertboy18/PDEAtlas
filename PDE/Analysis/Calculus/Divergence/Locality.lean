/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Divergence

/-!
# Locality of the coordinate divergence
-/

@[expose] public section

/-- Equal vector-field germs have equal divergence at their base point.
This also holds for the total derivative expressions without regularity assumptions. -/
theorem Filter.EventuallyEq.divergence_eq {n : ℕ} {F G : ℝ^n → ℝ^n} {x : ℝ^n}
    (h : F =ᶠ[nhds x] G) : ∇· F x = ∇· G x := by
  apply Finset.sum_congr rfl
  intro i _
  have hi : (fun y ↦ F y i) =ᶠ[nhds x] fun y ↦ G y i :=
    h.mono fun _ heq ↦ congrArg (fun z : ℝ^n ↦ z i) heq
  exact (hi.partialDeriv i).eq_of_nhds

/-- A vector field vanishing near a point has zero divergence there. -/
theorem Filter.EventuallyEq.divergence_eq_zero {n : ℕ} {F : ℝ^n → ℝ^n} {x : ℝ^n}
    (h : F =ᶠ[nhds x] 0) : ∇· F x = 0 := by
  rw [h.divergence_eq]
  apply Finset.sum_eq_zero
  intro i _
  simp [PDE.partialDeriv]

/-- Taking divergence preserves equality of vector-field germs. -/
theorem Filter.EventuallyEq.divergence {n : ℕ} {F G : ℝ^n → ℝ^n} {x : ℝ^n}
    (h : F =ᶠ[nhds x] G) : ∇· F =ᶠ[nhds x] ∇· G :=
  h.eventuallyEq_nhds.mono fun _ heq ↦ heq.divergence_eq
