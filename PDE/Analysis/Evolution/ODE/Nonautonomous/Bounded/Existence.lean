/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.ODE.ExistUnique

/-!
# Finite trajectories of bounded time-dependent fields

A uniform velocity bound permits Picard's construction on any prescribed finite
interval. Spatial Lipschitz bounds are only needed on bounded balls, uniformly
over that time interval. There is no smallness condition on the product of the
Lipschitz constant and the elapsed time.
-/

@[expose] public section

open Metric Set

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Construct a trajectory on a whole finite interval from a bounded velocity
and spatial Lipschitz bounds on bounded balls. The field only needs continuity
within the prescribed time interval. -/
theorem exists_solution_Icc_of_bounded
    {a b : ℝ} (t₀ : Icc a b) (x₀ : E) {F : ℝ → E → E} {M : NNReal}
    (hbound : ∀ t ∈ Icc a b, ∀ x, ‖F t x‖ ≤ M)
    (hcont : ∀ x, ContinuousOn (fun t ↦ F t x) (Icc a b))
    (hlip : ∀ R : ℝ, 0 < R →
      ∃ K : NNReal, ∀ t ∈ Icc a b, LipschitzOnWith K (F t) (closedBall x₀ R)) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧ ContinuousOn α (Icc a b) ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt α (F t (α t)) (Icc a b) t := by
  let S : NNReal := ⟨max (b - t₀) (t₀ - a), le_max_of_le_left (by linarith [t₀.2.2])⟩
  have hS : (S : ℝ) = max (b - t₀) (t₀ - a) := rfl
  let A : NNReal := M * S + 1
  obtain ⟨K, hK⟩ := hlip A (by dsimp [A]; positivity)
  have hpic : IsPicardLindelof F t₀ x₀ A 0 M K := {
    lipschitzOnWith := hK
    continuousOn := fun x _ ↦ hcont x
    norm_le := fun t ht x _ ↦ hbound t ht x
    mul_max_le := by
      change (M : ℝ) * max (b - t₀) (t₀ - a) ≤ (M : ℝ) * S + 1 - 0
      rw [hS]
      linarith }
  obtain ⟨α, hα₀, hα⟩ := hpic.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, hα₀, fun t ht ↦ (hα t ht).continuousWithinAt, hα⟩

omit [CompleteSpace E] in
/-- A bounded field with a continuous spatial derivative on a closed time slab
has finite trajectories through every point. Compact cylinders provide the
local Lipschitz constants. -/
theorem exists_solution_Icc_of_bounded_of_continuous_spatial_fderiv
    [ProperSpace E] {a b : ℝ} (t₀ : Icc a b) (x₀ : E)
    {F : ℝ × E → E} {D : ℝ × E → E →L[ℝ] E} {M : NNReal}
    (hbound : ∀ p : ℝ × E, p.1 ∈ Icc a b → ‖F p‖ ≤ M)
    (hcont : ContinuousOn F (Icc a b ×ˢ univ))
    (hDcont : ContinuousOn D (Icc a b ×ˢ univ))
    (hD : ∀ p : ℝ × E, p.1 ∈ Icc a b →
      HasFDerivAt (fun x ↦ F (p.1, x)) (D p) p.2) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧ ContinuousOn α (Icc a b) ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt α (F (t, α t)) (Icc a b) t := by
  apply exists_solution_Icc_of_bounded t₀ x₀
    (fun t ht x ↦ hbound (t, x) ht)
  · intro x
    exact hcont.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ ht ↦ ⟨ht, mem_univ _⟩)
  · intro R _
    have hcompact : IsCompact (Icc a b ×ˢ closedBall x₀ R) :=
      isCompact_Icc.prod (isCompact_closedBall x₀ R)
    obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn
      (hDcont.mono (prod_mono_right (subset_univ _)))
    let K : NNReal := ⟨max C 0, le_max_right _ _⟩
    refine ⟨K, fun t ht ↦ (convex_closedBall x₀ R).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
        (fun x _ ↦ (hD (t, x) ht).hasFDerivWithinAt) ?_⟩
    intro x hx
    exact (hC (t, x) ⟨ht, hx⟩).trans (le_max_left _ _)

end PDE.Analysis.Evolution
