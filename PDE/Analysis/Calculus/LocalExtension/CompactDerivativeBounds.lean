/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Uniform derivative bounds on a compact set

Local third-order regularity makes the first three derivative maps continuous
on a supplied compact set. Their compact images give one positive bound for all three full
operator norms. The compact set and function are fixed;
no later cutoff parameters enter the choice of constant.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace PDE.Analysis

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The first three derivatives of a map that is locally `C³` around a compact
set have one positive uniform operator-norm bound on that set. The third norm
is the full curried trilinear norm. The compact set may be empty, and neither
space needs to be complete or finite dimensional. -/
theorem exists_pos_derivative_bounds_of_isCompact {f : E → F} {K : Set E}
    (hK : IsCompact K) (hf : ∀ x ∈ K, ContDiffAt ℝ 3 f x) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K,
      ‖fderiv ℝ f x‖ ≤ C ∧
      ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C ∧
      ContinuousLinearMap.opNorm (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E)
        (F := E →L[ℝ] E →L[ℝ] F) (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x) ≤ C := by
  let D₁ : E → E →L[ℝ] F := fderiv ℝ f
  let D₂ : E → E →L[ℝ] E →L[ℝ] F := fderiv ℝ D₁
  let D₃ : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] F := fderiv ℝ D₂
  have hreg₁ (x : E) (hx : x ∈ K) : ContDiffAt ℝ 2 D₁ x :=
    (hf x hx).fderiv_right (by decide)
  have hreg₂ (x : E) (hx : x ∈ K) : ContDiffAt ℝ 1 D₂ x :=
    (hreg₁ x hx).fderiv_right (by decide)
  have hc₁ : ContinuousOn D₁ K := fun x hx ↦
    (hreg₁ x hx).continuousAt.continuousWithinAt
  have hc₂ : ContinuousOn D₂ K := fun x hx ↦
    (hreg₂ x hx).continuousAt.continuousWithinAt
  have hc₃ : ContinuousOn D₃ K := fun x hx ↦
    ((hreg₂ x hx).continuousAt_fderiv one_ne_zero).continuousWithinAt
  obtain ⟨C₁, h₁⟩ := hK.exists_bound_of_continuousOn hc₁
  obtain ⟨C₂, h₂⟩ := @IsCompact.exists_bound_of_continuousOn E (E →L[ℝ] E →L[ℝ] F)
    (ContinuousLinearMap.toSeminormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
      (σ₁₂ := RingHom.id ℝ) (E := E) (F := E →L[ℝ] F)).toSeminormedAddGroup
    _ K hK D₂ hc₂
  obtain ⟨C₃, h₃⟩ := @IsCompact.exists_bound_of_continuousOn
    E (E →L[ℝ] E →L[ℝ] E →L[ℝ] F)
    (ContinuousLinearMap.toSeminormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
      (σ₁₂ := RingHom.id ℝ) (E := E) (F := E →L[ℝ] E →L[ℝ] F)).toSeminormedAddGroup
    _ K hK D₃ hc₃
  refine ⟨max 1 (max C₁ (max C₂ C₃)), zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro x hx
  refine ⟨(h₁ x hx).trans ((le_max_left _ _).trans (le_max_right _ _)),
    (h₂ x hx).trans ((le_max_left _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))), ?_⟩
  exact (h₃ x hx).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))

end PDE.Analysis
