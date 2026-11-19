/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Integrated.Solution

/-!
# Changing a form on a null set

The integrated weak evolution equation is unchanged by almost-everywhere equality
of the forms. This allows an essentially bounded Gårding form to be given a uniformly
bounded representative before constructing finite-dimensional trajectories.
-/

@[expose] public section

open MeasureTheory

namespace PDE.Analysis.Evolution

/-- Almost-everywhere equality of the forms preserves the integrated weak equation. -/
theorem IsGelfandIntegratedWeakSolution.congr_form_ae
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {B₁ B₂ : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))} {uInit : H}
    (h : B₁ =ᵐ[volume.restrict (Set.Ioc a b)] B₂)
    (hu : IsGelfandIntegratedWeakSolution T B₁ ell u uInit) :
    IsGelfandIntegratedWeakSolution T B₂ ell u uInit := by
  have heq (v : V) (τ : TimeTest a b) :
      (fun t ↦ B₁ t (u t) v * τ.toLp t) =ᵐ[volume.restrict (Set.Ioc a b)]
        (fun t ↦ B₂ t (u t) v * τ.toLp t) :=
    h.mono fun _ ht ↦ by dsimp only; rw [ht]
  refine ⟨hu.interval_nonempty, ?_, hu.integrable_forcing, ?_⟩
  · intro v τ
    exact (hu.integrable_form v τ).congr (heq v τ)
  · intro v τ
    rw [← integral_congr_ae (heq v τ)]
    exact hu.equation v τ

end PDE.Analysis.Evolution
