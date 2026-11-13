/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SmoothFamily

/-!
# Smooth families composed with maps smooth on an open set

A smooth family of order `m` whose values lie in an open set `U` stays a smooth family of order
`m` after composition with a map that is `C^m` on `U`. In a complete normed algebra the inverse is
smooth on the open set of units, so a smooth family of invertible elements has a smooth family of
inverses.

## Main results

* `IsSmoothFamilyOn.comp_contDiffOn`: if the values of a smooth family `G` of order `m` lie in an
  open set `U` and `f` is `C^m` on `U`, then `f ∘ G` is a smooth family of order `m`.
* `IsSmoothFamilyOn.ringInverse`: in a complete normed algebra, a smooth family of invertible
  elements has a smooth family of inverses.
-/

@[expose] public section

noncomputable section

open Set Function ContinuousLinearMap

namespace PDE.Analysis

universe u

variable {P : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P] {m : ℕ} {I : Set ℝ}

namespace IsSmoothFamilyOn

/-- **Composition with a map smooth on an open set.** If the values of a smooth family `G` of
order `m` lie in an open set `U` and `f` is `C^m` on `U`, then `f ∘ G` is a smooth family of
order `m`. -/
theorem comp_contDiffOn {Q R : Type u} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup R] [NormedSpace ℝ R] {f : Q → R} {G : ℝ → P → Q} {U : Set Q}
    (hU : IsOpen U) (hf : ContDiffOn ℝ m f U) (hG : IsSmoothFamilyOn m G I)
    (hGU : ∀ r ∈ I, ∀ p, G r p ∈ U) : IsSmoothFamilyOn m (fun r p ↦ f (G r p)) I := by
  induction m generalizing R with
  | zero =>
    rw [isSmoothFamilyOn_zero_iff] at *
    exact hf.continuousOn.comp hG fun q hq ↦ hGU q.1 hq.1 q.2
  | succ m ih =>
    have hG' := hG.mono (Nat.le_succ m)
    have hfd : ContDiffOn ℝ m (fun y ↦ fderiv ℝ f y) U :=
      hf.fderiv_of_isOpen hU (by exact_mod_cast le_rfl)
    have hdiff : ∀ y ∈ U, DifferentiableAt ℝ f y := fun y hy ↦
      (hf.differentiableOn (by simp) y hy).differentiableAt (hU.mem_nhds hy)
    rw [isSmoothFamilyOn_succ_iff] at hG ⊢
    have hderiv (r : ℝ) (hr : r ∈ I) (p : P) :
        HasFDerivAt (fun y ↦ f (G r y))
          (compL ℝ P Q R (fderiv ℝ f (G r p)) (fderiv ℝ (G r) p)) p :=
      (hdiff _ (hGU r hr p)).hasFDerivAt.comp p (hG.1 r hr p).hasFDerivAt
    refine ⟨fun r hr p ↦ (hderiv r hr p).differentiableAt,
      hf.continuousOn.comp hG.2.1 fun q hq ↦ hGU q.1 hq.1 q.2,
      (bilinear (compL ℝ P Q R) (ih hfd hG') hG.2.2).congr fun r hr ↦ ?_⟩
    funext p
    exact ((hderiv r hr p).fderiv).symm

/-- **Inverses.** In a complete normed algebra, a smooth family of invertible elements has a
smooth family of inverses. -/
theorem ringInverse {A : Type u} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    {G : ℝ → P → A} (hG : IsSmoothFamilyOn m G I) (hunit : ∀ r ∈ I, ∀ p, IsUnit (G r p)) :
    IsSmoothFamilyOn m (fun r p ↦ Ring.inverse (G r p)) I := by
  refine comp_contDiffOn Units.isOpen (fun y hy ↦ ?_) hG hunit
  obtain ⟨y, rfl⟩ := hy
  exact (contDiffAt_ringInverse ℝ y).contDiffWithinAt

end IsSmoothFamilyOn

end PDE.Analysis
