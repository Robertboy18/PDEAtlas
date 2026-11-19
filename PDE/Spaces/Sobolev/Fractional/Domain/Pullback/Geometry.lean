/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Pullback.Estimates
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.GraphOperator
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# C1 charts supply the fractional pullback constants

The atlas uses total C1 maps which are inverse on their open source and target.
A bounded target has bounded source, since the continuous inverse maps its
compact closure into a compact set. The forward map is Lipschitz on a closed
ball containing the source, and the inverse Jacobian is bounded on the compact
target closure. Thus the intrinsic estimates need no bounded Sobolev operator as a hypothesis.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace SobolevSpace.Fractional.Pullback

variable {n : ℕ} {s : ℝ} {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}

/-- Global C1 regularity gives a Lipschitz bound on any bounded set in Euclidean space. -/
theorem exists_lipschitzOnWith_of_contDiff_of_bounded
    {f : ℝ^n → ℝ^n} (hf : ContDiff ℝ 1 f)
    {A : Set (ℝ^n)} (hA : Bornology.IsBounded A) :
    ∃ L : ℝ≥0, LipschitzOnWith L f A := by
  obtain ⟨r, hr⟩ := hA.subset_closedBall (0 : ℝ^n)
  obtain ⟨L, hL⟩ := hf.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall (0 : ℝ^n) r) (isCompact_closedBall (0 : ℝ^n) r)
  exact ⟨L, hL.mono hr⟩

/-- The inverse Jacobian has a finite uniform bound on a bounded chart target. -/
theorem exists_det_bound_of_contDiff
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hTarget : Bornology.IsBounded E.target) :
    ∃ D : ℝ≥0, ∀ y ∈ E.target, |(fderiv ℝ (fun z ↦ E.symm z) y).det| ≤ D := by
  let J : ℝ^n → ℝ := fun y ↦ |(fderiv ℝ (fun z ↦ E.symm z) y).det|
  have hJ : Continuous J :=
    continuous_abs.comp (ContinuousLinearMap.continuous_det.comp
      (hSymm.continuous_fderiv (by simp)))
  have hB : BddAbove (J '' closure E.target) :=
    (hTarget.isCompact_closure.image hJ).bddAbove
  refine ⟨⟨max 1 (sSup (J '' closure E.target)), by positivity⟩, ?_⟩
  intro y hy
  exact (le_csSup hB ⟨y, subset_closure hy, rfl⟩).trans (le_max_right _ _)

/-- The geometric hypotheses of a bounded C1 chart provide both constants
in the intrinsic fractional pullback estimate. -/
theorem exists_pullback_bounds_of_contDiff
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hTarget : Bornology.IsBounded E.target) :
    ∃ L D : ℝ≥0, LipschitzOnWith L E E.source ∧
      Measure.map E (volume.restrict E.source) ≤
        (D : ℝ≥0∞) • volume.restrict E.target := by
  obtain ⟨L, hL⟩ := exists_lipschitzOnWith_of_contDiff_of_bounded hE
    (WeakChangeOfVariables.isBounded_source_of_isBounded_target hSymm.continuous hTarget)
  obtain ⟨D, hD⟩ := exists_det_bound_of_contDiff hSymm hTarget
  exact ⟨L, D, hL, map_restrict_le_of_det_le hE.continuous.measurable
    (hSymm.differentiable (by simp)) hD⟩

/-- Composition with a bounded C1 chart preserves intrinsic fractional membership
for real normed codomains, including exponent infinity and dimension zero. -/
theorem memGagliardo_comp_of_contDiff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞}
    (hs : 0 ≤ (n : ℝ) / p.toReal + s)
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hTarget : Bornology.IsBounded E.target)
    {u : ℝ^n → F} (hu : MemGagliardo n s E.target u (p := p)) :
    MemGagliardo n s E.source (u ∘ E) (p := p) := by
  obtain ⟨L, D, hL, hD⟩ := exists_pullback_bounds_of_contDiff hE hSymm hTarget
  exact memGagliardo_comp hs hE.continuous.measurable hL hD hu

end SobolevSpace.Fractional.Pullback
