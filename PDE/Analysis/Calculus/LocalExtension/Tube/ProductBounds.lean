/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Coordinates.Curve.NormalSegments
public import PDE.Analysis.Calculus.LocalExtension.Logarithmic.NormalProduct

import PDE.Analysis.Calculus.LocalExtension.CompactDerivativeBounds

/-!
# Uniform cutoff product bounds on a fixed compact tube

The supplied affine chart and its pilot radius remain fixed. Compactness bounds
all required derivatives of the actual function and inverse normal coordinate
before either cutoff parameter is chosen. Closed normal segments stay inside
that same pilot image, so the existing radial product estimate applies with one
constant on every smaller closed tube.

The coefficient in the Hessian estimate is the supplied base Hessian evaluated
at the actual inverse time coordinate. Its size is not assumed small. Compact
zero extension and transfer of these estimates by local equality are separate
applications.
-/

@[expose] public noncomputable section

open Metric Set
open scoped ContDiff

namespace PDE.Analysis

/-- On a fixed compact product tube, the actual logarithmic normal cutoff product
has uniformly small value and first derivative, and its Hessian differs from the
cutoff multiple of the base Hessian by at most `C * δ + C / L`.

The constant is chosen before `δ,L`. The pilot and smaller normal balls are
closed, and zero normal displacement is allowed. Local ambient `C³` regularity
is sufficient; the target needs neither completeness nor finite dimension. -/
theorem exists_pos_compact_tube_radial_product_bounds
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {γ : ℝ → E} {ell : E →L[ℝ] ℝ}
    {e : OpenPartialHomeomorph (ℝ × ell.ker) E}
    {T : Set ℝ} {ρ : ℝ} {Q : E → F}
    {B : ℝ → E →L[ℝ] E →L[ℝ] F}
    (hT : IsCompact T) (hρ : 0 < ρ)
    (he : EqOn e (fun p ↦ γ p.1 + (p.2 : E)) e.source)
    (hsource : T ×ˢ closedBall (0 : ell.ker) ρ ⊆ e.source)
    (hQ : ∀ x ∈ e '' (T ×ˢ closedBall (0 : ell.ker) ρ),
      ContDiffAt ℝ 3 Q x)
    (hz : ∀ x ∈ e '' (T ×ˢ closedBall (0 : ell.ker) ρ),
      ContDiffAt ℝ 3 (fun y : E ↦ ((e.symm y).2 : E)) x)
    (hzero : ∀ t ∈ T, Q (γ t) = 0)
    (hDzero : ∀ t ∈ T, fderiv ℝ Q (γ t) = 0)
    (hHbase : ∀ t ∈ T, fderiv ℝ (fderiv ℝ Q) (γ t) = B t) :
    let z : E → E := fun x ↦ ((e.symm x).2 : E)
    ∃ C : ℝ, 0 < C ∧ ∀ δ L : ℝ,
      0 < δ → δ ≤ min ρ 1 → 1 ≤ L →
      ∀ x ∈ e '' (T ×ˢ closedBall (0 : ell.ker) δ),
        ‖radialLogarithmicCutoff δ L (z x) • Q x‖ ≤ C * δ ^ 2 ∧
        ‖fderiv ℝ
          (fun y ↦ radialLogarithmicCutoff δ L (z y) • Q y) x‖ ≤ C * δ ∧
        ‖fderiv ℝ (fderiv ℝ
            (fun y ↦ radialLogarithmicCutoff δ L (z y) • Q y)) x -
          radialLogarithmicCutoff δ L (z x) • B (e.symm x).1‖ ≤
            C * δ + C / L := by
  let z : E → E := fun x ↦ ((e.symm x).2 : E)
  let Kpilot : Set E := e '' (T ×ˢ closedBall (0 : ell.ker) ρ)
  have hKpilot : IsCompact Kpilot :=
    (hT.prod (isCompact_closedBall (0 : ell.ker) ρ)).image_of_continuousOn
      (e.continuousOn.mono hsource)
  obtain ⟨CQ, hCQ, hQbounds⟩ :=
    exists_pos_derivative_bounds_of_isCompact (f := Q) hKpilot hQ
  obtain ⟨Cz, hCz, hzBounds⟩ :=
    exists_pos_derivative_bounds_of_isCompact (f := z) hKpilot hz
  obtain ⟨C, hC, hproduct⟩ :=
    exists_pos_radial_cutoff_product_bounds (D := E) (E := E) (F := F)
      (M := CQ) (K := CQ) (A := Cz) (B := Cz) hCQ.le hCQ.le hCz.le
  refine ⟨C, hC, ?_⟩
  intro δ L hδ hδsmall hL x hx
  have hδρ : δ ≤ ρ := hδsmall.trans (min_le_left _ _)
  have hδone : δ ≤ 1 := hδsmall.trans (min_le_right _ _)
  rcases hx with ⟨⟨t, y⟩, hty, htx⟩
  have hyρ : y ∈ closedBall (0 : ell.ker) ρ :=
    closedBall_subset_closedBall hδρ hty.2
  have hsrc : (t, y) ∈ e.source := hsource ⟨hty.1, hyρ⟩
  have hxpilot : x ∈ Kpilot := ⟨(t, y), ⟨hty.1, hyρ⟩, htx⟩
  have hforward : x = γ t + (y : E) := htx.symm.trans (he hsrc)
  have hinv : e.symm x = (t, y) := by
    rw [← htx]
    exact e.left_inv hsrc
  have hsegment : segment ℝ (γ t) x ⊆ Kpilot := by
    rw [hforward]
    exact curve_chart_normal_segment_subset_image_prod he hsource
      (convex_closedBall (0 : ell.ker) ρ) (mem_closedBall_self hρ.le) hty.1 hyρ
  have hbasepilot : γ t ∈ Kpilot := hsegment (left_mem_segment ℝ (γ t) x)
  have hdist : ‖z x‖ = ‖x - γ t‖ := by
    change ‖((e.symm x).2 : E)‖ = ‖x - γ t‖
    rw [hinv, hforward, add_sub_cancel_left]
  have hrδ : ‖x - γ t‖ ≤ δ := by
    rw [hforward, add_sub_cancel_left]
    exact mem_closedBall_zero_iff.mp hty.2
  have hz₂ : ContDiffAt ℝ 2 z x := (hz x hxpilot).of_le (by decide)
  have hbounds := hproduct δ L hδ hδone hL z Q (γ t) x hz₂
    (hzBounds x hxpilot).1 (hzBounds x hxpilot).2.1 hdist hrδ
    (fun q hq ↦ hQ q (hsegment hq))
    (fun q hq ↦ (hQbounds q (hsegment hq)).2.2)
    (hzero t hty.1) (hDzero t hty.1) (hQbounds (γ t) hbasepilot).2.1
  simpa only [z, hHbase t hty.1, hinv] using hbounds

end PDE.Analysis
