/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Comp

import Mathlib.Analysis.Calculus.MeanValue
import PDE.Analysis.Calculus.Coordinates.Curve.NormalSegments
import PDE.Analysis.Calculus.LocalExtension.CompactDerivativeBounds

/-!
# Derivative variation in a fixed compact curve tube

A compact product tube supplies one uniform bound for the actual derivatives of a locally
`C³` map. Each closed normal segment remains in this same tube. The mean value inequality
for the first and second derivative maps therefore bounds both variations by the smaller
normal radius, with one constant chosen before that radius and the evaluation point.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace PDE.Analysis

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The Jacobian and full Hessian vary by at most `C * δ` from the curve base of every
point in a smaller closed tube. The constant depends on the fixed map and compact tube,
but is chosen before `δ` and the point. The time set need not be an interval.

Compactness of the normal closed ball is explicit; no completeness or finite-dimensional
instance is required. Regularity is ambient at points of the fixed tube, with no condition
elsewhere. Zero radius is included, and a negative smaller radius gives an empty tube. -/
theorem exists_pos_compact_tube_derivative_variation_bounds
    {f : E → F} {γ : ℝ → E} {ell : E →L[ℝ] ℝ}
    {e : OpenPartialHomeomorph (ℝ × ell.ker) E} {T : Set ℝ} {ρ : ℝ}
    (hT : IsCompact T) (hball : IsCompact (Metric.closedBall (0 : ell.ker) ρ))
    (hρ : 0 < ρ)
    (he : EqOn e (fun p ↦ γ p.1 + (p.2 : E)) e.source)
    (hsource : T ×ˢ Metric.closedBall (0 : ell.ker) ρ ⊆ e.source)
    (hf : ∀ x ∈ e '' (T ×ˢ Metric.closedBall (0 : ell.ker) ρ),
      ContDiffAt ℝ 3 f x) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, δ ≤ ρ →
      ∀ x ∈ e '' (T ×ˢ Metric.closedBall (0 : ell.ker) δ),
        ‖fderiv ℝ f x - fderiv ℝ f (γ (e.symm x).1)‖ ≤ C * δ ∧
          ‖fderiv ℝ (fderiv ℝ f) x -
            fderiv ℝ (fderiv ℝ f) (γ (e.symm x).1)‖ ≤ C * δ := by
  let K : Set E := e '' (T ×ˢ Metric.closedBall (0 : ell.ker) ρ)
  have hK : IsCompact K :=
    (hT.prod hball).image_of_continuousOn (e.continuousOn.mono hsource)
  obtain ⟨C, hC, hbounds⟩ := exists_pos_derivative_bounds_of_isCompact
    (E := E) (F := F) (f := f) (K := K) hK hf
  refine ⟨C, hC, ?_⟩
  intro δ hδ x hx
  obtain ⟨⟨t, y⟩, hmem, rfl⟩ := hx
  have hyρ : y ∈ Metric.closedBall (0 : ell.ker) ρ :=
    Metric.closedBall_subset_closedBall hδ hmem.2
  have hs : (t, y) ∈ e.source := hsource ⟨hmem.1, hyρ⟩
  have hforward : e (t, y) = γ t + (y : E) := he hs
  have htime : (e.symm (e (t, y))).1 = t := congrArg Prod.fst (e.left_inv hs)
  -- The fixed tube contains the entire segment, even at either closed endpoint.
  have hsegment : segment ℝ (γ t) (e (t, y)) ⊆ K := by
    rw [hforward]
    exact curve_chart_normal_segment_subset_image_prod he hsource
      (convex_closedBall (0 : ell.ker) ρ) (Metric.mem_closedBall_self hρ.le) hmem.1 hyρ
  have hdist : ‖e (t, y) - γ t‖ ≤ δ := by
    rw [hforward, add_sub_cancel_left]
    change ‖y‖ ≤ δ
    exact mem_closedBall_zero_iff.mp hmem.2
  have hreg₁ (q : E) (hq : q ∈ segment ℝ (γ t) (e (t, y))) :
      ContDiffAt ℝ 2 (fderiv ℝ f) q :=
    (hf q (hsegment hq)).fderiv_right (by decide)
  have hreg₂ (q : E) (hq : q ∈ segment ℝ (γ t) (e (t, y))) :
      ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ f)) q :=
    (hreg₁ q hq).fderiv_right (by decide)
  have hfirst : ‖fderiv ℝ f (e (t, y)) - fderiv ℝ f (γ t)‖ ≤
      C * ‖e (t, y) - γ t‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := ℝ) (E := E) (G := E →L[ℝ] F) (f := fderiv ℝ f)
      (s := segment ℝ (γ t) (e (t, y))) (x := γ t) (y := e (t, y)) (C := C)
      (fun q hq ↦ (hreg₁ q hq).differentiableAt (by decide))
      (fun q hq ↦ (hbounds q (hsegment hq)).2.1)
      (convex_segment (γ t) (e (t, y)))
      (left_mem_segment ℝ (γ t) (e (t, y))) (right_mem_segment ℝ (γ t) (e (t, y)))
  have hsecond : ‖fderiv ℝ (fderiv ℝ f) (e (t, y)) -
      fderiv ℝ (fderiv ℝ f) (γ t)‖ ≤ C * ‖e (t, y) - γ t‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := ℝ) (E := E) (G := E →L[ℝ] E →L[ℝ] F)
      (f := fderiv ℝ (fderiv ℝ f))
      (s := segment ℝ (γ t) (e (t, y))) (x := γ t) (y := e (t, y)) (C := C)
      (fun q hq ↦ (hreg₂ q hq).differentiableAt_one)
      (fun q hq ↦ (hbounds q (hsegment hq)).2.2)
      (convex_segment (γ t) (e (t, y)))
      (left_mem_segment ℝ (γ t) (e (t, y))) (right_mem_segment ℝ (γ t) (e (t, y)))
  rw [htime]
  exact ⟨hfirst.trans (mul_le_mul_of_nonneg_left hdist hC.le),
    hsecond.trans (mul_le_mul_of_nonneg_left hdist hC.le)⟩

end PDE.Analysis
