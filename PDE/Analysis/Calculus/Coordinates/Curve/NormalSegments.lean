/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.OpenPartialHomeomorph.Defs

/-!
# Normal segments in a fixed transverse curve chart

The supplied chart has forward formula `e(t, y) = γ t + y` on its source,
where `y` belongs to the kernel of a fixed covector. Its inverse identities
therefore determine both coordinates along every normal segment whose lift
stays in the source. A convex normal section of a product tube guarantees
this containment.

The last theorem evaluates the same uncut quadratic expression used by the
quadratic tube jet construction. No chart, curve, bilinear family, or ambient
extension is selected here.
-/

@[expose] public noncomputable section

open Set

namespace PDE.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A lifted closed normal segment in the chart source has constant inverse time
coordinate and linearly varying normal coordinate. The ambient distance from
its base is exactly the norm of that normal coordinate, including both endpoints.

The source condition concerns `(t, a • y)` in the coordinate space; the ambient
segment's containment in `e.target` is a conclusion. -/
theorem curve_chart_normal_segment
    {γ : ℝ → E} {ell : E →L[ℝ] ℝ}
    {e : OpenPartialHomeomorph (ℝ × ell.ker) E} {t : ℝ} {y : ell.ker}
    (he : EqOn e (fun p ↦ γ p.1 + (p.2 : E)) e.source)
    (hsource : ∀ a ∈ Icc (0 : ℝ) 1, (t, a • y) ∈ e.source) :
    segment ℝ (γ t) (γ t + (y : E)) ⊆ e.target ∧
      ∀ a ∈ Icc (0 : ℝ) 1,
        e.symm (AffineMap.lineMap (γ t) (γ t + (y : E)) a) = (t, a • y) ∧
        ‖((e.symm (AffineMap.lineMap (γ t) (γ t + (y : E)) a)).2 : E)‖ =
          ‖AffineMap.lineMap (γ t) (γ t + (y : E)) a - γ t‖ ∧
        ‖AffineMap.lineMap (γ t) (γ t + (y : E)) a - γ t‖ = a * ‖(y : E)‖ := by
  have hline (a : ℝ) : AffineMap.lineMap (γ t) (γ t + (y : E)) a =
      γ t + a • (y : E) := by
    rw [AffineMap.lineMap_apply_module', add_sub_cancel_left, add_comm]
  have hforward (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) :
      e (t, a • y) = AffineMap.lineMap (γ t) (γ t + (y : E)) a := by
    calc
      e (t, a • y) = γ t + a • (y : E) := he (hsource a ha)
      _ = AffineMap.lineMap (γ t) (γ t + (y : E)) a := (hline a).symm
  refine ⟨?_, ?_⟩
  · intro q hq
    rw [segment_eq_image_lineMap ℝ] at hq
    obtain ⟨a, ha, rfl⟩ := hq
    rw [← hforward a ha]
    exact e.map_source (hsource a ha)
  · intro a ha
    have hinv : e.symm (AffineMap.lineMap (γ t) (γ t + (y : E)) a) =
        (t, a • y) := by
      rw [← hforward a ha]
      exact e.left_inv (hsource a ha)
    have hnormal : ((e.symm (AffineMap.lineMap (γ t) (γ t + (y : E)) a)).2 : E) =
        a • (y : E) :=
      congrArg (fun p : ℝ × ell.ker ↦ (p.2 : E)) hinv
    have hdiff : AffineMap.lineMap (γ t) (γ t + (y : E)) a - γ t =
        a • (y : E) := by
      rw [hline, add_sub_cancel_left]
    refine ⟨hinv, ?_, ?_⟩
    · rw [hnormal, hdiff]
    · rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha.1]

/-- A convex normal section containing zero keeps each closed normal segment
inside the image of the same product tube. The time set need not be convex or
open; open balls and closed balls about zero are both admissible normal sections. -/
theorem curve_chart_normal_segment_subset_image_prod
    {γ : ℝ → E} {ell : E →L[ℝ] ℝ}
    {e : OpenPartialHomeomorph (ℝ × ell.ker) E} {J : Set ℝ} {K : Set ell.ker}
    {t : ℝ} {y : ell.ker}
    (he : EqOn e (fun p ↦ γ p.1 + (p.2 : E)) e.source)
    (hsource : J ×ˢ K ⊆ e.source) (hK : Convex ℝ K) (hzero : (0 : ell.ker) ∈ K)
    (ht : t ∈ J) (hy : y ∈ K) :
    segment ℝ (γ t) (γ t + (y : E)) ⊆ e '' (J ×ˢ K) := by
  have hlift (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) : (t, a • y) ∈ J ×ˢ K :=
    ⟨ht, hK.smul_mem_of_zero_mem hzero hy ha⟩
  obtain ⟨htarget, hcoord⟩ := curve_chart_normal_segment he
    (fun a ha ↦ hsource (hlift a ha))
  intro q hq
  have hqtarget := htarget hq
  rw [segment_eq_image_lineMap ℝ] at hq
  obtain ⟨a, ha, rfl⟩ := hq
  refine ⟨(t, a • y), hlift a ha, ?_⟩
  rw [← (hcoord a ha).1]
  exact e.right_inv hqtarget

/-- Along a normal segment, the actual uncut quadratic in the inverse chart
uses the fixed coefficient `B t` and scales quadratically in the segment parameter.
No symmetry, differentiability, or tangent-annihilation assumption is needed
for this value identity. -/
theorem curve_chart_quadratic_lineMap
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {γ : ℝ → E} {ell : E →L[ℝ] ℝ}
    {e : OpenPartialHomeomorph (ℝ × ell.ker) E} {t : ℝ} {y : ell.ker}
    (B : ℝ → E →L[ℝ] E →L[ℝ] F)
    (he : EqOn e (fun p ↦ γ p.1 + (p.2 : E)) e.source)
    (hsource : ∀ a ∈ Icc (0 : ℝ) 1, (t, a • y) ∈ e.source) :
    let Q : E → F := fun x ↦
      (1 / 2 : ℝ) • B (e.symm x).1 ((e.symm x).2 : E) ((e.symm x).2 : E)
    ∀ a ∈ Icc (0 : ℝ) 1,
      Q (AffineMap.lineMap (γ t) (γ t + (y : E)) a) =
        a ^ 2 • ((1 / 2 : ℝ) • B t (y : E) (y : E)) := by
  dsimp only
  intro a ha
  have hcoord := ((curve_chart_normal_segment he hsource).2 a ha).1
  rw [hcoord]
  change (1 / 2 : ℝ) • B t (a • (y : E)) (a • (y : E)) =
    a ^ 2 • ((1 / 2 : ℝ) • B t (y : E) (y : E))
  simp only [map_smul, smul_apply, smul_smul, pow_two, mul_comm]

end PDE.Analysis
