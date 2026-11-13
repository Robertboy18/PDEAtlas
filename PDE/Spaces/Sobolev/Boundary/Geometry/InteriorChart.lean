/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Geometry.HalfSpace
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Interior sets as half-space chart patches

A bounded open set can be translated strictly into the upper half-space.
The resulting smooth chart has the entire open set as its source. Thus
an interior cutoff can use the same local analytic estimates as a boundary
cutoff, without meeting the flat boundary or changing the equation.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Boundary

open Set

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- A bounded open set admits a translation chart whose target is bounded
and lies strictly above the coordinate hyperplane. This includes the empty set. -/
theorem exists_interior_translation_chart (hΩ : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) :
    ∃ E : OpenPartialHomeomorph (ℝ^n) (ℝ^n),
      E.source = Ω ∧ ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ E x) ∧
      ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ E.symm y) ∧
      E.target ⊆ HalfSpace.upper n ∧ Bornology.IsBounded E.target := by
  obtain ⟨R, _, hR⟩ := hbounded.exists_pos_norm_le
  let v : ℝ^n := WithLp.toLp 2 (fun _ ↦ R + 1)
  let E := (Homeomorph.addRight v).toOpenPartialHomeomorph.restrOpen Ω hΩ
  have hsource : E.source = Ω := by
    simp only [E, OpenPartialHomeomorph.restrOpen_source,
      Homeomorph.toOpenPartialHomeomorph_source, univ_inter]
  have hE : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ E x) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ^n ↦ x + v)
    exact contDiff_id.add contDiff_const
  have hSymm : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ E.symm y) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ^n ↦ y + -v)
    exact contDiff_id.add contDiff_const
  have htarget : E.target = (fun x ↦ x + v) '' Ω := by
    rw [← E.image_source_eq_target, hsource]
    rfl
  refine ⟨E, hsource, hE, hSymm, ?_, ?_⟩
  · rw [htarget]
    rintro y ⟨x, hx, rfl⟩
    have hcoord := (PiLp.norm_apply_le x (PDE.Common.lastIndex (n := n))).trans (hR x hx)
    change |x (PDE.Common.lastIndex (n := n))| ≤ R at hcoord
    change 0 < x (PDE.Common.lastIndex (n := n)) + (R + 1)
    linarith [(abs_le.mp hcoord).1]
  · rw [htarget]
    exact (hbounded.isCompact_closure.image hE.continuous).isBounded.subset
      (image_mono subset_closure)

end SobolevSpace.Boundary
