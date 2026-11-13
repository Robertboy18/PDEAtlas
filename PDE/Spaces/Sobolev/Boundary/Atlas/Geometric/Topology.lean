/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convex.Star.Topology
public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.GraphBoundary
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-!
# Topology of domains with graph boundary

An open domain with a graph boundary is the interior of its closure. Locally this is
the same statement for a half-space, transported by a boundary chart. No boundedness
or global extension atlas is needed.

Consequently, if the closure is star-shaped, each positive contraction toward a star
center sends the open domain into itself. The center may lie on the boundary.
-/

@[expose] public section

open Set

namespace SobolevSpace.Boundary

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- An open domain with a local C1 graph boundary is the interior of its closure. -/
theorem HasC1GraphBoundary.interior_closure (hΩ : HasC1GraphBoundary Ω)
    (hopen : IsOpen Ω) : interior (closure Ω) = Ω := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Fact.out : 0 < n))
  apply Subset.antisymm
  · intro x hx
    by_contra hxΩ
    have hxfront : x ∈ frontier Ω := by
      rw [hopen.frontier_eq]
      exact ⟨interior_subset hx, hxΩ⟩
    obtain ⟨e, hxe, _, _, hside⟩ := hΩ.local_flattening_charts x hxfront
    have himage : e.IsImage Ω (HalfSpace.upper (m + 1)) :=
      fun y hy ↦ (hside y hy).symm
    have hy : e x ∈ interior (closure (HalfSpace.upper (m + 1))) :=
      (himage.closure.interior.apply_mem_iff hxe).mpr hx
    have hnonempty : (interior (HalfSpace.upper (m + 1))).Nonempty := by
      rw [(HalfSpace.isOpen_upper (m + 1)).interior_eq]
      exact ⟨EuclideanSpace.single (PDE.Common.lastIndex (n := m + 1)) 1, by
        simp [HalfSpace.upper]⟩
    rw [(HalfSpace.convex_upper (m + 1)).interior_closure_eq_interior_of_nonempty_interior
      hnonempty, (HalfSpace.isOpen_upper (m + 1)).interior_eq] at hy
    exact hxΩ ((himage.apply_mem_iff hxe).mp hy)
  · exact interior_maximal subset_closure hopen

/-- Positive contractions toward a star center of the closed domain preserve the open
domain. At factor zero the center can be a boundary point, so that case is excluded. -/
theorem HasC1GraphBoundary.homothety_mem_of_starConvex_closure
    (hΩ : HasC1GraphBoundary Ω) (hopen : IsOpen Ω)
    {c x : ℝ^n} (hstar : StarConvex ℝ c (closure Ω)) (hx : x ∈ Ω)
    {t : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1) :
    (1 - t) • c + t • x ∈ Ω := by
  rw [← hΩ.interior_closure hopen] at hx ⊢
  exact hstar.combo_mem_interior hx (sub_nonneg.mpr ht₁) ht (sub_add_cancel 1 t)

/-- A scalar dilation of functions by a factor at least one contracts their domain
toward the origin. A boundary star center is allowed. -/
theorem HasC1GraphBoundary.preimage_smul_subset_of_starConvex_closure
    (hΩ : HasC1GraphBoundary Ω) (hopen : IsOpen Ω)
    (hstar : StarConvex ℝ 0 (closure Ω)) {a : ℝ} (ha : 1 ≤ a) :
    (fun x : ℝ^n ↦ a • x) ⁻¹' Ω ⊆ Ω := by
  intro x hx
  have ha₀ : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have h := hΩ.homothety_mem_of_starConvex_closure hopen hstar hx
    (inv_pos.mpr ha₀) ((inv_le_one₀ ha₀).mpr ha)
  simpa only [smul_zero, zero_add, smul_smul, inv_mul_cancel₀ ha₀.ne', one_smul] using h

end SobolevSpace.Boundary
