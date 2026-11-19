/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Convex.Star
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Topology of star-convex sets

For fixed coefficients, a point on the segment from the center depends continuously on
the other endpoint. Passing that endpoint to the closure therefore preserves star-convexity.
Only continuity of addition and of multiplication by a fixed scalar is needed.

Moving an interior point toward the center also stays in the interior until the center
is reached: each nonconstant affine contraction is an open map. The center itself need
not be an interior point. Consequently the frontier points on each open ray from the
center form an interval.
-/

@[expose] public section

open Set

section Closure

variable {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommMonoid E] [SMul 𝕜 E] [TopologicalSpace E]
  [ContinuousAdd E] [ContinuousConstSMul 𝕜 E] {x : E} {s : Set E}

/-- Taking the closure preserves star-convexity about the same center. -/
protected theorem StarConvex.closure (hs : StarConvex 𝕜 x s) :
    StarConvex 𝕜 x (closure s) := by
  intro y hy a b ha hb hab
  have hf : Continuous (fun z : E ↦ a • x + b • z) :=
    continuous_const.add (continuous_id.const_smul b)
  exact map_mem_closure (f := fun z : E ↦ a • x + b • z) hf hy
    (fun z hz ↦ hs hz ha hb hab)

end Closure

section Interior

variable {𝕜 E : Type*} [Field 𝕜] [PartialOrder 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]
  {x y : E} {s : Set E} {a b : 𝕜}

/-- A segment from a star center to an interior point stays in the interior away from
the center. No interior assumption on the center is needed. -/
theorem StarConvex.combo_mem_interior (hs : StarConvex 𝕜 x s)
    (hy : y ∈ interior s) (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1) :
    a • x + b • y ∈ interior s := by
  have hopen : IsOpenMap (fun z : E ↦ a • x + b • z) :=
    (Homeomorph.addLeft (a • x)).isOpenMap.comp (isOpenMap_smul₀ hb.ne')
  have hsub : (fun z : E ↦ a • x + b • z) '' interior s ⊆ s := by
    rintro _ ⟨z, hz, rfl⟩
    exact hs (interior_subset hz) ha hb.le hab
  exact interior_maximal hsub (hopen _ isOpen_interior) ⟨y, hy, rfl⟩

end Interior

section Frontier

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]

/-- If `a • v` and `c • v` lie on the frontier of a set star-convex about `0` and
`0 < a ≤ b ≤ c`, then `b • v` lies on the frontier. Star-convexity of the closure puts
`b • v` in the closure, and if `b • v` were interior then so would be `a • v`. -/
theorem StarConvex.smul_mem_frontier_of_between {s : Set E} {v : E}
    (hs : StarConvex 𝕜 0 s) {a b c : 𝕜} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hax : a • v ∈ frontier s) (hcx : c • v ∈ frontier s) :
    b • v ∈ frontier s := by
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := hb.trans_le hbc
  refine ⟨?_, ?_⟩
  · have hratio : b / c ≤ 1 := (div_le_one hc).mpr hbc
    have h := hs.closure hcx.1 (a := 1 - b / c) (b := b / c)
      (sub_nonneg.mpr hratio) (div_nonneg hb.le hc.le) (sub_add_cancel 1 _)
    simpa only [smul_zero, zero_add, smul_smul, div_mul_cancel₀ _ hc.ne'] using h
  · intro hbx
    have hratio : a / b ≤ 1 := (div_le_one hb).mpr hab
    have h := hs.combo_mem_interior hbx (a := 1 - a / b) (b := a / b)
      (sub_nonneg.mpr hratio) (div_pos ha hb) (sub_add_cancel 1 _)
    apply hax.2
    simpa only [smul_zero, zero_add, smul_smul, div_mul_cancel₀ _ hb.ne'] using h

end Frontier
