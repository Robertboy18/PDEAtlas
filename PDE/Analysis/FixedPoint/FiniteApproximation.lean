/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Convex.PartitionOfUnity
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Finite-dimensional approximations on compact sets

A compact subset of a real normed space admits continuous approximations to its inclusion,
with arbitrarily small uniform error and values in the convex hull of finitely many of its
points. A finite ball cover supplies local constant choices, and Mathlib's
`exists_continuous_forall_mem_convex_of_local_const`, proved with a partition of unity,
combines them while preserving both the convex hull and the error ball.

The approximations are in general not linear, and the compact set need not be convex. They
are step 1 of Evans's proof of Schauder's theorem (§9.2.2, Theorem 3), where the map is
written down explicitly with distance weights and satisfies the estimate (16).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.2.2, step 1 of the proof of Theorem 3, (15)-(16),
  p. 538. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open Set Metric
open scoped Topology

namespace PDE.FixedPoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E}

/-- The inclusion of a compact set can be approximated continuously, with error strictly less
than `ε` everywhere, by a map into the convex hull of finitely many points of that set. -/
theorem exists_continuous_finite_convexHull_approximation (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset E, (↑s : Set E) ⊆ K ∧
      ∃ p : C(K, E), ∀ x : K, p x ∈ convexHull ℝ (↑s : Set E) ∧ ‖p x - (x : E)‖ < ε := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨s, hsK, hs, hcover⟩ := hK.finite_cover_balls hε
  obtain ⟨p, hp⟩ := exists_continuous_forall_mem_convex_of_local_const
    (t := fun x : K ↦ convexHull ℝ s ∩ ball (x : E) ε)
    (fun x ↦ (convex_convexHull ℝ s).inter (convex_ball (x : E) ε)) (by
      intro x
      obtain ⟨c, hcs, hxc⟩ := mem_iUnion₂.mp (hcover x.property)
      refine ⟨c, ?_⟩
      have hnear : ∀ᶠ y : K in 𝓝 x, (y : E) ∈ ball c ε :=
        continuous_subtype_val.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds hxc)
      filter_upwards [hnear] with y hy
      exact ⟨subset_convexHull ℝ s hcs, by simpa only [mem_ball, dist_comm] using hy⟩)
  refine ⟨hs.toFinset, by simpa using hsK, p, ?_⟩
  intro x
  simpa only [hs.coe_toFinset, mem_inter_iff, mem_ball, dist_eq_norm] using hp x

/-- The approximation may be viewed as a continuous map into a finite-dimensional subspace.
Its values remain in the convex hull of the original compact set. -/
theorem exists_continuous_finiteDimensional_approximation (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ V : Submodule ℝ E, FiniteDimensional ℝ V ∧
      ∃ p : C(K, V), ∀ x : K, (p x : E) ∈ convexHull ℝ K ∧ ‖(p x : E) - (x : E)‖ < ε := by
  obtain ⟨s, hsK, p, hp⟩ := exists_continuous_finite_convexHull_approximation hK hε
  let V := Submodule.span ℝ (↑s : Set E)
  have hpV (x : K) : p x ∈ V :=
    convexHull_min Submodule.subset_span V.convex (hp x).1
  refine ⟨V, FiniteDimensional.span_of_finite ℝ s.finite_toSet,
    ⟨fun x ↦ ⟨p x, hpV x⟩, p.continuous.subtype_mk hpV⟩, ?_⟩
  intro x
  exact ⟨convexHull_mono hsK (hp x).1, (hp x).2⟩

end PDE.FixedPoint
