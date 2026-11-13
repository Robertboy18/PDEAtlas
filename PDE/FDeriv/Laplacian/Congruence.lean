/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Operators
import PDE.FDeriv.Calculus

/-!
# Locality of the coordinate Laplacian

The Laplacian at a point depends only on the function near that point, for maps into any real
normed space. In
particular, differentiation cannot enlarge its closed support. These facts
apply to cutoffs even when the original function has no regularity outside
the region being studied.
-/

@[expose] public section

open PDE (partialDeriv laplacian)

open Filter Topology

namespace EuclideanLaplacian

/-- Maps into a real normed space that agree on a neighborhood of `x` have the same Laplacian
at `x`. -/
theorem laplacian_congr_nhds {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ^n → E} {x : ℝ^n}
    (h : f =ᶠ[nhds x] g) :
    laplacian f x = laplacian g x := by
  unfold laplacian
  exact Finset.sum_congr rfl fun i _ ↦
    PDE.partialDeriv_second_congr_nhds (n := n) i h

/-- The Laplacian vanishes outside the closed support, without a smoothness
assumption on the function. -/
theorem laplacian_eq_zero_of_notMem_tsupport {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ^n → E} {x : ℝ^n}
    (hx : x ∉ tsupport f) : laplacian f x = 0 := by
  simpa [laplacian, partialDeriv] using
    laplacian_congr_nhds (notMem_tsupport_iff_eventuallyEq.mp hx)

end EuclideanLaplacian

/-- Taking the coordinate Laplacian preserves compact support. -/
theorem HasCompactSupport.coordinate_laplacian {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ^n → E}
    (hf : HasCompactSupport f) : HasCompactSupport (laplacian f) :=
  HasCompactSupport.intro hf fun _ hx ↦
    EuclideanLaplacian.laplacian_eq_zero_of_notMem_tsupport hx
