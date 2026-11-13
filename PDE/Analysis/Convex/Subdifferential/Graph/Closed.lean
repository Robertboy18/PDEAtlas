/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convex.Proximal.Resolvent

/-!
# Strong/weak closure of the subdifferential graph

The resolvent proves maximality: a pair monotone against the whole graph already
belongs to it. Testing at the resolvent of `x + y` reduces this assertion to a negative
squared norm. Strong convergence of base points and bounded weak convergence of supporting
vectors then preserve graph membership. No separability assumption or countable family of
supporting inequalities is used.
-/

@[expose] public section

open Filter
open scoped Topology

namespace PDE.Analysis.Convex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {I : H → EReal} (hproper : IsProper I)
  (hconvex : Convex ℝ (realEpigraph I)) (hlsc : LowerSemicontinuous I)

include hproper hconvex hlsc

/-- A pair monotone against every subgradient belongs to the subdifferential graph. -/
theorem mem_subdifferential_of_monotone {x y : H}
    (hmono : ∀ z v, v ∈ subdifferential I z → 0 ≤ inner ℝ (y - v) (x - z)) :
    y ∈ subdifferential I x := by
  let z := resolvent I hproper hconvex hlsc 1 zero_lt_one (x + y)
  have hv : x + y - z ∈ subdifferential I z := by
    simpa only [inv_one, one_smul] using
      resolvent_residual_mem_subdifferential hproper hconvex hlsc zero_lt_one (x + y)
  have h := hmono z (x + y - z) hv
  have heq : y - (x + y - z) = -(x - z) := by abel
  rw [heq, inner_neg_left, real_inner_self_eq_norm_sq] at h
  have hxz : x = z := sub_eq_zero.1 (norm_eq_zero.1 (by
    nlinarith [norm_nonneg (x - z)]))
  simpa only [← hxz, add_sub_cancel_left] using hv

/-- The graph is closed for strong base-point convergence and bounded weak vector convergence.
The filter may be an ultrafilter; sequential compactness is not required. -/
theorem mem_subdifferential_of_tendsto_strong_weak
    {ι : Type*} {l : Filter ι} [l.NeBot] {x y : ι → H} {x₀ y₀ : H}
    (hx : Tendsto x l (𝓝 x₀))
    (hy : Tendsto (fun i ↦ toWeakSpace ℝ H (y i)) l (𝓝 (toWeakSpace ℝ H y₀)))
    (R : ℝ) (hR : ∀ i, ‖y i‖ ≤ R)
    (hgraph : ∀ᶠ i in l, y i ∈ subdifferential I (x i)) :
    y₀ ∈ subdifferential I x₀ := by
  apply mem_subdifferential_of_monotone hproper hconvex hlsc
  intro z v hv
  apply ge_of_tendsto
    (WeakCompactness.tendsto_inner_sub_of_tendsto_strong_weak hx hy R hR z v)
  filter_upwards [hgraph] with i hi
  exact subdifferential_monotone hproper hi hv

end PDE.Analysis.Convex
