/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convex.Real.Monge
public import PDE.Analysis.Order.Monotone.Fibers
public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Footpoint.AlmostEverywhere

/-!
# Ordered minimizing footpoints and countably many failures of uniqueness

Strict convexity of the cost orders every pair of attained minimizers at
different endpoints. Consequently any choice of a minimizer is monotone;
there is no need to choose the smallest minimizer. Disjoint intervals between
two minimizers give countability at each fixed positive time.

These are parts (i) and (ii) of Theorem 1 in Evans, §3.4.2: the minimizer is unique except at
countably many points, and the minimizing footpoint is nondecreasing in `x`.
The initial potential is Lipschitz and need not be convex.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.2, Theorem 1(i)-(ii).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open Set PDE.Analysis
open scoped NNReal

namespace HamiltonJacobi.HopfLax

/-- Every attained minimizer at an earlier endpoint is at most every attained
minimizer at a later endpoint. The primitive need not be convex. -/
theorem fixed_footpoint_le_of_lt {L h : ℝ → ℝ} (hL : Superlinear L)
    (hstrict : StrictConvexOn ℝ univ L) {K : ℝ≥0} (hh : LipschitzWith K h) {t x₁ x₂ y₁ y₂ : ℝ}
    (ht : 0 < t) (hx : x₁ < x₂) (hy₁ : value L h t x₁ = h y₁ + t * L ((x₁ - y₁) / t))
    (hy₂ : value L h t x₂ = h y₂ + t * L ((x₂ - y₂) / t)) :
    y₁ ≤ y₂ := by
  by_contra hnot
  have hcross := mul_lt_mul_of_pos_left (hstrict.crossing_sum_lt ht hx (lt_of_not_ge hnot)) ht
  have h₁ := value_le_fixed_footpoint hL hh ht x₁ y₂
  have h₂ := value_le_fixed_footpoint hL hh ht x₂ y₁
  rw [hy₁] at h₁
  rw [hy₂] at h₂
  nlinarith only [hcross, h₁, h₂]

/-- The chosen minimizing footpoint is monotone on each positive
time slice, including endpoints with more than one minimizer. -/
theorem monotone_minimizingFootpoint {L h : ℝ → ℝ} (hcont : Continuous L) (hL : Superlinear L)
    (hstrict : StrictConvexOn ℝ univ L) {K : ℝ≥0} (hh : LipschitzWith K h) {t : ℝ} (ht : 0 < t) :
    Monotone (minimizingFootpoint L h t) := by
  intro x₁ x₂ hx
  rcases hx.eq_or_lt with rfl | hx
  · exact le_rfl
  · exact fixed_footpoint_le_of_lt hL hstrict hh ht hx (minimizingFootpoint_spec hcont hL hh ht x₁)
      (minimizingFootpoint_spec hcont hL hh ht x₂)

/-- At each positive time only countably many endpoints fail to have a unique
attained footpoint. The exceptional set may depend on time. -/
theorem countable_not_existsUnique_fixed_footpoint {L h : ℝ → ℝ} (hcont : Continuous L)
    (hL : Superlinear L) (hstrict : StrictConvexOn ℝ univ L) {K : ℝ≥0} (hh : LipschitzWith K h)
    {t : ℝ} (ht : 0 < t) :
    {x | ¬ ∃! y, value L h t x = h y + t * L ((x - y) / t)}.Countable := by
  have hc := countable_not_subsingleton_of_ordered_fibers
    (S := fun x ↦ {y | value L h t x = h y + t * L ((x - y) / t)})
    (fun _ _ hx y₁ hy₁ y₂ hy₂ ↦ fixed_footpoint_le_of_lt hL hstrict hh ht hx hy₁ hy₂)
  apply hc.mono
  intro x hx hsub
  apply hx
  obtain ⟨y, hy⟩ := exists_value_eq_fixed_footpoint hcont hL hh ht x
  exact ⟨y, hy, fun z hz ↦ hsub hz hy⟩

end HamiltonJacobi.HopfLax
