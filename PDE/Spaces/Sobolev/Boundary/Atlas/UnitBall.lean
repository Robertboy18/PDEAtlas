/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Construction

/-!
# A finite smooth boundary cover of the Euclidean unit ball

For every dimension we construct the geometric and partition-of-unity
part of an operational extension atlas for the open unit ball. In positive
dimension, the boundary neighborhoods are the `2n` bounded signed coordinate
graph caps

`{x | 0 < ±x i} ∩ {x | ∑_{j ≠ i} x_j² < 1} ∩ ball 0 2`.

Together with the unit ball itself they cover its closure. The generic
`Boundary.FiniteBoundaryCover` construction therefore supplies one interior
test function and `2n` boundary test functions with exactly the support and
sum properties required by `Boundary.C1ExtensionAtlas`.

The tangential-radius restriction keeps compact cutoff supports in a strictly
smaller graph cylinder. The boundary-atlas construction can
therefore replace the local spherical square-root height by a globally
smooth function which agrees with it exactly on the support.

On the cap `{0 < ±x i}` the unit sphere is the graph `x i = ±√(1 - ∑_{j ≠ i} x_j²)` over the
tangential variables, which is the local graph description of a `C^k` boundary in Evans, PDE,
Appendix C.1. The height function is smooth only where the tangential norm is below `1`, hence
the restriction `tangentialNormSq < 1` in the caps. We also record the standard defining
function `1 - ‖x‖²` of the ball and the nondegeneracy of its differential on the sphere, which is
the input for producing flattening charts by the inverse function theorem.

## Main declarations

* `domain`, `boundaryCap`, `boundaryCover`: the open unit ball, the `2n` signed caps, and the
  resulting `FiniteBoundaryCover` (for `0 < n`).
* `definingFunction`, `definingFunction_contDiff`, `definingFunction_pos_iff`,
  `radialCovector_ne_zero_of_mem_sphere`: the defining function `1 - ‖x‖²`, its smoothness, its
  positivity set, and the fact that the covector `⟪x, ·⟫` is nonzero for `x` on the sphere.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, App. C.1, pp. 710-711, for the local graph description of a
  `C^k` boundary.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped Distributions

set_option linter.missingDocs true

namespace SobolevSpace.Boundary.Atlas.UnitBall

open Metric Set


variable (n : ℕ)

/-- The open Euclidean unit ball in dimension `n`. -/
def domain : Set (ℝ^n) :=
  ball 0 1

/-- Squared norm of all coordinates except `i`. -/
def tangentialNormSq (i : Fin n) (x : ℝ^n) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, x j ^ 2

private theorem tangentialNormSq_continuous (i : Fin n) :
    Continuous (tangentialNormSq n i) := by
  exact continuous_finsetSum _ fun j _ ↦
    (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.pow 2

/-- The positive coordinate cap, made bounded by intersecting with the ball
of radius `2` and restricted to the sphere's graph region. -/
def positiveCap (i : Fin n) : Set (ℝ^n) :=
  ({x | 0 < x i} ∩ {x | tangentialNormSq n i x < 1}) ∩ ball 0 2

/-- The negative coordinate cap, made bounded by intersecting with the ball
of radius `2` and restricted to the sphere's graph region. -/
def negativeCap (i : Fin n) : Set (ℝ^n) :=
  ({x | x i < 0} ∩ {x | tangentialNormSq n i x < 1}) ∩ ball 0 2

/-- The `2n` signed boundary caps, with positive caps first and negative caps
second. -/
def boundaryCap : Fin (n + n) → Set (ℝ^n) :=
  fun i ↦
    match (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)).symm i with
    | Sum.inl j => positiveCap n j
    | Sum.inr j => negativeCap n j

/-- The Euclidean unit ball is open. -/
theorem isOpen_domain : IsOpen (domain n) := by
  exact isOpen_ball

/-- The Euclidean unit ball is bounded. -/
theorem bounded_domain : Bornology.IsBounded (domain n) := by
  exact Metric.isBounded_ball

private theorem isOpen_positiveCap (i : Fin n) : IsOpen (positiveCap n i) := by
  exact
    ((isOpen_Ioi.preimage (EuclideanSpace.proj i).continuous).inter
      (isOpen_Iio.preimage (tangentialNormSq_continuous n i))).inter isOpen_ball

private theorem isOpen_negativeCap (i : Fin n) : IsOpen (negativeCap n i) := by
  exact
    ((isOpen_Iio.preimage (EuclideanSpace.proj i).continuous).inter
      (isOpen_Iio.preimage (tangentialNormSq_continuous n i))).inter isOpen_ball

private theorem bounded_positiveCap (i : Fin n) :
    Bornology.IsBounded (positiveCap n i) :=
  Metric.isBounded_ball.subset inter_subset_right

private theorem bounded_negativeCap (i : Fin n) :
    Bornology.IsBounded (negativeCap n i) :=
  Metric.isBounded_ball.subset inter_subset_right

/-- Every signed coordinate cap is open. -/
theorem isOpen_boundaryCap (i : Fin (n + n)) :
    IsOpen (boundaryCap n i) := by
  generalize hs : finSumFinEquiv.symm i = s
  rcases s with j | j
  · simpa [boundaryCap, hs] using isOpen_positiveCap n j
  · simpa [boundaryCap, hs] using isOpen_negativeCap n j

/-- Every signed coordinate cap is bounded. -/
theorem bounded_boundaryCap (i : Fin (n + n)) :
    Bornology.IsBounded (boundaryCap n i) := by
  generalize hs : finSumFinEquiv.symm i = s
  rcases s with j | j
  · simpa [boundaryCap, hs] using bounded_positiveCap n j
  · simpa [boundaryCap, hs] using bounded_negativeCap n j

private theorem exists_ne_zero_coordinate {x : ℝ^n}
    (hx : x ≠ 0) : ∃ i : Fin n, x i ≠ 0 := by
  by_contra h
  push Not at h
  apply hx
  ext i
  exact h i

/-- Every point of the closed unit ball which is not in the open ball lies
in one of the signed coordinate caps. -/
private theorem mem_boundaryCap_of_mem_closedBall_not_mem_domain
    {x : ℝ^n} (hx : x ∈ closedBall (0 : ℝ^n) 1)
    (hxin : x ∉ domain n) :
    ∃ i : Fin (n + n), x ∈ boundaryCap n i := by
  have hxnorm : ‖x‖ = 1 := by
    have hle : ‖x‖ ≤ 1 := by
      simpa [mem_closedBall, dist_zero_right] using hx
    have hnotlt : ¬ ‖x‖ < 1 := by
      simpa [domain, mem_ball, dist_zero_right] using hxin
    exact le_antisymm hle (le_of_not_gt hnotlt)
  have hx0 : x ≠ 0 := by
    intro hzero
    simp [hzero] at hxnorm
  obtain ⟨i, hi⟩ := exists_ne_zero_coordinate (n := n) hx0
  have hdecomp :
      x i ^ 2 + tangentialNormSq n i x = 1 := by
    calc
      x i ^ 2 + tangentialNormSq n i x =
          ∑ j : Fin n, x j ^ 2 := by
            exact Finset.add_sum_erase Finset.univ
              (fun j : Fin n ↦ x j ^ 2) (Finset.mem_univ i)
      _ = ‖x‖ ^ 2 := (EuclideanSpace.real_norm_sq_eq x).symm
      _ = 1 := by rw [hxnorm]; norm_num
  have hiSq : 0 < x i ^ 2 := sq_pos_of_ne_zero hi
  have htan : tangentialNormSq n i x < 1 := by
    nlinarith
  have hxBall : x ∈ ball (0 : ℝ^n) 2 := by
    simp [mem_ball, dist_zero_right, hxnorm]
  rcases lt_or_gt_of_ne hi with hiNeg | hiPos
  · refine
      ⟨(finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)) (Sum.inr i), ?_⟩
    rw [show
      boundaryCap n
          ((finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)) (Sum.inr i)) =
        negativeCap n i by
      unfold boundaryCap
      rw [Equiv.symm_apply_apply]]
    exact ⟨⟨hiNeg, htan⟩, hxBall⟩
  · refine
      ⟨(finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)) (Sum.inl i), ?_⟩
    rw [show
      boundaryCap n
          ((finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)) (Sum.inl i)) =
        positiveCap n i by
      unfold boundaryCap
      rw [Equiv.symm_apply_apply]]
    exact ⟨⟨hiPos, htan⟩, hxBall⟩

/-- The `2n` signed coordinate caps cover the frontier of the unit ball. -/
theorem frontier_domain_subset_boundaryCap :
    frontier (domain n) ⊆ ⋃ i, boundaryCap n i := by
  intro x hx
  rw [(isOpen_domain n).frontier_eq] at hx
  have hxClosed : x ∈ closedBall (0 : ℝ^n) 1 := by
    exact closure_ball_subset_closedBall hx.1
  obtain ⟨i, hi⟩ :=
    mem_boundaryCap_of_mem_closedBall_not_mem_domain (n := n) hxClosed hx.2
  exact mem_iUnion.2 ⟨i, hi⟩

/-- The signed coordinate caps form a finite boundary cover of the open unit
ball in every positive dimension. The generic construction supplies its
subordinate smooth interior and boundary cutoffs. -/
def boundaryCover [Fact (0 < n)] :
    Boundary.FiniteBoundaryCover n (domain n) where
  isOpen := isOpen_domain n
  bounded := bounded_domain n
  N := n + n
  boundaryPatch := boundaryCap n
  boundaryPatch_open := isOpen_boundaryCap n
  boundaryPatch_bounded := bounded_boundaryCap n
  frontier_subset_iUnion := frontier_domain_subset_boundaryCap n

/-- The standard smooth defining function for the unit ball. -/
def definingFunction (x : ℝ^n) : ℝ :=
  1 - ‖x‖ ^ 2

/-- The standard defining function of the unit ball is smooth to every finite order. -/
theorem definingFunction_contDiff (m : ℕ∞) :
    ContDiff ℝ m (definingFunction n) := by
  exact contDiff_const.sub (contDiff_norm_sq ℝ)

/-- The radial covector is nonzero at every point of the unit sphere.  In
combination with `hasStrictFDerivAt_norm_sq`, this is the nondegeneracy input
for applying the inverse-function theorem to the defining function. -/
theorem radialCovector_ne_zero_of_mem_sphere
    {x : ℝ^n} (hx : x ∈ sphere (0 : ℝ^n) 1) :
    innerSL ℝ x ≠ 0 := by
  intro hzero
  have happly := congrArg (fun L : ℝ^n →L[ℝ] ℝ ↦ L x) hzero
  have hxnorm : ‖x‖ = 1 := by
    simpa [mem_sphere, dist_zero_right] using hx
  simp [hxnorm] at happly

/-- The defining function is positive exactly in the unit ball. -/
theorem definingFunction_pos_iff (x : ℝ^n) :
    0 < definingFunction n x ↔ x ∈ domain n := by
  rw [domain, mem_ball, dist_zero_right]
  constructor
  · intro h
    have hsq : ‖x‖ ^ 2 < 1 := by
      simpa [definingFunction] using h
    nlinarith [norm_nonneg x]
  · intro h
    dsimp [definingFunction]
    nlinarith [norm_nonneg x]

end SobolevSpace.Boundary.Atlas.UnitBall
