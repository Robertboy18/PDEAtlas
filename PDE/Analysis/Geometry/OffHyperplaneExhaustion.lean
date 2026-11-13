/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Topology.Sets.Compacts
public import PDE.Common.Euclidean

/-!
# Compact supports away from a coordinate hyperplane

The sets `‖x‖ ≤ n + 1`, `1 / (n + 1) ≤ |x i|` form a monotone family of compact
sets away from the coordinate hyperplane `x i = 0`. Every compact set disjoint
from that hyperplane lies in one member: compactness bounds its radius and gives
a positive minimum of `|x i|`.

For signed meridian profiles, take dimension two and coordinate zero. Both
supports of a compact scalar/vorticity pair fit in the same member. This family
exhausts the complement of the hyperplane, not the whole Euclidean space.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Set TopologicalSpace

variable {d : ℕ}

/-- Compact sets of increasing radius and decreasing distance from a coordinate
hyperplane. In the signed meridian plane, coordinate zero is the radial coordinate. -/
def offHyperplaneCompacts (i : Fin d) (n : ℕ) : Compacts (ℝ^d) :=
  ⟨Metric.closedBall 0 ((n : ℝ) + 1) ∩ {x | 1 / ((n : ℝ) + 1) ≤ |x i|},
    (isCompact_closedBall _ _).inter_right
      (isClosed_le continuous_const (EuclideanSpace.proj i).continuous.abs)⟩

/-- Membership records both the radius bound and a positive coordinate separation. -/
@[simp]
theorem mem_offHyperplaneCompacts (i : Fin d) (n : ℕ) (x : ℝ^d) :
    x ∈ offHyperplaneCompacts i n ↔
      ‖x‖ ≤ (n : ℝ) + 1 ∧ 1 / ((n : ℝ) + 1) ≤ |x i| := by
  change (dist x 0 ≤ (n : ℝ) + 1 ∧ 1 / ((n : ℝ) + 1) ≤ |x i|) ↔ _
  rw [dist_zero_right]

/-- Coordinatewise linear isometries preserve every member. Taking negation in
one coordinate and the identity in the others gives coordinate-reflection invariance. -/
theorem mem_offHyperplaneCompacts_piLpCongrRight_iff (i : Fin d) (n : ℕ)
    (e : Fin d → ℝ ≃ₗᵢ[ℝ] ℝ) (x : ℝ^d) :
    LinearIsometryEquiv.piLpCongrRight 2 e x ∈ offHyperplaneCompacts i n ↔
      x ∈ offHyperplaneCompacts i n := by
  rw [mem_offHyperplaneCompacts, mem_offHyperplaneCompacts,
    (LinearIsometryEquiv.piLpCongrRight 2 e).norm_map]
  have hcoord : |(LinearIsometryEquiv.piLpCongrRight 2 e x) i| = |x i| := by
    change |e i (x i)| = |x i|
    simpa only [Real.norm_eq_abs] using (e i).norm_map (x i)
  rw [hcoord]

/-- The compact support regions increase with their index. -/
theorem monotone_offHyperplaneCompacts (i : Fin d) : Monotone (offHyperplaneCompacts i) := by
  intro n m hnm x hx
  obtain ⟨hxn, hxi⟩ := (mem_offHyperplaneCompacts i n x).mp hx
  have hnm' : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
    have : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm
    linarith
  exact (mem_offHyperplaneCompacts i m x).mpr
    ⟨hxn.trans hnm', (one_div_le_one_div_of_le (by positivity) hnm').trans hxi⟩

/-- Every member stays away from the coordinate hyperplane. -/
theorem offHyperplaneCompacts_disjoint (i : Fin d) (n : ℕ) :
    Disjoint (offHyperplaneCompacts i n : Set (ℝ^d))
      {x | x i = 0} := by
  apply Set.disjoint_left.mpr
  intro x hx hzero
  have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have hxi := ((mem_offHyperplaneCompacts i n x).mp hx).2
  change x i = 0 at hzero
  rw [hzero, abs_zero] at hxi
  exact (not_le_of_gt hpos) hxi

/-- Every compact set disjoint from a coordinate hyperplane fits inside one
member. The positive coordinate separation is derived from compactness. -/
theorem exists_subset_offHyperplaneCompacts (i : Fin d)
    {S : Set (ℝ^d)} (hS : IsCompact S)
    (haxis : Disjoint S {x | x i = 0}) :
    ∃ n, S ⊆ offHyperplaneCompacts i n := by
  obtain ⟨R, hR⟩ := hS.isBounded.subset_closedBall 0
  obtain ⟨ε, hε, hsep⟩ := hS.exists_forall_le'
    (EuclideanSpace.proj i).continuous.abs.continuousOn
    (fun x hx ↦ abs_pos.mpr (fun hzero ↦ Set.disjoint_left.mp haxis hx hzero))
  obtain ⟨n, hn⟩ := exists_nat_gt (max R (1 / ε))
  have hRn : R ≤ (n : ℝ) + 1 := by
    have := (le_max_left R (1 / ε)).trans hn.le
    linarith
  have hεn : 1 / ε ≤ (n : ℝ) + 1 := by
    have := (le_max_right R (1 / ε)).trans hn.le
    linarith
  have hsmall : 1 / ((n : ℝ) + 1) ≤ ε := by
    simpa using one_div_le_one_div_of_le (one_div_pos.mpr hε) hεn
  refine ⟨n, fun x hx ↦ (mem_offHyperplaneCompacts i n x).mpr ⟨?_, ?_⟩⟩
  · have hxR : ‖x‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hR hx
    exact hxR.trans hRn
  · exact hsmall.trans (hsep x hx)

/-- Two compact supports away from the coordinate hyperplane share one member,
so they can be treated in a common fixed-support test space. -/
theorem exists_tsupports_subset_offHyperplaneCompacts (i : Fin d)
    {f g : ℝ^d → ℝ}
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfaxis : Disjoint (tsupport f) {x | x i = 0})
    (hgaxis : Disjoint (tsupport g) {x | x i = 0}) :
    ∃ n, tsupport f ⊆ offHyperplaneCompacts i n ∧
      tsupport g ⊆ offHyperplaneCompacts i n := by
  obtain ⟨n, hn⟩ := exists_subset_offHyperplaneCompacts i (hf.union hg)
    (disjoint_union_left.mpr ⟨hfaxis, hgaxis⟩)
  exact ⟨n, Set.subset_union_left.trans hn, Set.subset_union_right.trans hn⟩

/-- A function supported in one of these compact sets vanishes on the entire
coordinate hyperplane, in particular at the origin. -/
theorem eq_zero_of_tsupport_subset_offHyperplaneCompacts (i : Fin d) (n : ℕ)
    {f : ℝ^d → ℝ}
    (hf : tsupport f ⊆ offHyperplaneCompacts i n)
    {x : ℝ^d} (hx : x i = 0) : f x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hxf
  exact Set.disjoint_left.mp (offHyperplaneCompacts_disjoint i n) (hf hxf) hx

end PDE.Analysis
