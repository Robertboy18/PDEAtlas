/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Upper regularization of a supremum

The upper regularization is Mathlib's `Filter.limsup` along neighborhoods
within the domain. Local upper bounds make it real valued with the expected
order properties. Its values can be approached by values of the original
family in every neighborhood; no convergence of contact points is assumed.
-/

@[expose] public section

open Set Filter
open scoped Topology

variable {X ι : Type*} [TopologicalSpace X]

namespace PDE

/-- The value at a point bounds every eventual upper bound from below. -/
theorem isCoboundedUnder_nhdsWithin {R : Type*} [Preorder R]
    {U : Set X} {u : X → R} {x : X}
    (hx : x ∈ U) : IsCoboundedUnder (· ≤ ·) (𝓝[U] x) u := by
  refine ⟨u x, fun b hb ↦ ?_⟩
  exact (show ∀ᶠ y in 𝓝[U] x, u y ≤ b from hb).self_of_nhdsWithin hx

/-- Upper regularization majorizes the original function wherever it is
locally bounded above. -/
theorem le_limsup_nhdsWithin {R : Type*} [ConditionallyCompleteLattice R]
    {U : Set X} {u : X → R} {x : X}
    (hx : x ∈ U) (hu : IsBoundedUnder (· ≤ ·) (𝓝[U] x) u) :
    u x ≤ limsup u (𝓝[U] x) :=
  le_limsup_of_le hu fun _ hb ↦ hb.self_of_nhdsWithin hx

/-- A function locally bounded above has an upper semicontinuous
regularization relative to its domain. -/
theorem upperSemicontinuousOn_limsup_nhdsWithin
    {R : Type*} [ConditionallyCompleteLinearOrder R] [DenselyOrdered R]
    {U : Set X} {u : X → R}
    (hu : ∀ x ∈ U, IsBoundedUnder (· ≤ ·) (𝓝[U] x) u) :
    UpperSemicontinuousOn (fun x ↦ limsup u (𝓝[U] x)) U := by
  intro x hx b hb
  obtain ⟨a, ha, hab⟩ := exists_between hb
  have hevent := eventually_lt_of_limsup_lt ha (hu x hx)
  filter_upwards [eventually_eventually_nhdsWithin.mpr hevent,
    self_mem_nhdsWithin] with y hy hyU
  exact (limsup_le_of_le (isCoboundedUnder_nhdsWithin hyU)
    (hy.mono fun _ h ↦ h.le)).trans_lt hab

/-- A semicontinuous upper bound also bounds the regularization. -/
theorem limsup_nhdsWithin_le_of_upperSemicontinuousWithinAt
    {R : Type*} [ConditionallyCompleteLinearOrder R] [DenselyOrdered R]
    {U : Set X} {u b : X → R} {x : X} (hx : x ∈ U)
    (hb : UpperSemicontinuousWithinAt b U x)
    (hub : ∀ᶠ y in 𝓝[U] x, u y ≤ b y) :
    limsup u (𝓝[U] x) ≤ b x := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro a ha
  apply limsup_le_of_le (isCoboundedUnder_nhdsWithin hx)
  filter_upwards [hub, hb a ha] with y hy hyb
  exact hy.trans hyb.le

/-- Lower regularization minorizes a locally bounded-below function. -/
theorem liminf_nhdsWithin_le {R : Type*} [ConditionallyCompleteLattice R]
    {U : Set X} {u : X → R} {x : X}
    (hx : x ∈ U) (hu : IsBoundedUnder (· ≥ ·) (𝓝[U] x) u) :
    liminf u (𝓝[U] x) ≤ u x :=
  le_limsup_nhdsWithin (R := Rᵒᵈ) hx hu

/-- Lower regularization is lower semicontinuous under local lower bounds. -/
theorem lowerSemicontinuousOn_liminf_nhdsWithin
    {R : Type*} [ConditionallyCompleteLinearOrder R] [DenselyOrdered R]
    {U : Set X} {u : X → R}
    (hu : ∀ x ∈ U, IsBoundedUnder (· ≥ ·) (𝓝[U] x) u) :
    LowerSemicontinuousOn (fun x ↦ liminf u (𝓝[U] x)) U :=
  upperSemicontinuousOn_limsup_nhdsWithin (R := Rᵒᵈ) hu

/-- A lower semicontinuous local lower bound also bounds lower regularization. -/
theorem le_liminf_nhdsWithin_of_lowerSemicontinuousWithinAt
    {R : Type*} [ConditionallyCompleteLinearOrder R] [DenselyOrdered R]
    {U : Set X} {u b : X → R} {x : X} (hx : x ∈ U)
    (hb : LowerSemicontinuousWithinAt b U x)
    (hub : ∀ᶠ y in 𝓝[U] x, b y ≤ u y) :
    b x ≤ liminf u (𝓝[U] x) :=
  limsup_nhdsWithin_le_of_upperSemicontinuousWithinAt (R := Rᵒᵈ) hx hb hub

/-- Local upper bounds for a family give the bounds needed by the
conditionally complete supremum and its upper regularization. -/
theorem isBoundedUnder_ciSup [Nonempty ι] {U : Set X} {v : ι → X → ℝ}
    {x : X} (hbound : ∃ b, ∀ᶠ y in 𝓝[U] x, ∀ i, v i y ≤ b) :
    IsBoundedUnder (· ≤ ·) (𝓝[U] x) (fun y ↦ ⨆ i, v i y) := by
  obtain ⟨b, hb⟩ := hbound
  exact ⟨b, hb.mono fun y hy ↦ ciSup_le hy⟩

/-- Each member of a locally bounded family lies below its regularized supremum. -/
theorem le_limsup_ciSup_nhdsWithin [Nonempty ι] {U : Set X} {v : ι → X → ℝ}
    {x : X} (hx : x ∈ U)
    (hbound : ∃ b, ∀ᶠ y in 𝓝[U] x, ∀ i, v i y ≤ b) (i : ι) :
    v i x ≤ limsup (fun y ↦ ⨆ j, v j y) (𝓝[U] x) := by
  obtain ⟨b, hb⟩ := hbound
  have hpoint : BddAbove (range fun j ↦ v j x) :=
    ⟨b, by simpa only [mem_upperBounds, forall_mem_range] using hb.self_of_nhdsWithin hx⟩
  exact (le_ciSup hpoint i).trans
    (le_limsup_nhdsWithin hx (isBoundedUnder_ciSup ⟨b, hb⟩))

/-- Every neighborhood contains a family value above any strict lower
bound for the regularized supremum. This selects both the point and the
member of the family from the supremum itself. -/
theorem exists_lt_of_lt_limsup_ciSup [Nonempty ι] {U s : Set X} {v : ι → X → ℝ}
    {x : X} (hx : x ∈ U)
    (hs : s ∈ 𝓝[U] x) {a : ℝ}
    (ha : a < limsup (fun y ↦ ⨆ i, v i y) (𝓝[U] x)) :
    ∃ y ∈ s ∩ U, ∃ i, a < v i y := by
  have hfreq := frequently_lt_of_lt_limsup (isCoboundedUnder_nhdsWithin hx) ha
  obtain ⟨y, hy, hys, hyU⟩ := (hfreq.and_eventually
    (Filter.inter_mem hs self_mem_nhdsWithin)).exists
  obtain ⟨i, hi⟩ := exists_lt_of_lt_ciSup hy
  exact ⟨y, ⟨hys, hyU⟩, i, hi⟩

end PDE
