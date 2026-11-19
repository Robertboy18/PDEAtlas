/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Definitions
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Constructing operational boundary atlases

An operational extension atlas has two inputs.

* `Boundary.FiniteBoundaryCover` is finite geometric data: bounded open
  neighborhoods covering the frontier of a bounded open domain.
* `Boundary.C1FlatteningCharts` attaches a flattening chart to each boundary
  neighborhood after a subordinate smooth partition of unity has been chosen.

Mathlib's smooth partition-of-unity theorem turns every finite boundary cover
into one interior test function and finitely many boundary test functions.
Consequently, concrete domains only need to construct their geometric cover
and charts; they do not need to repeat the partition construction.

This is the localization step of the extension and trace theorems for a
bounded `C¹` domain: cover the boundary by finitely many open sets on each of which the domain is
flattened to the upper half-space, choose a partition of unity subordinate to this cover together
with the domain itself, and treat each piece separately (Evans, PDE, §5.4, and Appendix C.1 for
the definition of a `C¹` boundary via local flattening).

## Main declarations

* `FiniteBoundaryCover`: finitely many bounded open sets covering `frontier Ω`.
* `FiniteBoundaryCover.interiorCutoff`, `FiniteBoundaryCover.boundaryCutoff`,
  `FiniteBoundaryCover.cutoff_sum_eq_one`: the subordinate smooth partition of unity, given as
  test functions. The exported identity `ψ₀ + ∑ ψᵢ = 1` is stated at points of `Ω`; the
  underlying Mathlib partition is built on the compact set `closure Ω`.
* `C1FlatteningCharts`: globally `C¹` flattening charts whose sources contain the supports of the
  boundary cutoffs.
* `C1FlatteningCharts.toC1ExtensionAtlas`: assembly of a `C1ExtensionAtlas` from the two inputs.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.4, Theorem 1, pp. 268-271, whose proof flattens the
  boundary near finitely many points and glues the local extensions with a partition of unity (steps
  5 and 6), and App. C.1, pp. 710-711, for `C^k` boundaries and straightening the boundary.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped Distributions

set_option linter.missingDocs true

namespace SobolevSpace.Boundary

open Set
open scoped Manifold

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- A finite family of bounded open neighborhoods covering the frontier of a
bounded open domain.

The domain itself is used as the interior member of the partition cover. -/
structure FiniteBoundaryCover (n : ℕ) [Fact (0 < n)] (Ω : Set (ℝ^n)) where
  /-- The domain is open. -/
  isOpen : IsOpen Ω
  /-- The domain is bounded. -/
  bounded : Bornology.IsBounded Ω
  /-- Number of boundary neighborhoods. -/
  N : ℕ
  /-- Boundary neighborhoods. -/
  boundaryPatch : Fin N → Set (ℝ^n)
  /-- Every boundary neighborhood is open. -/
  boundaryPatch_open : ∀ i, IsOpen (boundaryPatch i)
  /-- Every boundary neighborhood is bounded. -/
  boundaryPatch_bounded : ∀ i, Bornology.IsBounded (boundaryPatch i)
  /-- The boundary neighborhoods cover the frontier of the domain. -/
  frontier_subset_iUnion : frontier Ω ⊆ ⋃ i, boundaryPatch i

namespace FiniteBoundaryCover

variable (cover : FiniteBoundaryCover n Ω)

/-- The boundary neighborhoods followed by the domain itself. -/
def partitionCover : Fin (cover.N + 1) → Set (ℝ^n) :=
  Fin.lastCases Ω cover.boundaryPatch

/-- Every member of the partition cover is open. -/
theorem partitionCover_open (i : Fin (cover.N + 1)) :
    IsOpen (partitionCover cover i) := by
  induction i using Fin.lastCases with
  | last =>
      simpa [partitionCover] using cover.isOpen
  | cast i =>
      simpa [partitionCover] using cover.boundaryPatch_open i

private theorem partitionCover_bounded (i : Fin (cover.N + 1)) :
    Bornology.IsBounded (partitionCover cover i) := by
  induction i using Fin.lastCases with
  | last =>
      simpa [partitionCover] using cover.bounded
  | cast i =>
      simpa [partitionCover] using cover.boundaryPatch_bounded i

/-- The partition cover covers the closure of the domain. -/
theorem closure_subset_partitionCover :
    closure Ω ⊆ ⋃ i, partitionCover cover i := by
  intro x hx
  rw [closure_eq_self_union_frontier] at hx
  rcases hx with hx | hx
  · exact mem_iUnion.2
      ⟨Fin.last cover.N, by simpa [partitionCover] using hx⟩
  · obtain ⟨i, hi⟩ := mem_iUnion.1 (cover.frontier_subset_iUnion hx)
    exact mem_iUnion.2
      ⟨i.castSucc, by simpa [partitionCover] using hi⟩

/-- A smooth partition of unity on the closure of the domain subordinate to
the boundary cover and the domain itself. -/
def smoothPartition :
    SmoothPartitionOfUnity (Fin (cover.N + 1)) 𝓘(ℝ, ℝ^n) (ℝ^n) (closure Ω) :=
  Classical.choose <|
    SmoothPartitionOfUnity.exists_isSubordinate
      𝓘(ℝ, ℝ^n) isClosed_closure (partitionCover cover)
        (partitionCover_open cover) (closure_subset_partitionCover cover)

private theorem smoothPartition_subordinate :
    (smoothPartition cover).IsSubordinate (partitionCover cover) :=
  Classical.choose_spec <|
    SmoothPartitionOfUnity.exists_isSubordinate
      𝓘(ℝ, ℝ^n) isClosed_closure (partitionCover cover)
        (partitionCover_open cover) (closure_subset_partitionCover cover)

/-- Every member of the subordinate smooth partition is smooth. -/
theorem smoothPartition_contDiff (i : Fin (cover.N + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) fun x ↦ smoothPartition cover i x :=
  (smoothPartition cover i).contMDiff.contDiff

/-- Every member of the subordinate smooth partition has compact support. -/
theorem smoothPartition_hasCompactSupport (i : Fin (cover.N + 1)) :
    HasCompactSupport fun x ↦ smoothPartition cover i x := by
  rw [hasCompactSupport_def]
  exact Metric.isCompact_of_isClosed_isBounded isClosed_closure <|
    (partitionCover_bounded cover i).subset (smoothPartition_subordinate cover i)

/-- A member of the subordinate smooth partition, bundled as a Euclidean
test function. -/
def partitionTestFunction (i : Fin (cover.N + 1)) :
    𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
  _root_.TestFunction.mk
    (fun x ↦ smoothPartition cover i x)
    (smoothPartition_contDiff cover i)
    (smoothPartition_hasCompactSupport cover i)
    (Set.subset_univ _)

@[simp]
private theorem partitionTestFunction_apply (i : Fin (cover.N + 1)) (x : ℝ^n) :
    (partitionTestFunction cover i).toFun x = smoothPartition cover i x := rfl

/-- The partition function subordinate to the interior domain. -/
def interiorCutoff : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
  partitionTestFunction cover (Fin.last cover.N)

/-- The partition function subordinate to the `i`-th boundary neighborhood. -/
def boundaryCutoff (i : Fin cover.N) : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
  partitionTestFunction cover i.castSucc

/-- The interior cutoff is supported in the domain. -/
theorem interiorCutoff_support :
    tsupport cover.interiorCutoff.toFun ⊆ Ω := by
  change tsupport (fun x ↦ smoothPartition cover (Fin.last cover.N) x) ⊆ Ω
  simpa [partitionCover] using
    smoothPartition_subordinate cover (Fin.last cover.N)

/-- Each boundary cutoff is supported in its corresponding boundary
neighborhood. -/
theorem boundaryCutoff_support (i : Fin cover.N) :
    tsupport (cover.boundaryCutoff i).toFun ⊆ cover.boundaryPatch i := by
  change tsupport (fun x ↦ smoothPartition cover i.castSucc x) ⊆
    cover.boundaryPatch i
  simpa [partitionCover] using smoothPartition_subordinate cover i.castSucc

/-- The interior and boundary cutoffs sum to one throughout the domain. -/
theorem cutoff_sum_eq_one (x : ℝ^n) (hx : x ∈ Ω) :
    cover.interiorCutoff.toFun x +
        ∑ i, (cover.boundaryCutoff i).toFun x = 1 := by
  have hsum := (smoothPartition cover).sum_eq_one (subset_closure hx)
  rw [finsum_eq_sum_of_fintype, Fin.sum_univ_castSucc] at hsum
  simpa only [interiorCutoff, boundaryCutoff, partitionTestFunction_apply, add_comm]
    using hsum

end FiniteBoundaryCover

/-- Globally represented `C¹` flattening charts attached to a finite boundary
cover.

Only the compact support of each subordinate boundary cutoff must lie in the
corresponding chart source. This permits chart neighborhoods to be shrunk
after the partition of unity has been selected. -/
structure C1FlatteningCharts (cover : FiniteBoundaryCover n Ω) where
  /-- Boundary-flattening charts, indexed by the boundary neighborhoods. -/
  chart : Fin cover.N → OpenPartialHomeomorph (ℝ^n) (ℝ^n)
  /-- Each chart source contains the corresponding cutoff support. -/
  cutoff_support_subset_source :
    ∀ i, tsupport (cover.boundaryCutoff i).toFun ⊆ (chart i).source
  /-- Every total forward chart representative is globally `C¹`. -/
  chart_contDiff : ∀ i, ContDiff ℝ 1 fun x ↦ chart i x
  /-- Every total inverse-chart representative is globally `C¹`. -/
  chart_symm_contDiff : ∀ i, ContDiff ℝ 1 fun y ↦ (chart i).symm y
  /-- On its source, each chart identifies the domain with the upper
  half-space. -/
  chart_mem_iff_upper :
    ∀ i, ∀ x ∈ (chart i).source,
      (x ∈ Ω ↔ chart i x ∈ SobolevSpace.HalfSpace.upper n)
  /-- Every chart target is bounded. -/
  chart_target_bounded : ∀ i, Bornology.IsBounded (chart i).target

namespace C1FlatteningCharts

variable {cover : FiniteBoundaryCover n Ω}

/-- Construct an operational extension atlas from a finite boundary cover and
compatible globally represented `C¹` flattening charts. -/
@[reducible]
def toC1ExtensionAtlas (charts : C1FlatteningCharts cover) :
    C1ExtensionAtlas n Ω where
  isOpen := cover.isOpen
  bounded := cover.bounded
  N := cover.N
  chart := charts.chart
  chart_contDiff := charts.chart_contDiff
  chart_symm_contDiff := charts.chart_symm_contDiff
  chart_mem_iff_upper := charts.chart_mem_iff_upper
  chart_target_bounded := charts.chart_target_bounded
  interiorCutoff := cover.interiorCutoff
  interiorCutoff_support := cover.interiorCutoff_support
  boundaryCutoff := cover.boundaryCutoff
  boundaryCutoff_support := charts.cutoff_support_subset_source
  cutoff_sum_eq_one := cover.cutoff_sum_eq_one

end C1FlatteningCharts

end SobolevSpace.Boundary
