/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Compactness.Rellich.CellAverages
public import PDE.Spaces.Sobolev.GraphSpace.Model.Definitions
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Euclidean grids for Rellich compactness

The abstract cell-averaging operators of `Rellich.CellAverages` are specialised
here to the regular lattice of half-open cubes of side `δ` in `ℝ^n`.  For a
ball `B(0, R)` only finitely many lattice cells are needed, and averaging over
them defines a compact operator `euclideanGridAverageOperator δ R` on
`L²(ℝ^n)`.  We also record the elementary geometry used in the
Rellich–Kondrachov argument: cells are Borel, have volume `δⁿ`,
partition space, and two points of one cell differ by a vector in the cube
`[-δ, δ]ⁿ`, whose volume is `(2δ)ⁿ` and whose points have norm at most
`√n · δ`.

The pairwise-oscillation bound from `Rellich.CellAverages` is thus reduced to an integral over
translation vectors ranging in a compact box of small diameter, which is where the translation
estimates for `H¹` functions take over. This is the finite spatial truncation in our proof of the
Rellich–Kondrachov theorem; Evans's proof (§5.7, Theorem 1) uses mollifiers and the Arzelà–Ascoli
theorem instead of grids.

## Main definitions and results

* `euclideanGridCell δ k`, `plainEuclideanGridCell`: the half-open cube with
  integer index `k`, in Euclidean and in coordinate-space form.
* `measurableSet_euclideanGridCell`, `volume_euclideanGridCell`,
  `disjoint_euclideanGridCell_of_ne`, `mem_euclideanGridCell_gridIndex`: the
  cells are measurable, have volume `δⁿ`, are pairwise disjoint, and every
  point lies in the cell of its floor index `euclideanGridIndex δ x`.
* `euclideanGridIndicesForBall δ R`, `ball_subset_iUnion_euclideanGridCell`:
  the finite index box whose cells cover `B(0, R)`.
* `euclideanGridAverageOperator δ R` and its compactness.
* `euclideanDifferenceBox δ`, `volume_euclideanDifferenceBox`,
  `isCompact_euclideanDifferenceBox`,
  `sub_mem_euclideanDifferenceBox_of_mem_gridCell`,
  `norm_sq_le_of_mem_euclideanDifferenceBox`: the box of within-cell
  translation vectors and its size.

## Implementation notes

Half-open cells `[kδ, (k+1)δ)` are used so that the partition is
disjoint; the closed difference box `[-δ, δ]ⁿ` is used so that it is compact.
Volumes are computed by transporting to `Fin n → ℝ` along `WithLp.ofLp`, which
is measure preserving.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.7, Theorem 1, pp. 286-288, for the Rellich–Kondrachov
  theorem.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace
namespace GraphSpace
namespace Rellich

open MeasureTheory Set Function
open scoped ENNReal Topology InnerProductSpace RealInnerProductSpace

variable {n : ℕ}

section EuclideanGrid

/-- Coordinate-space version of a half-open lattice cell. -/
def plainEuclideanGridCell (δ : ℝ) (k : Fin n → ℤ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ fun i ↦
    Set.Ico ((k i : ℝ) * δ) (((k i : ℝ) + 1) * δ)

/-- Half-open Euclidean lattice cell of side length `δ` with integer index
`k`.  Half-open cells form a disjoint partition. -/
def euclideanGridCell (δ : ℝ) (k : Fin n → ℤ) : Set (ℝ^n) :=
  {x | ∀ i : Fin n,
    x i ∈ Set.Ico ((k i : ℝ) * δ) (((k i : ℝ) + 1) * δ)}

/-- Every Euclidean lattice cell is Borel measurable. -/
theorem measurableSet_euclideanGridCell (δ : ℝ) (k : Fin n → ℤ) :
    MeasurableSet (euclideanGridCell (n := n) δ k) := by
  simp only [euclideanGridCell, Set.ofPred_forall]
  exact MeasurableSet.iInter fun i ↦
    measurableSet_Ico.preimage
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin n ↦ ℝ) i).measurable

/-- The Euclidean cell is the inverse image of its coordinate-space box. -/
theorem euclideanGridCell_eq_preimage_plain
    (δ : ℝ) (k : Fin n → ℤ) :
    euclideanGridCell (n := n) δ k =
      (@WithLp.ofLp 2 (Fin n → ℝ)) ⁻¹' plainEuclideanGridCell δ k := by
  ext x
  simp [euclideanGridCell, plainEuclideanGridCell]

/-- Exact volume of a Euclidean lattice cell. -/
theorem volume_euclideanGridCell
    (δ : ℝ) (k : Fin n → ℤ) :
    (MeasureTheory.volume : Measure (ℝ^n))
        (euclideanGridCell (n := n) δ k) =
      ENNReal.ofReal δ ^ n := by
  rw [euclideanGridCell_eq_preimage_plain]
  rw [(PiLp.volume_preserving_ofLp (Fin n)).measure_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurableEmbedding]
  unfold plainEuclideanGridCell
  rw [Real.volume_pi_Ico]
  calc
    (∏ i, ENNReal.ofReal
        (((k i : ℝ) + 1) * δ - (k i : ℝ) * δ)) =
        ∏ _ : Fin n, ENNReal.ofReal δ := by
      apply Finset.prod_congr rfl
      intro i _
      congr 1
      ring
    _ = ENNReal.ofReal δ ^ n := by simp

/-- A positive-side-length Euclidean lattice cell has nonzero volume. -/
theorem volume_euclideanGridCell_ne_zero
    {δ : ℝ} (hδ : 0 < δ) (k : Fin n → ℤ) :
    (MeasureTheory.volume : Measure (ℝ^n))
        (euclideanGridCell (n := n) δ k) ≠ 0 := by
  rw [volume_euclideanGridCell]
  positivity

/-- Real-valued volume of a positive-side-length grid cell. -/
theorem volumeReal_euclideanGridCell
    {δ : ℝ} (hδ : 0 < δ) (k : Fin n → ℤ) :
    (MeasureTheory.volume : Measure (ℝ^n)).real
        (euclideanGridCell (n := n) δ k) = δ ^ n := by
  change ((MeasureTheory.volume : Measure (ℝ^n))
    (euclideanGridCell (n := n) δ k)).toReal = δ ^ n
  rw [volume_euclideanGridCell, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hδ.le]

/-- The canonical lattice index of a point at scale `δ`. -/
def euclideanGridIndex (δ : ℝ) (x : ℝ^n) : Fin n → ℤ :=
  fun i ↦ ⌊x i / δ⌋

/-- Every point belongs to its canonical half-open lattice cell when the
side length is positive. -/
theorem mem_euclideanGridCell_gridIndex
    {δ : ℝ} (hδ : 0 < δ) (x : ℝ^n) :
    x ∈ euclideanGridCell (n := n) δ (euclideanGridIndex δ x) := by
  intro i
  constructor
  · have hfloor : ((⌊x i / δ⌋ : ℤ) : ℝ) ≤ x i / δ := Int.floor_le _
    exact (le_div_iff₀ hδ).1 hfloor
  · have hlt : x i / δ < ((⌊x i / δ⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    exact (div_lt_iff₀ hδ).1 hlt

/-- Distinct positive-scale lattice cells are disjoint. -/
theorem disjoint_euclideanGridCell_of_ne
    {δ : ℝ} (hδ : 0 < δ) {k l : Fin n → ℤ} (hkl : k ≠ l) :
    Disjoint (euclideanGridCell (n := n) δ k)
      (euclideanGridCell (n := n) δ l) := by
  rw [Set.disjoint_left]
  intro x hxk hxl
  exfalso
  apply hkl
  funext i
  by_contra hki
  rcases lt_or_gt_of_ne hki with hlt | hgt
  · have hsucc : k i + 1 ≤ l i := Int.add_one_le_iff.mpr hlt
    have hcast : (((k i : ℤ) : ℝ) + 1) * δ ≤ ((l i : ℤ) : ℝ) * δ := by
      apply mul_le_mul_of_nonneg_right _ hδ.le
      exact_mod_cast hsucc
    have hkUpper := (hxk i).2
    have hlLower := (hxl i).1
    linarith
  · have hsucc : l i + 1 ≤ k i := Int.add_one_le_iff.mpr hgt
    have hcast : (((l i : ℤ) : ℝ) + 1) * δ ≤ ((k i : ℤ) : ℝ) * δ := by
      apply mul_le_mul_of_nonneg_right _ hδ.le
      exact_mod_cast hsucc
    have hlUpper := (hxl i).2
    have hkLower := (hxk i).1
    linarith

/-- Any finite family of distinct positive-scale lattice cells is pairwise
disjoint. -/
theorem pairwiseDisjoint_euclideanGridCell
    {δ : ℝ} (hδ : 0 < δ) (I : Finset (Fin n → ℤ)) :
    Set.Pairwise (↑I : Set (Fin n → ℤ))
      (Disjoint on euclideanGridCell (n := n) δ) := by
  intro k _ l _ hkl
  exact disjoint_euclideanGridCell_of_ne (n := n) hδ hkl

/-- The squared diameter of a side-`δ` Euclidean lattice cell is at most
`n * δ²`. -/
theorem dist_sq_le_of_mem_euclideanGridCell
    {δ : ℝ} {k : Fin n → ℤ} {x y : ℝ^n}
    (hx : x ∈ euclideanGridCell (n := n) δ k)
    (hy : y ∈ euclideanGridCell (n := n) δ k) :
    dist x y ^ 2 ≤ (n : ℝ) * δ ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  calc
    (∑ i, dist (x i) (y i) ^ 2) ≤ ∑ _ : Fin n, δ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hxUpper : x i < (k i : ℝ) * δ + δ := by
        simpa only [add_mul, one_mul] using (hx i).2
      have hyUpper : y i < (k i : ℝ) * δ + δ := by
        simpa only [add_mul, one_mul] using (hy i).2
      have hLower : -δ ≤ x i - y i := by
        have := (hx i).1
        linarith [hyUpper]
      have hUpper : x i - y i ≤ δ := by
        have := (hy i).1
        linarith [hxUpper]
      simpa [Real.dist_eq] using sq_le_sq' hLower hUpper
    _ = (n : ℝ) * δ ^ 2 := by simp

/-- The finite box of lattice indices that contains the canonical index of
every point in `ball 0 R` at scale `δ`.

This is the finite-dimensional truncation used in the finite-rank part of
the `H¹₀ → L²` Rellich argument of `Rellich.ZeroExtension`. -/
def euclideanGridIndicesForBall (δ R : ℝ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun _ : Fin n ↦ Finset.Icc ⌊-R / δ⌋ ⌊R / δ⌋

/-- The canonical grid index of a point in `ball 0 R` belongs to the finite
index box selected for that ball. -/
theorem euclideanGridIndex_mem_indicesForBall
    {δ R : ℝ} (hδ : 0 < δ) {x : ℝ^n}
    (hx : x ∈ Metric.ball (0 : ℝ^n) R) :
    euclideanGridIndex δ x ∈
      euclideanGridIndicesForBall (n := n) δ R := by
  rw [euclideanGridIndicesForBall, Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have hxnorm : ‖x‖ < R := by
    simpa [Metric.mem_ball, dist_eq_norm] using hx
  have hcoordNorm : |x i| ≤ ‖x‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x i
  have hLower : -R ≤ x i := by
    linarith [neg_abs_le (x i)]
  have hUpper : x i ≤ R := by
    linarith [le_abs_self (x i)]
  constructor
  · exact Int.floor_le_floor ((div_le_div_iff_of_pos_right hδ).2 hLower)
  · exact Int.floor_le_floor ((div_le_div_iff_of_pos_right hδ).2 hUpper)

/-- The finitely many grid cells indexed by
`euclideanGridIndicesForBall δ R` cover `ball 0 R`. -/
theorem ball_subset_iUnion_euclideanGridCell
    {δ R : ℝ} (hδ : 0 < δ) :
    Metric.ball (0 : ℝ^n) R ⊆
      ⋃ k ∈ euclideanGridIndicesForBall (n := n) δ R,
        euclideanGridCell (n := n) δ k := by
  intro x hx
  refine Set.mem_iUnion.2 ⟨euclideanGridIndex δ x, ?_⟩
  refine Set.mem_iUnion.2 ⟨euclideanGridIndex_mem_indicesForBall
    (n := n) hδ hx, ?_⟩
  exact mem_euclideanGridCell_gridIndex (n := n) hδ x

/-- Finite-rank averaging over the regular grid cells needed to cover
`ball 0 R`. -/
noncomputable def euclideanGridAverageOperator (δ R : ℝ) :
    DerivLp n 2 Set.univ →L[ℝ] DerivLp n 2 Set.univ :=
  finiteCellAverageOperator
    (euclideanGridIndicesForBall (n := n) δ R)
    (euclideanGridCell (n := n) δ)
    (measurableSet_euclideanGridCell (n := n) δ)
    (fun k ↦ by simp [domainMeasure, volume_euclideanGridCell])

/-- Grid averaging over a bounded spatial region is compact because its
range is spanned by finitely many cell indicators. -/
theorem euclideanGridAverageOperator.isCompactOperator (δ R : ℝ) :
    IsCompactOperator (euclideanGridAverageOperator (n := n) δ R) := by
  exact finiteCellAverageOperator.isCompactOperator
    (euclideanGridIndicesForBall (n := n) δ R)
    (euclideanGridCell (n := n) δ)
    (measurableSet_euclideanGridCell (n := n) δ)
    (fun k ↦ by simp [domainMeasure, volume_euclideanGridCell])

/-- Coordinate-space box of all possible differences of two points lying in
one side-`δ` grid cell. -/
def plainEuclideanDifferenceBox (δ : ℝ) : Set (Fin n → ℝ) :=
  Set.Icc (fun _ ↦ -δ) (fun _ ↦ δ)

/-- Euclidean box of all possible within-cell translation vectors. -/
def euclideanDifferenceBox (δ : ℝ) : Set (ℝ^n) :=
  {h | ∀ i : Fin n, h i ∈ Set.Icc (-δ) δ}

/-- The within-cell translation box is Borel measurable, being a finite
intersection of coordinate preimages of closed intervals. -/
theorem measurableSet_euclideanDifferenceBox (δ : ℝ) :
    MeasurableSet (euclideanDifferenceBox (n := n) δ) := by
  simp only [euclideanDifferenceBox, Set.ofPred_forall]
  exact MeasurableSet.iInter fun i ↦
    measurableSet_Icc.preimage
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin n ↦ ℝ) i).measurable

/-- The Euclidean translation box is the inverse image under `WithLp.ofLp` of
the coordinate-space box `[-δ, δ]ⁿ`; this is how its volume and compactness
are transported from `Fin n → ℝ`. -/
theorem euclideanDifferenceBox_eq_preimage_plain (δ : ℝ) :
    euclideanDifferenceBox (n := n) δ =
      (@WithLp.ofLp 2 (Fin n → ℝ)) ⁻¹' plainEuclideanDifferenceBox δ := by
  ext h
  change (∀ i : Fin n, -δ ≤ h i ∧ h i ≤ δ) ↔
    (∀ i : Fin n, -δ ≤ h i) ∧ ∀ i : Fin n, h i ≤ δ
  constructor
  · intro hh
    exact ⟨fun i ↦ (hh i).1, fun i ↦ (hh i).2⟩
  · rintro ⟨hl, hu⟩ i
    exact ⟨hl i, hu i⟩

/-- Exact volume of the within-cell translation box. -/
theorem volume_euclideanDifferenceBox (δ : ℝ) :
    (MeasureTheory.volume : Measure (ℝ^n))
        (euclideanDifferenceBox (n := n) δ) =
      ENNReal.ofReal (2 * δ) ^ n := by
  rw [euclideanDifferenceBox_eq_preimage_plain]
  rw [(PiLp.volume_preserving_ofLp (Fin n)).measure_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurableEmbedding]
  unfold plainEuclideanDifferenceBox
  rw [Real.volume_Icc_pi]
  calc
    (∏ _ : Fin n, ENNReal.ofReal (δ - -δ)) =
        ∏ _ : Fin n, ENNReal.ofReal (2 * δ) := by
      apply Finset.prod_congr rfl
      intro i _
      congr 1
      ring
    _ = ENNReal.ofReal (2 * δ) ^ n := by simp

/-- The within-cell translation box is compact. -/
theorem isCompact_euclideanDifferenceBox (δ : ℝ) :
    IsCompact (euclideanDifferenceBox (n := n) δ) := by
  rw [euclideanDifferenceBox_eq_preimage_plain]
  have heq :
      (@WithLp.ofLp 2 (Fin n → ℝ)) ⁻¹' plainEuclideanDifferenceBox δ =
        (@WithLp.toLp 2 (Fin n → ℝ)) '' plainEuclideanDifferenceBox δ := by
    ext h
    constructor
    · intro hh
      exact ⟨WithLp.ofLp h, hh, by simp⟩
    · rintro ⟨g, hg, rfl⟩
      simpa using hg
  rw [heq]
  exact isCompact_Icc.image (PiLp.continuous_toLp 2 fun _ : Fin n ↦ ℝ)

/-- The difference of two points in one grid cell lies in the common
translation box. -/
theorem sub_mem_euclideanDifferenceBox_of_mem_gridCell
    {δ : ℝ} {k : Fin n → ℤ} {x y : ℝ^n}
    (hx : x ∈ euclideanGridCell (n := n) δ k)
    (hy : y ∈ euclideanGridCell (n := n) δ k) :
    y - x ∈ euclideanDifferenceBox (n := n) δ := by
  intro i
  have hxUpper : x i < (k i : ℝ) * δ + δ := by
    simpa only [add_mul, one_mul] using (hx i).2
  have hyUpper : y i < (k i : ℝ) * δ + δ := by
    simpa only [add_mul, one_mul] using (hy i).2
  constructor
  · change -δ ≤ y i - x i
    have := (hy i).1
    linarith [hxUpper]
  · change y i - x i ≤ δ
    have := (hx i).1
    linarith [hyUpper]

/-- Every translation vector in the difference box has squared norm at most
`n * δ²`. -/
theorem norm_sq_le_of_mem_euclideanDifferenceBox
    {δ : ℝ} {h : ℝ^n}
    (hh : h ∈ euclideanDifferenceBox (n := n) δ) :
    ‖h‖ ^ 2 ≤ (n : ℝ) * δ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    (∑ i, (h i) ^ 2) ≤ ∑ _ : Fin n, δ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact sq_le_sq' (hh i).1 (hh i).2
    _ = (n : ℝ) * δ ^ 2 := by simp

end EuclideanGrid

end Rellich
end GraphSpace
end SobolevSpace
