/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Construction

/-!
# A concrete extension atlas on a bounded interval

We construct the operational boundary data required by
`Boundary.C1ExtensionAtlas` for the nonempty interval `(-1, 1) ⊂ ℝ`.
The construction has two boundary charts:

* near the left endpoint, `x ↦ x + 1`;
* near the right endpoint, `x ↦ 1 - x`.

Both are global affine isometries and flatten the interval to the upper
half-line on their bounded chart neighborhoods. A finite smooth partition
of unity on the closure of the interval supplies the compactly supported
interior and boundary cutoffs.

In one dimension the upper half-space `HalfSpace.upper 1` is the open half-line `{x | 0 < x 0}`,
so "flattening" the endpoint neighborhoods just means translating (and, at the right endpoint,
reflecting) so that the endpoint lands at `0` with the interval on the positive side. Because the
charts are affine, they are `C^∞`, not only `C¹`; `atlas_chart_contDiff` and
`atlas_chart_symm_contDiff` record this.

## Main declarations

* `domain`: the interval `(-1, 1)` as a subset of `ℝ^1`.
* `boundaryCover`, `c1FlatteningCharts`, `c1ExtensionAtlas`: the finite boundary cover, the two
  affine charts, and the assembled atlas.
* `domainC1ExtensionAtlas`: the atlas registered as an instance.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, App. C.1, pp. 710-711, for the definition of a `C^k` boundary
  by local graphs and the flattening map `Φ(x) = (x', x_n - γ(x'))`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped Distributions

set_option linter.missingDocs true

namespace SobolevSpace.Boundary.Atlas.Interval

open Set

private def one : ℝ^1 :=
  WithLp.toLp 2 fun _ ↦ 1

@[simp]
private theorem one_apply (i : Fin 1) : one i = 1 := by
  simp [one]

/-- The concrete bounded domain `(-1, 1) ⊂ ℝ^1`. -/
def domain : Set (ℝ^1) :=
  {x | (-1 : ℝ) < x 0 ∧ x 0 < 1}

private def leftSource : Set (ℝ^1) :=
  {x | (-2 : ℝ) < x 0 ∧ x 0 < (1 / 2 : ℝ)}

private def rightSource : Set (ℝ^1) :=
  {x | (-1 / 2 : ℝ) < x 0 ∧ x 0 < 2}

private theorem norm_eq_abs_coord (x : ℝ^1) :
    ‖x‖ = |x (0 : Fin 1)| := by
  rw [EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_one, Real.norm_eq_abs]
  simpa using Real.sqrt_sq_eq_abs |x (0 : Fin 1)|

private theorem bounded_coordinate_interval (a b : ℝ) :
    Bornology.IsBounded {x : ℝ^1 | a < x 0 ∧ x 0 < b} := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨max |a| |b|, ?_⟩
  intro x hx
  rw [norm_eq_abs_coord]
  apply abs_le.2
  constructor
  · exact
      (le_trans (neg_le_neg (le_max_left |a| |b|)) (neg_abs_le a)).trans
        (le_of_lt hx.1)
  · exact
      (le_of_lt hx.2).trans <|
        (le_abs_self b).trans (le_max_right |a| |b|)

/-- The interval `domain = (-1,1)` is open. -/
theorem isOpen_domain : IsOpen domain := by
  exact (isOpen_Ioo.preimage (EuclideanSpace.proj (0 : Fin 1)).continuous)

/-- The interval `domain = (-1,1)` is bounded. -/
theorem bounded_domain : Bornology.IsBounded domain := by
  exact bounded_coordinate_interval (-1) 1

/-- The origin belongs to `domain = (-1,1)`. -/
theorem zero_mem_domain : (0 : ℝ^1) ∈ domain := by
  simp [domain]

/-- The interval `domain = (-1,1)` is nonempty. -/
theorem nonempty_domain : domain.Nonempty :=
  ⟨0, zero_mem_domain⟩

private theorem isOpen_leftSource : IsOpen leftSource := by
  exact (isOpen_Ioo.preimage (EuclideanSpace.proj (0 : Fin 1)).continuous)

private theorem bounded_leftSource : Bornology.IsBounded leftSource := by
  exact bounded_coordinate_interval (-2) (1 / 2)

private theorem isOpen_rightSource : IsOpen rightSource := by
  exact (isOpen_Ioo.preimage (EuclideanSpace.proj (0 : Fin 1)).continuous)

private theorem bounded_rightSource : Bornology.IsBounded rightSource := by
  exact bounded_coordinate_interval (-1 / 2) 2

private def leftEquiv : ℝ^1 ≃ᵢ ℝ^1 :=
  IsometryEquiv.vaddConst one

private def rightEquiv : ℝ^1 ≃ᵢ ℝ^1 :=
  IsometryEquiv.constVSub one

@[simp]
private theorem leftEquiv_apply (x : ℝ^1) :
    leftEquiv x = x + one := rfl

@[simp]
private theorem rightEquiv_apply (x : ℝ^1) :
    rightEquiv x = one - x := rfl

@[simp]
private theorem rightEquiv_symm_apply (x : ℝ^1) :
    rightEquiv.symm x = one - x := by
  ext i
  simp [rightEquiv, sub_eq_add_neg, add_comm]

private def leftChart : OpenPartialHomeomorph (ℝ^1) (ℝ^1) :=
  leftEquiv.toHomeomorph.toOpenPartialHomeomorphOfImageEq
    leftSource isOpen_leftSource (leftEquiv '' leftSource) rfl

private def rightChart : OpenPartialHomeomorph (ℝ^1) (ℝ^1) :=
  rightEquiv.toHomeomorph.toOpenPartialHomeomorphOfImageEq
    rightSource isOpen_rightSource (rightEquiv '' rightSource) rfl

@[simp]
private theorem leftChart_source : leftChart.source = leftSource := by
  rfl

@[simp]
private theorem rightChart_source : rightChart.source = rightSource := by
  rfl

@[simp]
private theorem leftChart_apply (x : ℝ^1) : leftChart x = x + one := rfl

@[simp]
private theorem rightChart_apply (x : ℝ^1) : rightChart x = one - x := rfl

@[simp]
private theorem leftChart_symm_apply (x : ℝ^1) : leftChart.symm x = x - one := rfl

@[simp]
private theorem rightChart_symm_apply (x : ℝ^1) : rightChart.symm x = one - x := by
  change rightEquiv.symm x = one - x
  exact rightEquiv_symm_apply x

private theorem leftChart_contDiff (m : ℕ∞) :
    ContDiff ℝ m fun x ↦ leftChart x := by
  simpa only [leftChart_apply, id_eq] using
    (contDiff_id.add (contDiff_const : ContDiff ℝ m fun _ : ℝ^1 ↦ one))

private theorem leftChart_symm_contDiff (m : ℕ∞) :
    ContDiff ℝ m fun x ↦ leftChart.symm x := by
  simpa only [leftChart_symm_apply, id_eq] using
    (contDiff_id.sub (contDiff_const : ContDiff ℝ m fun _ : ℝ^1 ↦ one))

private theorem rightChart_contDiff (m : ℕ∞) :
    ContDiff ℝ m fun x ↦ rightChart x := by
  simpa only [rightChart_apply, id_eq] using
    ((contDiff_const : ContDiff ℝ m fun _ : ℝ^1 ↦ one).sub contDiff_id)

private theorem rightChart_symm_contDiff (m : ℕ∞) :
    ContDiff ℝ m fun x ↦ rightChart.symm x := by
  simpa only [rightChart_symm_apply, id_eq] using
    ((contDiff_const : ContDiff ℝ m fun _ : ℝ^1 ↦ one).sub contDiff_id)

private theorem leftChart_mem_iff_upper (x : ℝ^1) (hx : x ∈ leftChart.source) :
    x ∈ domain ↔ leftChart x ∈ SobolevSpace.HalfSpace.upper 1 := by
  have hx' : (-2 : ℝ) < x 0 ∧ x 0 < (1 / 2 : ℝ) := by
    simpa [leftSource] using hx
  have hlast : PDE.Common.lastIndex (n := 1) = (0 : Fin 1) :=
    Subsingleton.elim _ _
  simp only [domain, SobolevSpace.HalfSpace.upper, Set.mem_ofPred_eq, leftChart_apply,
    PiLp.add_apply, one_apply, hlast]
  constructor
  · exact fun h ↦ by linarith [h.1]
  · exact fun h ↦ ⟨by linarith, by linarith [hx'.2]⟩

private theorem rightChart_mem_iff_upper (x : ℝ^1) (hx : x ∈ rightChart.source) :
    x ∈ domain ↔ rightChart x ∈ SobolevSpace.HalfSpace.upper 1 := by
  have hx' : (-1 / 2 : ℝ) < x 0 ∧ x 0 < 2 := by
    simpa [rightSource] using hx
  have hlast : PDE.Common.lastIndex (n := 1) = (0 : Fin 1) :=
    Subsingleton.elim _ _
  simp only [domain, SobolevSpace.HalfSpace.upper, Set.mem_ofPred_eq, rightChart_apply,
    PiLp.sub_apply, one_apply, hlast]
  constructor
  · exact fun h ↦ by linarith [h.2]
  · exact fun h ↦ ⟨by linarith [hx'.1], by linarith⟩

private theorem bounded_leftChart_target :
    Bornology.IsBounded leftChart.target := by
  refine (bounded_coordinate_interval (-1) (3 / 2)).subset ?_
  intro y hy
  change y ∈ leftEquiv '' leftSource at hy
  rcases hy with ⟨x, hx, rfl⟩
  simp only [leftSource, Set.mem_ofPred_eq] at hx
  simp only [Set.mem_ofPred_eq, leftEquiv_apply, PiLp.add_apply, one_apply]
  constructor <;> linarith [hx.1, hx.2]

private theorem bounded_rightChart_target :
    Bornology.IsBounded rightChart.target := by
  refine (bounded_coordinate_interval (-1) (3 / 2)).subset ?_
  intro y hy
  change y ∈ rightEquiv '' rightSource at hy
  rcases hy with ⟨x, hx, rfl⟩
  simp only [rightSource, Set.mem_ofPred_eq] at hx
  simp only [Set.mem_ofPred_eq, rightEquiv_apply, PiLp.sub_apply, one_apply]
  constructor <;> linarith [hx.1, hx.2]

/-- The left endpoint chart followed by the right endpoint chart. -/
@[no_expose]
def chart : Fin 2 → OpenPartialHomeomorph (ℝ^1) (ℝ^1) :=
  Fin.cases leftChart fun _ ↦ rightChart

/-- The left endpoint neighborhood followed by the right endpoint neighborhood. -/
@[no_expose]
def boundaryPatch : Fin 2 → Set (ℝ^1) :=
  Fin.cases leftSource fun _ ↦ rightSource

private theorem chart_source_eq_boundaryPatch (i : Fin 2) :
    (chart i).source = boundaryPatch i := by
  fin_cases i <;> rfl

/-- Both endpoint neighborhoods are open. -/
theorem boundaryPatch_open (i : Fin 2) : IsOpen (boundaryPatch i) := by
  fin_cases i
  · exact isOpen_leftSource
  · exact isOpen_rightSource

/-- Both endpoint neighborhoods are bounded. -/
theorem boundaryPatch_bounded (i : Fin 2) :
    Bornology.IsBounded (boundaryPatch i) := by
  fin_cases i
  · exact bounded_leftSource
  · exact bounded_rightSource

/-- The two endpoint neighborhoods cover the frontier of the interval. -/
theorem frontier_domain_subset_boundaryPatch :
    frontier domain ⊆ ⋃ i, boundaryPatch i := by
  intro x hx
  have hclosed : IsClosed {x : ℝ^1 | (-1 : ℝ) ≤ x 0 ∧ x 0 ≤ 1} :=
    (isClosed_Icc.preimage (EuclideanSpace.proj (0 : Fin 1)).continuous)
  have hdomain :
      domain ⊆ {x : ℝ^1 | (-1 : ℝ) ≤ x 0 ∧ x 0 ≤ 1} := by
    intro y hy
    exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  have hxBounds : (-1 : ℝ) ≤ x 0 ∧ x 0 ≤ 1 :=
    (closure_minimal hdomain hclosed) (frontier_subset_closure hx)
  by_cases hx : x 0 < (1 / 2 : ℝ)
  · apply Set.mem_iUnion.2
    refine ⟨(0 : Fin 2), ?_⟩
    change x ∈ leftSource
    exact ⟨by linarith [hxBounds.1], hx⟩
  · exact Set.mem_iUnion.2
      ⟨(1 : Fin 2), by
        change x ∈ rightSource
        exact ⟨by linarith, by linarith [hxBounds.2]⟩⟩

/-- The two bounded endpoint neighborhoods form a finite boundary cover of
`(-1,1)`. -/
def boundaryCover : Boundary.FiniteBoundaryCover 1 domain where
  isOpen := isOpen_domain
  bounded := bounded_domain
  N := 2
  boundaryPatch := boundaryPatch
  boundaryPatch_open := boundaryPatch_open
  boundaryPatch_bounded := boundaryPatch_bounded
  frontier_subset_iUnion := frontier_domain_subset_boundaryPatch

/-- The two affine endpoint charts, attached to the finite boundary cover. -/
def c1FlatteningCharts : Boundary.C1FlatteningCharts boundaryCover where
  chart := chart
  cutoff_support_subset_source := by
    change ∀ i : Fin 2,
      tsupport (boundaryCover.boundaryCutoff i).toFun ⊆ (chart i).source
    intro i
    have hi := boundaryCover.boundaryCutoff_support i
    rw [chart_source_eq_boundaryPatch]
    simpa [boundaryCover] using hi
  chart_contDiff := by
    intro i
    refine Fin.cases ?_ (fun _ ↦ ?_) i
    · exact leftChart_contDiff 1
    · exact rightChart_contDiff 1
  chart_symm_contDiff := by
    intro i
    refine Fin.cases ?_ (fun _ ↦ ?_) i
    · exact leftChart_symm_contDiff 1
    · exact rightChart_symm_contDiff 1
  chart_mem_iff_upper := by
    intro i
    refine Fin.cases ?_ (fun _ ↦ ?_) i
    · exact leftChart_mem_iff_upper
    · exact rightChart_mem_iff_upper
  chart_target_bounded := by
    intro i
    refine Fin.cases ?_ (fun _ ↦ ?_) i
    · exact bounded_leftChart_target
    · exact bounded_rightChart_target

/-- The fully explicit operational `C¹` extension atlas on `(-1,1)`. -/
@[reducible]
def c1ExtensionAtlas : Boundary.C1ExtensionAtlas 1 domain :=
  c1FlatteningCharts.toC1ExtensionAtlas

/-- The concrete interval carries its constructed extension atlas by typeclass inference. -/
instance domainC1ExtensionAtlas : Boundary.C1ExtensionAtlas 1 domain :=
  c1ExtensionAtlas

/-- Every boundary chart in the concrete interval atlas is smooth to arbitrary finite or
infinite order. -/
theorem atlas_chart_contDiff (m : ℕ∞) (i : Fin c1ExtensionAtlas.N) :
    ContDiff ℝ m fun x ↦ c1ExtensionAtlas.chart i x := by
  refine Fin.cases ?_ (fun _ ↦ ?_) i
  · exact leftChart_contDiff m
  · exact rightChart_contDiff m

/-- The inverse of every boundary chart in the concrete interval atlas is smooth to arbitrary
finite or infinite order. -/
theorem atlas_chart_symm_contDiff (m : ℕ∞) (i : Fin c1ExtensionAtlas.N) :
    ContDiff ℝ m fun x ↦ (c1ExtensionAtlas.chart i).symm x := by
  refine Fin.cases ?_ (fun _ ↦ ?_) i
  · exact leftChart_symm_contDiff m
  · exact rightChart_symm_contDiff m

end SobolevSpace.Boundary.Atlas.Interval
