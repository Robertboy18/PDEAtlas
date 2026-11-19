/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Geometry.HalfSpace
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions

/-!
# C¹ extension atlases

An operational `C¹` extension atlas on a bounded open set `Ω ⊆ ℝ^n` consists of finitely many
boundary charts `chart i`, each a partial homeomorphism of `ℝ^n` whose total representative and
inverse are globally `C¹` and which identifies `Ω ∩ source` with the upper half-space
`{y | 0 < y_n}` inside the target, together with a smooth partition of unity on `Ω` made of one
interior cutoff supported in `Ω` and one cutoff per chart supported in its source. This is the
data used in the proof of the extension theorem for bounded `C¹` domains (Evans, PDE, §5.4):
localize with the partition of unity, flatten each boundary piece, extend by reflection across the
hyperplane, and pull back.

The class `C1ExtensionAtlas` records this data, with charts that are globally `C¹`
representatives. `Boundary.Atlas.Construction` assembles an atlas from a finite boundary cover
and flattening charts, and `Boundary.Atlas.Geometric.GraphConstruction` produces one for a
bounded open set with `C¹` graph boundary.

The ambient `C1ExtensionAtlas` instance selects an atlas and its partition of unity.
All constructions are relative to that choice; in particular, an extension may depend
on the chosen atlas outside the domain. The class holds auxiliary data, not a canonical
geometric structure.

## Main declarations

* `C1ExtensionAtlas`: the atlas data as a class on `(n, Ω)`.
* `C1ExtensionAtlas.Charts.chartOnΩ`: the `i`-th chart restricted to `Ω` on the source side, with
  `chartOnΩ_target_eq_target_inter_upper` identifying its target as `target ∩ upper n`.

## Implementation notes

Charts are `OpenPartialHomeomorph (ℝ^n) (ℝ^n)`, so `chart i` and `(chart i).symm` are total
functions; the `C¹` hypotheses are about these total functions, which is what the weak chain rule
for Sobolev functions needs. Cutoffs are Euclidean test functions `𝓓(⊤, ℝ)`, and boundedness of
the chart targets is recorded so that finite-measure arguments are available for `p = ∞`.

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

namespace SobolevSpace

open Set


namespace Boundary

/-- Operational atlas for the extension construction on a bounded `C¹` domain.

It includes the specific charts and cutoffs needed to build an extension operator
by reducing to the half-space construction and summing via a partition of unity.

This structure is stronger than the geometric predicate that `Ω` has `C¹`
boundary; `Boundary.Atlas.Geometric.GraphConstruction` constructs it from local graph
charts. -/
class C1ExtensionAtlas (n : ℕ) [Fact (0 < n)] (Ω : Set (ℝ^n)) : Type where
  /-- `Ω` is open. -/
  isOpen : IsOpen Ω
  /-- `Ω` is bounded. -/
  bounded : Bornology.IsBounded Ω
  /-- Number of boundary charts (finite). -/
  N : ℕ
  /-- Boundary charts (partial homeomorphisms) that flatten `Ω` to the half-space. -/
  chart : Fin N → OpenPartialHomeomorph (ℝ^n) (ℝ^n)
  /-- `C¹` regularity of the (total) chart maps.

  We work with charts as total functions `ℝ^n → ℝ^n` which are `C¹` globally, and only later
  restrict them to an open source where they are invertible.

  The weak chain rule below uses globally defined maps. Obtaining such representatives from the
  standard local definition of a bounded `C¹` boundary requires shrinking the chart
  neighborhoods. -/
  chart_contDiff : ∀ i, ContDiff ℝ 1 (fun x ↦ chart i x)
  /-- `C¹` regularity of the (total) inverse chart maps. -/
  chart_symm_contDiff : ∀ i, ContDiff ℝ 1 (fun y ↦ (chart i).symm y)
  /-- On each chart domain, membership in `Ω` is equivalent to membership in
  the upper half-space. -/
  chart_mem_iff_upper :
    ∀ i, ∀ x ∈ (chart i).source, (x ∈ Ω ↔ chart i x ∈ SobolevSpace.HalfSpace.upper n)
  /-- Chart targets are bounded (useful for `p = ∞` reductions via finite measure). -/
  chart_target_bounded : ∀ i, Bornology.IsBounded (chart i).target
  /-- Interior cutoff supported strictly inside `Ω`. -/
  interiorCutoff : 𝓓((⊤ : Opens (ℝ^n)), ℝ)
  /-- The interior cutoff is supported in `Ω`. -/
  interiorCutoff_support : tsupport interiorCutoff.toFun ⊆ Ω
  /-- Boundary cutoffs indexed by the boundary charts. -/
  boundaryCutoff : Fin N → 𝓓((⊤ : Opens (ℝ^n)), ℝ)
  /-- Each boundary cutoff is supported in its corresponding chart source. -/
  boundaryCutoff_support :
    ∀ i, tsupport (boundaryCutoff i).toFun ⊆ (chart i).source
  /-- Partition of unity on `Ω`: the interior and boundary cutoffs sum to one. -/
  cutoff_sum_eq_one :
    ∀ x ∈ Ω, interiorCutoff.toFun x + ∑ i, (boundaryCutoff i).toFun x = 1

/-- A `C¹` extension domain is bounded, so its domain measure is finite. This is the
finite-measure hypothesis of the composition and compactness theorems on such domains. -/
instance C1ExtensionAtlas.isFiniteMeasure_domainMeasure {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
    [hΩ : C1ExtensionAtlas n Ω] : MeasureTheory.IsFiniteMeasure (domainMeasure n Ω) :=
  isFiniteMeasure_domainMeasure_of_isBounded hΩ.bounded

/-!
## Cutoffs equal to `1` on the partition supports

For each partition function, a smooth support cutoff `χᵢ` is supported in the chart domain and
equals `1` on the compact support of that partition function. These cutoffs follow from smooth
separation of a compact set from the complement of an open set; they are constructed in
`Boundary.Atlas.Cutoffs`.
-/

namespace C1ExtensionAtlas

/-!
## Charts restricted to `Ω`

For each boundary chart `chart i : OpenPartialHomeomorph (ℝ^n) (ℝ^n)`, we
restrict it to `Ω` (on the source side). This produces a partial
homeomorphism whose target is exactly `chart i`.target ∩ upper n, by the
`chart_mem_iff_upper` hypothesis.
-/

namespace Charts

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} [hΩ : C1ExtensionAtlas n Ω]

open SobolevSpace.HalfSpace

/-- The `i`-th boundary chart, restricted to `Ω` on its source side. -/
noncomputable def chartOnΩ (i : Fin hΩ.N) : OpenPartialHomeomorph (ℝ^n) (ℝ^n) :=
  (hΩ.chart i).restrOpen Ω hΩ.isOpen

/-- The source of the restricted chart is the original source intersected with `Ω`. -/
theorem chartOnΩ_source (i : Fin hΩ.N) :
    (chartOnΩ (n := n) (Ω := Ω) i).source = (hΩ.chart i).source ∩ Ω :=
  by simp [chartOnΩ]

/-- The partial equivalence underlying the restricted chart is the restriction of the original
one to `Ω`. -/
@[simp] theorem chartOnΩ_toPartialEquiv (i : Fin hΩ.N) :
    (chartOnΩ (n := n) (Ω := Ω) i).toPartialEquiv = (hΩ.chart i).toPartialEquiv.restr Ω :=
  by simp [chartOnΩ]

/-- The target of the restricted chart, in the form produced by `PartialEquiv.restr`: the
original target intersected with the preimage of `Ω` under the inverse chart. -/
theorem chartOnΩ_target (i : Fin hΩ.N) :
    (chartOnΩ (n := n) (Ω := Ω) i).target = (hΩ.chart i).target ∩ (hΩ.chart i).symm ⁻¹' Ω := by
  simp [chartOnΩ, PartialEquiv.restr_target]

/-- The restricted chart maps `Ω ∩ source` onto `target ∩ upper n`, by applying
`chart_mem_iff_upper` to the inverse chart. -/
theorem chartOnΩ_target_eq_target_inter_upper (i : Fin hΩ.N) :
    (chartOnΩ (n := n) (Ω := Ω) i).target = (hΩ.chart i).target ∩ upper n := by
  ext y
  constructor
  · intro hy
    have hy' : y ∈ (hΩ.chart i).target ∩ (hΩ.chart i).symm ⁻¹' Ω := by
      simpa [chartOnΩ_target (n := n) (Ω := Ω) (i := i)] using hy
    refine ⟨hy'.1, ?_⟩
    have hx_source : (hΩ.chart i).symm y ∈ (hΩ.chart i).source :=
      (hΩ.chart i).map_target hy'.1
    have hxΩ : (hΩ.chart i).symm y ∈ Ω := hy'.2
    -- `chart_mem_iff_upper` evaluated at `x = chart.symm y`.
    have : ((hΩ.chart i).symm y ∈ Ω ↔ (hΩ.chart i) ((hΩ.chart i).symm y) ∈ upper n) :=
      hΩ.chart_mem_iff_upper i ((hΩ.chart i).symm y) hx_source
    have : (hΩ.chart i) ((hΩ.chart i).symm y) ∈ upper n := (this.mp hxΩ)
    simpa [(hΩ.chart i).right_inv hy'.1] using this
  · rintro ⟨hyT, hyU⟩
    have hy_pre : (hΩ.chart i).symm y ∈ Ω := by
      have hx_source : (hΩ.chart i).symm y ∈ (hΩ.chart i).source :=
        (hΩ.chart i).map_target hyT
      have hiff : ((hΩ.chart i).symm y ∈ Ω ↔ (hΩ.chart i) ((hΩ.chart i).symm y) ∈ upper n) :=
        hΩ.chart_mem_iff_upper i ((hΩ.chart i).symm y) hx_source
      have hchart : (hΩ.chart i) ((hΩ.chart i).symm y) ∈ upper n := by
        simpa [(hΩ.chart i).right_inv hyT] using hyU
      exact hiff.2 hchart
    have : y ∈ (hΩ.chart i).target ∩ (hΩ.chart i).symm ⁻¹' Ω := ⟨hyT, hy_pre⟩
    simpa [chartOnΩ_target (n := n) (Ω := Ω) (i := i)] using this

/-- The image of `Ω ∩ source` under a boundary chart lies in the upper half-space. -/
theorem chartOnΩ_target_subset_upper (i : Fin hΩ.N) :
    (chartOnΩ (n := n) (Ω := Ω) i).target ⊆ upper n := by
  intro y hy
  have hy' : y ∈ (chartOnΩ (n := n) (Ω := Ω) i).target := hy
  -- Rewrite the target set before unfolding membership in the intersection.
  have hy'' := hy'
  rw [chartOnΩ_target_eq_target_inter_upper (n := n) (Ω := Ω) (i := i)] at hy''
  exact hy''.2

end Charts

end C1ExtensionAtlas

end Boundary

end SobolevSpace
