/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.Domain
public import PDE.Spaces.Sobolev.Boundary.Atlas.Construction

/-!
# Constructing operational C2 boundary atlases

We upgrade the generic first-order flattening-chart construction to
the `C²` operational atlas used by elliptic boundary regularity.
-/

@[expose] public section

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace.Boundary

open Set

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- Globally represented `C²` flattening charts attached to a finite boundary
cover. -/
structure C2FlatteningCharts (cover : FiniteBoundaryCover n Ω) where
  /-- Boundary-flattening charts, indexed by the boundary neighborhoods. -/
  chart : Fin cover.N → OpenPartialHomeomorph (ℝ^n) (ℝ^n)
  /-- Each chart source contains the corresponding cutoff support. -/
  cutoff_support_subset_source :
    ∀ i, tsupport (cover.boundaryCutoff i).toFun ⊆ (chart i).source
  /-- Every total forward chart representative is globally `C²`. -/
  chart_contDiff_two :
    ∀ i, ContDiff ℝ 2 fun x ↦ chart i x
  /-- Every total inverse-chart representative is globally `C²`. -/
  chart_symm_contDiff_two :
    ∀ i, ContDiff ℝ 2 fun y ↦ (chart i).symm y
  /-- On its source, each chart identifies the domain with the upper
  half-space. -/
  chart_mem_iff_upper :
    ∀ i, ∀ x ∈ (chart i).source,
      (x ∈ Ω ↔ chart i x ∈ SobolevSpace.HalfSpace.upper n)
  /-- Every chart target is bounded. -/
  chart_target_bounded : ∀ i, Bornology.IsBounded (chart i).target

namespace C2FlatteningCharts

variable {cover : FiniteBoundaryCover n Ω}

/-- Forget one derivative from a `C²` flattening family. -/
@[reducible]
def toC1FlatteningCharts (charts : C2FlatteningCharts cover) :
    C1FlatteningCharts cover where
  chart := charts.chart
  cutoff_support_subset_source := charts.cutoff_support_subset_source
  chart_contDiff := fun i ↦ (charts.chart_contDiff_two i).of_le (by norm_num)
  chart_symm_contDiff := fun i ↦
    (charts.chart_symm_contDiff_two i).of_le (by norm_num)
  chart_mem_iff_upper := charts.chart_mem_iff_upper
  chart_target_bounded := charts.chart_target_bounded

/-- Construct an operational `C²` boundary atlas from a finite boundary cover
and compatible globally represented `C²` flattening charts. -/
@[reducible]
def toC2BoundaryAtlas (charts : C2FlatteningCharts cover) :
    SobolevSpace.C2BoundaryAtlas n Ω where
  toC1ExtensionAtlas :=
    charts.toC1FlatteningCharts.toC1ExtensionAtlas
  chart_contDiff_two := charts.chart_contDiff_two
  chart_symm_contDiff_two := charts.chart_symm_contDiff_two

end C2FlatteningCharts

end SobolevSpace.Boundary
