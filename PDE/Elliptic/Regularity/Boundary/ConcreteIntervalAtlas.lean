/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.Construction
public import PDE.Spaces.Sobolev.Boundary.Atlas.Interval

/-!
# A concrete `C²` boundary atlas on a bounded interval

The affine interval charts constructed in
`PDE.Spaces.Sobolev.Boundary.Atlas.Interval` are smooth at every finite order.
We assemble their order-two regularity into the operational
`C2BoundaryAtlas` required by the elliptic boundary-regularity theory.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Boundary.Atlas.Interval

/-- The affine endpoint charts with their order-two regularity, attached to
the interval boundary cover. -/
def c2FlatteningCharts : Boundary.C2FlatteningCharts boundaryCover where
  chart := c1FlatteningCharts.chart
  cutoff_support_subset_source :=
    c1FlatteningCharts.cutoff_support_subset_source
  chart_contDiff_two := by
    intro i
    exact atlas_chart_contDiff 2 i
  chart_symm_contDiff_two := by
    intro i
    exact atlas_chart_symm_contDiff 2 i
  chart_mem_iff_upper := c1FlatteningCharts.chart_mem_iff_upper
  chart_target_bounded := c1FlatteningCharts.chart_target_bounded

/-- The explicit operational `C²` boundary atlas on `(-1,1) ⊂ ℝ^1`. -/
@[reducible]
def c2BoundaryAtlas : SobolevSpace.C2BoundaryAtlas 1 domain :=
  c2FlatteningCharts.toC2BoundaryAtlas

end SobolevSpace.Boundary.Atlas.Interval
