/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.C1.LocalPieces.ChartOperator
public import PDE.Spaces.Sobolev.Extension.HalfSpace.FirstOrder.Operator

/-!
# Reflected boundary operator for C1 extension

We compose half-space reflection, chart-target restriction, compact
relocalization, and chart pullback into one bounded boundary contribution.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace

open Set
open scoped ENNReal Topology

namespace Extension

namespace C1

variable {n : ℕ} {p : ℝ≥0∞} {Ω : Set (ℝ^n)}

open MeasureTheory
open CompactSupportLocalization

namespace BoundaryPiece

variable [Fact (0 < n)] [Fact (1 ≤ p)] [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- Reflect a flattened upper-half-space field globally and retain its
restriction to the `i`-th chart target. -/
noncomputable def reflectedChartTargetCLM (i : Fin hΩ.N) :
    W^{1,p}((SobolevSpace.HalfSpace.upper n)) →L[ℝ]
      W^{1,p}((hΩ.chart i).target) :=
  (SobolevSpace.GraphSpace.restrictCLM
    (n := n) (k := 1) (p := p) (Ω := (hΩ.chart i).target)
    (Ωbig := (Set.univ : Set (ℝ^n)))
    (hΩ.chart i).open_target.measurableSet (subset_univ _)).comp
      (SobolevSpace.Extension.GraphSpace.HalfSpace.operator
        (n := n) (p := p)).toContinuousLinearMap

/-- The complete bounded boundary-chart operation after flattening: reflect
across the flat boundary, relocalize in the chart target, and pull back to a
global `W^{1,p}(ℝ^n)` field. -/
noncomputable def boundaryFromUpperCLM (i : Fin hΩ.N) :
    W^{1,p}((SobolevSpace.HalfSpace.upper n)) →L[ℝ]
      W^{1,p}((Set.univ : Set (ℝ^n))) :=
  (preparedChartCLM (n := n) (p := p) (Ω := Ω) i).comp
    (reflectedChartTargetCLM (n := n) (p := p) (Ω := Ω) i)

/-- On ambient bundles, the chart-target map reflects across the boundary and restricts to
the chart target. -/
@[simp] theorem reflectedChartTargetCLM_apply_coe
    (i : Fin hΩ.N)
    (U : W^{1,p}((SobolevSpace.HalfSpace.upper n))) :
    ((reflectedChartTargetCLM (n := n) (p := p) (Ω := Ω) i U :
        W^{1,p}((hΩ.chart i).target)) :
        SobolevSpace.GraphSpace.WkpAmbientOn n 1 p (hΩ.chart i).target) =
      SobolevSpace.GraphSpace.restrictAmbient
        (n := n) (k := 1) (p := p)
        (subset_univ _)
        (((SobolevSpace.Extension.GraphSpace.HalfSpace.operator
          (n := n) (p := p)).toContinuousLinearMap U :
          W^{1,p}((Set.univ : Set (ℝ^n)))) :
          SobolevSpace.GraphSpace.WkpAmbientOn n 1 p (Set.univ : Set (ℝ^n))) :=
  rfl

/-- The ambient boundary piece is obtained by applying the prepared chart map to the
reflected upper-half-space field. -/
@[simp] theorem boundaryFromUpperCLM_apply_coe
    (i : Fin hΩ.N)
    (U : W^{1,p}((SobolevSpace.HalfSpace.upper n))) :
    ((boundaryFromUpperCLM (n := n) (p := p) (Ω := Ω) i U :
        W^{1,p}((Set.univ : Set (ℝ^n)))) :
        SobolevSpace.GraphSpace.WkpAmbientOn n 1 p (Set.univ : Set (ℝ^n))) =
      preparedChartAmbient (n := n) (p := p) (Ω := Ω) i
        (reflectedChartTargetCLM (n := n) (p := p) (Ω := Ω) i U) :=
  rfl

end BoundaryPiece

end C1

end Extension

end SobolevSpace
