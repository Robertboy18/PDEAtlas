/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.ContinuousRepresentative
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.ZeroTrace
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Geometry
import PDE.Spaces.Sobolev.Boundary.Trace.C1.MeasureClass

/-!
# Pointwise boundary values of continuous Sobolev functions

Continuous boundary functions equal almost everywhere for surface measure agree
everywhere. Pullback to an open tangential chart reduces this to the corresponding
Lebesgue-measure statement, including zero-dimensional charts in spatial dimension one.
Together with trace agreement and the trace kernel theorem, this characterizes zero
Sobolev trace by pointwise vanishing on the entire boundary.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1

open MeasureTheory Set GraphSpace Boundary
open Boundary.Geometry.SurfaceMeasure
open scoped ENNReal Sobolev

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}

/-- Continuous boundary representatives agreeing surface almost everywhere agree
at every boundary point. This also covers the two endpoint charts in dimension one. -/
theorem eqOn_frontier_of_ae_eq [H : Boundary.C1ExtensionAtlas (m + 1) Ω]
    {f g : ℝ^(m + 1) → ℝ}
    (hf : ContinuousOn f (frontier Ω)) (hg : ContinuousOn g (frontier Ω))
    (hfg : f =ᵐ[surfaceMeasure Ω] g) : EqOn f g (frontier Ω) := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp (frontier_subset_iUnion_chart_source hx)
  obtain ⟨y, hy, rfl⟩ :=
    (image_chartBoundaryParametrization i).symm ▸ (show x ∈
      (H.chart i).source ∩ frontier Ω from ⟨hi, hx⟩)
  have hmap := contDiff_chartBoundaryParametrization (Ω := Ω) i
  have hmem : MapsTo (chartBoundaryParametrization (Ω := Ω) i)
      (chartBoundaryParameterDomain (Ω := Ω) i) (frontier Ω) := by
    intro z hz
    have hzimage := (image_chartBoundaryParametrization i).subset ⟨z, hz, rfl⟩
    exact hzimage.2
  have hae := (chartBoundaryReferenceMeasure_absolutelyContinuous_surfaceMeasure
    (Ω := Ω) i).ae_eq hfg
  have hpull := ae_of_ae_map hmap.continuous.measurable.aemeasurable hae
  exact Measure.eqOn_open_of_ae_eq hpull (isOpen_chartBoundaryParameterDomain i)
    (hf.comp hmap.continuous.continuousOn hmem)
    (hg.comp hmap.continuous.continuousOn hmem) hy

/-- A continuous representative has zero trace exactly when it vanishes pointwise
on the boundary. The operational trace atlas is constructed from raw C¹ geometry. -/
theorem mem_Wkp0_iff_eq_zero_on_frontier_of_continuousOn
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : HasC1GraphBoundary Ω)
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (U : W^{1,ENNReal.ofReal p}(Ω))
    {f : ℝ^(m + 1) → ℝ} (hf : ContinuousOn f (closure Ω))
    (hUf : baseRepresentative U =ᵐ[domainMeasure (m + 1) Ω] f) :
    U ∈ (wkp0SubmoduleOn (n := m + 1) (k := 1) (p := ENNReal.ofReal p)
      (Ω := Ω)).toSubmodule ↔ ∀ x ∈ frontier Ω, f x = 0 := by
  let := hgraph.c1ExtensionAtlas hopen hbounded
  have htrace := traceLp_eq_ae_of_continuousOn_of_local_graph
    hopen hbounded hgraph p U hf hUf
  rw [← traceLp_eq_zero_iff_mem_Wkp0 p U]
  constructor
  · intro hzero
    have hae : f =ᵐ[surfaceMeasure Ω] (0 : ℝ^(m + 1) → ℝ) := by
      exact htrace.symm.trans (hzero ▸ Lp.coeFn_zero _ _ _)
    exact eqOn_frontier_of_ae_eq (hf.mono frontier_subset_closure)
      continuousOn_const hae
  · intro hzero
    apply Lp.ext
    refine htrace.trans ?_
    filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet,
      Lp.coeFn_zero ℝ (ENNReal.ofReal p) (μ := surfaceMeasure Ω)] with x hx h0
    exact (hzero x hx).trans h0.symm

/-- Continuous H¹ representatives with the same boundary values belong
to the same affine H¹₀ class. -/
theorem sub_mem_H10_of_eqOn_frontier [H : C1ExtensionAtlas (m + 1) Ω]
    (P : Approximation.UpToBoundary.InwardPartition Ω)
    (U V : H¹(Ω)) {u v : ℝ^(m + 1) → ℝ}
    (hu : ContinuousOn u (closure Ω)) (hv : ContinuousOn v (closure Ω))
    (hU : baseRepresentative U =ᵐ[domainMeasure (m + 1) Ω] u)
    (hV : baseRepresentative V =ᵐ[domainMeasure (m + 1) Ω] v)
    (heq : EqOn u v (frontier Ω)) :
    U - V ∈ (h10SubmoduleOn (n := m + 1) (Ω := Ω)).toSubmodule := by
  apply (trace_eq_zero_iff_mem_H10 _).mp
  rw [map_sub, sub_eq_zero]
  apply Lp.ext
  filter_upwards [trace_eq_ae_of_continuousOn P U hu hU,
    trace_eq_ae_of_continuousOn P V hv hV,
    ae_restrict_mem (μ := Measure.euclideanHausdorffMeasure m)
      isClosed_frontier.measurableSet] with x hux hvx hx
  exact hux.trans ((heq hx).trans hvx.symm)

end SobolevSpace.Trace.C1
