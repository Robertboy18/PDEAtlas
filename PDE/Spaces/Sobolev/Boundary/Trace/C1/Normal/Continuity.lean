/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal

/-!
# Continuity of the outward normal

The conormal of a C¹ boundary chart is continuous. Its nonvanishing on the
chart source permits normalization, and agreement on overlaps gives continuity
of the intrinsic outward normal on the boundary.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Trace.C1

open Filter Set
open scoped Topology

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
variable [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- The conormal of a globally C¹ chart is continuous. -/
theorem continuous_chartConormal (i : Fin hΩ.N) :
    Continuous (chartConormal (n := n) (Ω := Ω) i) := by
  unfold chartConormal
  exact (InnerProductSpace.toDual ℝ (ℝ^n)).symm.continuous.comp
    (continuous_const.clm_comp ((hΩ.chart_contDiff i).continuous_fderiv one_ne_zero))

/-- Normalization is continuous wherever the chart conormal is nonzero. -/
theorem continuousAt_chartOutwardUnitNormal (i : Fin hΩ.N) {x : ℝ^n}
    (hx : x ∈ (hΩ.chart i).source) :
    ContinuousAt (chartOutwardUnitNormal (n := n) (Ω := Ω) i) x := by
  unfold chartOutwardUnitNormal
  have hc := (continuous_chartConormal (n := n) (Ω := Ω) i).continuousAt (x := x)
  exact (hc.norm.inv₀ (norm_ne_zero_iff.mpr (chartConormal_ne_zero i hx))).neg.smul hc

/-- The intrinsic outward unit normal is continuous on the boundary subtype. -/
theorem continuous_outwardUnitNormal :
    Continuous (outwardUnitNormal (n := n) (Ω := Ω)) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨i, hi⟩ := exists_chart_source_of_mem_frontier
    (n := n) (Ω := Ω) x.property
  have hc := (continuousAt_chartOutwardUnitNormal i hi).comp
    continuous_subtype_val.continuousAt
  apply hc.congr
  filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
    ((hΩ.chart i).open_source.mem_nhds hi)] with y hy
  exact (outwardUnitNormal_eq_chart y i hy).symm

end SobolevSpace.Trace.C1
