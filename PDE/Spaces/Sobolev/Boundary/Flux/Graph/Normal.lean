/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Flux.Graph.Topology
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal.DefiningFunction

/-!
# Signed graph area and the outward normal

The negative normalized graph conormal agrees with the intrinsic outward
unit normal wherever the graph represents the domain. Multiplication by
the area factor cancels the normalization and retains its outward sign.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Boundary.Flux.Graph

open Set Filter Trace.HalfSpace Trace.C1
open scoped Topology

variable {m : ℕ}

/-- The outward unit normal of the graph, indexed by its tangential parameter. -/
def linearGraphOutwardNormal
    (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) (g : ℝ^m → ℝ) (y : ℝ^m) : ℝ^(m + 1) :=
  -‖linearGraphConormal A g y‖⁻¹ • linearGraphConormal A g y

/-- The physical conormal of a C¹ graph is continuous in its parameter. -/
theorem continuous_linearGraphConormal
    (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) {g : ℝ^m → ℝ} (hg : ContDiff ℝ 1 g) :
    Continuous (linearGraphConormal A g) := by
  unfold linearGraphConormal linearGraphCovector
  exact (InnerProductSpace.toDual ℝ (ℝ^(m + 1))).symm.continuous.comp
    ((continuous_const.sub
      ((hg.continuous_fderiv one_ne_zero).clm_comp continuous_const)).clm_comp
        continuous_const)

/-- The outward graph normal is continuous because the conormal never vanishes. -/
theorem continuous_linearGraphOutwardNormal
    (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) {g : ℝ^m → ℝ} (hg : ContDiff ℝ 1 g) :
    Continuous (linearGraphOutwardNormal A g) := by
  have hc := continuous_linearGraphConormal A hg
  exact (hc.norm.inv₀ (fun y ↦ norm_ne_zero_iff.mpr
    (linearGraphConormal_ne_zero A g y))).neg.smul hc

/-- Signed graph area is the negative conormal times the coordinate volume
factor; this includes the one-dimensional boundary case. -/
theorem normDet_linearGraphTangent_smul_outwardNormal
    (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) (g : ℝ^m → ℝ) (y : ℝ^m) :
    (linearGraphTangent A g y).toLinearMap.normDet • linearGraphOutwardNormal A g y =
      -|A.symm.toLinearMap.det| • linearGraphConormal A g y := by
  have hc := norm_ne_zero_iff.mpr (linearGraphConormal_ne_zero A g y)
  rw [normDet_linearGraphTangent, linearGraphOutwardNormal, smul_smul]
  congr 1
  field_simp

/-- The graph formula computes the intrinsic outward normal of any domain
which agrees with the epigraph on an open patch. -/
theorem outwardUnitNormal_eq_linearGraph
    {Ω U : Set (ℝ^(m + 1))} [C1ExtensionAtlas (m + 1) Ω]
    (hU : IsOpen U) (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1))
    {g : ℝ^m → ℝ} (hg : ContDiff ℝ 1 g)
    (hside : ∀ x ∈ U, x ∈ Ω ↔ x ∈ linearEpigraph A g)
    {x : ℝ^(m + 1)} (hx : x ∈ U) (hxb : x ∈ frontier Ω) :
    outwardUnitNormal (Ω := Ω) ⟨x, hxb⟩ =
      linearGraphOutwardNormal A g (splitTangentialNormal (A x)).1 := by
  apply outwardUnitNormal_eq_of_defining_function hxb
    (hasFDerivAt_linearGraphHeight A hg x) (linearGraphCovector_ne_zero A g _)
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact (mem_frontier_iff_graphHeight_eq_zero hU A g hg.continuous hside hy).mp
  · filter_upwards [hU.mem_nhds hx] with y hy
    intro hyΩ
    exact sub_nonneg.mpr ((hside y hy).mp hyΩ).le

end SobolevSpace.Boundary.Flux.Graph
