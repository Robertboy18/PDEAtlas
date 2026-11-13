/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Area.PairedMass
import PDE.Analysis.Integration.ApproximateIdentity.LebesguePoint
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Area.SurfaceBallGrowth

/-!
# Weighted paired-gradient limits on a C¹ boundary

The actual inward-minus-outward canonical-gradient kernel recovers every surface
L¹ density almost everywhere. The chart geometry supplies upper ball growth and
the vector mass; the actual kernel is measurable and satisfies the Poisson bound.
Besicovitch differentiation and the general weighted estimate complete the limit.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1

open Filter Set Metric MeasureTheory PDE.Analysis PotentialTheory
open Boundary.Geometry.SurfaceMeasure
open scoped Gradient Topology

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}
variable [Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- At almost every surface point, the actual paired canonical-gradient integral
recovers the L¹ density times the outward unit normal. All kernel estimates,
measurability, surface growth, and the vector mass limit follow from the C¹ atlas. -/
theorem ae_tendsto_integral_paired_gradient_fundamentalSolution_smul
    (hm : 1 ≤ m) {q : ℝ^(m + 1) → ℝ} (hq : Integrable q (surfaceMeasure Ω)) :
    ∀ᵐ x ∂surfaceMeasure Ω, ∀ hx : x ∈ frontier Ω,
      Tendsto (fun t : ℝ ↦ ∫ y : ℝ^(m + 1), q y •
        (∇ (fundamentalSolution (m + 1))
            (x - t • outwardUnitNormal (Ω := Ω) ⟨x, hx⟩ - y) -
          ∇ (fundamentalSolution (m + 1))
            (x + t • outwardUnitNormal (Ω := Ω) ⟨x, hx⟩ - y))
        ∂surfaceMeasure Ω) (𝓝[>] 0)
        (𝓝 (q x • outwardUnitNormal (Ω := Ω) ⟨x, hx⟩)) := by
  filter_upwards [ae_forall_tendsto_integral_smul_of_poisson_bound
    (E := ℝ^(m + 1)) hq] with x hx
  intro hxΩ
  let xb : frontier Ω := ⟨x, hxΩ⟩
  let K : ℝ → ℝ^(m + 1) → ℝ^(m + 1) := fun t y ↦
    ∇ (fundamentalSolution (m + 1))
        (x - t • outwardUnitNormal (Ω := Ω) xb - y) -
      ∇ (fundamentalSolution (m + 1))
        (x + t • outwardUnitNormal (Ω := Ω) xb - y)
  let C : ℝ := 2 ^ (m + 2) * (((m + 1 : ℕ) : ℝ) + 1) / unitSphereArea (m + 1)
  have hC : 0 ≤ C := div_nonneg (by positivity) (unitSphereArea_pos (n := m + 1)).le
  obtain ⟨A, _, δ, hδ, hgrowth⟩ := exists_surfaceMeasure_closedBall_le (Ω := Ω) xb
  obtain ⟨ε, hε, hbound⟩ := exists_paired_gradient_fundamentalSolution_bound
    (Ω := Ω) (by omega : 2 ≤ m + 1) xb
  apply hx m K (outwardUnitNormal (Ω := Ω) xb) A C hC
  · exact Eventually.of_forall (fun t ↦
      (measurable_paired_gradient_fundamentalSolution (m + 1) x _ t).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds] with t ht htε
    filter_upwards [ae_restrict_mem (μ := Measure.euclideanHausdorffMeasure m)
      isClosed_frontier.measurableSet] with y hy
    simpa only [K, C, xb, dist_eq_norm, norm_sub_rev y x] using hbound t ht htε y hy
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with r hr hrδ
    exact hgrowth r hr hrδ
  · exact tendsto_integral_paired_gradient_fundamentalSolution hm xb

end SobolevSpace.Trace.C1
