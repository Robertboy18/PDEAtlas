/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.Comparison.AffineBarrier
import PDE.Analysis.Topology.Compactness.Barrier

/-!
# Boundary limits from a weak barrier

Weak comparison bounds a harmonic function above and below by affine multiples
of a barrier. Compactness controls the boundary data away from the barrier's
vertex. Letting the barrier tend to zero proves the boundary limit of the
interior representative; continuity of that representative at the boundary is
not a hypothesis.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace PDE.Elliptic.BoundaryContinuity

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.Boundary SobolevSpace.Approximation.UpToBoundary
open SobolevSpace.Boundary.Geometry.SurfaceMeasure
open scoped ENNReal InnerProductSpace Topology

variable {m : ℕ} {Ω : Set ℝ^(m + 1)} [hΩ : C1ExtensionAtlas (m + 1) Ω]

/-- A continuous weak barrier at `z` gives the boundary limit of the continuous
interior representative of a weak harmonic function with continuous trace data. -/
theorem tendsto_at_boundary_of_dirichlet_barrier
    (P : InwardPartition Ω) (hbounded : Bornology.IsBounded Ω)
    (U B : H¹(Ω)) {u g b : ℝ^(m + 1) → ℝ}
    (hu : ContinuousOn u Ω) (hg : ContinuousOn g (closure Ω))
    (hb : ContinuousOn b (closure Ω))
    (hU : baseRepresentative U =ᵐ[domainMeasure (m + 1) Ω] u)
    (hB : baseRepresentative B =ᵐ[domainMeasure (m + 1) Ω] b)
    (htrace : (Trace.C1.trace U : ℝ^(m + 1) → ℝ) =ᵐ[surfaceMeasure Ω] g)
    (hweak : ∀ t : H¹₀(Ω),
      (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) U)
        (derivCoordCLM i t)) = 0)
    (hsuper : ∀ t : H¹₀(Ω),
      (∀ᵐ x ∂domainMeasure (m + 1) Ω, 0 ≤ baseCoordCLM t x) →
      0 ≤ ∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) B)
        (derivCoordCLM i t))
    (z : frontier Ω) (hbz : b z = 0)
    (hb0 : ∀ x ∈ closure Ω, 0 ≤ b x)
    (hbpos : ∀ x ∈ closure Ω, x ≠ z → 0 < b x) :
    Tendsto u (𝓝[Ω] (z : ℝ^(m + 1))) (𝓝 (g z)) := by
  have hz : (z : ℝ^(m + 1)) ∈ closure Ω := frontier_subset_closure z.property
  have hfrontier : ∀ᵐ x ∂surfaceMeasure Ω, x ∈ frontier Ω := by
    simpa only [surfaceMeasure, Nat.add_sub_cancel] using
      ae_restrict_mem (μ := Measure.euclideanHausdorffMeasure m) isClosed_frontier.measurableSet
  have hnegU : baseRepresentative (-U) =ᵐ[domainMeasure (m + 1) Ω] fun x ↦ -u x := by
    filter_upwards [baseRepresentative_neg_ae U, hU] with x hx hu
    simpa only [hu] using hx
  have hnegtrace : (Trace.C1.trace (-U) : ℝ^(m + 1) → ℝ)
      =ᵐ[surfaceMeasure Ω] fun x ↦ -g x := by
    rw [map_neg]
    filter_upwards [Lp.coeFn_neg (Trace.C1.trace U), htrace] with x hx ht
    simpa only [Pi.neg_apply, ht] using hx
  have hbound (ε : ℝ) (hε : 0 < ε) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Ω, |u x - g z| ≤ ε + C * b x := by
    obtain ⟨C, hC, hCg⟩ := PDE.Analysis.exists_nonneg_mul_barrier_bound
      hbounded.isCompact_closure hg hb hb0 hz hbpos hε
    have hupper := leOn_of_trace_le_affine_dirichlet_supersolution
      P hbounded U B hu hb hU hB (fun t _ ↦ (hweak t).le) hsuper (g z + ε) hC (by
        filter_upwards [htrace, hfrontier] with x ht hx
        have hgx := (abs_le.mp (hCg x (frontier_subset_closure hx))).2
        rw [ht]
        linarith)
    have hlower := leOn_of_trace_le_affine_dirichlet_supersolution
      P hbounded (-U) B hu.neg hb hnegU hB (by
        intro t _
        simp only [map_neg, inner_neg_left, Finset.sum_neg_distrib, hweak t, neg_zero, le_refl])
      hsuper (-g z + ε) hC (by
        filter_upwards [hnegtrace, hfrontier] with x ht hx
        have hgx := (abs_le.mp (hCg x (frontier_subset_closure hx))).1
        rw [ht]
        linarith)
    refine ⟨C, hC, fun x hx ↦ abs_le.mpr ⟨?_, ?_⟩⟩
    · have hlow : -u x ≤ -g z + ε + C * b x := hlower x hx
      linarith
    · linarith [hupper x hx]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨C, _, hC⟩ := hbound (ε / 2) (half_pos hε)
  have hlim : Tendsto (fun x ↦ C * b x) (𝓝[Ω] (z : ℝ^(m + 1))) (𝓝 0) := by
    have h := Filter.Tendsto.const_mul C
      ((hb z hz).mono subset_closure).tendsto
    simpa only [hbz, mul_zero] using h
  filter_upwards [self_mem_nhdsWithin, hlim.eventually (gt_mem_nhds (half_pos hε))]
    with x hx hsmall
  rw [Real.dist_eq]
  have hcx := hC x hx
  linarith

end PDE.Elliptic.BoundaryContinuity
