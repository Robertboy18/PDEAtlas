/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.Harmonic.Extension
public import PDE.Elliptic.Regularity.Interior.Weyl.Sobolev
public import PDE.Elliptic.Regularity.Boundary.Continuity.C1Domain

/-!
# Continuous harmonic extensions on C¹ domains

An H¹ lifting with continuous closure values determines a weak harmonic field
in its affine H¹₀ class. Weyl's lemma produces its interior classical
representative. The C¹ barriers give its boundary limits, which allow the
representative to be completed continuously with the prescribed boundary values.

Both the operational atlas and the inward partition are constructed from the
bounded open domain and its local C¹ graphs. No continuous harmonic extension,
trace right inverse, or boundary derivative is an input.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace

open Filter MeasureTheory Set
open SobolevSpace.Boundary SobolevSpace.Approximation.UpToBoundary
open SobolevSpace.Boundary.Geometry.SurfaceMeasure
open scoped ENNReal InnerProductSpace Topology

/-- A continuous H¹ lifting on a bounded open C¹ graph domain of dimension at
least two has a classical harmonic extension continuous on the closure and
belonging to the prescribed affine H¹₀ class. The construction allows empty and
disconnected domains. -/
theorem exists_continuous_harmonic_extension_of_local_graph
    {m : ℕ} {Ω : Set ℝ^(m + 1)} (hn : 2 ≤ m + 1)
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : HasC1GraphBoundary Ω)
    (G : H¹(Ω)) {g : ℝ^(m + 1) → ℝ}
    (hg : ContinuousOn g (closure Ω))
    (hG : baseRepresentative G =ᵐ[domainMeasure (m + 1) Ω] g) :
    ∃ w : H¹₀(Ω), ∃ u : ℝ^(m + 1) → ℝ,
      ContinuousOn u (closure Ω) ∧ LaplacianEquation.IsHarmonicPDE (m + 1) u Ω ∧
      EqOn u g (frontier Ω) ∧
      baseRepresentative (G + (w : H¹(Ω))) =ᵐ[domainMeasure (m + 1) Ω] u ∧
      ∀ t : H¹₀(Ω),
        (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i)
          (G + (w : H¹(Ω)))) (derivCoordCLM i t)) = 0 := by
  classical
  let := hgraph.c1ExtensionAtlas hΩ hbounded
  obtain ⟨P⟩ := exists_inwardPartition hΩ hbounded (hasC1Boundary_of_local_graph hgraph)
  obtain ⟨w, hw⟩ := exists_weak_harmonic_extension (by omega) hbounded G
  let U : H¹(Ω) := G + (w : H¹(Ω))
  have htrace : (Trace.C1.trace U : ℝ^(m + 1) → ℝ) =ᵐ[surfaceMeasure Ω] g := by
    have hT : Trace.C1.trace U = Trace.C1.trace G := by
      simp only [U, map_add, Trace.C1.trace_coe_H10_eq_zero, add_zero]
    rw [hT]
    exact Trace.C1.trace_eq_ae_of_continuousOn P G hg hG
  obtain ⟨v, hv, hUv⟩ := exists_isHarmonicPDE_ae_eq_of_dirichlet_eq_zero hΩ U hw
  have hlimit (z : frontier Ω) : Tendsto v (𝓝[Ω] (z : ℝ^(m + 1))) (𝓝 (g z)) :=
    PDE.Elliptic.BoundaryContinuity.tendsto_at_boundary_of_c1Domain hn P hbounded
      U hv.contDiffOn.continuousOn hg hUv htrace hw z
  have houtside {z : ℝ^(m + 1)} (hz : z ∈ frontier Ω) : z ∉ Ω := by
    rw [hΩ.frontier_eq] at hz
    exact hz.2
  let u : ℝ^(m + 1) → ℝ := fun x ↦ if x ∈ Ω then v x else g x
  have hu : ContinuousOn u (closure Ω) := by
    apply ContinuousOn.if'
    · intro z hz
      simp only [ite_eq_right (houtside hz.2)]
      exact (hlimit ⟨z, hz.2⟩).mono_left (nhdsWithin_mono _ inter_subset_right)
    · intro z hz
      simp only [ite_eq_right (houtside hz.2)]
      exact (hg z hz.1).mono inter_subset_left
    · exact hv.contDiffOn.continuousOn.mono inter_subset_right
    · exact hg.mono inter_subset_left
  have huv (x : ℝ^(m + 1)) (hx : x ∈ Ω) : u =ᶠ[𝓝 x] v := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact ite_eq_left hy
  refine ⟨w, u, hu, ⟨hv.contDiffOn.congr (fun x hx ↦ ite_eq_left hx), ?_⟩, ?_, ?_, hw⟩
  · intro x hx
    rw [EuclideanLaplacian.laplacian_congr_nhds (huv x hx)]
    exact hv.laplacian_eq_zero hx
  · intro x hx
    exact ite_eq_right (houtside hx)
  · filter_upwards [hUv, self_mem_ae_restrict hΩ.measurableSet] with x hx hxΩ
    simpa only [u, ite_eq_left hxΩ] using hx

end SobolevSpace.GraphSpace
