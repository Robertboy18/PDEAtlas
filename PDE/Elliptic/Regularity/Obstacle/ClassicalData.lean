/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Obstacle.Contact

/-!
# Obstacle regularity from classical data

A classical `C²` obstacle continuous on the closure and nonpositive on the
boundary supplies the Sobolev obstacle and its signed trace. The domain
assumptions are boundedness, openness, and `C²` graph boundary; the operational
atlas and inward partition are constructed in the proof.

This gives the global `H²` and complementary Poisson conclusions for the
Dirichlet-energy minimizer without any regularity assumption on that minimizer.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Sobolev Laplacian

namespace PDE.Elliptic.Obstacle

open SobolevSpace SobolevSpace.GraphSpace

open Boundary Approximation.UpToBoundary Boundary.Geometry.SurfaceMeasure

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}

/-- Classical `C²` obstacle data with the boundary sign required by the
homogeneous Dirichlet condition imply global `H²` regularity, the reaction
bound, complementarity, and the contact and noncontact equations for every
obstacle minimizer. All boundary infrastructure is derived from geometry. -/
theorem exists_h2_dirichletObstacle_minimizer_of_classical
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : HasContDiffGraphBoundary 2 Ω)
    (ψ : ℝ^(m + 1) → ℝ) (hψ : ContDiffUpToBoundary 2 ψ Ω)
    (hψcont : ContinuousOn ψ (closure Ω)) (hψboundary : ∀ x ∈ frontier Ω, ψ x ≤ 0)
    (f : DerivLp (m + 1) 2 Ω) (u : H¹₀(Ω))
    (hu : u ∈ dirichletObstacleSet (hψ.toLp hopen hbounded 2))
    (hmin : IsMinOn (dirichletEnergy f)
      (dirichletObstacleSet (hψ.toLp hopen hbounded 2)) u) :
    ∃ U : W^{2,2}(Ω), wkpBaseCoordinateCLM U = baseCoordCLM u ∧
      (-(Δ U) - f) ∈ Icc 0
        (Lp.posPart (-(Δ (hψ.toWkpSpaceOn hopen hbounded 2)) - f)) ∧
      (∀ᵐ x ∂domainMeasure (m + 1) Ω,
        (-(Δ U) - f) x * (wkpBaseCoordinateCLM U x - ψ x) = 0 ∧
        (wkpBaseCoordinateCLM U x = ψ x →
          (Δ U) x = (Δ (hψ.toWkpSpaceOn hopen hbounded 2)) x) ∧
        (ψ x < wkpBaseCoordinateCLM U x → (-(Δ U)) x = f x)) := by
  have hC1 := hgraph.hasC1GraphBoundary (by norm_num)
  let := hC1.c1ExtensionAtlas hopen hbounded
  obtain ⟨P⟩ := exists_inwardPartition hopen hbounded (hasC1Boundary_of_local_graph hC1)
  let Ψ : W^{2,2}(Ω) := hψ.toWkpSpaceOn hopen hbounded 2
  have hbase : baseRepresentative (lowerOrderCLM (by norm_num : 1 ≤ 2) Ψ)
      =ᵐ[domainMeasure (m + 1) Ω] ψ := by
    rw [baseRepresentative_lowerOrderCLM]
    exact hψ.toWkpSpaceOn_base_ae hopen hbounded 2
  have ht := Trace.C1.trace_eq_ae_of_continuousOn P
    (lowerOrderCLM (by norm_num : 1 ≤ 2) Ψ) hψcont hbase
  have hfrontier : ∀ᵐ x ∂surfaceMeasure Ω, x ∈ frontier Ω := by
    simpa only [surfaceMeasure, Nat.add_sub_cancel] using
      ae_restrict_mem (μ := Measure.euclideanHausdorffMeasure m) isClosed_frontier.measurableSet
  have htrace : ∀ᵐ x ∂surfaceMeasure Ω,
      Trace.C1.trace (lowerOrderCLM (by norm_num : 1 ≤ 2) Ψ) x ≤ 0 := by
    filter_upwards [ht, hfrontier] with x hx hxΩ
    rw [hx]
    exact hψboundary x hxΩ
  have hΨ : wkpBaseCoordinateCLM Ψ = hψ.toLp hopen hbounded 2 :=
    hψ.toWkpSpaceOn_base_eq_toLp hopen hbounded 2
  obtain ⟨U, hU, hbound, hpoint⟩ :=
    exists_h2_dirichletObstacle_minimizer_contact_equations P hbounded hgraph Ψ f htrace u
      (by simpa only [hΨ] using hu) (by simpa only [hΨ] using hmin)
  refine ⟨U, hU, hbound, ?_⟩
  filter_upwards [hpoint, hψ.toWkpSpaceOn_base_ae hopen hbounded 2] with x hx hψx
  simpa only [Ψ, hψx] using hx

end PDE.Elliptic.Obstacle
