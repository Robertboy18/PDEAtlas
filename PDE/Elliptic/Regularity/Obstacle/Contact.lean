/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Obstacle.H2
import PDE.Spaces.Sobolev.Calculus.LevelSet

/-!
# The obstacle equation on the contact set

The Sobolev coincidence-set theorem identifies the minimizer's Laplacian with
the obstacle Laplacian on contact. Together with H² regularity and the reaction
bound, this gives the contact and noncontact equations for the same minimizer.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Sobolev Laplacian

namespace PDE.Elliptic.Obstacle

open SobolevSpace SobolevSpace.GraphSpace

open Boundary Approximation.UpToBoundary Boundary.Geometry.SurfaceMeasure

variable {m : ℕ} {Ω : Set ℝ^(m + 1)} [C1ExtensionAtlas (m + 1) Ω]

/-- The obstacle minimizer is globally `H²`, satisfies complementarity and the
Lewy--Stampacchia bound, and has the obstacle Laplacian on contact and the
prescribed Poisson load off contact, almost everywhere. -/
theorem exists_h2_dirichletObstacle_minimizer_contact_equations
    (P : InwardPartition Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : HasContDiffGraphBoundary 2 Ω)
    (Ψ : W^{2,2}(Ω)) (f : DerivLp (m + 1) 2 Ω)
    (htrace : ∀ᵐ x ∂surfaceMeasure Ω,
      Trace.C1.trace (lowerOrderCLM (by norm_num : 1 ≤ 2) Ψ) x ≤ 0)
    (u : H¹₀(Ω)) (hu : u ∈ dirichletObstacleSet (wkpBaseCoordinateCLM Ψ))
    (hmin : IsMinOn (dirichletEnergy f)
      (dirichletObstacleSet (wkpBaseCoordinateCLM Ψ)) u) :
    ∃ U : W^{2,2}(Ω), wkpBaseCoordinateCLM U = baseCoordCLM u ∧
      (-(Δ U) - f) ∈ Icc 0 (Lp.posPart (-(Δ Ψ) - f)) ∧
      (∀ᵐ x ∂domainMeasure (m + 1) Ω,
        (-(Δ U) - f) x * (wkpBaseCoordinateCLM U x - wkpBaseCoordinateCLM Ψ x) = 0 ∧
        (wkpBaseCoordinateCLM U x = wkpBaseCoordinateCLM Ψ x → (Δ U) x = (Δ Ψ) x) ∧
        (wkpBaseCoordinateCLM Ψ x < wkpBaseCoordinateCLM U x → (-(Δ U)) x = f x)) := by
  obtain ⟨U, hU, hbound, hpoint⟩ :=
    exists_h2_representative_of_dirichletObstacle_minimizer
      P hbounded hgraph Ψ f htrace u hu hmin
  refine ⟨U, hU, hbound, ?_⟩
  filter_upwards [hpoint, laplacian_eq_ae_on_coincidence_set U Ψ] with x hx hcontact
  exact ⟨hx.1, hcontact, hx.2⟩

end PDE.Elliptic.Obstacle
