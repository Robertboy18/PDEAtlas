/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Obstacle.Reaction
public import PDE.Elliptic.Regularity.Global.Poisson

/-!
# Global H² regularity for the obstacle minimizer

On a bounded `C²` domain, an `H²` obstacle with nonpositive boundary trace and
an `L²` load give an `H²` representative of every Dirichlet obstacle minimizer.
The proof constructs the bounded reaction before applying Poisson regularity.
The domain geometry is supplied as a `C1ExtensionAtlas`, an `InwardPartition`, and
`C²` graph-boundary data; this theorem does not construct those objects.

The conclusion includes the Lewy--Stampacchia bound, complementarity, and the
Poisson equation almost everywhere on the noncontact set. None of these is
assumed of the original `H¹₀` minimizer.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Sobolev Laplacian

namespace PDE.Elliptic.Obstacle

open SobolevSpace SobolevSpace.GraphSpace

open Boundary Approximation.UpToBoundary Boundary.Geometry.SurfaceMeasure

variable {m : ℕ} {Ω : Set ℝ^(m + 1)} [C1ExtensionAtlas (m + 1) Ω]

/-- Every obstacle minimizer has global `H²` regularity, a bounded nonnegative
reaction, complementarity, and the noncontact Poisson equation. Only the
obstacle, not the minimizer, is assumed to be in `H²`. -/
theorem exists_h2_representative_of_dirichletObstacle_minimizer
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
        (wkpBaseCoordinateCLM Ψ x < wkpBaseCoordinateCLM U x → (-(Δ U)) x = f x)) := by
  obtain ⟨v, l, hv, hvmin, hl, heq, hcontact⟩ :=
    exists_dirichletObstacle_reaction P hbounded Ψ f htrace
  obtain ⟨w, _, huniq⟩ := existsUnique_dirichletObstacle_minimizer
    (by omega) hbounded (wkpBaseCoordinateCLM Ψ) f u hu
  have hvu : v = u := (huniq v ⟨hv, hvmin⟩).trans (huniq u ⟨hu, hmin⟩).symm
  subst v
  obtain ⟨U, hU, hΔ⟩ :=
    (BoundaryRegularity.dirichletForm_eq_load_iff_h2
      C1ExtensionAtlas.isOpen hbounded hgraph u (f + l)).mp heq
  have hreac : -(Δ U) - f = l := by rw [hΔ]; abel
  refine ⟨U, hU, by simpa only [hreac] using hl, ?_⟩
  rw [hU, hreac]
  filter_upwards [hcontact, Lp.coeFn_add f l] with x hc hadd
  refine ⟨hc, fun hlt ↦ ?_⟩
  have hlzero : l x = 0 := (mul_eq_zero.mp hc).resolve_right (ne_of_gt (sub_pos.mpr hlt))
  rw [hΔ, hadd, Pi.add_apply, hlzero, add_zero]

end PDE.Elliptic.Obstacle
