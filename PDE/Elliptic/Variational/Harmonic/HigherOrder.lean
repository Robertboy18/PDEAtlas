/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Global.Poisson.HigherOrder
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Laplacian.HigherOrder
import PDE.Spaces.Sobolev.Calculus.IntegrationByParts.LaplacianH10

/-!
# Higher regularity of affine harmonic fields

Subtract a Sobolev lifting from the harmonic field. The resulting H¹₀ field
solves the unshifted Poisson equation with the lifting's Laplacian as
load. Global Poisson regularity then restores the full order of the lifting.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

/-- A weak harmonic field in an affine H¹₀ class inherits the finite Sobolev
order of its lifting on a graph domain of that order. -/
theorem exists_higherOrder_of_affine_dirichlet_eq_zero
    {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n} (k : ℕ)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary (k + 2) Ω)
    (G : W^{k + 2,2}(Ω)) (w : H¹₀(Ω))
    (hw : ∀ t : H¹₀(Ω),
      (∑ i, ⟪wkpCoordinateCLM (singleDerivIndex n i)
        (lowerOrderCLM (by omega : 1 ≤ k + 2) G + (w : H¹(Ω))),
          derivCoordCLM i t⟫_ℝ) = 0) :
    ∃ V : W^{k + 2,2}(Ω),
      wkpBaseCoordinateCLM V =
        wkpBaseCoordinateCLM (lowerOrderCLM (by omega : 1 ≤ k + 2) G +
          (w : H¹(Ω))) := by
  let F : W^{k,2}(Ω) := higherOrderLaplacianCLM (by omega) G
  have hform : dirichletForm w = loadFunctional (wkpBaseCoordinateCLM F) := by
    ext t
    have hparts := sum_inner_gradient_eq_neg_inner_laplacian
      (lowerOrderCLM (by omega : 2 ≤ k + 2) G) t
    rw [lowerOrderCLM_trans_apply] at hparts
    have hzero := hw t
    simp only [map_add, inner_add_left, Finset.sum_add_distrib] at hzero
    rw [hparts] at hzero
    rw [dirichletForm_apply, loadFunctional_apply]
    dsimp only [F]
    rw [higherOrderLaplacianCLM_base]
    simp only [wkpCoordinateCLM_apply, derivCoordCLM_apply] at hzero ⊢
    linarith
  obtain ⟨W, hW⟩ :=
    BoundaryRegularity.exists_higherOrder_of_dirichletForm_eq_load
      k hopen hbounded hgraph F w hform
  refine ⟨G + W, ?_⟩
  rw [map_add, map_add, hW]
  rfl

end SobolevSpace.GraphSpace
