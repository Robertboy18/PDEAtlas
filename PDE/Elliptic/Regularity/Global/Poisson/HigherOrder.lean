/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Global.Poisson
public import PDE.Elliptic.Regularity.Global.ClassicalHigherBoundaryData

/-!
# Higher Poisson regularity from a graph boundary

The identity principal matrix and zero lower-order coefficients specialize the
finite-order global elliptic estimate to the unshifted Dirichlet form. The
result preserves the given weak solution and its L² representative.
There is no coercive mass shift in the equation.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

/-- An Hᵏ Poisson load on a bounded open Cᵏ⁺² graph domain gives an Hᵏ⁺²
representative of the H¹₀ weak solution. -/
theorem exists_higherOrder_of_dirichletForm_eq_load
    {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n} (k : ℕ)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary (k + 2) Ω)
    (F : W^{k,2}(Ω)) (u : H¹₀(Ω))
    (hu : dirichletForm u = loadFunctional (wkpBaseCoordinateCLM F)) :
    ∃ W : W^{k + 2,2}(Ω),
      wkpBaseCoordinateCLM W = baseCoordCLM u := by
  have hell (x : ℝ^n) (_hx : x ∈ Ω) :
      MatrixEllipticLowerBound (scalarIdentityMatrix (n := n) 1) 1 := by
    intro ξ
    rw [principalEnergy_scalarIdentityMatrix]
  obtain ⟨_, _, hreg⟩ :=
    exists_global_higherOrder_estimate_of_contDiffUpToBoundary k hopen hbounded hgraph
      (fun _ ↦ scalarIdentityMatrix 1) (fun _ _ ↦ 0) (fun _ ↦ 0)
      (fun i j ↦ ContDiffUpToBoundary.const (scalarIdentityMatrix 1 i j))
      (fun _ ↦ ContDiffUpToBoundary.const 0) (ContDiffUpToBoundary.const 0)
      0 1 zero_lt_one hell
  have hz : (ContDiffUpToBoundary.const (n := n) (Ω := Ω) (k := k + 1) 0).toLp
      hopen hbounded ∞ = 0 := by
    apply Lp.ext
    exact ((ContDiffUpToBoundary.const 0).toLp_coeFn hopen hbounded ∞).trans
      (Lp.coeFn_zero (E := ℝ) (p := ∞) (μ := domainMeasure n Ω)).symm
  have hw := (isWeakSolution_iff_isWeakShiftedFullDivergenceSolution hopen
    (fun i j : Fin n ↦
      (ContDiffUpToBoundary.const (k := 1) (scalarIdentityMatrix 1 i j)).toLp
        hopen hbounded ∞) 0 0 0 (wkpBaseCoordinateCLM F) 0 u).mp (by
      intro v
      rw [shiftedDivergenceForm_apply,
        fullDivergenceForm_identity_eq_dirichletForm hopen hbounded, hu]
      simp only [zero_mul, add_zero, generalizedLoad_apply, Pi.zero_apply,
        inner_zero_left, Finset.sum_const_zero, loadFunctional_apply])
  obtain ⟨W, hW, _⟩ := hreg F u (by
    simp only [hz]
    simpa only [ContDiffUpToBoundary.toLp, Pi.zero_def] using hw)
  exact ⟨W, hW⟩

end SobolevSpace.GraphSpace.BoundaryRegularity
