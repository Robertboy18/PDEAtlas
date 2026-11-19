/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.GeometricAtlas
public import PDE.Elliptic.Regularity.Global.HigherOrder
public import PDE.Elliptic.Regularity.SolutionOperator.Lift
public import PDE.Elliptic.Variational.DistributionalPoisson
import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData

/-!
# Dirichlet inverse regularity from smooth domain geometry

The global elliptic theorem gives two derivatives for the Dirichlet inverse on a
bounded domain with `C^{k+2}` graph boundary. Constant identity coefficients meet the
coefficient hypotheses automatically. The closed-graph lift of
`PDE.Elliptic.Regularity.SolutionOperator.Lift` then turns this qualitative regularity
into a bounded map `H^k → H^{k+2}`.

These maps transfer convergence and time differentiation of weighted heat series
to higher Sobolev norms. Neither an elliptic estimate nor eigenfunction bounds are
additional inputs.
-/

@[expose] public section

noncomputable section

namespace HeatEquation

open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.GraphSpace.BoundaryRegularity
open MeasureTheory
open scoped Sobolev ENNReal

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- Global Poisson regularity follows from the geometric boundary hypothesis. -/
theorem exists_higherOrder_dirichletPoisson (k : ℕ) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary (k + 2) Ω)
    (F : W^{k,2}(Ω)) (u : H¹₀(Ω))
    (hu : IsWeakPoissonSolution (wkpBaseCoordinateCLM F) u) :
    ∃ W : W^{k + 2,2}(Ω), wkpBaseCoordinateCLM W = baseCoordCLM u := by
  classical
  obtain ⟨atlas, hchart, hinv⟩ :=
    hgraph.exists_higherOrderBoundaryAtlas k hopen hbounded
  let hc (i j : Fin n) : ContDiffUpToBoundary (k + 1)
      (fun _ : ℝ^n ↦ if i = j then 1 else 0) Ω := ContDiffUpToBoundary.const _
  let A (i j : Fin n) : W^{k + 1,∞}(Ω) := (hc i j).toWkpSpaceOn hopen hbounded ∞
  have hrep (i j : Fin n) :
      (wkpBaseCoordinateCLM (A i j) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun _ ↦ if i = j then 1 else 0 :=
    (hc i j).toWkpSpaceOn_base_ae hopen hbounded ∞
  have hid := multiplicationCoefficientOperator_eq_identity_of_ae
    (fun i j ↦ wkpBaseCoordinateCLM (A i j)) hrep
  have hdiv : IsWeakDivergenceSolution
      (fun i j ↦ wkpBaseCoordinateCLM (A i j)) (wkpBaseCoordinateCLM F) u := by
    apply (isWeakSolution_iff_isWeakDivergenceSolution hopen _ _ _).1
    intro v
    rw [hid, variableCoeffForm_identity]
    exact (isWeakSolution_iff_isWeakPoissonSolution hopen _ _).2 hu v
  obtain ⟨W, hW⟩ := exists_global_higherOrder_of_isWeakDivergenceSolution k
    atlas hchart hinv A (fun _ ↦ scalarIdentityMatrix 1) hrep
    (fun _ _ ↦ contDiff_const) F u hdiv 1 zero_lt_one (fun _ _ ξ ↦ by
      rw [principalEnergy_scalarIdentityMatrix])
  exact ⟨W, Lp.ext hW⟩

/-- The qualitative higher-order lift of the Dirichlet inverse is derived from geometry. -/
theorem hasHigherSolutionLift_dirichletSolve (k : ℕ) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary (k + 2) Ω) :
    HasHigherSolutionLift k (dirichletSolveCLM (Fact.out : 0 < n) hbounded) := by
  intro F
  exact exists_higherOrder_dirichletPoisson k hopen hbounded hgraph F _
    (dirichletSolve.isWeakPoissonSolution hopen (Fact.out : 0 < n) hbounded _)

/-- The bounded two-derivative Dirichlet lift, constructed from a graph boundary. -/
def dirichletHigherSolveCLM (k : ℕ) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary (k + 2) Ω) :
    W^{k,2}(Ω) →L[ℝ] W^{k + 2,2}(Ω) :=
  higherSolutionOperator hopen (dirichletSolveCLM (Fact.out : 0 < n) hbounded)
    (hasHigherSolutionLift_dirichletSolve k hopen hbounded hgraph)

/-- The lifted inverse represents the same weak zero-boundary Poisson solution. -/
theorem dirichletHigherSolveCLM_base (k : ℕ) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary (k + 2) Ω) (F : W^{k,2}(Ω)) :
    wkpBaseCoordinateCLM (dirichletHigherSolveCLM k hopen hbounded hgraph F) =
      baseCoordCLM (dirichletSolveCLM (Fact.out : 0 < n) hbounded
        (wkpBaseCoordinateCLM F)) :=
  higherSolutionOperator_base hopen _ _ F

end HeatEquation
