/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.DirichletInverse.Operator

/-!
# Weak eigen-equations and the Dirichlet inverse

The two-sided inverse identifies a weak eigenfunction with its `L²`
resolvent eigenvector. Conversely, an `L²` eigenvector lifts to `H¹₀` and
satisfies every weak test. An adjoint eigenfunction gives the corresponding
weighted pairing identity without any additional regularity assumption.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

open scoped SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- Uniqueness identifies any weak solution with the constructed inverse. -/
theorem eq_dirichletSolution_of_form_eq
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω)
    (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    (hc : ∀ x ∈ Ω, 0 ≤ P.potential x)
    (u : H¹₀(Ω)) (f : DerivLp n 2 Ω)
    (heq : ∀ v : H¹₀(Ω),
      P.form hopen hbounded u v = ⟪f, baseCoordCLM v⟫_ℝ) :
    u = P.dirichletSolution hopen hbounded f := by
  apply (P.bijective_form hopen hbounded hgraph halpha hell hc).injective
  ext v
  exact (heq v).trans
    (P.form_dirichletSolution hopen hbounded hgraph halpha hell hc f v).symm

/-- A weak eigenfunction is an eigenvector of the `L²` inverse. -/
theorem base_eq_smul_l2SolutionOperator_of_eigenfunction
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω)
    (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    (hc : ∀ x ∈ Ω, 0 ≤ P.potential x)
    (r : ℝ) (u : H¹₀(Ω))
    (heq : ∀ v : H¹₀(Ω),
      P.form hopen hbounded u v = r * ⟪baseCoordCLM u, baseCoordCLM v⟫_ℝ) :
    baseCoordCLM u = r • P.l2SolutionOperator hopen hbounded (baseCoordCLM u) := by
  have hu := P.eq_dirichletSolution_of_form_eq hopen hbounded hgraph halpha hell hc
    u (r • baseCoordCLM u) (fun v ↦ by rw [real_inner_smul_left]; exact heq v)
  have h := congrArg baseCoordCLM hu
  simpa only [map_smul, l2SolutionOperator, ContinuousLinearMap.comp_apply] using h

/-- An inverse eigenvector lifts to a weak Dirichlet eigenfunction
with exactly the original `L²` base coordinate. -/
theorem exists_eigenfunction_of_eq_smul_l2SolutionOperator
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω)
    (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    (hc : ∀ x ∈ Ω, 0 ≤ P.potential x)
    (r : ℝ) (f : DerivLp n 2 Ω)
    (hf : f = r • P.l2SolutionOperator hopen hbounded f) :
    ∃ u : H¹₀(Ω), baseCoordCLM u = f ∧
      ∀ v : H¹₀(Ω),
        P.form hopen hbounded u v = r * ⟪baseCoordCLM u, baseCoordCLM v⟫_ℝ := by
  let u := r • P.dirichletSolution hopen hbounded f
  have hbase : baseCoordCLM u = f := by
    change baseCoordCLM (r • P.dirichletSolution hopen hbounded f) = f
    rw [map_smul]
    exact hf.symm
  refine ⟨u, hbase, fun v ↦ ?_⟩
  rw [hbase]
  change P.form hopen hbounded (r • P.dirichletSolution hopen hbounded f) v = _
  rw [map_smul, smul_apply]
  change r * P.form hopen hbounded (P.dirichletSolution hopen hbounded f) v = _
  rw [P.form_dirichletSolution hopen hbounded hgraph halpha hell hc]

/-- Testing the inverse against an adjoint eigenfunction gives its
exact weighted pairing identity. -/
theorem mul_inner_l2SolutionOperator_of_adjoint_eigenfunction
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω)
    (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    (hc : ∀ x ∈ Ω, 0 ≤ P.potential x)
    (r : ℝ) (q : H¹₀(Ω))
    (hq : ∀ v : H¹₀(Ω),
      P.form hopen hbounded v q = r * ⟪baseCoordCLM v, baseCoordCLM q⟫_ℝ)
    (f : DerivLp n 2 Ω) :
    r * ⟪baseCoordCLM q, P.l2SolutionOperator hopen hbounded f⟫_ℝ =
      ⟪baseCoordCLM q, f⟫_ℝ := by
  have h := P.form_dirichletSolution hopen hbounded hgraph halpha hell hc f q
  rw [hq, real_inner_comm (baseCoordCLM q), real_inner_comm (baseCoordCLM q)] at h
  exact h

end SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients
