/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.DirichletInverse.Subeigenvector
import PDE.Elliptic.Variational.Eigenfunction.Full.Regularity
import PDE.Analysis.Spectral.Positive.LpEigenvector

/-!
# A positive eigenpair for the full Dirichlet operator

The compact positive Dirichlet inverse and an interior subeigenvector
give a normalized nonnegative eigenvector by Schaefer compactness. Its
`H¹₀` representative solves the full weak eigen-equation. Smooth elliptic
regularity supplies its classical equation and geometric boundary values, and
the strong maximum principle makes it strictly positive.

This is the existence part of Evans §6.5.2, Theorem 3 for arbitrary drift and
nonnegative potential. Spectral ordering and geometric simplicity are
`Full.SpectralBound` and `Full.Simplicity`.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

open scoped SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- Construct a positive normalized Dirichlet eigenfunction and its
positive real eigenvalue from smooth geometry and full coefficients. -/
theorem exists_pos_eigenpair
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hconn : IsConnected Ω)
    (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    (hc : ∀ x ∈ Ω, 0 ≤ P.potential x) :
    ∃ (lambda : ℝ) (u : H¹₀(Ω)) (z : ℝ^n → ℝ),
      0 < lambda ∧ ‖baseCoordCLM u‖ = 1 ∧
      ContDiffOn ℝ (⊤ : ℕ∞) z (closure Ω) ∧
      (∀ k, ContDiffUpToBoundary k z Ω) ∧
      z =ᵐ[domainMeasure n Ω] weakSolutionBase u ∧
      (∀ x ∈ frontier Ω, z x = 0) ∧ (∀ x ∈ Ω, 0 < z x) ∧
      (∀ x ∈ Ω, P.classicalLoad z x = lambda * z x) ∧
      ∀ v : H¹₀(Ω),
        P.form hopen hbounded u v = lambda * ⟪baseCoordCLM u, baseCoordCLM v⟫_ℝ := by
  obtain ⟨w, M, hwne, hw0, hM, hsub⟩ :=
    P.exists_subeigenvector_l2SolutionOperator hopen hbounded hconn hgraph halpha hell hc
  obtain ⟨v, lambda, hvnorm, hvnonneg, hlambda, _, hveq⟩ :=
    (P.l2SolutionOperator hopen hbounded).exists_nonneg_eigenvector_of_subeigenvector
      (P.isCompactOperator_l2SolutionOperator hopen hbounded)
      (P.nonneg_l2SolutionOperator hopen hbounded hgraph halpha hell hc)
      hw0 hwne hM hsub
  let u : H¹₀(Ω) := lambda • P.dirichletSolution hopen hbounded v
  have hbase : baseCoordCLM u = v := by
    change baseCoordCLM (lambda • P.dirichletSolution hopen hbounded v) = v
    rw [map_smul]
    exact hveq.symm
  have hform (q : H¹₀(Ω)) :
      P.form hopen hbounded u q = lambda * ⟪baseCoordCLM u, baseCoordCLM q⟫_ℝ := by
    rw [hbase]
    change P.form hopen hbounded (lambda • P.dirichletSolution hopen hbounded v) q = _
    rw [map_smul, smul_apply]
    change lambda * P.form hopen hbounded (P.dirichletSolution hopen hbounded v) q = _
    rw [P.form_dirichletSolution hopen hbounded hgraph halpha hell hc]
  have hune : baseCoordCLM u ≠ 0 := by
    rw [hbase]
    intro hvzero
    rw [hvzero, norm_zero] at hvnorm
    exact zero_ne_one hvnorm
  obtain ⟨z, hz, hzraw, hzae, hboundary, hzpos, hload⟩ :=
    P.exists_pos_smoothRepresentative_of_eigenfunction hopen hbounded hconn.isPreconnected
      hgraph halpha hell lambda u hform (by simpa only [hbase] using hvnonneg) hune
  exact ⟨lambda, u, z, hlambda, by simpa only [hbase] using hvnorm,
    hz, hzraw, hzae, hboundary, hzpos, hload, hform⟩

end SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients
