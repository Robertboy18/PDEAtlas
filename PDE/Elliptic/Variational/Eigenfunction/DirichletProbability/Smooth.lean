/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.Coefficients.Laplace
public import PDE.Elliptic.Variational.Eigenfunction.DirichletProbability
public import PDE.Elliptic.Variational.Eigenfunction.Full.Regularity

/-!
# Smooth representatives of normalized Dirichlet eigenfunctions

The full-coefficient elliptic regularity theorem supplies a smooth
closure representative of the weak spectral weight on a smooth bounded domain.
Its normalization and classical Laplace eigen-equation follow from equality
almost everywhere and the constant-coefficient form identity.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open PDE (laplacian)
open scoped Sobolev ENNReal InnerProductSpace

namespace SobolevSpace.GraphSpace

open BoundaryRegularity

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- The normalized weak first eigenfunction has a positive smooth closure
representative on a smooth bounded domain. Its normalization is preserved. -/
theorem FirstDirichletEigenfunctionWeight.exists_smoothRepresentative
    (w : FirstDirichletEigenfunctionWeight Ω)
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hconn : IsPreconnected Ω)
    (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω) :
    ∃ z : ℝ^n → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) z (closure Ω) ∧
      (∀ k, ContDiffUpToBoundary k z Ω) ∧
      z =ᵐ[domainMeasure n Ω] baseCoordCLM w.vector ∧
      (∀ x ∈ frontier Ω, z x = 0) ∧ (∀ x ∈ Ω, 0 < z x) ∧
      (∫ x in Ω, z x) = 1 ∧
      ∀ x ∈ Ω, laplacian z x = -w.eigenvalue * z x := by
  have hell (x : ℝ^n) (_hx : x ∈ Ω) :
      MatrixEllipticLowerBound ((SmoothFullCoefficients.laplace (Ω := Ω)).principal x) 1 := by
    intro ξ
    change 1 * (ξ ⬝ᵥ ξ) ≤ principalEnergy (scalarIdentityMatrix 1) ξ
    rw [principalEnergy_scalarIdentityMatrix]
  have hne : baseCoordCLM w.vector ≠ 0 := by
    intro h
    apply w.eigenfunction.1
    apply baseCoordCLM_injective hΩ
    simpa only [map_zero] using h
  obtain ⟨z, hz, hzup, hzae, hzero, hpos, heq⟩ :=
    SmoothFullCoefficients.laplace.exists_pos_smoothRepresentative_of_eigenfunction
      hΩ hb hconn hgraph zero_lt_one hell w.eigenvalue w.vector (fun v ↦ by
        rw [SmoothFullCoefficients.form_laplace]
        simpa only [massFormCLM_apply] using w.eigenfunction.2 v)
      (w.positive.mono fun _ hx ↦ hx.le) hne
  refine ⟨z, hz, hzup, hzae, hzero, hpos, ?_, fun x hx ↦ ?_⟩
  · exact (integral_congr_ae hzae).trans w.integral_eq_one
  · have h := heq x hx
    rw [SmoothFullCoefficients.classicalLoad_laplace] at h
    linarith

end SobolevSpace.GraphSpace
