/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.OrderedDirichletSpectrum
public import PDE.Elliptic.Variational.DistributionalPoisson

/-!
# An ordered weak Dirichlet basis for heat evolution

The variational spectral theorem of `PDE.Elliptic.Variational.OrderedDirichletSpectrum`,
specialized to the identity coefficients,
constructs a complete ordered Laplace eigenbasis on any nonempty bounded open domain.
The eigenfunctions are recorded in `H¹₀`, with the distributional Poisson equation needed
to identify weighted heat sums through the Dirichlet inverse. No boundary smoothness
or pointwise eigenfunction estimate enters this construction.
-/

@[expose] public section

noncomputable section

namespace HeatEquation

open SobolevSpace SobolevSpace.GraphSpace Filter
open scoped Sobolev InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- An ordered Hilbert basis of weak zero-boundary Laplace eigenfunctions. -/
structure DirichletHeatSpectrum (n : ℕ) (Ω : Set (ℝ^n)) where
  /-- The complete orthonormal basis in the pivot space. -/
  basis : HilbertBasis ℕ ℝ (DerivLp n 2 Ω)
  /-- Positive eigenvalues, counted with multiplicity. -/
  eigenvalue : ℕ → ℝ
  /-- The energy-space representatives of the basis. -/
  eigenfunction : ℕ → H¹₀(Ω)
  /-- Every eigenvalue is strictly positive. -/
  eigenvalue_pos : ∀ i, 0 < eigenvalue i
  /-- The list is nondecreasing. -/
  monotone_eigenvalue : Monotone eigenvalue
  /-- The list tends to infinity. -/
  tendsto_eigenvalue : Tendsto eigenvalue atTop atTop
  /-- Energy and pivot representatives coincide. -/
  base_eigenfunction : ∀ i, baseCoordCLM (eigenfunction i) = basis i
  /-- Each eigenfunction satisfies its distributional Dirichlet equation. -/
  poisson_eigenfunction : ∀ i,
    IsWeakPoissonSolution (eigenvalue i • basis i) (eigenfunction i)

/-- Every nonempty bounded open domain in positive dimension has an ordered Dirichlet
heat spectrum. This is a consequence of the compact variational spectral theorem. -/
theorem nonempty_dirichletHeatSpectrum (hn : 0 < n) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    Nonempty (DirichletHeatSpectrum n Ω) := by
  obtain ⟨b, lambda, u, hmono, htendsto, hspec, _⟩ :=
    exists_ordered_hilbertBasis_variableCoeff_eigenfunctions hn hopen hbounded hne
      (identityCoefficientOperator (n := n) (Ω := Ω))
      integratedElliptic_identity symmetricCoefficientOperator_identity
  refine ⟨⟨b, lambda, u, fun i ↦ (hspec i).1, hmono, htendsto,
    fun i ↦ (hspec i).2.1, ?_⟩⟩
  intro i
  apply (isWeakSolution_iff_isWeakPoissonSolution hopen _ _).1
  intro v
  have h := (hspec i).2.2.2 v
  rw [variableCoeffForm_identity, massFormCLM_apply, (hspec i).2.1] at h
  simpa only [loadFunctional_apply, real_inner_smul_left] using h

/-- The spectrum chosen from bounded open domain geometry. -/
def dirichletHeatSpectrum (hn : 0 < n) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    DirichletHeatSpectrum n Ω :=
  Classical.choice (nonempty_dirichletHeatSpectrum hn hopen hbounded hne)

namespace DirichletHeatSpectrum

variable (S : DirichletHeatSpectrum n Ω)

/-- Dirichlet eigenvalues satisfy the nonnegativity required by Hilbert heat damping. -/
theorem eigenvalue_nonneg (i : ℕ) : 0 ≤ S.eigenvalue i :=
  (S.eigenvalue_pos i).le

/-- The Poisson inverse recovers an energy eigenfunction from its eigenvalue-weighted
pivot representative. -/
theorem dirichletSolve_eigenvalue_smul (hn : 0 < n) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (i : ℕ) :
    dirichletSolveCLM hn hbounded (S.eigenvalue i • S.basis i) = S.eigenfunction i :=
  ((IsWeakPoissonSolution.iff_eq_dirichletSolve hopen hn hbounded _).1
    (S.poisson_eigenfunction i)).symm

end DirichletHeatSpectrum

end HeatEquation
