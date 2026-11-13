/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Spectral.DirichletClassical

/-!
# The normalized Dirichlet eigenfunction heat series

The elliptic lifts construct smooth representatives of the original orthonormal
eigenbasis. They turn the regularized spectral sums into the usual series
`∑ exp(-λᵢ t) ⟪f, φᵢ⟫ φᵢ`, with the original `L²` normalization.

Convergence in every Hölder derivative graph, and hence uniform convergence of
the corresponding spatial derivative fields, is derived from the Hilbert series
and the bounded elliptic lifts. No eigenfunction growth bound is assumed.
-/

@[expose] public section

noncomputable section

namespace HeatEquation.DirichletHeatSpectrum

open SobolevSpace SobolevSpace.GraphSpace HolderSpace MeasureTheory Set
open scoped Sobolev ContDiff

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {γ : Exponent}
  (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
  (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω) (hγ : (γ : ℝ) < 1)
  (S : DirichletHeatSpectrum n Ω)

/-- Eigenvalue powers cancel the iterated Dirichlet inverse on each basis vector. -/
theorem iteratedDirichletSolveCLM_eigenvalue_pow_base (k i : ℕ) :
    wkpBaseCoordinateCLM (iteratedDirichletSolveCLM hopen hbounded hgraph k
      (S.eigenvalue i ^ k • S.basis i)) = S.basis i := by
  induction k with
  | zero =>
    rw [pow_zero, one_smul, iteratedDirichletSolveCLM_zero_base]
  | succ k ih =>
    rw [iteratedDirichletSolveCLM_succ_base, pow_succ', mul_smul, map_smul, map_smul, ih,
      S.dirichletSolve_eigenvalue_smul (Fact.out : 0 < n) hopen hbounded, S.base_eigenfunction]

/-- The normalized eigenfunction in the full `C^{j,γ}` derivative graph. -/
def eigenfunctionHolder (j i : ℕ) : CKGammaOn n j Ω γ :=
  dirichletHolderLiftCLM hopen hbounded hgraph hγ j
    (S.eigenvalue i ^ (j + n + 1) • S.basis i)

/-- Elliptic smoothing retains the original normalized eigenbasis almost everywhere. -/
theorem eigenfunctionHolder_ae (j i : ℕ) :
    (S.eigenfunctionHolder hopen hbounded hgraph hγ j i).interiorDerivative 0
      =ᵐ[domainMeasure n Ω] (S.basis i : ℝ^n → ℝ) := by
  have h := dirichletHolderLiftCLM_ae hopen hbounded hgraph hγ j
    (S.eigenvalue i ^ (j + n + 1) • S.basis i)
  apply h.trans
  exact Filter.Eventually.of_forall fun x ↦ congrArg (fun F : DerivLp n 2 Ω ↦ F x)
    (S.iteratedDirichletSolveCLM_eigenvalue_pow_base hopen hbounded hgraph (j + n + 1) i)

/-- A smooth representative of the original normalized Dirichlet eigenfunction. -/
def classicalEigenfunction (i : ℕ) : ℝ^n → ℝ :=
  (S.eigenfunctionHolder hopen hbounded hgraph hγ 2 i).interiorDerivative 0

/-- Classical and Hilbert eigenfunctions represent the same normalized class. -/
theorem classicalEigenfunction_ae (i : ℕ) :
    S.classicalEigenfunction hopen hbounded hgraph hγ i
      =ᵐ[domainMeasure n Ω] (S.basis i : ℝ^n → ℝ) :=
  S.eigenfunctionHolder_ae hopen hbounded hgraph hγ 2 i

/-- Every higher derivative graph represents the same classical eigenfunction. -/
theorem classicalEigenfunction_eq_holder (j i : ℕ) :
    S.classicalEigenfunction hopen hbounded hgraph hγ i =
      (S.eigenfunctionHolder hopen hbounded hgraph hγ j i).interiorDerivative 0 := by
  have h := CKGammaOn.toBoundedContinuousFunction_eq_of_ae_eq hopen
    ((S.eigenfunctionHolder_ae hopen hbounded hgraph hγ 2 i).trans
      (S.eigenfunctionHolder_ae hopen hbounded hgraph hγ j i).symm)
  change Function.extend Subtype.val
      (S.eigenfunctionHolder hopen hbounded hgraph hγ 2 i).toBoundedContinuousFunction 0 =
    Function.extend Subtype.val
      (S.eigenfunctionHolder hopen hbounded hgraph hγ j i).toBoundedContinuousFunction 0
  rw [h]

/-- Every normalized eigenfunction is spatially smooth, as a consequence of elliptic lifting. -/
theorem contDiffOn_classicalEigenfunction (i : ℕ) :
    ContDiffOn ℝ ∞ (S.classicalEigenfunction hopen hbounded hgraph hγ i) Ω := by
  apply contDiffOn_infty.mpr
  intro j
  rw [S.classicalEigenfunction_eq_holder hopen hbounded hgraph hγ j i]
  exact (S.eigenfunctionHolder hopen hbounded hgraph hγ j i).contDiffOn_derivative
    hopen j 0 (by simp)

/-- The usual eigenfunction series converges in every classical Hölder derivative norm,
also after any eigenvalue power. -/
theorem hasSum_eigenfunctionHolder (j m : ℕ) (f : DerivLp n 2 Ω)
    {t : ℝ} (ht : 0 < t) :
    HasSum (fun i ↦
      (S.eigenvalue i ^ m * Real.exp (-S.eigenvalue i * t) * S.basis.repr f i) •
        S.eigenfunctionHolder hopen hbounded hgraph hγ j i)
      (S.holderPower hopen hbounded hgraph hγ j m f t) := by
  apply (S.hasSum_holderPower hopen hbounded hgraph hγ j m f ht).congr_fun
  intro i
  unfold eigenfunctionHolder
  rw [map_smul, smul_smul]
  congr 1
  rw [pow_add]
  ring

/-- Every spatial derivative series converges uniformly on the closure, with the
original eigenfunction normalization and the usual heat coefficients. -/
theorem hasSum_eigenfunctionHolder_derivative (j m : ℕ) (a : MultiIndex n j)
    (f : DerivLp n 2 Ω) {t : ℝ} (ht : 0 < t) :
    HasSum (fun i ↦
      (S.eigenvalue i ^ m * Real.exp (-S.eigenvalue i * t) * S.basis.repr f i) •
        (S.eigenfunctionHolder hopen hbounded hgraph hγ j i).derivative a)
      ((S.holderPower hopen hbounded hgraph hγ j m f t).derivative a) := by
  simpa only [map_smul, CKGammaOn.derivativeCLM_apply] using
    (CKGammaOn.derivativeCLM a).hasSum
      (S.hasSum_eigenfunctionHolder hopen hbounded hgraph hγ j m f ht)

/-- The classical heat solution is the usual normalized eigenfunction series at every
point of the closure. -/
theorem hasSum_classicalEigenfunction (f : DerivLp n 2 Ω)
    {t : ℝ} (ht : 0 < t) {x : ℝ^n} (hx : x ∈ closure Ω) :
    HasSum (fun i ↦ Real.exp (-S.eigenvalue i * t) * S.basis.repr f i *
      S.classicalEigenfunction hopen hbounded hgraph hγ i x)
      (S.classicalPower hopen hbounded hgraph hγ 0 f t x) := by
  have h := (BoundedContinuousFunction.evalCLM ℝ ⟨x, hx⟩).hasSum
    (S.hasSum_eigenfunctionHolder_derivative hopen hbounded hgraph hγ 2 0 0 f ht)
  simpa only [map_smul, pow_zero, one_mul, smul_eq_mul,
    BoundedContinuousFunction.evalCLM_apply, classicalPower, classicalEigenfunction,
    CKGammaOn.interiorDerivative_apply _ _ hx] using h

end HeatEquation.DirichletHeatSpectrum
