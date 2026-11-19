/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Spectral.DirichletUniqueness
import PDE.Spaces.Sobolev.Calculus.IntegrationByParts.LaplacianTest

/-!
# Initial reconstruction for compact smooth data

Iterated negative Laplacians remain compactly supported smooth functions. Integration
by parts derives their weighted spectral coefficients, and the Dirichlet inverse
recovers the original datum. The resulting heat orbit is continuous through time zero
in every classical Hölder norm. Compatibility of these test data is proved here.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace HeatEquation

open SobolevSpace SobolevSpace.GraphSpace MeasureTheory Set HolderSpace
open scoped Sobolev InnerProductSpace Topology

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The negative Laplacian preserves compactly supported smooth domain tests. -/
def negativeTestLaplacian (φ : TestFunctionOn n Ω) : TestFunctionOn n Ω :=
  -∑ i : Fin n, φ.iteratedPartialDeriv [i, i]

/-- The test-function operation computes the classical negative Laplacian. -/
theorem negativeTestLaplacian_apply (φ : TestFunctionOn n Ω) (x : ℝ^n) :
    (negativeTestLaplacian φ).1.toFun x = -PDE.laplacian φ.1.toFun x := by
  simp [negativeTestLaplacian, TestFunction.toFun_eq_coe, PDE.laplacian,
    iteratedPartialDeriv]

/-- Integration by parts identifies a test function as the weak Dirichlet solution
for its classical negative Laplacian. -/
theorem isWeakPoissonSolution_negativeTestLaplacian (hopen : IsOpen Ω)
    (φ : TestFunctionOn n Ω) :
    IsWeakPoissonSolution (baseCoordCLM (testFunctionToH10 (negativeTestLaplacian φ)))
      (testFunctionToH10 φ) := by
  apply (isWeakSolution_iff_isWeakPoissonSolution hopen _ _).1
  intro v
  rw [dirichletForm_symm, dirichletForm_apply]
  have h := sum_inner_deriv_test_eq_neg_integral_laplacian v.1 φ
  change (∑ i, ⟪derivCoordCLM i v, derivCoordCLM i (testFunctionToH10 φ)⟫_ℝ) =
    -(∫ x, baseCoordCLM v x * PDE.laplacian φ.1.toFun x ∂domainMeasure n Ω) at h
  rw [h, loadFunctional_apply, L2.inner_def, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [baseCoordCLM_testFunction_apply_ae (negativeTestLaplacian φ)] with x hx
  rw [hx, negativeTestLaplacian_apply]
  simp only [RCLike.inner_apply, conj_trivial, mul_neg]

namespace DirichletHeatSpectrum

variable (S : DirichletHeatSpectrum n Ω)

/-- All powers of the spectral weights of compact smooth data are derived from its
iterated classical Laplacians, rather than assumed summable. -/
theorem repr_iterate_negativeTestLaplacian (hopen : IsOpen Ω)
    (k : ℕ) (φ : TestFunctionOn n Ω) (i : ℕ) :
    S.basis.repr (baseCoordCLM (testFunctionToH10 (negativeTestLaplacian^[k] φ))) i =
      S.eigenvalue i ^ k * S.basis.repr (baseCoordCLM (testFunctionToH10 φ)) i := by
  induction k generalizing φ with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih,
      S.repr_of_isWeakPoissonSolution (isWeakPoissonSolution_negativeTestLaplacian hopen φ),
      pow_succ]
    ring

end DirichletHeatSpectrum

variable [Fact (0 < n)] (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
  (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)

/-- Iterating the geometrically constructed inverse reconstructs each compact smooth
datum from the corresponding iterated classical negative Laplacian. -/
theorem iteratedDirichletSolveCLM_test_base (k : ℕ) (φ : TestFunctionOn n Ω) :
    wkpBaseCoordinateCLM (iteratedDirichletSolveCLM hopen hbounded hgraph k
      (baseCoordCLM (testFunctionToH10 (negativeTestLaplacian^[k] φ)))) =
      baseCoordCLM (testFunctionToH10 φ) := by
  induction k generalizing φ with
  | zero => exact iteratedDirichletSolveCLM_zero_base hopen hbounded hgraph _
  | succ k ih =>
    rw [iteratedDirichletSolveCLM_succ_base, Function.iterate_succ_apply, ih]
    congr 1
    exact ((IsWeakPoissonSolution.iff_eq_dirichletSolve hopen (Fact.out : 0 < n)
      hbounded _).1 (isWeakPoissonSolution_negativeTestLaplacian hopen φ)).symm

namespace DirichletHeatSpectrum

variable {γ : Exponent} (hγ : (γ : ℝ) < 1) (S : DirichletHeatSpectrum n Ω)

/-- A closed-time Hölder orbit for compact smooth data, constructed by evolving its
iterated Laplacian and applying the elliptic inverse and Sobolev embedding. -/
def testHeat (j : ℕ) (φ : TestFunctionOn n Ω) (t : ℝ) : CKGammaOn n j Ω γ :=
  dirichletHolderLiftCLM hopen hbounded hgraph hγ j
    (spectralHeatEvolution S.basis S.eigenvalue S.eigenvalue_nonneg
      (baseCoordCLM (testFunctionToH10 (negativeTestLaplacian^[j + n + 1] φ))) t.toNNReal)

/-- The closed-time orbit is continuous in the full Hölder graph norm. -/
theorem continuous_testHeat (j : ℕ) (φ : TestFunctionOn n Ω) :
    Continuous (S.testHeat hopen hbounded hgraph hγ j φ) :=
  (dirichletHolderLiftCLM hopen hbounded hgraph hγ j).continuous.comp
    ((continuous_spectralHeatEvolution S.basis S.eigenvalue S.eigenvalue_nonneg _).comp
      continuous_real_toNNReal)

/-- At positive times the reconstructed orbit is the classical spectral solution, in the
same Hölder space. -/
theorem testHeat_of_pos (j : ℕ) (φ : TestFunctionOn n Ω) {t : ℝ} (ht : 0 < t) :
    S.testHeat hopen hbounded hgraph hγ j φ t =
      S.holderPower hopen hbounded hgraph hγ j 0 (baseCoordCLM (testFunctionToH10 φ)) t := by
  unfold testHeat holderPower
  congr 1
  apply S.basis.repr.injective
  ext i
  rw [spectralHeatEvolution_repr, spectralHeatPower_repr _ _ _ _ _ ht,
    S.repr_iterate_negativeTestLaplacian hopen, Real.coe_toNNReal t ht.le]
  simp only [Nat.zero_add]
  change Real.exp (-S.eigenvalue i * t) *
      (S.eigenvalue i ^ (j + n + 1) * S.basis.repr (baseCoordCLM (testFunctionToH10 φ)) i) =
    S.eigenvalue i ^ (j + n + 1) * Real.exp (-S.eigenvalue i * t) *
      S.basis.repr (baseCoordCLM (testFunctionToH10 φ)) i
  ring

/-- The initial Hölder representative agrees almost everywhere with the original test. -/
theorem testHeat_zero_ae (j : ℕ) (φ : TestFunctionOn n Ω) :
    (S.testHeat hopen hbounded hgraph hγ j φ 0).interiorDerivative 0
      =ᵐ[domainMeasure n Ω] φ.1.toFun := by
  unfold testHeat
  rw [Real.toNNReal_zero, spectralHeatEvolution_zero]
  have h := dirichletHolderLiftCLM_ae hopen hbounded hgraph hγ j
    (baseCoordCLM (testFunctionToH10 (negativeTestLaplacian^[j + n + 1] φ)))
  change _ =ᵐ[domainMeasure n Ω] ⇑(wkpBaseCoordinateCLM
    (iteratedDirichletSolveCLM hopen hbounded hgraph (j + n + 1)
      (baseCoordCLM (testFunctionToH10 (negativeTestLaplacian^[j + n + 1] φ))))) at h
  rw [iteratedDirichletSolveCLM_test_base hopen hbounded hgraph] at h
  exact h.trans (baseCoordCLM_testFunction_apply_ae φ)

/-- The initial representative equals the prescribed test at every point of the closure. -/
theorem testHeat_zero (j : ℕ) (φ : TestFunctionOn n Ω) {x : ℝ^n} (hx : x ∈ closure Ω) :
    (S.testHeat hopen hbounded hgraph hγ j φ 0).interiorDerivative 0 x = φ.1.toFun x := by
  have hc := (S.testHeat hopen hbounded hgraph hγ j φ 0).derivative 0
    |>.continuousOn_extend_zero
  exact (Measure.eqOn_open_of_ae_eq (S.testHeat_zero_ae hopen hbounded hgraph hγ j φ)
    hopen (hc.mono subset_closure) φ.1.continuous.continuousOn).of_subset_closure
      hc φ.1.continuous.continuousOn subset_closure Subset.rfl hx

end DirichletHeatSpectrum

end HeatEquation
