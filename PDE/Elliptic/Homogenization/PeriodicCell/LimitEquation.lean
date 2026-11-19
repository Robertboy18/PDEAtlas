/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Homogenization.PeriodicCell.OscillatingTests
public import PDE.Spaces.Sobolev.Periodic.DirectionalTests

/-!
# Identification of the effective Dirichlet equation

Directional oscillating tests determine the limiting pairing against every
smooth test gradient. Density extends this identity to the canonical zero-boundary
Sobolev space. The resulting equation is the weak divergence-form equation
for the derived effective matrix, so weak uniqueness identifies
the limit with the constructed effective Dirichlet solution.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.PeriodicAveraging
open scoped ENNReal Topology InnerProductSpace Sobolev

namespace PDE.Elliptic.Homogenization.PeriodicCell

variable {n : ℕ} (A : Lp ((ℝ^n) →L[ℝ] (ℝ^n)) ∞ (cellMeasure n))
    {α : ℝ} (hα : 0 < α)
    (hA : ∀ᵐ x ∂cellMeasure n, ∀ ξ : ℝ^n, α * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    {Ω : Set (ℝ^n)}

/-- The effective vector flux agrees with the matrix coefficient form. -/
theorem effectiveOperator_gradient_eq (u : H¹₀(Ω)) :
    (effectiveOperator A hα hA).compLp (gradientCLM u) =
      Lp.euclideanTuple (fun i ↦ ∑ j : Fin n,
        effectiveMatrixCoefficient A hα hA Ω i j • derivCoordCLM j u) := by
  let a := effectiveMatrixCoefficient A hα hA Ω
  have hmul : ∀ᵐ x ∂domainMeasure n Ω, ∀ i j : Fin n,
      (a i j • derivCoordCLM j u) x = a i j x * derivCoordCLM j u x :=
    ae_all_iff.mpr fun i ↦ ae_all_iff.mpr fun j ↦ Lp.coeFn_lpSMul (a i j) _
  have hsum : ∀ᵐ x ∂domainMeasure n Ω, ∀ i : Fin n,
      (∑ j : Fin n, a i j • derivCoordCLM j u) x =
        ∑ j : Fin n, (a i j • derivCoordCLM j u) x :=
    ae_all_iff.mpr fun i ↦ Lp.coeFn_fun_finsetSum Finset.univ _
  apply Lp.ext
  filter_upwards [(effectiveOperator A hα hA).coeFn_compLp (gradientCLM u),
    Lp.euclideanTuple_apply_ae (fun i ↦ ∑ j : Fin n, a i j • derivCoordCLM j u),
    gradientCLM_apply_ae u, effectiveMatrixCoefficient_ae A hα hA Ω, hmul, hsum]
    with x hx hy hg ha hm hs
  change ∀ i : Fin n, (gradientCLM u x) i = derivCoordCLM i u x at hg
  apply PiLp.ext
  intro i
  rw [hx, hy i, hs i]
  have he := congrFun (effectiveMatrix_mulVec A hα hA (gradientCLM u x)) i
  change (∑ j : Fin n, effectiveMatrix A hα hA i j * (gradientCLM u x) j) = _ at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [hm i j, ha i j, hg j]

variable (hn : 0 < n) (hΩ : Bornology.IsBounded Ω) (hΩo : IsOpen Ω)
    (f : DerivLp n 2 Ω)

include hΩo in
/-- Every strong L² limit of the microscopic Dirichlet solutions satisfies
the canonical weak equation with the derived effective matrix. -/
theorem isWeakDivergenceSolution_of_strong_limit
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (ε : ι → ℝ) (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (ht : Tendsto ε l (𝓝 0)) (U : H¹₀(Ω))
    (hu : Tendsto (fun j ↦ baseCoordCLM
      (rescaledDirichletSolution A hα hA hn hΩ (ε j) (hε j).ne' f)) l
      (𝓝 (baseCoordCLM U))) :
    IsWeakDivergenceSolution (effectiveMatrixCoefficient A hα hA Ω) f U := by
  let := isFiniteMeasure_domainMeasure_of_isBounded hΩ
  let Q := (effectiveOperator A hα hA).compLp (gradientCLM U)
  have htest (φ : TestFunctionOn n Ω) :
      ⟪Q, gradientCLM (testFunctionToH10 φ)⟫_ℝ =
        ⟪f, baseCoordCLM (testFunctionToH10 φ)⟫_ℝ := by
    have ht_pair : Tendsto (fun j ↦
        ⟪rescaledDirichletFlux A hΩ hα hA hn f (ε j) (hε j) (hε1 j),
          gradientCLM (testFunctionToH10 φ)⟫_ℝ) l
        (𝓝 ⟪Q, gradientCLM (testFunctionToH10 φ)⟫_ℝ) := by
      have hd (i : Fin n) := tendsto_inner_dirichletFlux_weighted_const A hα hA hΩ
        hn hΩo f ε hε hε1 ht U hu (EuclideanSpace.single i (1 : ℝ))
        (φ.iteratedPartialDeriv [i]).1 (φ.iteratedPartialDeriv [i]).property
      simp only [SobolevSpace.Periodic.inner_const_adjoint_weighted] at hd
      simpa only [SobolevSpace.Periodic.testFunctionLpTop_partial, ← inner_sum,
        ← SobolevSpace.Periodic.gradient_testFunction_eq_sum] using
          tendsto_finsetSum Finset.univ (fun i _hi ↦ hd i)
    have he (j : ι) := SobolevSpace.Periodic.inner_gradient_eq_of_weakDivergenceFunctional
      (rescaledDirichletFlux A hΩ hα hA hn f (ε j) (hε j) (hε1 j)) f
      (weakDivergenceFunctional_rescaledDirichletFlux A hΩ hα hA hn hΩo f
        (ε j) (hε j) (hε1 j)) (testFunctionToH10 φ)
    simp_rw [he] at ht_pair
    exact tendsto_nhds_unique ht_pair tendsto_const_nhds
  have hall (v : H¹₀(Ω)) : ⟪Q, gradientCLM v⟫_ℝ = ⟪f, baseCoordCLM v⟫_ℝ := by
    refine DenseRange.induction_on denseRange_testFunctionToH10Linear v ?_ ?_
    · exact isClosed_eq ((innerSL ℝ Q).comp gradientCLM).continuous
        ((innerSL ℝ f).comp baseCoordCLM).continuous
    · exact htest
  apply (isWeakSolution_iff_isWeakDivergenceSolution hΩo
    (effectiveMatrixCoefficient A hα hA Ω) f U).1
  intro v
  have hv := hall v
  change ⟪(effectiveOperator A hα hA).compLp (gradientCLM U), gradientCLM v⟫_ℝ = _ at hv
  rw [effectiveOperator_gradient_eq] at hv
  change ⟪Lp.euclideanTuple _, Lp.euclideanTuple (fun i ↦ derivCoordCLM i v)⟫_ℝ = _ at hv
  simpa only [Lp.inner_euclideanTuple, sum_inner, variableCoeffForm_apply,
    multiplicationCoefficientOperator_apply, loadFunctional_apply] using hv

include hΩo in
/-- Uniqueness identifies every compactness limit with the constructed effective solution. -/
theorem strong_limit_eq_effectiveDirichletSolution
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (ε : ι → ℝ) (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (ht : Tendsto ε l (𝓝 0)) (U : H¹₀(Ω))
    (hu : Tendsto (fun j ↦ baseCoordCLM
      (rescaledDirichletSolution A hα hA hn hΩ (ε j) (hε j).ne' f)) l
      (𝓝 (baseCoordCLM U))) :
    U = effectiveDirichletSolution A hα hA hn hΩ f :=
  (IsWeakDivergenceSolution.existsUnique_of_ae hΩo hn hΩ
    (effectiveMatrixCoefficient A hα hA Ω)
    (aeUniformlyElliptic_effectiveMatrixCoefficient A hα hA Ω) f).unique
      (isWeakDivergenceSolution_of_strong_limit A hα hA hn hΩ hΩo f ε hε hε1 ht U hu)
      (effectiveDirichletSolution_isWeakDivergenceSolution A hα hA hn hΩ hΩo f)

end PDE.Elliptic.Homogenization.PeriodicCell
