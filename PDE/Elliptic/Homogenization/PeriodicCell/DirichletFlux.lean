/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Homogenization.PeriodicCell.Dirichlet
public import PDE.Elliptic.Homogenization.PeriodicCell.FluxAveraging
public import PDE.Spaces.Sobolev.Periodic.LoadedFluxProducts

/-!
# Microscopic Dirichlet fluxes

Mathlib's bilinear Hölder construction realizes multiplication by the rescaled
operator field on vector-valued L². Coordinate expansion identifies it with the
matrix in the weak elliptic form. The constructed Dirichlet solution's
flux therefore satisfies the canonical loaded weak divergence functional, and its
L² norm is bounded uniformly by the coefficient and the Sobolev energy estimate.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.PeriodicAveraging
open scoped ENNReal Topology InnerProductSpace Sobolev

namespace PDE.Elliptic.Homogenization.PeriodicCell

/-- Coordinate expansion of a linear map applied to a Euclidean vector. -/
theorem sum_matrix_entries_mul_eq {n : ℕ} (B : (ℝ^n) →L[ℝ] (ℝ^n))
    (ξ : ℝ^n) (i : Fin n) :
    (∑ j : Fin n, B (PiLp.single 2 j 1) i * ξ j) = B ξ i := by
  classical
  have hξ : (∑ j : Fin n, ξ j • (PiLp.single 2 j 1 : ℝ^n)) = ξ := by
    apply (WithLp.equiv 2 _).injective
    ext k
    simp [Pi.single_apply]
  conv_rhs => rw [← hξ, map_sum]
  simp [map_smul, mul_comm]

variable {n : ℕ} (A : Lp ((ℝ^n) →L[ℝ] (ℝ^n)) ∞ (cellMeasure n))
    {Ω : Set (ℝ^n)} (hΩ : Bornology.IsBounded Ω)

/-- Multiplication by the Euclidean periodic coefficient on vector L². -/
def rescaledCoefficientOperator (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Lp (ℝ^n) 2 (domainMeasure n Ω) →L[ℝ] Lp (ℝ^n) 2 (domainMeasure n Ω) :=
  (ContinuousLinearMap.id ℝ ((ℝ^n) →L[ℝ] (ℝ^n))).holderL
    (domainMeasure n Ω) ∞ 2 2 (rescaleLp hΩ ε hε hε1 A)

/-- Its representative is pointwise multiplication by A(x/ε). -/
theorem rescaledCoefficientOperator_ae (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (v : Lp (ℝ^n) 2 (domainMeasure n Ω)) :
    rescaledCoefficientOperator A hΩ ε hε hε1 v =ᵐ[domainMeasure n Ω]
      fun x ↦ A (toTorus n (ε⁻¹ • x)) (v x) := by
  have h := (ContinuousLinearMap.id ℝ ((ℝ^n) →L[ℝ] (ℝ^n))).coeFn_holder (r := 2)
    (rescaleLp hΩ ε hε hε1 A) v
  filter_upwards [h, rescaleLp_ae hΩ ε hε hε1 A] with x hx hAx
  exact hx.trans (congrArg (fun B ↦ B (v x)) hAx)

/-- The Euclidean flux operator has a period-independent norm bound. -/
theorem exists_rescaledCoefficientOperator_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ∀ hε1 : ε ≤ 1,
      ∀ v : Lp (ℝ^n) 2 (domainMeasure n Ω),
        ‖rescaledCoefficientOperator A hΩ ε hε hε1 v‖ ≤ C * ‖v‖ := by
  let B := ContinuousLinearMap.id ℝ ((ℝ^n) →L[ℝ] (ℝ^n))
  obtain ⟨C, hC, hbound⟩ := exists_norm_rescaleLp_le (E := (ℝ^n) →L[ℝ] (ℝ^n))
    (p := ∞) hΩ
  refine ⟨‖B‖ * (C * ‖A‖), mul_nonneg (norm_nonneg B) (mul_nonneg hC (norm_nonneg A)),
    fun ε hε hε1 v ↦ ?_⟩
  exact (B.norm_holder_apply_apply_le (r := 2) (rescaleLp hΩ ε hε hε1 A) v).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hbound ε hε hε1 A) (norm_nonneg B)) (norm_nonneg v))

/-- The vector flux agrees with the coordinate matrix in the canonical elliptic form. -/
theorem rescaledCoefficientOperator_gradient_eq (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (u : H¹₀(Ω)) :
    rescaledCoefficientOperator A hΩ ε hε hε1 (gradientCLM u) =
      Lp.euclideanTuple (fun i ↦ ∑ j : Fin n,
        rescaledMatrixCoefficient A Ω ε hε.ne' i j • derivCoordCLM j u) := by
  let a := rescaledMatrixCoefficient A Ω ε hε.ne'
  have hmul : ∀ᵐ x ∂domainMeasure n Ω, ∀ i j : Fin n,
      (a i j • derivCoordCLM j u) x = a i j x * derivCoordCLM j u x :=
    ae_all_iff.mpr fun i ↦ ae_all_iff.mpr fun j ↦ Lp.coeFn_lpSMul (a i j) _
  have hsum : ∀ᵐ x ∂domainMeasure n Ω, ∀ i : Fin n,
      (∑ j : Fin n, a i j • derivCoordCLM j u) x =
        ∑ j : Fin n, (a i j • derivCoordCLM j u) x :=
    ae_all_iff.mpr fun i ↦ Lp.coeFn_fun_finsetSum Finset.univ _
  apply Lp.ext
  filter_upwards [rescaledCoefficientOperator_ae A hΩ ε hε hε1 (gradientCLM u),
    Lp.euclideanTuple_apply_ae (fun i ↦ ∑ j : Fin n, a i j • derivCoordCLM j u),
    gradientCLM_apply_ae u, rescaledMatrixCoefficient_ae A Ω ε hε.ne', hmul, hsum]
    with x hx hy hg ha hm hs
  change ∀ i : Fin n, (gradientCLM u x) i = derivCoordCLM i u x at hg
  apply PiLp.ext
  intro i
  rw [hx, hy i, hs i]
  calc
    _ = ∑ j : Fin n, A (toTorus n (ε⁻¹ • x)) (PiLp.single 2 j 1) i *
        (gradientCLM u x) j := (sum_matrix_entries_mul_eq _ _ i).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [hm i j, hg j]
      exact congrArg (fun z ↦ z * derivCoordCLM j u x) (ha i j).symm

variable {α : ℝ} (hα : 0 < α)
    (hA : ∀ᵐ x ∂cellMeasure n, ∀ ξ : ℝ^n, α * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    (hn : 0 < n) (hΩo : IsOpen Ω) (f : DerivLp n 2 Ω)

/-- The microscopic Dirichlet flux as a vector-valued L² element. -/
def rescaledDirichletFlux (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Lp (ℝ^n) 2 (domainMeasure n Ω) :=
  rescaledCoefficientOperator A hΩ ε hε hε1
    (gradientCLM (rescaledDirichletSolution A hα hA hn hΩ ε hε.ne' f))

include hΩo in
/-- The microscopic Dirichlet flux satisfies the loaded divergence functional. -/
theorem weakDivergenceFunctional_rescaledDirichletFlux (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    weakDivergenceFunctional (fun i ↦ (EuclideanSpace.proj (𝕜 := ℝ) i).compLp
      (rescaledDirichletFlux A hΩ hα hA hn f ε hε hε1)) f = 0 := by
  let u := rescaledDirichletSolution A hα hA hn hΩ ε hε.ne' f
  have hu := (isWeakSolution_iff_isWeakDivergenceSolution hΩo
    (rescaledMatrixCoefficient A Ω ε hε.ne') f u).2
      (rescaledDirichletSolution_isWeakDivergenceSolution A hα hA hn hΩ hΩo ε hε.ne' f)
  ext v
  rw [weakDivergenceFunctional_apply, zero_apply]
  apply sub_eq_zero.mpr
  rw [← Lp.inner_euclideanTuple]
  have hQ : Lp.euclideanTuple (fun i ↦ (EuclideanSpace.proj (𝕜 := ℝ) i).compLp
      (rescaledDirichletFlux A hΩ hα hA hn f ε hε hε1)) =
      rescaledDirichletFlux A hΩ hα hA hn f ε hε hε1 := Lp.euclideanTuple_coordinates _
  rw [hQ]
  change ⟪rescaledCoefficientOperator A hΩ ε hε hε1 (gradientCLM u), gradientCLM v⟫_ℝ = _
  rw [rescaledCoefficientOperator_gradient_eq]
  change ⟪Lp.euclideanTuple _, Lp.euclideanTuple (fun i ↦ derivCoordCLM i v)⟫_ℝ = _
  rw [Lp.inner_euclideanTuple]
  simpa only [variableCoeffForm_apply, multiplicationCoefficientOperator_apply,
    loadFunctional_apply, sum_inner] using hu v

include hΩo in
/-- The energy bound controls the microscopic fluxes uniformly in L². -/
theorem exists_rescaledDirichletFlux_norm_bound :
    ∃ R : ℝ, ∀ ε : ℝ, ∀ hε : 0 < ε, ∀ hε1 : ε ≤ 1,
      ‖rescaledDirichletFlux A hΩ hα hA hn f ε hε hε1‖ ≤ R := by
  obtain ⟨C, hC, hbound⟩ := exists_rescaledCoefficientOperator_bound A hΩ
  obtain ⟨M, hM⟩ := exists_rescaledDirichletSolution_norm_bound A hα hA hn hΩ hΩo f
  refine ⟨C * M, fun ε hε hε1 ↦ ?_⟩
  exact (hbound ε hε hε1 _).trans (mul_le_mul_of_nonneg_left
    ((gradientCLM_norm_le _).trans (hM ε hε.ne')) hC)

end PDE.Elliptic.Homogenization.PeriodicCell
