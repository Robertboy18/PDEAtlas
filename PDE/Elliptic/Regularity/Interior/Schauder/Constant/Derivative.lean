/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.Rescaling.Testing
public import PDE.Spaces.Sobolev.GraphSpace.Operators.PartialDerivatives

/-!
# Differentiating the constant coefficient weak equation

An H² solution of a homogeneous constant coefficient divergence equation has
first derivatives solving the same equation. Differentiating the test function
and commuting its smooth partial derivatives proves this in the
interior weak formulation. No boundary condition on the solution or its
derivatives is needed.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set SobolevSpace
open scoped Sobolev ENNReal Distributions

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

private theorem constantCoefficient_test_integral
    (A : Fin n → Fin n → DerivLp n ∞ Ω) (a : Fin n → Fin n → ℝ)
    (hA : ∀ i j, (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun _ ↦ a i j)
    (v : H¹(Ω)) (φ : TestFunctionOn n Ω) (i j : Fin n) :
    (∫ x, A i j x * wkpCoordinateCLM (singleDerivIndex n j) v x *
      (∂[i] φ.1.toFun) x ∂domainMeasure n Ω) =
      a i j * ∫ x, wkpCoordinateCLM (singleDerivIndex n j) v x *
        (∂[i] φ.1.toFun) x ∂domainMeasure n Ω := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hA i j] with x hx
  rw [hx, mul_assoc]

/-- First derivatives of an H² constant coefficient solution satisfy the
same homogeneous weak equation. This conclusion is obtained by weak
integration by parts, without zero traces on the differentiated field. -/
theorem IsInteriorWeakDivergenceSolution.partialDeriv_of_constant_representatives
    (A : Fin n → Fin n → DerivLp n ∞ Ω) (a : Fin n → Fin n → ℝ)
    (hA : ∀ i j, (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun _ ↦ a i j)
    (W : W^{2,2}(Ω))
    (hu : IsInteriorWeakDivergenceSolution A 0
      (lowerOrderCLM (by omega : 1 ≤ 2) W)) (k : Fin n) :
    IsInteriorWeakDivergenceSolution A 0 (∂[k] W) := by
  let U : H¹(Ω) := lowerOrderCLM (by omega : 1 ≤ 2) W
  have hbase (j : Fin n) : wkpBaseCoordinateCLM (∂[j] W) =
      wkpCoordinateCLM (singleDerivIndex n j) U := by
    simp only [U, wkpBaseCoordinateCLM_apply, partialDerivCLM,
      derivativeWordCLM_apply, derivativeWordIndex_baseIndex, wkpCoordinateCLM_apply,
      lowerOrderCLM_apply, DerivIndex.castOrder_singleDerivIndex]
    rfl
  have hcomm (j : Fin n) :
      wkpCoordinateCLM (singleDerivIndex n k) (∂[j] W) =
        wkpCoordinateCLM (singleDerivIndex n j) (∂[k] W) := by
    simp only [partialDerivCLM, wkpCoordinateCLM_apply, derivativeWordCLM_apply,
      derivativeWordIndex_singleDerivIndex_comm j k (by omega : 2 ≤ 2)]
  have hzero (φ : TestFunctionOn n Ω) :
      (∫ x, (0 : DerivLp n 2 Ω) x * φ.1.toFun x ∂domainMeasure n Ω) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero ℝ 2 (domainMeasure n Ω)] with x hx
    simp only [hx, Pi.zero_apply, zero_mul]
  apply (isInteriorWeakDivergenceSolution_iff_testFunctions hu.isOpen A 0 (∂[k] W)).mpr
  intro φ
  let ψ := φ.iteratedPartialDeriv [k]
  have hψ : ψ.1.toFun = ∂[k] φ.1.toFun := rfl
  have ht := (isInteriorWeakDivergenceSolution_iff_testFunctions hu.isOpen A 0 U).mp hu ψ
  simp only [constantCoefficient_test_integral A a hA, hzero] at ht ⊢
  have hparts (i j : Fin n) :
      (∫ x, wkpCoordinateCLM (singleDerivIndex n j) U x *
        (∂[i] ψ.1.toFun) x ∂domainMeasure n Ω) =
      -(∫ x, wkpCoordinateCLM (singleDerivIndex n j) (∂[k] W) x *
        (∂[i] φ.1.toFun) x ∂domainMeasure n Ω) := by
    have hw : HasWeakDerivativeOn Ω [k]
        (wkpBaseCoordinateCLM (∂[j] W))
        (wkpCoordinateCLM (singleDerivIndex n k) (∂[j] W)) := by
      simpa only [firstDerivIndex_one, wkpBaseCoordinateCLM_apply, wkpCoordinateCLM_apply]
        using (∂[j] W : H¹(Ω)).property.hasWeakDerivativeOn_first (by norm_num) k
    rw [hbase, hcomm] at hw
    have htest : ∂[i] ψ.1.toFun =
        iteratedPartialDeriv [k] (φ.iteratedPartialDeriv [i]).1.toFun := by
      rw [hψ, TestFunctionOn.iteratedPartialDeriv_toFun]
      simpa only [iteratedPartialDeriv, TestFunction.toFun_eq_coe] using
        iteratedPartialDeriv_congr_perm_smooth φ.1.contDiff (List.Perm.swap k i [])
    rw [htest]
    simpa only [TestFunctionOn.iteratedPartialDeriv_toFun, iteratedPartialDeriv,
      List.length_cons, List.length_nil, zero_add, pow_one, neg_one_mul] using
        hw (φ.iteratedPartialDeriv [i]).1 (φ.iteratedPartialDeriv [i]).2
  simp_rw [hparts, mul_neg, Finset.sum_neg_distrib] at ht
  exact neg_eq_zero.mp ht

end SobolevSpace.GraphSpace
