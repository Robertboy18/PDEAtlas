/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Interior.HigherOrder.Coefficients
public import PDE.Elliptic.Regularity.Quasilinear.Interior.HigherOrder.Flux
import PDE.Elliptic.Variational.ShiftedDivergenceForm

/-!
# The differentiated nonlinear Euler–Lagrange equation

An `H²` solution of `-div A(Du) = f`, with `f ∈ H¹`, satisfies
`-div(DA(Du) D(∂ₖu)) = ∂ₖf`. The equation is differentiated by testing against
derivatives of compactly supported smooth functions. The weak chain rule
supplies the differentiated flux, and density extends the result to all `H¹₀`
tests in the interior divergence-form formulation.
-/

@[expose] public noncomputable section

namespace PDE.Elliptic.Regularity.Quasilinear

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis
open scoped ENNReal NNReal RealInnerProductSpace Sobolev

variable {n : ℕ} {Ω : Set (ℝ^n)}

private theorem coordinateDerivative_flux_test (Q : Fin n → H¹(Ω)) (F : H¹(Ω))
    (hweak : ∀ v : H¹₀(Ω),
      (∑ i, ⟪wkpBaseCoordinateCLM (Q i), derivCoordCLM i v⟫) =
        ⟪wkpBaseCoordinateCLM F, baseCoordCLM v⟫)
    (k : Fin n) (φ : TestFunctionOn n Ω) :
    (∑ i, ⟪wkpCoordinateCLM (singleDerivIndex n k) (Q i),
      derivCoordCLM i (testFunctionToH10 φ)⟫) =
        ⟪wkpCoordinateCLM (singleDerivIndex n k) F,
          baseCoordCLM (testFunctionToH10 φ)⟫ := by
  let ψ := φ.iteratedPartialDeriv [k]
  have hψ : ψ.1.toFun = ∂[k] φ.1.toFun := rfl
  have htest := hweak (testFunctionToH10 ψ)
  simp only [inner_deriv_testFunction_data_eq_integral,
    inner_base_testFunction_eq_integral] at htest ⊢
  have hf : HasWeakDerivativeOn Ω [k]
      (wkpBaseCoordinateCLM F) (wkpCoordinateCLM (singleDerivIndex n k) F) := by
    simpa only [firstDerivIndex_one, wkpBaseCoordinateCLM_apply, wkpCoordinateCLM_apply] using
      F.property.hasWeakDerivativeOn_first (by norm_num) k
  have hfTest :
      (∫ x, wkpBaseCoordinateCLM F x * ψ.1.toFun x ∂domainMeasure n Ω) =
        -(∫ x, wkpCoordinateCLM (singleDerivIndex n k) F x * φ.1.toFun x
          ∂domainMeasure n Ω) := by
    simpa only [hψ, iteratedPartialDeriv, List.length_cons, List.length_nil,
      zero_add, pow_one, neg_one_mul] using hf φ.1 φ.2
  have hfluxTest (i : Fin n) :
      (∫ x, wkpBaseCoordinateCLM (Q i) x * (∂[i] ψ.1.toFun) x
        ∂domainMeasure n Ω) =
      -(∫ x, wkpCoordinateCLM (singleDerivIndex n k) (Q i) x *
        (∂[i] φ.1.toFun) x ∂domainMeasure n Ω) := by
    have hQi : HasWeakDerivativeOn Ω [k]
        (wkpBaseCoordinateCLM (Q i))
        (wkpCoordinateCLM (singleDerivIndex n k) (Q i)) := by
      simpa only [firstDerivIndex_one, wkpBaseCoordinateCLM_apply, wkpCoordinateCLM_apply] using
        (Q i).property.hasWeakDerivativeOn_first (by norm_num) k
    have hcomm :
        ∂[i] ψ.1.toFun =
          iteratedPartialDeriv [k] (φ.iteratedPartialDeriv [i]).1.toFun := by
      rw [hψ, TestFunctionOn.iteratedPartialDeriv_toFun]
      simpa only [iteratedPartialDeriv, TestFunction.toFun_eq_coe]
        using iteratedPartialDeriv_congr_perm_smooth φ.1.contDiff (List.Perm.swap k i [])
    rw [hcomm]
    simpa only [TestFunctionOn.iteratedPartialDeriv_toFun, iteratedPartialDeriv,
      List.length_cons, List.length_nil, zero_add, pow_one, neg_one_mul]
      using hQi (φ.iteratedPartialDeriv [i]).1 (φ.iteratedPartialDeriv [i]).2
  rw [hfTest] at htest
  simp_rw [hfluxTest] at htest
  exact neg_injective (by simpa only [Finset.sum_neg_distrib] using htest)

/-- Differentiating the nonlinear weak equation gives the
interior linear weak equation for each first derivative. The flux components
and the Hessian coefficient representatives are identified almost everywhere;
the differentiated equation itself is a conclusion. -/
theorem isInteriorWeakDivergenceSolution_linearized
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    {A : ℝ^n → ℝ^n} (hA : ContDiff ℝ 1 A) {C : ℝ≥0} (hLip : LipschitzWith C A)
    (W : W^{2,2}(Ω)) (F : H¹(Ω)) (q : Fin n → DerivLp n 2 Ω)
    (hq : ∀ᵐ x ∂domainMeasure n Ω,
      A (∇ (lowerOrderCLM (by omega : 1 ≤ 2) W) x) = Lp.euclideanTuple q x)
    (hweak : ∀ v : H¹₀(Ω), (∑ i, ⟪q i, derivCoordCLM i v⟫) =
      ⟪wkpBaseCoordinateCLM F, baseCoordCLM v⟫)
    {g : ℝ^n → ℝ^n}
    (hg : (∇ (lowerOrderCLM (by omega : 1 ≤ 2) W) : ℝ^n → ℝ^n)
      =ᵐ[domainMeasure n Ω] g)
    (B : Fin n → Fin n → DerivLp n ∞ Ω)
    (hB : ∀ i j, (B i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun x ↦ jacobianMatrix A (g x) i j) (k : Fin n) :
    IsInteriorWeakDivergenceSolution B
      (wkpCoordinateCLM (singleDerivIndex n k) F) (∂[k] W) := by
  obtain ⟨Q, hQ, hDQ⟩ := exists_H1_linearizedFlux hΩ hbounded hA hLip W
  have hQq (i : Fin n) : wkpBaseCoordinateCLM (Q i) = q i := by
    apply Lp.ext
    filter_upwards [hQ, hq, Lp.euclideanTuple_apply_ae q] with x hx hqx htuple
    exact (hx i).trans ((congrArg (fun z : ℝ^n ↦ z i) hqx).trans (htuple i))
  have hweakQ (v : H¹₀(Ω)) :
      (∑ i, ⟪wkpBaseCoordinateCLM (Q i), derivCoordCLM i v⟫) =
        ⟪wkpBaseCoordinateCLM F, baseCoordCLM v⟫ := by
    simpa only [hQq] using hweak v
  let w : H¹(Ω) := ∂[k] W
  let T (i j : Fin n) : DerivLp n 2 Ω :=
    multiplicationCoefficientOperator B i j (wkpCoordinateCLM (singleDerivIndex n j) w)
  have hrow (i : Fin n) :
      wkpCoordinateCLM (singleDerivIndex n k) (Q i) = ∑ j, T i j := by
    apply Lp.ext
    have hT := ae_all_iff.mpr fun j ↦ multiplicationCoefficientOperator_apply_ae B i j
      (wkpCoordinateCLM (singleDerivIndex n j) w)
    filter_upwards [hDQ, hg, ae_all_iff.mpr (hB i), hT, wkpGradientCLM_apply_ae w,
      Lp.coeFn_fun_finsetSum Finset.univ (T i)] with x hDx hgx hBx hTx hwx hsum
    rw [hsum]
    change _ = ∑ j, T i j x
    rw [hDx i k, hgx, ← sum_jacobianMatrix_mul (hA.differentiable_one (g x))]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [hTx j, hBx j, hwx j]; rfl
  let form := interiorVariableCoeffForm (multiplicationCoefficientOperator B) w
  let load := loadFunctional (wkpCoordinateCLM (singleDerivIndex n k) F)
  have htest : (form : H¹₀(Ω) → ℝ) ∘ testFunctionToH10Linear =
      (load : H¹₀(Ω) → ℝ) ∘ testFunctionToH10Linear := by
    funext φ
    change form (testFunctionToH10 φ) = load (testFunctionToH10 φ)
    have h := coordinateDerivative_flux_test Q F hweakQ k φ
    simp only [hrow, sum_inner] at h
    exact h
  refine ⟨hΩ, fun v ↦ ?_⟩
  exact congrFun (denseRange_testFunctionToH10Linear.equalizer
    form.continuous load.continuous htest) v

end PDE.Elliptic.Regularity.Quasilinear
