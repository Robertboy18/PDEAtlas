/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.ShiftedDivergenceForm
public import PDE.Spaces.Sobolev.GraphSpace.Operators.PartialDerivatives

/-!
# Differentiating a weak divergence identity

A weakly divergence-free L² flux remains divergence-free after any derivative
word whose components have L² weak derivatives. The proof differentiates the
smooth test, commutes its partial derivatives, and cancels the integration by
parts sign. Density extends the resulting identity to all H¹₀ tests.

This is the distributional step in the higher interior Schauder bootstrap.
The derivative certificates concern the flux components, not the conclusion
that their divergence vanishes.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set SobolevSpace
open scoped ENNReal Sobolev InnerProductSpace

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set ℝ^n}

/-- Weak differentiation preserves the zero-divergence identity. No trace
condition or classical differentiability of the flux is required. -/
theorem sum_inner_deriv_eq_zero_of_weakDerivative
    (α : List (Fin n)) (Q DQ : Fin n → DerivLp n 2 Ω)
    (hQ : ∀ i, HasWeakDerivativeOn Ω α (Q i) (DQ i))
    (hweak : ∀ v : H¹₀(Ω), (∑ i, ⟪Q i, derivCoordCLM i v⟫_ℝ) = 0) :
    ∀ v : H¹₀(Ω), (∑ i, ⟪DQ i, derivCoordCLM i v⟫_ℝ) = 0 := by
  let T : H¹₀(Ω) →L[ℝ] ℝ := ∑ i, (innerSL ℝ (DQ i)).comp (derivCoordCLM i)
  have htest : (T : H¹₀(Ω) → ℝ) ∘ testFunctionToH10Linear =
      (0 : H¹₀(Ω) →L[ℝ] ℝ) ∘ testFunctionToH10Linear := by
    funext φ
    let ψ := φ.iteratedPartialDeriv α
    have ht := hweak (testFunctionToH10 ψ)
    simp only [inner_deriv_testFunction_data_eq_integral] at ht
    have hparts (i : Fin n) :
        (∫ x, Q i x * (∂[i] ψ.1.toFun) x ∂domainMeasure n Ω) =
          (-1 : ℝ) ^ α.length *
            ∫ x, DQ i x * (∂[i] φ.1.toFun) x ∂domainMeasure n Ω := by
      have hcomm : ∂[i] ψ.1.toFun =
          iteratedPartialDeriv α (φ.iteratedPartialDeriv [i]).1.toFun := by
        have hperm : (i :: α).Perm (α ++ [i]) := by
          simpa only [List.singleton_append] using (List.perm_append_comm (l₁ := [i]) (l₂ := α))
        have h := iteratedPartialDeriv_congr_perm_smooth φ.1.contDiff hperm
        change (∂[i] (φ.iteratedPartialDeriv α).1.toFun) = _
        rw [TestFunctionOn.iteratedPartialDeriv_toFun,
          TestFunctionOn.iteratedPartialDeriv_toFun]
        simpa only [PDE.iteratedPartialDeriv_append_single, iteratedPartialDeriv,
          TestFunction.toFun_eq_coe] using h
      rw [hcomm]
      simpa only [TestFunctionOn.iteratedPartialDeriv_toFun,
        iteratedPartialDeriv] using
          hQ i (φ.iteratedPartialDeriv [i]).1 (φ.iteratedPartialDeriv [i]).2
    simp_rw [hparts] at ht
    rw [← Finset.mul_sum] at ht
    have hz := (mul_eq_zero.mp ht).resolve_left (pow_ne_zero _ (by norm_num))
    change T (testFunctionToH10 φ) = 0
    simpa only [T, sum_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      inner_deriv_testFunction_data_eq_integral] using hz
  have heq := denseRange_testFunctionToH10Linear.equalizer T.continuous
    (0 : H¹₀(Ω) →L[ℝ] ℝ).continuous htest
  intro v
  simpa only [T, sum_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    zero_apply] using congrFun heq v

/-- The first derivatives of a divergence-free H¹ flux satisfy the same
weak zero-divergence identity. Their weak derivative certificates come from
the Sobolev bundles. -/
theorem sum_inner_coordinateDerivative_eq_zero
    (Q : Fin n → H¹(Ω))
    (hweak : ∀ v : H¹₀(Ω),
      (∑ i, ⟪wkpBaseCoordinateCLM (Q i), derivCoordCLM i v⟫_ℝ) = 0)
    (k : Fin n) :
    ∀ v : H¹₀(Ω),
      (∑ i, ⟪wkpCoordinateCLM (singleDerivIndex n k) (Q i), derivCoordCLM i v⟫_ℝ) = 0 := by
  apply sum_inner_deriv_eq_zero_of_weakDerivative [k] _ _ _ hweak
  intro i
  simpa only [firstDerivIndex_one, wkpBaseCoordinateCLM_apply, wkpCoordinateCLM_apply]
    using (Q i).property.hasWeakDerivativeOn_first (by norm_num) k

end SobolevSpace.GraphSpace
