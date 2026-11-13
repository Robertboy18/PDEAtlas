/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.InteriorLowerOrder
public import PDE.Elliptic.Variational.ShiftedDivergenceForm

/-!
# Locality of the full divergence form on a positive-part test

Every bounded multiplication coefficient localizes to the positive set.
This algebra applies to arbitrary H¹ states and an H¹₀ test whose coordinates
are the positive-part coordinates. No trace or ellipticity hypothesis is used.
-/

open scoped Sobolev

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

variable {n : ℕ} {Ω : Set ℝ^n}

/-- On a zero-boundary state the interior operator is the full weak form. -/
theorem interiorFullDivergenceOperator_coe_H10
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω) (u v : H¹₀(Ω)) :
    interiorFullDivergenceOperator a b c (u : H¹(Ω)) v =
      fullDivergenceForm (multiplicationCoefficientOperator a)
        (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c) u v := by
  simp only [interiorFullDivergenceOperator, add_apply,
    ContinuousLinearMap.comp_apply, loadFunctionalCLM_apply, loadFunctional_apply,
    interiorLowerOrderOperator_apply, inner_add_left, sum_inner,
    interiorVariableCoeffForm_apply, fullDivergenceForm_apply, add_assoc]
  rfl

/-- A bounded multiplier paired with a positive-part coordinate sees only the positive set. -/
private theorem inner_mul_positivePart_coord
    (c : DerivLp n ∞ Ω)
    (w : H¹(Ω)) (t : H¹₀(Ω))
    (hloc : ∀ i : DerivIndex n 1, (coordCLM i t : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] fun x ↦
        if 0 < wkpBaseCoordinateCLM w x then wkpCoordinateCLM i w x else 0)
    (i j : DerivIndex n 1) :
    inner ℝ (c • wkpCoordinateCLM i w)
        (coordCLM j t) =
      inner ℝ (c • coordCLM i t)
        (coordCLM j t) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) c (wkpCoordinateCLM i w),
     Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) c
       (coordCLM i t),
     hloc i, hloc j] with x hw ht hi hj
  simp only [smul_eq_mul, Pi.mul_apply] at hw ht
  rw [hw, ht, hi, hj]
  split_ifs <;> simp

/-- The mass pairing also localizes to the positive set. -/
private theorem inner_base_positivePart
    (w : H¹(Ω)) (t : H¹₀(Ω))
    (hloc : ∀ i : DerivIndex n 1, (coordCLM i t : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] fun x ↦
        if 0 < wkpBaseCoordinateCLM w x then wkpCoordinateCLM i w x else 0) :
    inner ℝ (wkpBaseCoordinateCLM w)
        (baseCoordCLM t) =
      inner ℝ (baseCoordCLM t)
        (baseCoordCLM t) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hloc (baseIndex n 1)] with x hx
  change baseCoordCLM t x =
    (if 0 < wkpBaseCoordinateCLM w x then wkpBaseCoordinateCLM w x else 0) at hx
  rw [hx]
  split_ifs <;> simp

/-- Testing the full shifted form with `w⁺` gives its quadratic form at `w⁺`.
This uses locality of multiplication, not ellipticity or coefficient symmetry. -/
theorem interiorFullDivergenceOperator_positivePart_right
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    (mu : ℝ) (w : H¹(Ω)) (t : H¹₀(Ω))
    (hloc : ∀ i : DerivIndex n 1, (coordCLM i t : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] fun x ↦
        if 0 < wkpBaseCoordinateCLM w x then wkpCoordinateCLM i w x else 0) :
    interiorFullDivergenceOperator a b c w t +
        mu * inner ℝ (wkpBaseCoordinateCLM w) (baseCoordCLM t) =
      shiftedDivergenceForm (multiplicationCoefficientOperator a)
        (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c)
        mu t t := by
  simp only [interiorFullDivergenceOperator, add_apply,
    ContinuousLinearMap.comp_apply, loadFunctionalCLM_apply, loadFunctional_apply,
    interiorLowerOrderOperator_apply, inner_add_left, sum_inner,
    interiorVariableCoeffForm_apply, shiftedDivergenceForm_apply, fullDivergenceForm_apply,
    ← add_assoc]
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact inner_mul_positivePart_coord (a i j) w t hloc
          (singleDerivIndex n j) (singleDerivIndex n i)
      · apply Finset.sum_congr rfl
        intro i _
        exact inner_mul_positivePart_coord (b i) w t hloc
          (singleDerivIndex n i) (baseIndex n 1)
    · exact inner_mul_positivePart_coord c w t hloc (baseIndex n 1) (baseIndex n 1)
  · exact congrArg (mu * ·) (inner_base_positivePart w t hloc)


end SobolevSpace.GraphSpace
