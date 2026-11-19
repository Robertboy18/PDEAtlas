/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.LowerOrderForm
public import PDE.Spaces.Sobolev.GraphSpace.Model.Complex
import PDE.Analysis.MeasureTheory.Lp.ComplexPairing

/-!
# Complex weak equations for full divergence forms

The coefficients and derivative coordinates are `L∞` and `L²`
classes. Real `H¹₀` tests split the complex integral equation into
the two coupled real forms. Principal, drift, and potential contributions
are all retained; no symmetry or spectral assumption is used.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The full complex divergence integral against a real Dirichlet
test. Testing real and imaginary parts determines the complex weak equation. -/
def complexFullDivergenceForm
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    (U : ComplexWkSpaceOn n 1 Ω) (v : H¹₀(Ω)) : ℂ :=
  (∑ i, ∑ j, ∫ x, (a i j x : ℂ) * U.1 (singleDerivIndex n j) x *
    (derivCoordCLM i v x : ℂ) ∂domainMeasure n Ω) +
  (∑ i, ∫ x, (b i x : ℂ) * U.1 (singleDerivIndex n i) x *
    (baseCoordCLM v x : ℂ) ∂domainMeasure n Ω) +
  ∫ x, (c x : ℂ) * U.1 (baseIndex n 1) x *
    (baseCoordCLM v x : ℂ) ∂domainMeasure n Ω

/-- Real and imaginary splitting of the full complex integral form agrees
with the real full form. -/
theorem complexFullDivergenceForm_eq_parts
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    (U : ComplexWkSpaceOn n 1 Ω)
    (hUr : U.re ∈ h10SubmoduleOn (n := n) (Ω := Ω))
    (hUi : U.im ∈ h10SubmoduleOn (n := n) (Ω := Ω))
    (v : H¹₀(Ω)) :
    complexFullDivergenceForm a b c U v =
      (fullDivergenceForm (multiplicationCoefficientOperator a)
        (fun i ↦ mulLpLeft (b i)) (mulLpLeft c) ⟨U.re, hUr⟩ v : ℂ) +
      Complex.I * (fullDivergenceForm (multiplicationCoefficientOperator a)
        (fun i ↦ mulLpLeft (b i)) (mulLpLeft c) ⟨U.im, hUi⟩ v : ℂ) := by
  simp only [complexFullDivergenceForm, Lp.integral_complex_coefficient_pairing,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Complex.ofReal_sum,
    fullDivergenceForm_apply, Complex.ofReal_add,
    ComplexWkSpaceOn.re, ComplexWkSpaceOn.im, realCoordinateTuple,
    derivCoordCLM_apply, baseCoordCLM_apply, multiplicationCoefficientOperator_apply,
    mulLpLeft_apply, LinearMap.coe_mk, AddHom.coe_mk]
  ring

/-- A complex integral eigen-equation gives the coupled real weak
equations of the full operator, including drift and potential. -/
theorem parts_of_complexFullDivergenceForm_eq
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    (U : ComplexWkSpaceOn n 1 Ω)
    (hUr : U.re ∈ h10SubmoduleOn (n := n) (Ω := Ω))
    (hUi : U.im ∈ h10SubmoduleOn (n := n) (Ω := Ω))
    (lambda : ℂ) (v : H¹₀(Ω))
    (heq : complexFullDivergenceForm a b c U v =
      lambda * ∫ x, U.1 (baseIndex n 1) x *
        (baseCoordCLM v x : ℂ) ∂domainMeasure n Ω) :
    fullDivergenceForm (multiplicationCoefficientOperator a)
        (fun i ↦ mulLpLeft (b i)) (mulLpLeft c) ⟨U.re, hUr⟩ v =
      lambda.re * ⟪baseCoordCLM ⟨U.re, hUr⟩, baseCoordCLM v⟫_ℝ -
        lambda.im * ⟪baseCoordCLM ⟨U.im, hUi⟩, baseCoordCLM v⟫_ℝ ∧
    fullDivergenceForm (multiplicationCoefficientOperator a)
        (fun i ↦ mulLpLeft (b i)) (mulLpLeft c) ⟨U.im, hUi⟩ v =
      lambda.re * ⟪baseCoordCLM ⟨U.im, hUi⟩, baseCoordCLM v⟫_ℝ +
        lambda.im * ⟪baseCoordCLM ⟨U.re, hUr⟩, baseCoordCLM v⟫_ℝ := by
  rw [complexFullDivergenceForm_eq_parts a b c U hUr hUi,
    Lp.integral_complex_pairing] at heq
  constructor
  · simpa [Complex.mul_re, ComplexWkSpaceOn.re, ComplexWkSpaceOn.im,
      realCoordinateTuple, baseCoordCLM_apply] using congrArg Complex.re heq
  · simpa [Complex.mul_im, ComplexWkSpaceOn.re, ComplexWkSpaceOn.im,
      realCoordinateTuple, baseCoordCLM_apply] using congrArg Complex.im heq

end SobolevSpace.GraphSpace
