/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.WeakSpectrum
public import PDE.Spaces.Sobolev.GraphSpace.Model.Complex
import PDE.Analysis.MeasureTheory.Lp.ComplexPairing

/-!
# Complex weak eigenfunctions of real divergence forms

The state is a complex Sobolev graph with distributional derivatives. Its real and
imaginary parts have zero boundary values in the closure-of-test-functions sense.
The equation uses complex integrals against real `H¹₀` tests. These tests determine a
complex-linear distribution, and allow testing separately against both parts of the state.

Symmetry forces every complex weak eigenvalue to be real. No regularity of the coefficients
or boundary is needed for this energy argument.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The complex distributional Dirichlet eigenproblem. Real `H¹₀` tests determine the
sesquilinear equation by splitting a complex test into its real and imaginary parts.
The derivatives are the rows of the complex weak-derivative graph. -/
structure IsComplexWeakDivergenceEigenfunction
    (a : Fin n → Fin n → DerivLp n ∞ Ω) (lambda : ℂ)
    (U : ComplexWkSpaceOn n 1 Ω) : Prop where
  isOpen : IsOpen Ω
  re_zeroBoundary : U.re ∈ h10SubmoduleOn (n := n) (Ω := Ω)
  im_zeroBoundary : U.im ∈ h10SubmoduleOn (n := n) (Ω := Ω)
  nonzero : U.1 (baseIndex n 1) ≠ 0
  equation : ∀ v : H¹₀(Ω),
    (∑ i : Fin n, ∑ j : Fin n,
      ∫ x, (a i j x : ℂ) * U.1 (singleDerivIndex n j) x *
        (derivCoordCLM i v x : ℂ) ∂domainMeasure n Ω) =
      lambda * ∫ x, U.1 (baseIndex n 1) x * (baseCoordCLM v x : ℂ) ∂domainMeasure n Ω

namespace IsComplexWeakDivergenceEigenfunction

variable {a : Fin n → Fin n → DerivLp n ∞ Ω} {lambda : ℂ}
  {U : ComplexWkSpaceOn n 1 Ω}

/-- The real component belongs to the real zero-boundary Sobolev space. -/
def re (h : IsComplexWeakDivergenceEigenfunction a lambda U) : H¹₀(Ω) :=
  ⟨U.re, h.re_zeroBoundary⟩

/-- The imaginary component belongs to the real zero-boundary Sobolev space. -/
def im (h : IsComplexWeakDivergenceEigenfunction a lambda U) : H¹₀(Ω) :=
  ⟨U.im, h.im_zeroBoundary⟩

/-- The equation holds against every complex zero-boundary Sobolev test, with complex
conjugation in the test factor. Hölder integrability justifies splitting the integrals. -/
theorem equation_complex_test (h : IsComplexWeakDivergenceEigenfunction a lambda U)
    (V : ComplexWkSpaceOn n 1 Ω)
    (hVr : V.re ∈ h10SubmoduleOn (n := n) (Ω := Ω))
    (hVi : V.im ∈ h10SubmoduleOn (n := n) (Ω := Ω)) :
    (∑ i : Fin n, ∑ j : Fin n,
      ∫ x, (a i j x : ℂ) * U.1 (singleDerivIndex n j) x *
        star (V.1 (singleDerivIndex n i) x) ∂domainMeasure n Ω) =
      lambda * ∫ x, U.1 (baseIndex n 1) x * star (V.1 (baseIndex n 1) x)
        ∂domainMeasure n Ω := by
  let vr : H¹₀(Ω) := ⟨V.re, hVr⟩
  let vi : H¹₀(Ω) := ⟨V.im, hVi⟩
  have hc (i j : Fin n) : MemLp
      (fun x ↦ (a i j x : ℂ) * U.1 (singleDerivIndex n j) x) 2 (domainMeasure n Ω) :=
    (Lp.memLp (a i j)).ofReal.mul (Lp.memLp (U.1 (singleDerivIndex n j)))
  simp_rw [Lp.integral_mul_conj_eq _ (hc _ _),
    Lp.integral_mul_conj_eq _ (Lp.memLp (U.1 (baseIndex n 1))),
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  change
    (∑ i, ∑ j, ∫ x, (a i j x : ℂ) * U.1 (singleDerivIndex n j) x *
      (derivCoordCLM i vr x : ℂ) ∂domainMeasure n Ω) -
    Complex.I * (∑ i, ∑ j, ∫ x, (a i j x : ℂ) * U.1 (singleDerivIndex n j) x *
      (derivCoordCLM i vi x : ℂ) ∂domainMeasure n Ω) = _
  rw [h.equation vr, h.equation vi]
  have hbr : baseCoordCLM vr =
      Complex.reCLM.compLpL 2 (domainMeasure n Ω) (V.1 (baseIndex n 1)) := rfl
  have hbi : baseCoordCLM vi =
      Complex.imCLM.compLpL 2 (domainMeasure n Ω) (V.1 (baseIndex n 1)) := rfl
  rw [hbr, hbi]
  ring

/-- Splitting the integral equation produces the coupled real variational equations. -/
theorem parts (h : IsComplexWeakDivergenceEigenfunction a lambda U)
    (v : H¹₀(Ω)) :
    variableCoeffForm (multiplicationCoefficientOperator a) h.re v =
        lambda.re * massFormCLM h.re v - lambda.im * massFormCLM h.im v ∧
      variableCoeffForm (multiplicationCoefficientOperator a) h.im v =
        lambda.re * massFormCLM h.im v + lambda.im * massFormCLM h.re v := by
  have heq := h.equation v
  simp_rw [Lp.integral_complex_coefficient_pairing, Lp.integral_complex_pairing,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Complex.ofReal_sum] at heq
  exact ⟨by simpa [variableCoeffForm_apply, massFormCLM_apply, re, im,
      ComplexWkSpaceOn.re, ComplexWkSpaceOn.im, realCoordinateTuple,
      derivCoordCLM, baseCoordCLM, Complex.mul_re] using congrArg Complex.re heq,
    by simpa [variableCoeffForm_apply, massFormCLM_apply, re, im,
      ComplexWkSpaceOn.re, ComplexWkSpaceOn.im, realCoordinateTuple,
      derivCoordCLM, baseCoordCLM, Complex.mul_im] using congrArg Complex.im heq⟩

/-- A nonzero complex state has a nonzero real or imaginary component. -/
theorem re_ne_zero_or_im_ne_zero (h : IsComplexWeakDivergenceEigenfunction a lambda U) :
    h.re ≠ 0 ∨ h.im ≠ 0 := by
  by_contra hzero
  push Not at hzero
  have hr : Complex.reCLM.compLpL 2 (domainMeasure n Ω) (U.1 (baseIndex n 1)) = 0 := by
    change baseCoordCLM h.re = 0
    rw [hzero.1, map_zero]
  have hi : Complex.imCLM.compLpL 2 (domainMeasure n Ω) (U.1 (baseIndex n 1)) = 0 := by
    change baseCoordCLM h.im = 0
    rw [hzero.2, map_zero]
  apply h.nonzero
  apply Lp.ext
  have hreal := Complex.reCLM.coeFn_compLpL (U.1 (baseIndex n 1))
  have himag := Complex.imCLM.coeFn_compLpL (U.1 (baseIndex n 1))
  rw [hr] at hreal
  rw [hi] at himag
  filter_upwards [hreal, himag, Lp.coeFn_zero ℝ 2 (domainMeasure n Ω),
    Lp.coeFn_zero ℂ 2 (domainMeasure n Ω)] with x hx hy hz hcz
  rw [hcz]
  apply Complex.ext
  · simpa only [hz, Complex.reCLM_apply, Pi.zero_apply, Complex.zero_re] using hx.symm
  · simpa only [hz, Complex.imCLM_apply, Pi.zero_apply, Complex.zero_im] using hy.symm

/-- The imaginary part of every complex weak eigenvalue of a symmetric real divergence
form is zero. Testing the coupled equations against opposite components gives
`Im(lambda) * (‖Re U‖₂² + ‖Im U‖₂²) = 0`. -/
theorem im_eq_zero (h : IsComplexWeakDivergenceEigenfunction a lambda U)
    (hsymm : AESymmetricCoefficient a) : lambda.im = 0 := by
  have hpos (v : H¹₀(Ω)) (hv : v ≠ 0) :
      0 < ‖baseCoordCLM v‖ ^ 2 := by
    apply sq_pos_of_pos
    apply norm_pos_iff.mpr
    intro hz
    exact hv (baseCoordCLM_injective h.isOpen (hz.trans (map_zero baseCoordCLM).symm))
  have hmass : 0 < ‖baseCoordCLM h.re‖ ^ 2 + ‖baseCoordCLM h.im‖ ^ 2 := by
    obtain hr | hi := h.re_ne_zero_or_im_ne_zero
    · exact add_pos_of_pos_of_nonneg (hpos _ hr) (sq_nonneg _)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (hpos _ hi)
  have heq := (h.parts h.re).2
  rw [variableCoeffForm_symm (symmetricCoefficientOperator_multiplication_of_ae a hsymm),
    (h.parts h.im).1] at heq
  simp only [massFormCLM_apply, real_inner_self_eq_norm_sq] at heq
  rw [real_inner_comm (baseCoordCLM h.im) (baseCoordCLM h.re)] at heq
  have hmul : lambda.im * (‖baseCoordCLM h.re‖ ^ 2 + ‖baseCoordCLM h.im‖ ^ 2) = 0 := by
    nlinarith only [heq]
  exact (mul_eq_zero.mp hmul).resolve_right (ne_of_gt hmass)

/-- Every complex weak eigenvalue is the complex inclusion of its real part. -/
theorem eq_ofReal (h : IsComplexWeakDivergenceEigenfunction a lambda U)
    (hsymm : AESymmetricCoefficient a) : lambda = (lambda.re : ℂ) := by
  apply Complex.ext
  · simp
  · simpa using h.im_eq_zero hsymm

/-- At least one component is a nonzero eigenfunction of the real form pencil.
This connects the complex weak problem to the real spectral enumeration. -/
theorem exists_real_weakEigenfunction (h : IsComplexWeakDivergenceEigenfunction a lambda U)
    (hsymm : AESymmetricCoefficient a) :
    ∃ v : H¹₀(Ω),
      Weak.IsWeakEigenfunction (variableCoeffForm (multiplicationCoefficientOperator a))
        massFormCLM lambda.re v := by
  have hz := h.im_eq_zero hsymm
  obtain hr | hi := h.re_ne_zero_or_im_ne_zero
  · exact ⟨h.re, hr, fun v ↦ by simpa only [hz, zero_mul, sub_zero] using (h.parts v).1⟩
  · exact ⟨h.im, hi, fun v ↦ by simpa only [hz, zero_mul, add_zero] using (h.parts v).2⟩

/-- On a bounded domain, uniform ellipticity makes every complex weak eigenvalue
strictly positive as a real number. Poincaré supplies coercivity of the energy form. -/
theorem re_pos (h : IsComplexWeakDivergenceEigenfunction a lambda U)
    (hn : 0 < n) (hbounded : Bornology.IsBounded Ω)
    (hsymm : AESymmetricCoefficient a)
    {alpha : ℝ} (helliptic : AEUniformlyElliptic a alpha) : 0 < lambda.re := by
  obtain ⟨v, hv⟩ := h.exists_real_weakEigenfunction hsymm
  obtain ⟨c, hc, hbound⟩ := variableCoeffForm_isCoercive hn hbounded
    (multiplicationCoefficientOperator a) (integratedElliptic_multiplication_of_ae a helliptic)
  have hnorm := norm_pos_iff.mpr hv.1
  have henergy := (mul_pos (mul_pos hc hnorm) hnorm).trans_le (hbound v)
  rw [hv.2 v, massFormCLM_apply, real_inner_self_eq_norm_sq] at henergy
  by_contra hnonpos
  exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hnonpos) (sq_nonneg _)))
    henergy

end IsComplexWeakDivergenceEigenfunction

end SobolevSpace.GraphSpace
