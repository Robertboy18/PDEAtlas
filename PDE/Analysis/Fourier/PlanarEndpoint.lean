/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import PDE.FDeriv.PartialDeriv
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import PDE.CoordinateSystems.Polar
import PDE.Analysis.Fourier.BesselEndpoint
import CAS.ExactTactic

/-!
# Order-two Fourier endpoint on the plane

Fourier inversion turns an integrable transform into a pointwise bound. Here a weighted
Cauchy–Schwarz estimate controls that integral by the order-two Bessel energy; polynomial
comparisons then express the bound through first and second derivatives. The final
Schwartz-function estimates include the Fourier inversion and Plancherel steps.

`angularFourierTransform2D` is the transform of (218) of Duruisseaux, Ganeshram, George and
Anandkumar, and `angularFourier_inversion2D` and `angularFourier_plancherel_schwartz` are their
(218) and (219). `angularFourierEndpoint_orderTwo` is their Proposition 9, (258), at `s = 2`,
with constant `1 / (2√π)`. `derivativePolynomialR2_orderTwo_le_besselPolynomial` and
`besselPolynomialR2_orderTwo_le_derivativePolynomial` are (229) and (233) in the proof of their
Proposition 6 for `k = 2`; the second gives the factor `3` in the constant `3 / (2√π)` of
`angularFourierEndpoint_orderTwo_derivativeEnergy` and
`morosi_pizzocchero_endpoint_orderTwo_schwartz`.

## References

* C. Morosi and L. Pizzocchero, "On the constants for some Sobolev imbeddings",
  *J. Inequal. Appl.* 6 (2001), no. 6, 665-679, numbering of arXiv:math/0011141v1,
  Propositions 2.1 and 3.1, (2.4). <https://arxiv.org/abs/math/0011141v1>
* V. Duruisseaux, A. Ganeshram, R. J. George and A. Anandkumar, "Stability Framework for the
  Singularity of the Euler Equations on ℝ³", arXiv:2609.10860v2, Appendix B.1, (218)-(219),
  p. 45, and Proposition 6, (223), and its proof, (225)-(234), pp. 46-47, and Appendix B.4,
  Proposition 9, (258), p. 53. <https://arxiv.org/abs/2609.10860v2>
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter LineDeriv
open scoped ENNReal RealInnerProductSpace Topology
open scoped FourierTransform SchwartzMap

namespace PDE.Analysis.Fourier

/-!
The next two lemmas compare the order-two derivative and Bessel polynomials.
The reverse comparison gives the factor `3` in the endpoint constant
`3 / (2 * sqrt pi)`. The integral estimates and Plancherel identity below
transfer this comparison to derivatives of Schwartz functions.

The factors `3` and `9` are valid but not optimal. Writing `D` for the derivative polynomial,
`D ≤ (1 + x² + y²)² ≤ (3/2) D`, since
`3 D - 2 (1 + x² + y²)² = ((x² - y²)² + (x² - 1)² + (y² - 1)²) / 2`; equality holds at the
origin on the left and at `x² = y² = 1` on the right. This would give the endpoint constant
`sqrt (3/2) / (2 * sqrt pi)`.
-/

/-- Order-two derivative polynomial is controlled by the Bessel polynomial: the
six-term derivative polynomial is at most `3` times `(1 + x² + y²)²`.
-/
theorem derivativePolynomialR2_orderTwo_le_besselPolynomial (x y : ℝ) :
    1 + x ^ 2 + y ^ 2 + x ^ 4 + x ^ 2 * y ^ 2 + y ^ 4 ≤
      3 * (1 + (x ^ 2 + y ^ 2)) ^ 2 := by
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
  have hx4 : 0 ≤ x ^ 4 := by positivity
  have hy4 : 0 ≤ y ^ 4 := by positivity
  have hxy : 0 ≤ x ^ 2 * y ^ 2 := mul_nonneg hx2 hy2
  nlinarith

/-- Order-two Bessel polynomial is controlled by nine times the derivative
polynomial.
-/
theorem besselPolynomialR2_orderTwo_le_derivativePolynomial (x y : ℝ) :
    (1 + (x ^ 2 + y ^ 2)) ^ 2 ≤
      9 * (1 + x ^ 2 + y ^ 2 + x ^ 4 + x ^ 2 * y ^ 2 + y ^ 4) := by
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
  have hx4 : 0 ≤ x ^ 4 := by positivity
  have hy4 : 0 ≤ y ^ 4 := by positivity
  have hxy : 0 ≤ x ^ 2 * y ^ 2 := mul_nonneg hx2 hy2
  nlinarith

/--
The order-two symbol comparison integrated against an arbitrary nonnegative
Fourier density.  This is the measure-theoretic step between the polynomial
calculation and the Sobolev–Bessel norm comparison; Plancherel is separate.
-/
theorem integral_orderTwo_derivative_bessel_comparison
    (g : (ℝ^2) → ℝ)
    (hDeriv : Integrable (fun ξ ↦
      (1 + ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 0 ^ 4 + ξ 0 ^ 2 * ξ 1 ^ 2 + ξ 1 ^ 4) * g ξ ^ 2))
    (hBessel : Integrable (fun ξ ↦
      (1 + (ξ 0 ^ 2 + ξ 1 ^ 2)) ^ 2 * g ξ ^ 2)) :
    (∫ ξ : (ℝ^2),
        (1 + ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 0 ^ 4 + ξ 0 ^ 2 * ξ 1 ^ 2 + ξ 1 ^ 4) *
          g ξ ^ 2) ≤
      3 * ∫ ξ : (ℝ^2), (1 + (ξ 0 ^ 2 + ξ 1 ^ 2)) ^ 2 * g ξ ^ 2 ∧
    (∫ ξ : (ℝ^2), (1 + (ξ 0 ^ 2 + ξ 1 ^ 2)) ^ 2 * g ξ ^ 2) ≤
      9 * ∫ ξ : (ℝ^2),
        (1 + ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 0 ^ 4 + ξ 0 ^ 2 * ξ 1 ^ 2 + ξ 1 ^ 4) *
          g ξ ^ 2 := by
  constructor <;> rw [← integral_const_mul]
  · exact integral_mono hDeriv (hBessel.const_mul 3) fun ξ ↦ (mul_le_mul_of_nonneg_right
      (derivativePolynomialR2_orderTwo_le_besselPolynomial (ξ 0) (ξ 1)) (sq_nonneg _)).trans_eq
      (mul_assoc _ _ _)
  · exact integral_mono hBessel (hDeriv.const_mul 9) fun ξ ↦ (mul_le_mul_of_nonneg_right
      (besselPolynomialR2_orderTwo_le_derivativePolynomial (ξ 0) (ξ 1)) (sq_nonneg _)).trans_eq
      (mul_assoc _ _ _)

private theorem sqrt_nine : √(9 : ℝ) = 3 := by
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/--
Square-root form of the integrated order-two comparison.  These are exactly
the factors `sqrt 3` and `3` used to pass between the two squared norms.
-/
theorem sqrt_integral_orderTwo_derivative_bessel_comparison
    (g : (ℝ^2) → ℝ)
    (hDeriv : Integrable (fun ξ ↦
      (1 + ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 0 ^ 4 + ξ 0 ^ 2 * ξ 1 ^ 2 + ξ 1 ^ 4) * g ξ ^ 2))
    (hBessel : Integrable (fun ξ ↦
      (1 + (ξ 0 ^ 2 + ξ 1 ^ 2)) ^ 2 * g ξ ^ 2)) :
    √(∫ ξ : (ℝ^2),
        (1 + ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 0 ^ 4 + ξ 0 ^ 2 * ξ 1 ^ 2 + ξ 1 ^ 4) *
          g ξ ^ 2) ≤
        √3 * √(∫ ξ : (ℝ^2),
          (1 + (ξ 0 ^ 2 + ξ 1 ^ 2)) ^ 2 * g ξ ^ 2) ∧
    √(∫ ξ : (ℝ^2),
        (1 + (ξ 0 ^ 2 + ξ 1 ^ 2)) ^ 2 * g ξ ^ 2) ≤
        3 * √(∫ ξ : (ℝ^2),
          (1 + ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 0 ^ 4 + ξ 0 ^ 2 * ξ 1 ^ 2 + ξ 1 ^ 4) *
            g ξ ^ 2) := by
  obtain ⟨hDB, hBD⟩ := integral_orderTwo_derivative_bessel_comparison g hDeriv hBessel
  exact ⟨(Real.sqrt_le_sqrt hDB).trans_eq (Real.sqrt_mul (by norm_num) _),
    (Real.sqrt_le_sqrt hBD).trans_eq (by rw [Real.sqrt_mul (by norm_num), sqrt_nine])⟩

/-- Order-two Bessel Fourier energy is at most nine times derivative Fourier energy on `(ℝ^2)`. -/
theorem integral_point_orderTwo_bessel_le_nine_derivative
    (g : (ℝ^2) → ℝ)
    (hDeriv : Integrable (fun ξ ↦
      (1 + ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 0 ^ 4 + ξ 0 ^ 2 * ξ 1 ^ 2 + ξ 1 ^ 4) * g ξ ^ 2))
    (hBessel : Integrable (fun ξ ↦
      (1 + (ξ 0 ^ 2 + ξ 1 ^ 2)) ^ 2 * g ξ ^ 2)) :
    (∫ ξ : (ℝ^2), (1 + (ξ 0 ^ 2 + ξ 1 ^ 2)) ^ 2 * g ξ ^ 2) ≤
      9 * ∫ ξ : (ℝ^2),
        (1 + ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 0 ^ 4 + ξ 0 ^ 2 * ξ 1 ^ 2 + ξ 1 ^ 4) *
          g ξ ^ 2 :=
  (integral_orderTwo_derivative_bessel_comparison g hDeriv hBessel).2

/-- Normalized square-root form of the order-two Bessel/derivative Fourier comparison. -/
theorem sqrt_normalized_point_orderTwo_bessel_le_three_derivative
    (g : (ℝ^2) → ℝ)
    (hDeriv : Integrable (fun ξ ↦
      (1 + ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 0 ^ 4 + ξ 0 ^ 2 * ξ 1 ^ 2 + ξ 1 ^ 4) * g ξ ^ 2))
    (hBessel : Integrable (fun ξ ↦
      (1 + (ξ 0 ^ 2 + ξ 1 ^ 2)) ^ 2 * g ξ ^ 2)) :
    √(((2 * Real.pi) ^ 2)⁻¹ *
        ∫ ξ : (ℝ^2), (1 + (ξ 0 ^ 2 + ξ 1 ^ 2)) ^ 2 * g ξ ^ 2) ≤
      3 * √(((2 * Real.pi) ^ 2)⁻¹ *
        ∫ ξ : (ℝ^2),
          (1 + ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 0 ^ 4 + ξ 0 ^ 2 * ξ 1 ^ 2 + ξ 1 ^ 4) *
            g ξ ^ 2) := by
  have hBD := mul_le_mul_of_nonneg_left
    (integral_point_orderTwo_bessel_le_nine_derivative g hDeriv hBessel)
    (by positivity : (0 : ℝ) ≤ ((2 * Real.pi) ^ 2)⁻¹)
  refine (Real.sqrt_le_sqrt (hBD.trans_eq (mul_left_comm _ _ _))).trans_eq ?_
  rw [Real.sqrt_mul (by norm_num), sqrt_nine]

/-- An explicit antiderivative of the radial order-two Bessel weight. -/
theorem hasDerivAt_neg_inv_two_mul_one_add_sq (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ -(2 * (1 + y ^ 2))⁻¹)
      (x * ((1 + x ^ 2) ^ 2)⁻¹) x := by
  cas

/-- Exact radial integral entering the sharp `H²(R²) → L∞(R²)` constant. -/
theorem integral_Ioi_mul_inv_one_add_sq_sq :
    (∫ x : ℝ in Set.Ioi 0, x * ((1 + x ^ 2) ^ 2)⁻¹) = 1 / 2 := by
  have h := PDE.Analysis.integral_Ioi_mul_one_add_sq_rpow_neg 2 (by norm_num)
  norm_num [Real.rpow_neg_natCast] at h
  exact h

/-- Exact two-dimensional Bessel-weight integral at Sobolev order two. -/
theorem integral_prod_one_add_sq_sq_inv :
    (∫ p : ℝ × ℝ, ((1 + p.1 ^ 2 + p.2 ^ 2) ^ 2)⁻¹) = Real.pi := by
  have h := PDE.Analysis.integral_prod_one_add_sq_rpow_neg 2 (by norm_num)
  norm_num [Real.rpow_neg_natCast] at h
  exact h

/-- The same exact Bessel-weight integral on the repository's `(ℝ^2)` type. -/
theorem integral_point_one_add_sq_sq_inv :
    (∫ x : (ℝ^2), ((1 + x 0 ^ 2 + x 1 ^ 2) ^ 2)⁻¹) = Real.pi := by
  have hToFun := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)
  have hToPair := volume_preserving_finTwoArrow ℝ
  calc
    (∫ x : (ℝ^2), ((1 + x 0 ^ 2 + x 1 ^ 2) ^ 2)⁻¹) =
        ∫ v : Fin 2 → ℝ, ((1 + v 0 ^ 2 + v 1 ^ 2) ^ 2)⁻¹ := by
      simpa using hToFun.integral_comp'
        (fun v : Fin 2 → ℝ ↦ ((1 + v 0 ^ 2 + v 1 ^ 2) ^ 2)⁻¹)
    _ = ∫ p : ℝ × ℝ, ((1 + p.1 ^ 2 + p.2 ^ 2) ^ 2)⁻¹ := by
      simpa [MeasurableEquiv.finTwoArrow_apply] using hToPair.integral_comp'
        (fun p : ℝ × ℝ ↦ ((1 + p.1 ^ 2 + p.2 ^ 2) ^ 2)⁻¹)
    _ = Real.pi := integral_prod_one_add_sq_sq_inv

/--
The exact weighted Cauchy–Schwarz estimate for the inverse-Fourier integral
at order two, before inserting the inverse-transform factor `(2*pi)⁻²`.
-/
theorem norm_oscillatoryIntegral_le_sqrt_pi_mul_besselEnergy
    (Fhat : (ℝ × ℝ) → ℂ) (x : ℝ × ℝ)
    (hFhat : AEStronglyMeasurable Fhat)
    (hEnergy : Integrable (fun p : ℝ × ℝ ↦
      (1 + p.1 ^ 2 + p.2 ^ 2) ^ 2 * ‖Fhat p‖ ^ 2)) :
    ‖∫ p : ℝ × ℝ,
        Complex.exp (Complex.I * (x.1 * p.1 + x.2 * p.2)) * Fhat p‖ ≤
      √Real.pi * √(∫ p : ℝ × ℝ,
        (1 + p.1 ^ 2 + p.2 ^ 2) ^ 2 * ‖Fhat p‖ ^ 2) := by
  have h := PDE.Analysis.norm_oscillatoryIntegral_le_sqrt_besselWeight
    2 (by norm_num) Fhat x hFhat (by simpa only [Real.rpow_two] using hEnergy)
  norm_num only [Real.rpow_two, show (2 : ℝ) - 1 = 1 by norm_num, div_one] at h
  exact h

/--
The order-two endpoint bound with factor `(2*pi)⁻²` in both the inverse
transform and the squared Bessel norm.
-/
theorem norm_angularInverseFourierIntegral_le_orderTwoBessel
    (Fhat : (ℝ × ℝ) → ℂ) (x : ℝ × ℝ)
    (hFhat : AEStronglyMeasurable Fhat)
    (hEnergy : Integrable (fun p : ℝ × ℝ ↦
      (1 + p.1 ^ 2 + p.2 ^ 2) ^ 2 * ‖Fhat p‖ ^ 2)) :
    ‖(((2 * Real.pi) ^ 2)⁻¹ : ℂ) *
        ∫ p : ℝ × ℝ,
          Complex.exp (Complex.I * (x.1 * p.1 + x.2 * p.2)) * Fhat p‖ ≤
      (1 / (2 * √Real.pi)) *
        √(((2 * Real.pi) ^ 2)⁻¹ *
          ∫ p : ℝ × ℝ,
            (1 + p.1 ^ 2 + p.2 ^ 2) ^ 2 * ‖Fhat p‖ ^ 2) := by
  have h := PDE.Analysis.fullSpace_bessel_endpoint 2 (by norm_num)
    (fun y ↦ (((2 * Real.pi) ^ 2)⁻¹ : ℂ) *
      ∫ p : ℝ × ℝ, Complex.exp (Complex.I * (y.1 * p.1 + y.2 * p.2)) * Fhat p)
    Fhat hFhat (by simpa only [Real.rpow_two] using hEnergy) (fun _ ↦ rfl) x
  norm_num only [Real.rpow_two, show (2 : ℝ) - 1 = 1 by norm_num, mul_one] at h
  exact h

/-- (ℝ^2)-space version of the exact weighted oscillatory Cauchy–Schwarz estimate. -/
theorem norm_oscillatoryIntegral_point_le_sqrt_pi_mul_besselEnergy
    (Fhat : (ℝ^2) → ℂ) (x : (ℝ^2))
    (hFhat : AEStronglyMeasurable Fhat)
    (hEnergy : Integrable (fun p : (ℝ^2) ↦
      (1 + p 0 ^ 2 + p 1 ^ 2) ^ 2 * ‖Fhat p‖ ^ 2)) :
    ‖∫ p : (ℝ^2),
        Complex.exp (Complex.I * (x 0 * p 0 + x 1 * p 1)) * Fhat p‖ ≤
      √Real.pi * √(∫ p : (ℝ^2),
        (1 + p 0 ^ 2 + p 1 ^ 2) ^ 2 * ‖Fhat p‖ ^ 2) := by
  let w : (ℝ^2) → ℝ := fun p ↦ 1 + p 0 ^ 2 + p 1 ^ 2
  let a : (ℝ^2) → ℂ := fun p ↦ ((w p : ℂ))⁻¹
  let b : (ℝ^2) → ℂ := fun p ↦
    Complex.exp (Complex.I * (x 0 * p 0 + x 1 * p 1)) * (w p : ℂ) * Fhat p
  have hwpos (p : ℝ^2) : 0 < w p := by dsimp only [w]; positivity
  have ha_sq : (∫ p : (ℝ^2), ‖a p‖ ^ 2) = Real.pi := by
    rw [← integral_point_one_add_sq_sq_inv]
    refine integral_congr_ae (.of_forall fun p ↦ ?_)
    simp only [a, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hwpos p)]
    simp [w, inv_pow]
  have ha : MemLp a 2 := (memLp_two_iff_integrable_sq_norm (by fun_prop)).2
    (Integrable.of_integral_ne_zero (ha_sq.trans_ne Real.pi_ne_zero))
  have hb_norm (p : (ℝ^2)) : ‖b p‖ ^ 2 = w p ^ 2 * ‖Fhat p‖ ^ 2 := by
    simp [b, Complex.norm_exp, abs_of_pos (hwpos p), mul_pow]
  have hb : MemLp b 2 := (memLp_two_iff_integrable_sq_norm
    ((by fun_prop : Continuous fun p : (ℝ^2) ↦ Complex.exp (Complex.I * (x 0 * p 0 + x 1 * p 1)) *
      (w p : ℂ)).aestronglyMeasurable.mul hFhat)).2
    (hEnergy.congr (.of_forall fun p ↦ (hb_norm p).symm))
  have hab (p : (ℝ^2)) :
      a p * b p = Complex.exp (Complex.I * (x 0 * p 0 + x 1 * p 1)) * Fhat p := by
    have hw : (w p : ℂ) ≠ 0 := by exact_mod_cast (hwpos p).ne'
    dsimp only [a, b]
    field_simp
  calc _ = ‖∫ p : (ℝ^2), a p * b p‖ := by simp_rw [hab]
    _ ≤ ∫ p : (ℝ^2), ‖a p‖ * ‖b p‖ :=
      (norm_integral_le_integral_norm _).trans_eq (by simp_rw [norm_mul])
    _ ≤ √(∫ p : (ℝ^2), ‖a p‖ ^ 2) * √(∫ p : (ℝ^2), ‖b p‖ ^ 2) := by
      simpa [Real.sqrt_eq_rpow] using integral_mul_norm_le_Lp_mul_Lq (μ := volume)
        (p := (2 : ℝ)) (q := (2 : ℝ)) Real.HolderConjugate.two_two (by simpa using ha)
        (by simpa using hb)
    _ = _ := by
      simp_rw [ha_sq, hb_norm]
      rfl

/-- Exact normalized order-two endpoint inequality directly on `(ℝ^2)`. -/
theorem norm_angularInverseFourierIntegral_point_le_orderTwoBessel
    (Fhat : (ℝ^2) → ℂ) (x : (ℝ^2))
    (hFhat : AEStronglyMeasurable Fhat)
    (hEnergy : Integrable (fun p : (ℝ^2) ↦
      (1 + p 0 ^ 2 + p 1 ^ 2) ^ 2 * ‖Fhat p‖ ^ 2)) :
    ‖(((2 * Real.pi) ^ 2)⁻¹ : ℂ) *
        ∫ p : (ℝ^2),
          Complex.exp (Complex.I * (x 0 * p 0 + x 1 * p 1)) * Fhat p‖ ≤
      (1 / (2 * √Real.pi)) *
        √(((2 * Real.pi) ^ 2)⁻¹ *
          ∫ p : (ℝ^2),
            (1 + p 0 ^ 2 + p 1 ^ 2) ^ 2 * ‖Fhat p‖ ^ 2) := by
  set c : ℝ := ((2 * Real.pi) ^ 2)⁻¹ with hc_def
  have hc : 0 < c := by positivity
  have hsqrtc : √c = (2 * Real.pi)⁻¹ := by
    rw [hc_def]
    cas
  have hcoeff : c * √Real.pi = (1 / (2 * √Real.pi)) * √c := by
    rw [hsqrtc, hc_def]
    cas
  rw [show (((2 * Real.pi) ^ 2)⁻¹ : ℂ) = (c : ℂ) by rw [hc_def]; norm_cast, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hc.le, Real.sqrt_mul hc.le]
  refine (mul_le_mul_of_nonneg_left (norm_oscillatoryIntegral_point_le_sqrt_pi_mul_besselEnergy
    Fhat x hFhat hEnergy) hc.le).trans_eq ?_
  linear_combination √(∫ p : (ℝ^2), (1 + p 0 ^ 2 + p 1 ^ 2) ^ 2 * ‖Fhat p‖ ^ 2) * hcoeff

/--
The order-two endpoint bound assuming the inverse Fourier formula with
factor `(2*pi)⁻²`.
-/
theorem angularFourierEndpoint_orderTwo_of_inverseFormula
    (F Fhat : (ℝ × ℝ) → ℂ)
    (hFhat : AEStronglyMeasurable Fhat)
    (hEnergy : Integrable (fun p : ℝ × ℝ ↦
      (1 + p.1 ^ 2 + p.2 ^ 2) ^ 2 * ‖Fhat p‖ ^ 2))
    (hInverse : ∀ x,
      F x = (((2 * Real.pi) ^ 2)⁻¹ : ℂ) *
        ∫ p : ℝ × ℝ,
          Complex.exp (Complex.I * (x.1 * p.1 + x.2 * p.2)) * Fhat p)
    (x : ℝ × ℝ) :
    ‖F x‖ ≤ (1 / (2 * √Real.pi)) *
      √(((2 * Real.pi) ^ 2)⁻¹ *
        ∫ p : ℝ × ℝ,
          (1 + p.1 ^ 2 + p.2 ^ 2) ^ 2 * ‖Fhat p‖ ^ 2) := by
  rw [hInverse x]
  exact norm_angularInverseFourierIntegral_le_orderTwoBessel Fhat x hFhat hEnergy

/--
The Fourier transform in angular frequency, `eta ↦ ∫ exp(-i ⟪x, eta⟫) f(x) dx`, obtained
from Mathlib's `2*pi` Fourier convention by the frequency rescaling `eta ↦ eta/(2*pi)`.
-/
def angularFourierTransform2D (f : (ℝ^2) → ℂ) : (ℝ^2) → ℂ :=
  fun eta ↦ 𝓕 f ((2 * Real.pi)⁻¹ • eta)

/-- The real inner product on the plane is the sum of the coordinate products. -/
theorem point_inner_eq_coordinates (u v : (ℝ^2)) :
    inner ℝ u v = u 0 * v 0 + u 1 * v 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply, Real.inner_apply]

/--
The inverse Fourier formula with factor `(2*pi)⁻²`, for integrable data with
integrable transform, at a point of continuity.
-/
theorem angularFourier_inversion2D
    (f : (ℝ^2) → ℂ)
    (hf : Integrable f) (hFourier : Integrable (𝓕 f))
    {x : (ℝ^2)} (hx : ContinuousAt f x) :
    f x = (((2 * Real.pi) ^ 2)⁻¹ : ℂ) *
      ∫ eta : (ℝ^2),
        Complex.exp (Complex.I * (x 0 * eta 0 + x 1 * eta 1)) *
          angularFourierTransform2D f eta := by
  let G : (ℝ^2) → ℂ := fun eta ↦
    Complex.exp (Complex.I * (x 0 * eta 0 + x 1 * eta 1)) *
      angularFourierTransform2D f eta
  have hR : 0 ≤ 2 * Real.pi := by positivity
  have hscale := Measure.integral_comp_smul_of_nonneg
    (μ := (volume : Measure (ℝ^2))) G (2 * Real.pi) (hR := hR)
  have hscale' :
      (∫ xi : (ℝ^2),
        Complex.exp (Complex.I *
          (2 * Real.pi * (x 0 * xi 0 + x 1 * xi 1))) * 𝓕 f xi) =
        (((2 * Real.pi) ^ 2)⁻¹ : ℂ) * ∫ eta : (ℝ^2), G eta := by
    simpa [G, angularFourierTransform2D, smul_eq_mul, smul_smul, Real.pi_ne_zero,
      mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm] using hscale
  have hinv := hf.fourierInv_fourier_eq hFourier hx
  rw [Real.fourierInv_eq'] at hinv
  rw [← hinv]
  simpa [G, point_inner_eq_coordinates, real_inner_comm, smul_eq_mul, mul_comm,
    mul_left_comm, mul_assoc] using hscale'

/-- Plancherel identity with Fourier-energy factor `(2*pi)⁻²` for Schwartz functions.
-/
theorem angularFourier_plancherel_schwartz (f : 𝓢((ℝ^2), ℂ)) :
    ((2 * Real.pi) ^ 2)⁻¹ *
        ∫ eta : (ℝ^2), ‖angularFourierTransform2D (fun x ↦ f x) eta‖ ^ 2 =
      ∫ x : (ℝ^2), ‖f x‖ ^ 2 := by
  have hR : 0 ≤ 2 * Real.pi := by positivity
  have hscale := Measure.integral_comp_inv_smul_of_nonneg
    (μ := (volume : Measure (ℝ^2)))
    (fun xi : (ℝ^2) ↦ ‖𝓕 (fun x ↦ f x) xi‖ ^ 2) hR
  have hscale' :
      (∫ eta : (ℝ^2), ‖angularFourierTransform2D (fun x ↦ f x) eta‖ ^ 2) =
        (2 * Real.pi) ^ 2 * ∫ xi : (ℝ^2), ‖𝓕 f xi‖ ^ 2 := by
    simpa [angularFourierTransform2D, SchwartzMap.fourier_coe] using hscale
  rw [hscale', SchwartzMap.integral_norm_sq_fourier]
  have hne : (2 * Real.pi) ^ 2 ≠ 0 := by positivity
  field_simp

/-- Integrability of the squared norm of the rescaled Fourier transform of Schwartz data. -/
theorem integrable_angularFourier_norm_sq_schwartz (f : 𝓢((ℝ^2), ℂ)) :
    Integrable (fun eta : (ℝ^2) ↦
      ‖angularFourierTransform2D (fun x ↦ f x) eta‖ ^ 2) := by
  have h := ((memLp_two_iff_integrable_sq_norm
    (𝓕 f).continuous.aestronglyMeasurable).1 ((𝓕 f).memLp 2)).comp_smul
    (inv_ne_zero (by positivity : (2 * Real.pi) ≠ 0))
  simpa [angularFourierTransform2D, SchwartzMap.fourier_coe] using h

/-- Non-unitary Fourier multiplier formula for a Schwartz directional derivative. -/
theorem angularFourier_lineDeriv_schwartz
    (f : 𝓢((ℝ^2), ℂ)) (m eta : (ℝ^2)) :
    angularFourierTransform2D (fun x ↦ (∂_{m} f) x) eta =
      Complex.I * (inner ℝ eta m : ℝ) * angularFourierTransform2D (fun x ↦ f x) eta := by
  let xi : (ℝ^2) := (2 * Real.pi)⁻¹ • eta
  have hFourier := congrArg (fun g : 𝓢((ℝ^2), ℂ) ↦ g xi)
    (SchwartzMap.fourier_lineDerivOp_eq f m)
  have hinner : (inner ℝ · m : (ℝ^2) → ℝ).HasTemperateGrowth :=
    ((innerSL ℝ).flip m).hasTemperateGrowth
  calc
    angularFourierTransform2D (fun x ↦ (∂_{m} f) x) eta = (𝓕 (∂_{m} f)) xi := by
      rfl
    _ = ((2 * Real.pi * Complex.I) •
        (SchwartzMap.smulLeftCLM ℂ (inner ℝ · m)) (𝓕 f)) xi := hFourier
    _ = Complex.I * (inner ℝ eta m : ℝ) *
        angularFourierTransform2D (fun x ↦ f x) eta := by
      simp [SchwartzMap.smulLeftCLM_apply_apply hinner, xi, angularFourierTransform2D,
        inner_smul_left, smul_eq_mul, SchwartzMap.fourier_coe]
      field_simp [Real.pi_ne_zero]

/--
Non-unitary Plancherel for a directional derivative.  This identifies the
Fourier multiplier energy with the physical-space derivative norm.
-/
theorem angularFourier_lineDeriv_plancherel_schwartz
    (f : 𝓢((ℝ^2), ℂ)) (m : (ℝ^2)) :
    ((2 * Real.pi) ^ 2)⁻¹ *
        ∫ eta : (ℝ^2), (inner ℝ eta m) ^ 2 *
          ‖angularFourierTransform2D (fun x ↦ f x) eta‖ ^ 2 =
      ∫ x : (ℝ^2), ‖(∂_{m} f) x‖ ^ 2 := by
  rw [← angularFourier_plancherel_schwartz (∂_{m} f)]
  congr 1
  refine integral_congr_ae (.of_forall fun eta ↦ ?_)
  simp only [angularFourier_lineDeriv_schwartz, norm_mul, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, one_mul, mul_pow, sq_abs]

/-- Non-unitary Plancherel for two successive directional derivatives. -/
theorem angularFourier_twoLineDeriv_plancherel_schwartz
    (f : 𝓢((ℝ^2), ℂ)) (m n : (ℝ^2)) :
    ((2 * Real.pi) ^ 2)⁻¹ *
        ∫ eta : (ℝ^2), (inner ℝ eta m) ^ 2 * (inner ℝ eta n) ^ 2 *
          ‖angularFourierTransform2D (fun x ↦ f x) eta‖ ^ 2 =
      ∫ x : (ℝ^2), ‖(∂_{m} (∂_{n} f)) x‖ ^ 2 := by
  rw [← angularFourier_lineDeriv_plancherel_schwartz (∂_{n} f) m]
  congr 1
  refine integral_congr_ae (.of_forall fun eta ↦ ?_)
  simp only [angularFourier_lineDeriv_schwartz, norm_mul, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, one_mul, mul_pow, sq_abs, mul_assoc]

/-- The first-derivative Fourier multiplier density is integrable for Schwartz data. -/
theorem integrable_angularFourier_lineDeriv_density_schwartz
    (f : 𝓢((ℝ^2), ℂ)) (m : (ℝ^2)) :
    Integrable (fun eta : (ℝ^2) ↦ (inner ℝ eta m) ^ 2 *
      ‖angularFourierTransform2D (fun x ↦ f x) eta‖ ^ 2) := by
  refine (integrable_angularFourier_norm_sq_schwartz (∂_{m} f)).congr ?_
  filter_upwards [] with eta
  rw [angularFourier_lineDeriv_schwartz]
  simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    one_mul, mul_pow, sq_abs, mul_assoc]

/-- The mixed second-derivative Fourier multiplier density is integrable for Schwartz data. -/
theorem integrable_angularFourier_twoLineDeriv_density_schwartz
    (f : 𝓢((ℝ^2), ℂ)) (m n : (ℝ^2)) :
    Integrable (fun eta : (ℝ^2) ↦ (inner ℝ eta m) ^ 2 * (inner ℝ eta n) ^ 2 *
      ‖angularFourierTransform2D (fun x ↦ f x) eta‖ ^ 2) := by
  refine (integrable_angularFourier_norm_sq_schwartz (∂_{m} (∂_{n} f))).congr ?_
  filter_upwards [] with eta
  rw [angularFourier_lineDeriv_schwartz, angularFourier_lineDeriv_schwartz]
  simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    one_mul, mul_pow, sq_abs, mul_assoc]

/-- The complete order-two Fourier derivative density is integrable for Schwartz data. -/
theorem integrable_angularFourier_orderTwo_derivativeEnergy_schwartz
    (f : 𝓢((ℝ^2), ℂ)) :
    Integrable (fun eta : (ℝ^2) ↦
      (1 + eta 0 ^ 2 + eta 1 ^ 2 + eta 0 ^ 4 +
          eta 0 ^ 2 * eta 1 ^ 2 + eta 1 ^ 4) *
        ‖angularFourierTransform2D (fun x ↦ f x) eta‖ ^ 2) := by
  let e0 : (ℝ^2) := EuclideanSpace.single (0 : Fin 2) 1
  let e1 : (ℝ^2) := EuclideanSpace.single (1 : Fin 2) 1
  have h0 := integrable_angularFourier_norm_sq_schwartz f
  have h10 := integrable_angularFourier_lineDeriv_density_schwartz f e0
  have h01 := integrable_angularFourier_lineDeriv_density_schwartz f e1
  have h20 := integrable_angularFourier_twoLineDeriv_density_schwartz f e0 e0
  have h11 := integrable_angularFourier_twoLineDeriv_density_schwartz f e0 e1
  have h02 := integrable_angularFourier_twoLineDeriv_density_schwartz f e1 e1
  have hsum := ((((h0.add h10).add h01).add h20).add h11).add h02
  refine hsum.congr ?_
  filter_upwards [] with eta
  simp [e0, e1, EuclideanSpace.inner_single_right]
  ring

/--
The order-two Bessel-potential density used by the endpoint proof is integrable for Schwartz data.
-/
theorem integrable_angularFourier_orderTwo_besselEnergy_schwartz
    (f : 𝓢((ℝ^2), ℂ)) :
    Integrable (fun eta : (ℝ^2) ↦
      (1 + (eta 0 ^ 2 + eta 1 ^ 2)) ^ 2 *
        ‖angularFourierTransform2D (fun x ↦ f x) eta‖ ^ 2) := by
  let e0 : (ℝ^2) := EuclideanSpace.single (0 : Fin 2) 1
  let e1 : (ℝ^2) := EuclideanSpace.single (1 : Fin 2) 1
  have h0 := integrable_angularFourier_norm_sq_schwartz f
  have h10 := integrable_angularFourier_lineDeriv_density_schwartz f e0
  have h01 := integrable_angularFourier_lineDeriv_density_schwartz f e1
  have h20 := integrable_angularFourier_twoLineDeriv_density_schwartz f e0 e0
  have h11 := integrable_angularFourier_twoLineDeriv_density_schwartz f e0 e1
  have h02 := integrable_angularFourier_twoLineDeriv_density_schwartz f e1 e1
  have hsum1 := (h0.add h10).add h10
  have hsum2 := (hsum1.add h01).add h01
  have hsum3 := (hsum2.add h20).add h11
  have hsum := (hsum3.add h11).add h02
  refine hsum.congr ?_
  filter_upwards [] with eta
  simp [e0, e1, EuclideanSpace.inner_single_right]
  ring

/--
The Fourier derivative energy with factor `(2*pi)⁻²` equals the sum of
the six physical-space squared `L²` norms through order two for Schwartz data.
-/
theorem angularFourier_orderTwo_derivativeEnergy_eq_schwartz
    (f : 𝓢((ℝ^2), ℂ)) :
    ((2 * Real.pi) ^ 2)⁻¹ *
        ∫ eta : (ℝ^2),
          (1 + eta 0 ^ 2 + eta 1 ^ 2 + eta 0 ^ 4 +
              eta 0 ^ 2 * eta 1 ^ 2 + eta 1 ^ 4) *
            ‖angularFourierTransform2D (fun x ↦ f x) eta‖ ^ 2 =
      (∫ x : (ℝ^2), ‖f x‖ ^ 2) +
      (∫ x : (ℝ^2),
        ‖(∂_{EuclideanSpace.single (0 : Fin 2) (1 : ℝ)} f) x‖ ^ 2) +
      (∫ x : (ℝ^2),
        ‖(∂_{EuclideanSpace.single (1 : Fin 2) (1 : ℝ)} f) x‖ ^ 2) +
      (∫ x : (ℝ^2),
        ‖(∂_{EuclideanSpace.single (0 : Fin 2) (1 : ℝ)}
          (∂_{EuclideanSpace.single (0 : Fin 2) (1 : ℝ)} f)) x‖ ^ 2) +
      (∫ x : (ℝ^2),
        ‖(∂_{EuclideanSpace.single (0 : Fin 2) (1 : ℝ)}
          (∂_{EuclideanSpace.single (1 : Fin 2) (1 : ℝ)} f)) x‖ ^ 2) +
      ∫ x : (ℝ^2),
        ‖(∂_{EuclideanSpace.single (1 : Fin 2) (1 : ℝ)}
          (∂_{EuclideanSpace.single (1 : Fin 2) (1 : ℝ)} f)) x‖ ^ 2 := by
  set e0 : (ℝ^2) := EuclideanSpace.single (0 : Fin 2) 1
  set e1 : (ℝ^2) := EuclideanSpace.single (1 : Fin 2) 1
  have hp0 := angularFourier_plancherel_schwartz f
  have hp10 := angularFourier_lineDeriv_plancherel_schwartz f e0
  have hp01 := angularFourier_lineDeriv_plancherel_schwartz f e1
  have hp20 := angularFourier_twoLineDeriv_plancherel_schwartz f e0 e0
  have hp11 := angularFourier_twoLineDeriv_plancherel_schwartz f e0 e1
  have hp02 := angularFourier_twoLineDeriv_plancherel_schwartz f e1 e1
  have hint : ∀ i ∈ Finset.univ, Integrable
      (![fun eta ↦ ‖angularFourierTransform2D (fun x ↦ f x) eta‖ ^ 2,
        fun eta ↦ inner ℝ eta e0 ^ 2 * ‖angularFourierTransform2D (fun x ↦ f x) eta‖ ^ 2,
        fun eta ↦ inner ℝ eta e1 ^ 2 * ‖angularFourierTransform2D (fun x ↦ f x) eta‖ ^ 2,
        fun eta ↦ inner ℝ eta e0 ^ 2 * inner ℝ eta e0 ^ 2 *
          ‖angularFourierTransform2D (fun x ↦ f x) eta‖ ^ 2,
        fun eta ↦ inner ℝ eta e0 ^ 2 * inner ℝ eta e1 ^ 2 *
          ‖angularFourierTransform2D (fun x ↦ f x) eta‖ ^ 2,
        fun eta ↦ inner ℝ eta e1 ^ 2 * inner ℝ eta e1 ^ 2 *
          ‖angularFourierTransform2D (fun x ↦ f x) eta‖ ^ 2] i) := by
    intro i _
    fin_cases i
    exacts [integrable_angularFourier_norm_sq_schwartz f,
      integrable_angularFourier_lineDeriv_density_schwartz f e0,
      integrable_angularFourier_lineDeriv_density_schwartz f e1,
      integrable_angularFourier_twoLineDeriv_density_schwartz f e0 e0,
      integrable_angularFourier_twoLineDeriv_density_schwartz f e0 e1,
      integrable_angularFourier_twoLineDeriv_density_schwartz f e1 e1]
  -- the polynomial weight is the sum of the six Fourier multipliers
  rw [integral_congr_ae (.of_forall fun eta ↦ ?_) |>.trans (integral_finsetSum _ hint)]
  · simp only [Fin.sum_univ_six, Matrix.cons_val]
    linear_combination hp0 + hp10 + hp01 + hp20 + hp11 + hp02
  · simp [Fin.sum_univ_six, e0, e1, EuclideanSpace.inner_single_right]
    ring

/--
The order-two Morosi–Pizzocchero endpoint bound on the plane, for integrable
data with integrable transform and finite Bessel energy, at a point of continuity.
-/
theorem angularFourierEndpoint_orderTwo
    (f : (ℝ^2) → ℂ)
    (hf : Integrable f) (hFourier : Integrable (𝓕 f))
    {x : (ℝ^2)} (hx : ContinuousAt f x)
    (hEnergy : Integrable (fun p : (ℝ^2) ↦
      (1 + p 0 ^ 2 + p 1 ^ 2) ^ 2 * ‖angularFourierTransform2D f p‖ ^ 2)) :
    ‖f x‖ ≤ (1 / (2 * √Real.pi)) *
      √(((2 * Real.pi) ^ 2)⁻¹ *
        ∫ p : (ℝ^2),
          (1 + p 0 ^ 2 + p 1 ^ 2) ^ 2 * ‖angularFourierTransform2D f p‖ ^ 2) := by
  have hFourierCont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar continuous_inner hf
  have hReferenceMeas : AEStronglyMeasurable (angularFourierTransform2D f) :=
    (hFourierCont.comp (by fun_prop)).aestronglyMeasurable
  rw [angularFourier_inversion2D f hf hFourier hx]
  exact norm_angularInverseFourierIntegral_point_le_orderTwoBessel
    (angularFourierTransform2D f) x hReferenceMeas hEnergy

/--
The order-two endpoint estimate in terms of the six-term Fourier derivative
energy, with constant `3 / (2*sqrt pi)`.
-/
theorem angularFourierEndpoint_orderTwo_derivativeEnergy
    (f : (ℝ^2) → ℂ)
    (hf : Integrable f) (hFourier : Integrable (𝓕 f))
    {x : (ℝ^2)} (hx : ContinuousAt f x)
    (hDeriv : Integrable (fun ξ : (ℝ^2) ↦
      (1 + ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 0 ^ 4 + ξ 0 ^ 2 * ξ 1 ^ 2 + ξ 1 ^ 4) *
        ‖angularFourierTransform2D f ξ‖ ^ 2))
    (hBessel : Integrable (fun ξ : (ℝ^2) ↦
      (1 + (ξ 0 ^ 2 + ξ 1 ^ 2)) ^ 2 * ‖angularFourierTransform2D f ξ‖ ^ 2)) :
    ‖f x‖ ≤ (3 / (2 * √Real.pi)) *
      √(((2 * Real.pi) ^ 2)⁻¹ *
        ∫ ξ : (ℝ^2),
          (1 + ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 0 ^ 4 + ξ 0 ^ 2 * ξ 1 ^ 2 + ξ 1 ^ 4) *
            ‖angularFourierTransform2D f ξ‖ ^ 2) := by
  have hEndpoint := angularFourierEndpoint_orderTwo f hf hFourier hx
    (by simpa [add_assoc] using hBessel)
  have hComparison := sqrt_normalized_point_orderTwo_bessel_le_three_derivative
    (fun ξ ↦ ‖angularFourierTransform2D f ξ‖) hDeriv hBessel
  simp only [add_assoc] at hEndpoint hComparison ⊢
  refine hEndpoint.trans ((mul_le_mul_of_nonneg_left hComparison (by positivity)).trans_eq ?_)
  ring

/--
The order-two endpoint estimate for a Schwartz function on the plane, in terms of the `L²`
norms of the function and of its first and second partial derivatives, with constant
`3 / (2√π)`: Proposition 9, (258), at `s = 2` combined with the right inequality of
Proposition 6, (223), for `k = 2`, of Duruisseaux et al.
-/
theorem morosi_pizzocchero_endpoint_orderTwo_schwartz
    (f : 𝓢((ℝ^2), ℂ)) (x : (ℝ^2)) :
    ‖f x‖ ≤ (3 / (2 * √Real.pi)) * √(
      (∫ y : (ℝ^2), ‖f y‖ ^ 2) +
      (∫ y : (ℝ^2),
        ‖(∂_{EuclideanSpace.single (0 : Fin 2) (1 : ℝ)} f) y‖ ^ 2) +
      (∫ y : (ℝ^2),
        ‖(∂_{EuclideanSpace.single (1 : Fin 2) (1 : ℝ)} f) y‖ ^ 2) +
      (∫ y : (ℝ^2),
        ‖(∂_{EuclideanSpace.single (0 : Fin 2) (1 : ℝ)}
          (∂_{EuclideanSpace.single (0 : Fin 2) (1 : ℝ)} f)) y‖ ^ 2) +
      (∫ y : (ℝ^2),
        ‖(∂_{EuclideanSpace.single (0 : Fin 2) (1 : ℝ)}
          (∂_{EuclideanSpace.single (1 : Fin 2) (1 : ℝ)} f)) y‖ ^ 2) +
      ∫ y : (ℝ^2),
        ‖(∂_{EuclideanSpace.single (1 : Fin 2) (1 : ℝ)}
          (∂_{EuclideanSpace.single (1 : Fin 2) (1 : ℝ)} f)) y‖ ^ 2) := by
  have hf : Integrable (fun y : (ℝ^2) ↦ f y) := f.integrable
  have hFourier : Integrable (𝓕 (fun y : (ℝ^2) ↦ f y)) := by
    simpa [SchwartzMap.fourier_coe] using (𝓕 f).integrable
  have hEndpoint := angularFourierEndpoint_orderTwo_derivativeEnergy
    (fun y : (ℝ^2) ↦ f y) hf hFourier (x := x) f.continuous.continuousAt
    (integrable_angularFourier_orderTwo_derivativeEnergy_schwartz f)
    (integrable_angularFourier_orderTwo_besselEnergy_schwartz f)
  rw [angularFourier_orderTwo_derivativeEnergy_eq_schwartz f] at hEndpoint
  exact hEndpoint

/--
Evaluation of the general Morosi–Pizzocchero constant `1 / (2√(π (s - 1)))`
at `s = 2`: it is positive and equals `1 / (2√π)`.  This is arithmetic only;
the embedding theorem with this constant is
`angularFourierEndpoint_orderTwo`.
-/
theorem morosi_pizzocchero_endpoint_sobolev_constant :
    0 < (1 / (2 * √(Real.pi * ((2 : ℝ) - 1))) : ℝ) ∧
      (1 / (2 * √(Real.pi * ((2 : ℝ) - 1))) : ℝ) =
        1 / (2 * √Real.pi) := by
  constructor
  · positivity
  · norm_num

end PDE.Analysis.Fourier
