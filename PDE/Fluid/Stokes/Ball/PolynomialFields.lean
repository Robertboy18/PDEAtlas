/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Legendre.SolidHarmonic
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Polynomial vector fields with radial factors

Let `P` be a polynomial in three variables with `∑ⱼ Xⱼ ∂ⱼ P = c P` (Euler's identity for a
homogeneous polynomial of degree `c`) and `∑ⱼ ∂ⱼ∂ⱼ P = 0`. The fields built from a harmonic
homogeneous `P` that enter the Stokes modes of a ball are `P x`, the gradient `∇P` and the swirl
field `x × ∇P`. Their components are again homogeneous: `P Xᵢ` of degree `c + 1`, `∂ᵢ P` of degree
`c - 1` and `X_{i+1} ∂_{i+2} P - X_{i+2} ∂_{i+1} P` of degree `c`; the last two are harmonic and
`Δ (P Xᵢ) = 2 ∂ᵢ P`. The divergence sums are `∑ᵢ ∂ᵢ (P Xᵢ) = (c + 3) P`, `∑ᵢ ∂ᵢ∂ᵢ P = 0` and
`∑ᵢ ∂ᵢ (x × ∇P)ᵢ = 0`, and `x · (x × ∇P) = 0`.

For a function `F` of the squared radius and a polynomial `Q` with `∑ⱼ Xⱼ ∂ⱼ Q = c Q`, the
function `F(‖x‖²) Q(x)` has Laplacian `(4 ‖x‖² F'' + (4c + 6) F') Q + F ΔQ` and radial derivative
`∑ⱼ xⱼ ∂ⱼ (F Q) = (2 ‖x‖² F' + c F) Q`, with `F'` and `F''` at `‖x‖²`.
-/

@[expose] public noncomputable section

open PDE (partialDeriv laplacian)
open MvPolynomial EuclideanLaplacian PDE.Analysis.SpecialFunctions

namespace PDE.Fluid.Stokes.Ball

/-- The `i`-th component `X_{i+1} ∂_{i+2} P - X_{i+2} ∂_{i+1} P` of the swirl field `x × ∇P`. -/
def swirlPolynomial (P : MvPolynomial (Fin 3) ℝ) (i : Fin 3) : MvPolynomial (Fin 3) ℝ :=
  X (i + 1) * pderiv (i + 2) P - X (i + 2) * pderiv (i + 1) P

section Algebra

variable {P : MvPolynomial (Fin 3) ℝ} {c : ℝ}

/-- Euler's identity for `P Xᵢ`: the degree goes up by one. -/
theorem sum_X_mul_pderiv_mul_X (hE : ∑ j, X j * pderiv j P = C c * P) (i : Fin 3) :
    ∑ j, X j * pderiv j (P * X i) = C (c + 1) * (P * X i) := by
  simp only [Fin.sum_univ_three] at hE ⊢
  rw [C_add, map_one]
  fin_cases i
  · simp only [Fin.isValue, Fin.zero_eta, Derivation.leibniz, pderiv_X, Pi.single_eq_same,
      smul_eq_mul, mul_one, ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, mul_zero,
      zero_add, Fin.reduceEq]
    linear_combination X 0 * hE
  · simp only [Fin.isValue, Fin.mk_one, Derivation.leibniz, pderiv_X, ne_eq, one_ne_zero,
      not_false_eq_true, Pi.single_eq_of_ne, smul_eq_mul, mul_zero, zero_add, Pi.single_eq_same,
      mul_one, Fin.reduceEq]
    linear_combination X 1 * hE
  · simp only [Fin.isValue, Fin.reduceFinMk, Derivation.leibniz, pderiv_X, ne_eq, Fin.reduceEq,
      not_false_eq_true, Pi.single_eq_of_ne, smul_eq_mul, mul_zero, zero_add, Pi.single_eq_same,
      mul_one]
    linear_combination X 2 * hE

/-- Euler's identity for `∂ᵢ P`: the degree goes down by one. -/
theorem sum_X_mul_pderiv_pderiv (hE : ∑ j, X j * pderiv j P = C c * P) (i : Fin 3) :
    ∑ j, X j * pderiv j (pderiv i P) = C (c - 1) * pderiv i P := by
  have h := congrArg (pderiv i) hE
  simp only [Fin.sum_univ_three, map_add, pderiv_mul, pderiv_X, Pi.single_apply, pderiv_C, zero_mul,
    zero_add] at h ⊢
  rw [map_sub, map_one, pderiv_comm 0 i, pderiv_comm 1 i, pderiv_comm 2 i]
  fin_cases i <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, ↓reduceIte, one_mul,
      one_ne_zero, zero_ne_one, zero_mul, zero_add, Fin.reduceEq] at h ⊢ <;>
    linear_combination h

/-- Euler's identity for `Xₐ Q`: `∑ⱼ Xⱼ ∂ⱼ (Xₐ Q) = Xₐ Q + Xₐ ∑ⱼ Xⱼ ∂ⱼ Q`. -/
theorem sum_X_mul_pderiv_X_mul (a : Fin 3) (Q : MvPolynomial (Fin 3) ℝ) :
    ∑ j, X j * pderiv j (X a * Q) = X a * Q + X a * ∑ j, X j * pderiv j Q := by
  simp only [Fin.sum_univ_three]
  fin_cases a <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Derivation.leibniz,
      smul_eq_mul, pderiv_X, Pi.single_eq_same, mul_one, ne_eq, zero_ne_one, one_ne_zero,
      not_false_eq_true, Pi.single_eq_of_ne, mul_zero, add_zero, Fin.reduceEq] <;>
    ring

/-- Euler's identity for the swirl components: the degree is unchanged. -/
theorem sum_X_mul_pderiv_swirlPolynomial (hE : ∑ j, X j * pderiv j P = C c * P) (i : Fin 3) :
    ∑ j, X j * pderiv j (swirlPolynomial P i) = C c * swirlPolynomial P i := by
  have hA := sum_X_mul_pderiv_pderiv hE (i + 2)
  have hB := sum_X_mul_pderiv_pderiv hE (i + 1)
  simp only [swirlPolynomial, map_sub, mul_sub, Finset.sum_sub_distrib]
  rw [sum_X_mul_pderiv_X_mul, sum_X_mul_pderiv_X_mul, hA, hB, map_sub, map_one]
  ring

/-- The Laplacian of `Xₐ Q` is `Xₐ ΔQ + 2 ∂ₐ Q`. -/
theorem polynomialLaplacian_X_mul (a : Fin 3) (Q : MvPolynomial (Fin 3) ℝ) :
    polynomialLaplacian (X a * Q) = X a * polynomialLaplacian Q + 2 * pderiv a Q := by
  simp only [polynomialLaplacian, Fin.sum_univ_three]
  fin_cases a <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Derivation.leibniz,
      smul_eq_mul, pderiv_X, Pi.single_eq_same, mul_one, map_add, ne_eq, zero_ne_one,
      one_ne_zero, not_false_eq_true, Pi.single_eq_of_ne, mul_zero, add_zero, Fin.reduceEq] <;>
    ring

/-- `Δ (P Xᵢ) = 2 ∂ᵢ P` for harmonic `P`. -/
theorem polynomialLaplacian_mul_X (hL : polynomialLaplacian P = 0) (i : Fin 3) :
    polynomialLaplacian (P * X i) = 2 * pderiv i P := by
  rw [mul_comm, polynomialLaplacian_X_mul, hL, mul_zero, zero_add]

/-- The partial derivatives of a harmonic polynomial are harmonic. -/
theorem polynomialLaplacian_pderiv_eq_zero (hL : polynomialLaplacian P = 0) (i : Fin 3) :
    polynomialLaplacian (pderiv i P) = 0 := by
  rw [polynomialLaplacian_pderiv, hL, map_zero]

/-- The swirl components of a harmonic polynomial are harmonic. -/
theorem polynomialLaplacian_swirlPolynomial (hL : polynomialLaplacian P = 0) (i : Fin 3) :
    polynomialLaplacian (swirlPolynomial P i) = 0 := by
  simp only [swirlPolynomial]
  rw [show polynomialLaplacian (X (i + 1) * pderiv (i + 2) P - X (i + 2) * pderiv (i + 1) P) =
      polynomialLaplacian (X (i + 1) * pderiv (i + 2) P) -
        polynomialLaplacian (X (i + 2) * pderiv (i + 1) P) by
    simp only [polynomialLaplacian, map_sub, Finset.sum_sub_distrib]]
  rw [polynomialLaplacian_X_mul, polynomialLaplacian_X_mul,
    polynomialLaplacian_pderiv_eq_zero hL, polynomialLaplacian_pderiv_eq_zero hL,
    pderiv_comm (i + 1) (i + 2)]
  ring

/-- The divergence sum of `P x` is `(c + 3) P`. -/
theorem sum_pderiv_mul_X (hE : ∑ j, X j * pderiv j P = C c * P) :
    ∑ i, pderiv i (P * X i) = C (c + 3) * P := by
  simp only [Fin.sum_univ_three] at hE ⊢
  simp only [pderiv_mul, pderiv_X, Pi.single_apply, ite_true, mul_one, C_add]
  rw [show (C 3 : MvPolynomial (Fin 3) ℝ) = 3 from map_ofNat C 3]
  linear_combination hE

/-- The divergence sum of the swirl field vanishes. -/
theorem sum_pderiv_swirlPolynomial (P : MvPolynomial (Fin 3) ℝ) :
    ∑ i, pderiv i (swirlPolynomial P i) = 0 := by
  simp only [swirlPolynomial, Fin.sum_univ_three]
  simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl,
    show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl,
    show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl]
  simp only [map_sub, pderiv_mul, pderiv_X, Pi.single_apply]
  simp only [Fin.isValue, Fin.reduceEq, ite_false, zero_mul, zero_add]
  rw [pderiv_comm 0 1, pderiv_comm 0 2, pderiv_comm 1 2]
  ring

/-- The swirl field is orthogonal to the position: `x · (x × ∇P) = 0`. -/
theorem sum_X_mul_swirlPolynomial (P : MvPolynomial (Fin 3) ℝ) :
    ∑ i, X i * swirlPolynomial P i = 0 := by
  simp only [swirlPolynomial, Fin.sum_univ_three]
  simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl,
    show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl,
    show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl]
  ring

end Algebra

section Analysis

variable {F : ℝ → ℝ} {Q : MvPolynomial (Fin 3) ℝ} {c : ℝ}

/-- The coordinate derivative of `F(‖x‖²) Q(x)`. -/
theorem partialDeriv_radial_mul_eval (hF : Differentiable ℝ F) (j : Fin 3) (x : ℝ^3) :
    ∂[j] (fun y : ℝ^3 ↦ F (‖y‖ ^ 2) * eval y.ofLp Q) x =
      2 * x j * deriv F (‖x‖ ^ 2) * eval x.ofLp Q + F (‖x‖ ^ 2) * eval x.ofLp (pderiv j Q) := by
  rw [partialDeriv_comp_norm_sq_mul j (hF _)
    ((contDiff_eval_ofLp Q (k := 1)).differentiable one_ne_zero x), partialDeriv_eval_ofLp]

/-- The radial derivative `∑ⱼ xⱼ ∂ⱼ (F Q) = (2 ‖x‖² F' + c F) Q` for `∑ⱼ Xⱼ ∂ⱼ Q = c Q`. -/
theorem sum_partialDeriv_radial_mul_eval_mul (hF : Differentiable ℝ F)
    (hE : ∑ j, X j * pderiv j Q = C c * Q) (x : ℝ^3) :
    ∑ j, ∂[j] (fun y : ℝ^3 ↦ F (‖y‖ ^ 2) * eval y.ofLp Q) x * x j =
      (2 * ‖x‖ ^ 2 * deriv F (‖x‖ ^ 2) + c * F (‖x‖ ^ 2)) * eval x.ofLp Q := by
  have h := sum_mul_partialDeriv_comp_norm_sq_mul (q := fun y : ℝ^3 ↦ eval y.ofLp Q) (hF _)
    ((contDiff_eval_ofLp Q (k := 1)).differentiable one_ne_zero x)
  have hsum : ∑ j, x j * ∂[j] (fun y : ℝ^3 ↦ eval y.ofLp Q) x = c * eval x.ofLp Q := by
    have := congrArg (eval x.ofLp) hE
    simpa [map_sum, partialDeriv_eval_ofLp] using this
  rw [hsum] at h
  rw [show ∑ j, ∂[j] (fun y : ℝ^3 ↦ F (‖y‖ ^ 2) * eval y.ofLp Q) x * x j =
      ∑ j, x j * ∂[j] (fun y : ℝ^3 ↦ F (‖y‖ ^ 2) * eval y.ofLp Q) x from
    Finset.sum_congr rfl fun j _ ↦ mul_comm _ _, h]
  ring

/-- The Laplacian `Δ (F Q) = (4 ‖x‖² F'' + (4c + 6) F') Q + F ΔQ` for `∑ⱼ Xⱼ ∂ⱼ Q = c Q`. -/
theorem laplacian_radial_mul_eval (hF : ContDiff ℝ 2 F)
    (hE : ∑ j, X j * pderiv j Q = C c * Q) (x : ℝ^3) :
    laplacian (fun y : ℝ^3 ↦ F (‖y‖ ^ 2) * eval y.ofLp Q) x =
      (4 * ‖x‖ ^ 2 * deriv (deriv F) (‖x‖ ^ 2) + (4 * c + 6) * deriv F (‖x‖ ^ 2)) *
          eval x.ofLp Q + F (‖x‖ ^ 2) * eval x.ofLp (polynomialLaplacian Q) := by
  rw [laplacian_comp_norm_sq_mul hF.contDiffAt (contDiff_eval_ofLp Q).contDiffAt,
    laplacian_eval_ofLp]
  have hsum : ∑ j, x j * ∂[j] (fun y : ℝ^3 ↦ eval y.ofLp Q) x = c * eval x.ofLp Q := by
    have := congrArg (eval x.ofLp) hE
    simpa [map_sum, partialDeriv_eval_ofLp] using this
  rw [hsum, polynomialLaplacian]
  push_cast
  ring

end Analysis

end PDE.Fluid.Stokes.Ball
