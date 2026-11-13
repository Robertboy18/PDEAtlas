/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.Polynomial.NestedCoefficientList
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Derivatives of a polynomial times a real power of a polynomial

For coefficient lists `N` and `D` and a rational exponent `a`, the `k`-th derivative of
`x ↦ N(x) D(x) ^ a` is `N_k(x) D(x) ^ (a - k)` wherever `D > 0`, where `N_0 = N` and
`N_{k+1} = N_k' D + (a - k) N_k D'`. The numerators are computable coefficient lists, so explicit
functions such as `1 / (1 + x ^ 4)`, `x ^ 7 / (1 + x ^ 2) ^ (7 / 2)` or `1 / (2 + 2 y + y ^ 2)`
get their derivative formulas of every order from this one theorem, never from symbolic output.

## Main definitions

* `powerDerivNumerator`: the numerators `N_k` of the derivatives of `N D ^ a`.

## Main results

* `hasDerivAt_coeffEval_mul_rpow`: one derivative of `M D ^ b` where `D > 0`.
* `iteratedDeriv_coeffEval_mul_rpow`: the `k`-th derivative of `N D ^ a` is `N_k D ^ (a - k)` on
  an open set where `D > 0`.
* `iteratedDeriv_coeffEval_mul_rpow_of_pos`: the same on the whole line when `D` is positive
  everywhere.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open CAS.Polynomial
open scoped Topology

/-- The numerator of the `k`-th derivative of `N D ^ a`: `N_0 = N` and
`N_{k+1} = N_k' D + (a - k) N_k D'`, without trailing zeros. -/
def powerDerivNumerator (N D : List ℚ) (a : ℚ) : ℕ → List ℚ
  | 0 => N
  | k + 1 => coeffTrim (coeffAdd (coeffMul (coeffDeriv (powerDerivNumerator N D a k)) D)
      (coeffScale (a - k) (coeffMul (powerDerivNumerator N D a k) (coeffDeriv D))))

/-- One derivative of `M D ^ b` where `D > 0`. -/
theorem hasDerivAt_coeffEval_mul_rpow (M D : List ℚ) (b : ℝ) {x : ℝ}
    (hD : 0 < coeffEval D x) :
    HasDerivAt (fun y ↦ coeffEval M y * coeffEval D y ^ b)
      ((coeffEval (coeffDeriv M) x * coeffEval D x +
          b * coeffEval M x * coeffEval (coeffDeriv D) x) * coeffEval D x ^ (b - 1)) x := by
  have hM := hasDerivAt_coeffEval M x
  have hP := (hasDerivAt_coeffEval D x).rpow_const (p := b) (Or.inl hD.ne')
  convert hM.mul hP using 1
  rw [Real.rpow_sub_one hD.ne']
  field_simp

/-- The `k`-th derivative of `N D ^ a` on an open set where `D > 0`. -/
theorem iteratedDeriv_coeffEval_mul_rpow (N D : List ℚ) (a : ℚ) {U : Set ℝ} (hU : IsOpen U)
    (hD : ∀ x ∈ U, 0 < coeffEval D x) (k : ℕ) {x : ℝ} (hx : x ∈ U) :
    iteratedDeriv k (fun y ↦ coeffEval N y * coeffEval D y ^ (a : ℝ)) x =
      coeffEval (powerDerivNumerator N D a k) x * coeffEval D x ^ ((a : ℝ) - k) := by
  induction k generalizing x with
  | zero => simp [powerDerivNumerator]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv k (fun y ↦ coeffEval N y * coeffEval D y ^ (a : ℝ)) =ᶠ[𝓝 x]
        fun y ↦ coeffEval (powerDerivNumerator N D a k) y * coeffEval D y ^ ((a : ℝ) - k) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact ih hy
    rw [heq.deriv_eq, (hasDerivAt_coeffEval_mul_rpow _ D _ (hD x hx)).deriv]
    simp only [powerDerivNumerator, coeffEval_coeffTrim, coeffEval_coeffAdd, coeffEval_coeffMul,
      coeffEval_coeffScale]
    push_cast
    ring_nf

/-- The derivatives of `N D ^ a` on the whole line when `D` is positive everywhere. -/
theorem iteratedDeriv_coeffEval_mul_rpow_of_pos (N D : List ℚ) (a : ℚ)
    (hD : ∀ x, 0 < coeffEval D x) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun y ↦ coeffEval N y * coeffEval D y ^ (a : ℝ)) x =
      coeffEval (powerDerivNumerator N D a k) x * coeffEval D x ^ ((a : ℝ) - k) :=
  iteratedDeriv_coeffEval_mul_rpow N D a isOpen_univ (fun x _ ↦ hD x) k (Set.mem_univ x)

end PDE.Analysis
