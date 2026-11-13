/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.Analysis.SpecialFunctions.Legendre.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Orthogonality of the Legendre polynomials

The Legendre equation `((1 - x²) P_n')' = -n (n + 1) P_n` puts the Wronskian-type product
`(1 - x²) (P_l' P_m - P_m' P_l)` in divergence form, and the weight `1 - x²` vanishes at
`x = ±1`, so distinct Legendre polynomials are orthogonal on `[-1, 1]`. Since `P_0, …, P_{n-1}`
span the polynomials of degree less than `n`, `P_n` is orthogonal to all of them.

The norm follows from one integration by parts. The polynomial `x P_n' - n P_n` has degree
less than `n`, so `∫ x P_n P_n' = n ∫ P_n²`, while `(x P_n²)' = P_n² + 2 x P_n P_n'` and
`P_n (±1)² = 1` give `∫ P_n² + 2 ∫ x P_n P_n' = 2`. Hence `∫ P_n² = 2 / (2n + 1)`. With the
equation once more, `∫ (1 - x²) P_l' P_m' = l (l + 1) ∫ P_l P_m`.

The same divergence form shows that any polynomial solution `Q` of the Legendre equation with
eigenvalue `n (n + 1)` is orthogonal to every `P_m`, `m ≠ n`; expanding `Q` in the Legendre
polynomials then gives `Q = Q (1) · P_n`.

The substitution `x = cos θ` carries these integrals to `(0, π)` with the weight `sin θ`.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.SpecialFunctions

open CAS.Analysis.SpecialFunctions
open Polynomial intervalIntegral

/-- The integral over `[-1, 1]` of the derivative of a polynomial is the difference of its
endpoint values. -/
theorem integral_derivative_eval (p : ℝ[X]) :
    ∫ x in (-1 : ℝ)..1, (derivative p).eval x = p.eval 1 - p.eval (-1) :=
  integral_eq_sub_of_hasDerivAt (fun x _ ↦ p.hasDerivAt x)
    (p.derivative.continuous.intervalIntegrable _ _)

/-- The integral over `[-1, 1]` of a product of polynomials is additive in the second factor. -/
theorem integral_eval_mul_add (p q r : ℝ[X]) :
    ∫ x in (-1 : ℝ)..1, p.eval x * (q + r).eval x =
      (∫ x in (-1 : ℝ)..1, p.eval x * q.eval x) + ∫ x in (-1 : ℝ)..1, p.eval x * r.eval x := by
  simp only [eval_add, mul_add]
  exact integral_add ((p.continuous.mul q.continuous).intervalIntegrable _ _)
    ((p.continuous.mul r.continuous).intervalIntegrable _ _)

/-- Polynomial solutions of Legendre equations `((1 - x²) A')' = -a A` and
`((1 - x²) B')' = -b B` with `a ≠ b` are orthogonal on `[-1, 1]`. -/
theorem integral_mul_eq_zero_of_legendre_equation {A B : ℝ[X]} {a b : ℝ}
    (hA : derivative ((1 - X ^ 2) * derivative A) = -C a * A)
    (hB : derivative ((1 - X ^ 2) * derivative B) = -C b * B) (hab : a ≠ b) :
    ∫ x in (-1 : ℝ)..1, A.eval x * B.eval x = 0 := by
  have hW : derivative ((1 - X ^ 2) * derivative A * B - (1 - X ^ 2) * derivative B * A) =
      C (b - a) * (A * B) := by
    rw [derivative_sub, derivative_mul (f := (1 - X ^ 2) * derivative A),
      derivative_mul (f := (1 - X ^ 2) * derivative B), hA, hB, C_sub]
    ring
  have hint := integral_derivative_eval ((1 - X ^ 2) * derivative A * B -
      (1 - X ^ 2) * derivative B * A)
  rw [hW] at hint
  simp only [eval_mul, eval_C, eval_sub, eval_one, eval_pow, eval_X, integral_const_mul] at hint
  norm_num at hint
  exact hint.resolve_left (sub_ne_zero.mpr hab.symm)

/-- Distinct degrees give distinct Legendre eigenvalues `n (n + 1)`. -/
theorem natCast_mul_add_one_ne {l m : ℕ} (hlm : l ≠ m) :
    (l : ℝ) * (l + 1) ≠ m * (m + 1) := by
  intro h
  have h' : ((l : ℝ) - m) * (l + m + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h'' | h''
  · exact hlm (by exact_mod_cast sub_eq_zero.mp h'')
  · have : (0 : ℝ) < l + m + 1 := by positivity
    linarith

/-- Distinct Legendre polynomials are orthogonal on `[-1, 1]`. -/
theorem integral_legendre_mul_legendre_of_ne {l m : ℕ} (hlm : l ≠ m) :
    ∫ x in (-1 : ℝ)..1, (legendre l).eval x * (legendre m).eval x = 0 :=
  integral_mul_eq_zero_of_legendre_equation (legendre_equation l) (legendre_equation m)
    (natCast_mul_add_one_ne hlm)

/-- The Legendre polynomial `P_n` is orthogonal on `[-1, 1]` to every polynomial of degree less
than `n`. -/
theorem integral_legendre_mul_eq_zero_of_degree_lt {n : ℕ} {q : ℝ[X]} (hq : q.degree < n) :
    ∫ x in (-1 : ℝ)..1, (legendre n).eval x * q.eval x = 0 := by
  have hspan := mem_span_legendre_of_degree_lt hq
  clear hq
  induction hspan using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨m, hm, rfl⟩ := hr
    exact integral_legendre_mul_legendre_of_ne (ne_of_gt (Set.mem_Iio.mp hm))
  | zero => simp
  | add r s _ _ hr hs => rw [integral_eval_mul_add, hr, hs, add_zero]
  | smul c r _ hr =>
    simp only [eval_smul, smul_eq_mul, mul_left_comm _ c, integral_const_mul, hr, mul_zero]

/-- The polynomial `x P_n' - n P_n` has degree less than `n`. -/
theorem degree_X_mul_derivative_legendre_sub_lt (n : ℕ) :
    (X * derivative (legendre n) - C (n : ℝ) * legendre n).degree < (n : WithBot ℕ) := by
  rw [degree_lt_iff_coeff_zero]
  intro k hk
  rw [coeff_sub, coeff_X_mul_derivative, coeff_C_mul]
  rcases hk.lt_or_eq with hk | rfl
  · rw [coeff_eq_zero_of_natDegree_lt (by simpa using hk)]
    ring
  · ring

/-- The squared norm of the Legendre polynomial on `[-1, 1]` is `2 / (2n + 1)`. -/
theorem integral_legendre_mul_self (n : ℕ) :
    ∫ x in (-1 : ℝ)..1, (legendre n).eval x * (legendre n).eval x = 2 / (2 * n + 1) := by
  set P := legendre n with hP
  set r := X * derivative P - C (n : ℝ) * P with hr
  have hparts : ∫ x in (-1 : ℝ)..1, (derivative (X * (P * P))).eval x = 2 := by
    rw [integral_derivative_eval]
    simp only [eval_mul, eval_X, hP, legendre_eval_one, legendre_eval_neg_one]
    rw [← mul_pow, show ((-1 : ℝ) * -1) = 1 by norm_num, one_pow]
    norm_num
  have hpoint (x : ℝ) : (derivative (X * (P * P))).eval x =
      (2 * n + 1) * (P.eval x * P.eval x) + 2 * (P.eval x * r.eval x) := by
    rw [derivative_mul, derivative_mul, derivative_X, hr]
    simp only [eval_add, eval_mul, eval_one, eval_X, eval_sub, eval_C]
    ring
  simp only [hpoint] at hparts
  rw [integral_add ((by fun_prop : Continuous fun x ↦
        (2 * (n : ℝ) + 1) * (P.eval x * P.eval x)).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun x ↦ 2 * (P.eval x * r.eval x)).intervalIntegrable _ _),
    integral_const_mul, integral_const_mul, integral_legendre_mul_eq_zero_of_degree_lt
      (degree_X_mul_derivative_legendre_sub_lt n), mul_zero, add_zero] at hparts
  rw [eq_div_iff (by positivity), mul_comm]
  exact hparts

/-- The derivatives of the Legendre polynomials are orthogonal on `[-1, 1]` for the weight
`1 - x²`: `∫ (1 - x²) P_l' P_m' = l (l + 1) ∫ P_l P_m`. -/
theorem integral_one_sub_sq_mul_derivative_legendre (l m : ℕ) :
    ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) * (derivative (legendre l)).eval x *
        (derivative (legendre m)).eval x =
      l * (l + 1) * ∫ x in (-1 : ℝ)..1, (legendre l).eval x * (legendre m).eval x := by
  have hparts := integral_derivative_eval ((1 - X ^ 2) * derivative (legendre l) * legendre m)
  have hpoint (x : ℝ) :
      (derivative ((1 - X ^ 2) * derivative (legendre l) * legendre m)).eval x =
        (1 - x ^ 2) * (derivative (legendre l)).eval x * (derivative (legendre m)).eval x -
          l * (l + 1) * ((legendre l).eval x * (legendre m).eval x) := by
    rw [derivative_mul (f := (1 - X ^ 2) * derivative (legendre l)), legendre_equation]
    simp only [eval_add, eval_mul, eval_neg, eval_C, eval_sub, eval_one, eval_pow, eval_X]
    ring
  simp only [hpoint, eval_mul, eval_sub, eval_one, eval_pow, eval_X] at hparts
  rw [integral_sub ((by fun_prop : Continuous fun x ↦ (1 - x ^ 2) *
        (derivative (legendre l)).eval x * (derivative (legendre m)).eval x).intervalIntegrable
        _ _)
      ((by fun_prop : Continuous fun x ↦ (l : ℝ) * (l + 1) *
        ((legendre l).eval x * (legendre m).eval x)).intervalIntegrable _ _),
    integral_const_mul] at hparts
  norm_num at hparts
  linarith

/-- The Legendre polynomials are orthogonal on `[-1, 1]` with squared norms `2 / (2l + 1)`. -/
theorem integral_legendre_mul_legendre (l m : ℕ) :
    ∫ x in (-1 : ℝ)..1, (legendre l).eval x * (legendre m).eval x =
      if l = m then 2 / (2 * (l : ℝ) + 1) else 0 := by
  split_ifs with h
  · subst h
    exact integral_legendre_mul_self l
  · exact integral_legendre_mul_legendre_of_ne h

/-- The derivatives of the Legendre polynomials are orthogonal on `[-1, 1]` for the weight
`1 - x²`, with squared norms `2 l (l + 1) / (2l + 1)`. -/
theorem integral_one_sub_sq_mul_derivative_legendre_mul (l m : ℕ) :
    ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) * (derivative (legendre l)).eval x *
        (derivative (legendre m)).eval x =
      if l = m then 2 * (l : ℝ) * (l + 1) / (2 * l + 1) else 0 := by
  rw [integral_one_sub_sq_mul_derivative_legendre, integral_legendre_mul_legendre]
  split_ifs
  · ring
  · ring

/-- The substitution `x = cos θ`: for continuous `g`,
`∫_0^π g (cos θ) sin θ dθ = ∫_{-1}^1 g (x) dx`. -/
theorem integral_comp_cos_mul_sin {g : ℝ → ℝ} (hg : Continuous g) :
    ∫ θ in (0 : ℝ)..Real.pi, g (Real.cos θ) * Real.sin θ = ∫ x in (-1 : ℝ)..1, g x := by
  have h := integral_comp_mul_deriv (a := 0) (b := Real.pi) (f := Real.cos)
    (f' := fun θ ↦ -Real.sin θ) (fun θ _ ↦ Real.hasDerivAt_cos θ)
    (Real.continuous_sin.neg.continuousOn) hg
  simp only [Function.comp_def, mul_neg, intervalIntegral.integral_neg, Real.cos_zero,
    Real.cos_pi] at h
  rw [integral_symm (-1) 1] at h
  linarith

/-- A polynomial solution of the Legendre equation `((1 - x²) Q')' = -n (n + 1) Q` is the
multiple `Q (1) · P_n` of the Legendre polynomial. -/
theorem eq_C_mul_legendre_of_legendre_equation {Q : ℝ[X]} {n : ℕ}
    (hQ : derivative ((1 - X ^ 2) * derivative Q) = -C ((n : ℝ) * (n + 1)) * Q) :
    Q = C (Q.eval 1) * legendre n := by
  have hmem : Q ∈ Submodule.span ℝ (Set.range legendre) := span_legendre ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hmem
  have hsum : Q = ∑ i ∈ c.support, c i • legendre i := hc.symm
  have hmoment (m : ℕ) : ∫ x in (-1 : ℝ)..1, Q.eval x * (legendre m).eval x =
      c m * (2 / (2 * (m : ℝ) + 1)) := by
    rw [hsum]
    simp only [eval_finsetSum, eval_smul, smul_eq_mul, Finset.sum_mul]
    rw [intervalIntegral.integral_finsetSum fun i _ ↦
      (by fun_prop : Continuous fun x ↦ c i * (legendre i).eval x * (legendre m).eval x
        ).intervalIntegrable _ _]
    simp only [mul_assoc, integral_const_mul, integral_legendre_mul_legendre, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq']
    split_ifs with hm
    · rfl
    · rw [Finsupp.notMem_support_iff.mp hm, zero_mul]
  have hzero (m : ℕ) (hm : m ≠ n) : c m = 0 := by
    have h := hmoment m
    rw [integral_mul_eq_zero_of_legendre_equation hQ (legendre_equation m)
      (natCast_mul_add_one_ne hm.symm)] at h
    have hpos : (0 : ℝ) < 2 / (2 * (m : ℝ) + 1) := by positivity
    exact (mul_eq_zero.mp h.symm).resolve_right hpos.ne'
  have hQn : Q = c n • legendre n := by
    rw [hsum, Finset.sum_eq_single n (fun m _ hm ↦ by rw [hzero m hm, zero_smul])
      (fun hn ↦ by rw [Finsupp.notMem_support_iff.mp hn, zero_smul])]
  have h1 : Q.eval 1 = c n := by
    rw [hQn, eval_smul, legendre_eval_one, smul_eq_mul, mul_one]
  rw [h1, ← smul_eq_C_mul]
  exact hQn

/-- A polynomial solving `(1 - x²) Q'' - 2x Q' + n (n + 1) Q = 0` at every real argument is the
multiple `Q (1) · P_n` of the Legendre polynomial. -/
theorem eq_C_mul_legendre_of_legendre_equation_eval {Q : ℝ[X]} {n : ℕ}
    (h : ∀ x : ℝ, (1 - x ^ 2) * Q.derivative.derivative.eval x - 2 * x * Q.derivative.eval x +
      n * (n + 1) * Q.eval x = 0) :
    Q = C (Q.eval 1) * legendre n :=
  eq_C_mul_legendre_of_legendre_equation (derivative_one_sub_sq_mul_derivative_of_eval h)

end PDE.Analysis.SpecialFunctions
