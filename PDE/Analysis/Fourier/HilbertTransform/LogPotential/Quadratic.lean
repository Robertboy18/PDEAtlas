/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.Analysis.Fourier.HilbertTransform.LogPotential.Polynomial
import CAS.ExactTactic

/-!
# Differentiating quadratic log panels

An endpoint formula can be differentiated whenever the evaluation point differs from
the two endpoints. The point may lie inside the panel: the formula already includes the
integrable logarithmic singularity. Boundary terms are retained for later telescoping.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Polynomial

namespace PDE.Analysis

open CAS.Analysis

/-- The endpoint primitive for a quadratic expressed in physical coordinates. -/
def quadraticLogEndpoint (c₀ c₁ c₂ t x : ℝ) : ℝ :=
  (c₀ + c₁ * x + c₂ * x ^ 2) * logMonomialPrimitive 0 (t - x) +
    (c₁ + 2 * c₂ * x) * logMonomialPrimitive 1 (t - x) +
    c₂ * logMonomialPrimitive 2 (t - x)

/-- Translation to the singularity gives three integrable monomial-log terms. -/
theorem integral_quadratic_mul_log (c₀ c₁ c₂ a b x : ℝ) :
    (∫ y in a..b, (c₀ + c₁ * y + c₂ * y ^ 2) * Real.log (x - y)) =
      quadraticLogEndpoint c₀ c₁ c₂ b x - quadraticLogEndpoint c₀ c₁ c₂ a x := by
  have heq (y : ℝ) :
      (c₀ + c₁ * y + c₂ * y ^ 2) * Real.log (x - y) =
        (c₀ + c₁ * x + c₂ * x ^ 2) * ((y - x) ^ 0 * Real.log (y - x)) +
          (c₁ + 2 * c₂ * x) * ((y - x) ^ 1 * Real.log (y - x)) +
          c₂ * ((y - x) ^ 2 * Real.log (y - x)) := by
    rw [← Real.log_neg_eq_log (x - y), neg_sub]
    cas
  simp_rw [heq]
  rw [intervalIntegral.integral_comp_sub_right
    (f := fun t ↦ (c₀ + c₁ * x + c₂ * x ^ 2) * (t ^ 0 * Real.log t) +
      (c₁ + 2 * c₂ * x) * (t ^ 1 * Real.log t) + c₂ * (t ^ 2 * Real.log t))]
  have h (n : ℕ) (c : ℝ) :=
    (intervalIntegrable_pow_mul_log n (a - x) (b - x)).const_mul c
  rw [intervalIntegral.integral_add ((h 0 _).add (h 1 _)) (h 2 _),
    intervalIntegral.integral_add (h 0 _) (h 1 _)]
  simp only [intervalIntegral.integral_const_mul, integral_pow_mul_log]
  unfold quadraticLogEndpoint
  ring

/-- Every polynomial of degree at most two has the corresponding endpoint expression. -/
theorem polynomialLogPanel_eq_quadratic (p : ℝ[X]) (hp : p.natDegree ≤ 2)
    (a b x : ℝ) :
    polynomialLogPanel p a b x =
      quadraticLogEndpoint (p.coeff 0) (p.coeff 1) (p.coeff 2) b x -
        quadraticLogEndpoint (p.coeff 0) (p.coeff 1) (p.coeff 2) a x := by
  rw [← integral_polynomial_mul_log_sub]
  have heval (y : ℝ) :
      p.eval y = p.coeff 0 + p.coeff 1 * y + p.coeff 2 * y ^ 2 := by
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, pow_one, mul_one] using p.eval_eq_sum_range' (by omega : p.natDegree < 3) y
  simp_rw [heval]
  exact integral_quadratic_mul_log _ _ _ _ _ _

/-- Differentiation keeps the endpoint value multiplying the logarithm. -/
theorem hasDerivAt_quadraticLogEndpoint (c₀ c₁ c₂ t x : ℝ) (hx : t - x ≠ 0) :
    HasDerivAt (quadraticLogEndpoint c₀ c₁ c₂ t)
      ((c₁ + 2 * c₂ * x) * logMonomialPrimitive 0 (t - x) +
        2 * c₂ * logMonomialPrimitive 1 (t - x) -
        (c₀ + c₁ * t + c₂ * t ^ 2) * Real.log (t - x)) x := by
  have hsub : HasDerivAt (fun z : ℝ ↦ t - z) (-1) x := by cas
  have h₀ := (hasDerivAt_logMonomialPrimitive 0 hx).comp x hsub
  have h₁ := (hasDerivAt_logMonomialPrimitive 1 hx).comp x hsub
  have h₂ := (hasDerivAt_logMonomialPrimitive 2 hx).comp x hsub
  have ha : HasDerivAt (fun z : ℝ ↦ c₀ + c₁ * z + c₂ * z ^ 2)
      (c₁ + 2 * c₂ * x) x := by cas
  have hb : HasDerivAt (fun z : ℝ ↦ c₁ + 2 * c₂ * z) (2 * c₂) x := by cas
  convert ((ha.mul h₀).add (hb.mul h₁)).add (h₂.const_mul c₂) using 1
  · rfl
  · simp only [pow_zero, pow_one, one_mul]
    cas

/-- The quadratic panel primitive is continuous even when its evaluation
point crosses a panel endpoint. -/
theorem continuous_polynomialLogPanel (p : Polynomial ℝ) (hp : p.natDegree ≤ 2)
    (a b : ℝ) : Continuous (polynomialLogPanel p a b) := by
  have h (t : ℝ) : Continuous (quadraticLogEndpoint (p.coeff 0) (p.coeff 1) (p.coeff 2) t) := by
    unfold quadraticLogEndpoint
    have hlog (n : ℕ) : Continuous (fun x : ℝ ↦ logMonomialPrimitive n (t - x)) :=
      (continuous_logMonomialPrimitive n).comp (continuous_const.sub continuous_id)
    fun_prop
  have he : polynomialLogPanel p a b = fun x ↦
      quadraticLogEndpoint (p.coeff 0) (p.coeff 1) (p.coeff 2) b x -
        quadraticLogEndpoint (p.coeff 0) (p.coeff 1) (p.coeff 2) a x :=
    funext (polynomialLogPanel_eq_quadratic p hp a b)
  rw [he]
  exact (h b).sub (h a)

/-- The derivative of a quadratic log panel includes both boundary logarithms.
Only the endpoints are excluded; an interior logarithmic singularity is permitted. -/
theorem hasDerivAt_polynomialLogPanel (p : ℝ[X]) (hp : p.natDegree ≤ 2)
    (a b x : ℝ) (ha : x ≠ a) (hb : x ≠ b) :
    HasDerivAt (polynomialLogPanel p a b)
      (polynomialLogPanel p.derivative a b x +
        p.eval a * Real.log (x - a) - p.eval b * Real.log (x - b)) x := by
  have hfun : polynomialLogPanel p a b =
      fun z ↦ quadraticLogEndpoint (p.coeff 0) (p.coeff 1) (p.coeff 2) b z -
        quadraticLogEndpoint (p.coeff 0) (p.coeff 1) (p.coeff 2) a z :=
    funext (polynomialLogPanel_eq_quadratic p hp a b)
  rw [hfun]
  have h := (hasDerivAt_quadraticLogEndpoint (p.coeff 0) (p.coeff 1) (p.coeff 2)
    b x (sub_ne_zero.mpr hb.symm)).sub
    (hasDerivAt_quadraticLogEndpoint (p.coeff 0) (p.coeff 1) (p.coeff 2)
      a x (sub_ne_zero.mpr ha.symm))
  convert h using 1
  have hp' : p.derivative.natDegree ≤ 2 :=
    p.natDegree_derivative_le.trans (by omega)
  rw [polynomialLogPanel_eq_quadratic p.derivative hp' a b x]
  have hp3 : p.coeff 3 = 0 := p.coeff_eq_zero_of_natDegree_lt (by omega)
  have heval (y : ℝ) :
      p.eval y = p.coeff 0 + p.coeff 1 * y + p.coeff 2 * y ^ 2 := by
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, pow_one, mul_one] using p.eval_eq_sum_range' (by omega : p.natDegree < 3) y
  simp only [Polynomial.coeff_derivative, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one,
    hp3, zero_mul, quadraticLogEndpoint, zero_add, add_zero, heval]
  rw [← Real.log_neg_eq_log (a - x), ← Real.log_neg_eq_log (b - x), neg_sub, neg_sub]
  cas

end PDE.Analysis
