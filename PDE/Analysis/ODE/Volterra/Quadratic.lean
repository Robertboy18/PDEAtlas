/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.Volterra
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Volterra contraction from a quadratic integral estimate

Parabolic response operators control squared distances by the time integral
of squared input distances. Iteration produces a factorial denominator, so
some iterate contracts on every finite interval. This gives a fixed point
without a smallness condition on the interval length or the coefficient bound.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.ODE

open Filter Function MeasureTheory Set
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E]
  {a b : ℝ}

/-- A quadratic Volterra estimate gains a factorial under iteration. -/
theorem dist_sq_iterate_apply_le_of_integral_dist_sq_le
    (hab : a ≤ b) (P : C(Icc a b, E) → C(Icc a b, E)) (K : ℝ≥0)
    (hP : ∀ u v (t : Icc a b), dist (P u t) (P v t) ^ 2 ≤
      (K : ℝ) * ∫ s in a..t.1,
        dist (u (projIcc a b hab s)) (v (projIcc a b hab s)) ^ 2)
    (u v : C(Icc a b, E)) (n : ℕ) (t : Icc a b) :
    dist ((P^[n]) u t) ((P^[n]) v t) ^ 2 ≤
      (((K : ℝ) * |t.1 - a|) ^ n / n.factorial) * dist u v ^ 2 := by
  induction n generalizing t with
  | zero =>
      simpa using pow_le_pow_left₀ (dist_nonneg) (ContinuousMap.dist_apply_le_dist t) 2
  | succ n hn =>
      rw [iterate_succ_apply', iterate_succ_apply']
      apply (hP _ _ t).trans
      calc
        _ ≤ (K : ℝ) * ∫ s in a..t.1,
            (((K : ℝ) * |s - a|) ^ n / n.factorial) * dist u v ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
          apply intervalIntegral.integral_mono_on t.2.1
            (Continuous.intervalIntegrable (by fun_prop) _ _)
            (Continuous.intervalIntegrable (by fun_prop) _ _)
          intro s hs
          have hs' : s ∈ Icc a b := ⟨hs.1, hs.2.trans t.2.2⟩
          simpa only [projIcc_of_mem hab hs'] using hn ⟨s, hs'⟩
        _ = (((K : ℝ) * |t.1 - a|) ^ (n + 1) / (n + 1).factorial) * dist u v ^ 2 := by
          have hf (s : ℝ) :
              (((K : ℝ) * |s - a|) ^ n / n.factorial) * dist u v ^ 2 =
                ((K : ℝ) ^ n / n.factorial * dist u v ^ 2) * |s - a| ^ n := by ring
          simp_rw [hf]
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le t.2.1,
            ← uIoc_of_le t.2.1, integral_pow_abs_sub_uIoc, Nat.factorial_succ, Nat.cast_mul,
            Nat.cast_add, Nat.cast_one]
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring

/-- The uniform distance of the iterates is controlled by the square root
of the factorial bound. -/
theorem dist_iterate_le_of_integral_dist_sq_le
    (hab : a ≤ b) (P : C(Icc a b, E) → C(Icc a b, E)) (K : ℝ≥0)
    (hP : ∀ u v (t : Icc a b), dist (P u t) (P v t) ^ 2 ≤
      (K : ℝ) * ∫ s in a..t.1,
        dist (u (projIcc a b hab s)) (v (projIcc a b hab s)) ^ 2)
    (u v : C(Icc a b, E)) (n : ℕ) :
    dist ((P^[n]) u) ((P^[n]) v) ≤
      Real.sqrt (((K : ℝ) * (b - a)) ^ n / n.factorial) * dist u v := by
  have hC : 0 ≤ (((K : ℝ) * (b - a)) ^ n / n.factorial) := by positivity
  rw [ContinuousMap.dist_le (by positivity)]
  intro t
  apply (sq_le_sq₀ dist_nonneg (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt hC]
  apply (dist_sq_iterate_apply_le_of_integral_dist_sq_le hab P K hP u v n t).trans
  gcongr
  rw [abs_of_nonneg (sub_nonneg.mpr t.2.1)]
  exact sub_le_sub_right t.2.2 a

/-- A quadratic causal bound gives a unique fixed point on every finite
closed interval in a Banach space. -/
theorem existsUnique_isFixedPt_of_integral_dist_sq_le [CompleteSpace E]
    (hab : a ≤ b) (P : C(Icc a b, E) → C(Icc a b, E)) (K : ℝ≥0)
    (hP : ∀ u v (t : Icc a b), dist (P u t) (P v t) ^ 2 ≤
      (K : ℝ) * ∫ s in a..t.1,
        dist (u (projIcc a b hab s)) (v (projIcc a b hab s)) ^ 2) :
    ∃! u : C(Icc a b, E), IsFixedPt P u := by
  obtain ⟨n, hn⟩ :=
    FloorSemiring.tendsto_pow_div_factorial_atTop ((K : ℝ) * (b - a))
      |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have hnonneg : 0 ≤ (((K : ℝ) * (b - a)) ^ n / n.factorial) := by positivity
  let C : ℝ≥0 := ⟨Real.sqrt (((K : ℝ) * (b - a)) ^ n / n.factorial), Real.sqrt_nonneg _⟩
  have hC : (C : ℝ) < 1 := by
    have hs := Real.sq_sqrt hnonneg
    have hp := Real.sqrt_nonneg (((K : ℝ) * (b - a)) ^ n / n.factorial)
    change Real.sqrt (((K : ℝ) * (b - a)) ^ n / n.factorial) < 1
    nlinarith
  have hPn : ContractingWith C (P^[n]) := ⟨hC, LipschitzWith.of_dist_le_mul fun u v ↦
    dist_iterate_le_of_integral_dist_sq_le hab P K hP u v n⟩
  let u := ContractingWith.fixedPoint (P^[n]) hPn
  have hu : IsFixedPt P u := hPn.isFixedPt_fixedPoint_iterate
  refine ⟨u, hu, ?_⟩
  intro v hv
  exact hPn.fixedPoint_unique' (hv.iterate n) hPn.fixedPoint_isFixedPt

end PDE.Analysis.ODE
