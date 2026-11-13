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
# Volterra contraction from an integral estimate

An operator on continuous curves over `[a, b]` whose output distance at time `t` is at most `K`
times the time integral of the input distances over `[a, t]` gains a factorial under iteration, so
some iterate contracts. This gives a unique fixed point on every finite closed interval without a
smallness condition on the interval or on `K`. Linear and nonlinear Volterra equations of the
second kind `u(t) = f(t) + ∫ₐᵗ k(t, s, u(s)) ds` with kernels Lipschitz in `u` and bounded in
`(t, s)`, convolution or not, satisfy the estimate, as do kernels multiplied by a bounded function
of the outer time `t`; the operator must in addition map continuous curves to continuous curves,
which bounded kernels alone do not give (`k(t, s, u) = 1` for `t ≥ 1/2` and `0` before makes the
integral jump). Integration from the left endpoint with a pointwise Lipschitz integrand
(`existsUnique_isFixedPt_volterra` with `t₀ = a`) satisfies the estimate.

## Main results

* `dist_iterate_apply_le_of_dist_le_integral_dist`: an integral Volterra estimate gains
  `(K |t - a|)ⁿ / n!` under `n` iterations.
* `existsUnique_isFixedPt_of_dist_le_integral_dist`: an operator on `C([a, b], E)`, `E` complete,
  with the integral Volterra estimate has exactly one fixed point.
* `exists_continuousOn_eq_of_dist_le_integral_dist`: an operator on functions `ℝ → E` that keeps
  continuity on `[a, b]` and satisfies the estimate there has a solution of `u = F u` on `[a, b]`.
* `eqOn_of_dist_le_integral_dist`: two solutions of `u = F u` continuous on `[a, b]` agree there.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.ODE

open Filter Function MeasureTheory Set
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] {a b : ℝ}

/-- **The factorial bound.** An integral Volterra estimate gains `(K |t - a|)ⁿ / n!` under `n`
iterations. -/
theorem dist_iterate_apply_le_of_dist_le_integral_dist
    (hab : a ≤ b) (P : C(Icc a b, E) → C(Icc a b, E)) (K : ℝ≥0)
    (hP : ∀ u v (t : Icc a b), dist (P u t) (P v t) ≤
      (K : ℝ) * ∫ s in a..t.1, dist (u (projIcc a b hab s)) (v (projIcc a b hab s)))
    (u v : C(Icc a b, E)) (n : ℕ) (t : Icc a b) :
    dist ((P^[n]) u t) ((P^[n]) v t) ≤
      (((K : ℝ) * |t.1 - a|) ^ n / n.factorial) * dist u v := by
  induction n generalizing t with
  | zero => simpa using ContinuousMap.dist_apply_le_dist t
  | succ n hn =>
      rw [iterate_succ_apply', iterate_succ_apply']
      apply (hP _ _ t).trans
      calc
        _ ≤ (K : ℝ) * ∫ s in a..t.1,
            (((K : ℝ) * |s - a|) ^ n / n.factorial) * dist u v := by
          apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
          have hc : Continuous fun s ↦ dist (((P^[n]) u) (projIcc a b hab s))
              (((P^[n]) v) (projIcc a b hab s)) :=
            (((P^[n]) u).continuous.comp continuous_projIcc).dist
              (((P^[n]) v).continuous.comp continuous_projIcc)
          apply intervalIntegral.integral_mono_on t.2.1 (hc.intervalIntegrable _ _)
            (Continuous.intervalIntegrable (by fun_prop) _ _)
          intro s hs
          have hs' : s ∈ Icc a b := ⟨hs.1, hs.2.trans t.2.2⟩
          simpa only [projIcc_of_mem hab hs'] using hn ⟨s, hs'⟩
        _ = (((K : ℝ) * |t.1 - a|) ^ (n + 1) / (n + 1).factorial) * dist u v := by
          have hf (s : ℝ) :
              (((K : ℝ) * |s - a|) ^ n / n.factorial) * dist u v =
                ((K : ℝ) ^ n / n.factorial * dist u v) * |s - a| ^ n := by ring
          simp_rw [hf]
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le t.2.1,
            ← uIoc_of_le t.2.1, integral_pow_abs_sub_uIoc, Nat.factorial_succ, Nat.cast_mul,
            Nat.cast_add, Nat.cast_one]
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring

/-- **A unique fixed point.** An operator on `C([a, b], E)`, `E` complete, with the integral
Volterra estimate has exactly one fixed point. -/
theorem existsUnique_isFixedPt_of_dist_le_integral_dist [CompleteSpace E]
    (hab : a ≤ b) (P : C(Icc a b, E) → C(Icc a b, E)) (K : ℝ≥0)
    (hP : ∀ u v (t : Icc a b), dist (P u t) (P v t) ≤
      (K : ℝ) * ∫ s in a..t.1, dist (u (projIcc a b hab s)) (v (projIcc a b hab s))) :
    ∃! u : C(Icc a b, E), IsFixedPt P u := by
  obtain ⟨n, hn⟩ :=
    FloorSemiring.tendsto_pow_div_factorial_atTop ((K : ℝ) * (b - a))
      |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have hnonneg : 0 ≤ (((K : ℝ) * (b - a)) ^ n / n.factorial) := by
    have : 0 ≤ b - a := sub_nonneg.2 hab
    positivity
  let C : ℝ≥0 := ⟨((K : ℝ) * (b - a)) ^ n / n.factorial, hnonneg⟩
  have hPn : ContractingWith C (P^[n]) := by
    refine ⟨hn, LipschitzWith.of_dist_le_mul fun u v ↦ ?_⟩
    change dist _ _ ≤ ((K : ℝ) * (b - a)) ^ n / n.factorial * dist u v
    rw [ContinuousMap.dist_le (mul_nonneg hnonneg dist_nonneg)]
    intro t
    refine (dist_iterate_apply_le_of_dist_le_integral_dist hab P K hP u v n t).trans ?_
    gcongr
    rw [abs_of_nonneg (sub_nonneg.2 t.2.1)]
    exact sub_le_sub_right t.2.2 a
  refine ⟨ContractingWith.fixedPoint (P^[n]) hPn, hPn.isFixedPt_fixedPoint_iterate, ?_⟩
  intro v hv
  exact hPn.fixedPoint_unique' (hv.iterate n) hPn.fixedPoint_isFixedPt

/-- **Existence for functions on `ℝ`.** An operator `F` on functions `ℝ → E` that keeps
continuity on `[a, b]` and satisfies `dist (F u t) (F v t) ≤ K ∫ₐᵗ dist (u s) (v s) ds` on `[a, b]`
for inputs continuous there has a solution of `u = F u` on `[a, b]` continuous there. -/
theorem exists_continuousOn_eq_of_dist_le_integral_dist [CompleteSpace E] (hab : a ≤ b)
    (F : (ℝ → E) → ℝ → E) (K : ℝ≥0)
    (hF : ∀ u, ContinuousOn u (Icc a b) → ContinuousOn (F u) (Icc a b))
    (hFK : ∀ u v, ContinuousOn u (Icc a b) → ContinuousOn v (Icc a b) → ∀ t ∈ Icc a b,
      dist (F u t) (F v t) ≤ (K : ℝ) * ∫ s in a..t, dist (u s) (v s)) :
    ∃ u : ℝ → E, ContinuousOn u (Icc a b) ∧ ∀ t ∈ Icc a b, u t = F u t := by
  have hcomp : ∀ w : C(Icc a b, E), ContinuousOn (fun s ↦ w (projIcc a b hab s)) (Icc a b) :=
    fun w ↦ (w.continuous.comp continuous_projIcc).continuousOn
  let P : C(Icc a b, E) → C(Icc a b, E) := fun w ↦
    ⟨fun t ↦ F (fun s ↦ w (projIcc a b hab s)) t,
      (hF _ (hcomp w)).comp_continuous continuous_subtype_val fun t ↦ t.2⟩
  obtain ⟨w, hw, -⟩ := existsUnique_isFixedPt_of_dist_le_integral_dist hab P K
    fun u v t ↦ hFK _ _ (hcomp u) (hcomp v) t t.2
  refine ⟨fun s ↦ w (projIcc a b hab s), hcomp w, fun t ht ↦ ?_⟩
  have h := congrArg (fun z : C(Icc a b, E) ↦ z ⟨t, ht⟩) hw
  change w (projIcc a b hab t) = F (fun s ↦ w (projIcc a b hab s)) t
  rw [projIcc_of_mem hab ht]
  exact h.symm

/-- **Uniqueness for functions on `ℝ`.** Two solutions of `u = F u` on `[a, b]`, continuous
there, agree on `[a, b]` under the integral Volterra estimate. -/
theorem eqOn_of_dist_le_integral_dist [CompleteSpace E] (hab : a ≤ b)
    (F : (ℝ → E) → ℝ → E) (K : ℝ≥0)
    (hF : ∀ u, ContinuousOn u (Icc a b) → ContinuousOn (F u) (Icc a b))
    (hFK : ∀ u v, ContinuousOn u (Icc a b) → ContinuousOn v (Icc a b) → ∀ t ∈ Icc a b,
      dist (F u t) (F v t) ≤ (K : ℝ) * ∫ s in a..t, dist (u s) (v s))
    {u v : ℝ → E} (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hue : ∀ t ∈ Icc a b, u t = F u t) (hve : ∀ t ∈ Icc a b, v t = F v t) :
    EqOn u v (Icc a b) := by
  have hcomp : ∀ w : C(Icc a b, E), ContinuousOn (fun s ↦ w (projIcc a b hab s)) (Icc a b) :=
    fun w ↦ (w.continuous.comp continuous_projIcc).continuousOn
  let P : C(Icc a b, E) → C(Icc a b, E) := fun w ↦
    ⟨fun t ↦ F (fun s ↦ w (projIcc a b hab s)) t,
      (hF _ (hcomp w)).comp_continuous continuous_subtype_val fun t ↦ t.2⟩
  have hP : ∀ u v (t : Icc a b), dist (P u t) (P v t) ≤
      (K : ℝ) * ∫ s in a..t.1, dist (u (projIcc a b hab s)) (v (projIcc a b hab s)) :=
    fun u v t ↦ hFK _ _ (hcomp u) (hcomp v) t t.2
  -- a solution restricted to `[a, b]` is a fixed point of `P`
  have hfix : ∀ w : ℝ → E, ∀ hw : ContinuousOn w (Icc a b), (∀ t ∈ Icc a b, w t = F w t) →
      IsFixedPt P ⟨(Icc a b).domRestrict w, hw.domRestrict⟩ := by
    intro w hw hwe
    ext t
    have hw' : ContinuousOn (fun s ↦ w (projIcc a b hab s)) (Icc a b) :=
      hcomp ⟨(Icc a b).domRestrict w, hw.domRestrict⟩
    change F (fun s ↦ w (projIcc a b hab s)) t = w t
    rw [hwe t t.2]
    have hd := hFK _ _ hw' hw t t.2
    have h0 : (∫ s in a..t.1, dist (w (projIcc a b hab s)) (w s)) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) ?_]
      · simp
      intro s hs
      rw [uIcc_of_le t.2.1] at hs
      simp [projIcc_of_mem hab ⟨hs.1, hs.2.trans t.2.2⟩]
    rw [h0, mul_zero] at hd
    exact dist_le_zero.1 hd
  obtain ⟨w₀, -, huniq⟩ := existsUnique_isFixedPt_of_dist_le_integral_dist hab P K hP
  intro t ht
  have h1 := huniq _ (hfix u hu hue)
  have h2 := huniq _ (hfix v hv hve)
  have := congrArg (fun z : C(Icc a b, E) ↦ z ⟨t, ht⟩) (h1.trans h2.symm)
  exact this

end PDE.Analysis.ODE
