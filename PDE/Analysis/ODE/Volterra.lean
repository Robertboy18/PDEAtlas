/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Factorial estimates for Volterra operators

If the difference of two integrands is bounded by `K` times the pointwise
curve distance, integration from any initial time `t₀ ∈ [a,b]` and successive
integrations give `(K * (b-a))^n / n!`.
Some iterate therefore contracts on every finite interval. The affine and
nonlinear Carathéodory constructions both use this estimate. The state space
need not be separable.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set
open scoped Topology

namespace PDE.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The `n`-th Volterra iterate gains the factor `(K * |t-t₀|)^n / n!`.
Integrability is required of the operator's integrands; concrete field
constructors prove it from their data before applying this estimate. -/
theorem dist_iterate_volterra_apply_le
    {a b : ℝ} (t₀ : Icc a b)
    (P : C(Set.Icc a b, E) → C(Set.Icc a b, E))
    (g : C(Set.Icc a b, E) → ℝ → E) (x₀ : E) (K : NNReal)
    (hg : ∀ u, IntegrableOn (g u) (Icc a b) volume)
    (hP : ∀ u (t : Set.Icc a b), P u t = x₀ + ∫ s in t₀.1..t.1, g u s)
    (hK : ∀ u v (t : Set.Icc a b),
      ‖g u t - g v t‖ ≤ (K : ℝ) * dist (u t) (v t))
    (u v : C(Set.Icc a b, E)) (n : ℕ) (t : Set.Icc a b) :
    dist ((P^[n]) u t) ((P^[n]) v t) ≤
      (((K : ℝ) * |t.1 - t₀.1|) ^ n / n.factorial) * dist u v := by
  induction n generalizing t with
  | zero =>
      simpa using ContinuousMap.dist_apply_le_dist
        (f := u) (g := v) t
  | succ n hn =>
      have huInt := ((hg ((P^[n]) u)).mono_set
        (Set.uIcc_subset_Icc t₀.2 t.2)).intervalIntegrable
      have hvInt := ((hg ((P^[n]) v)).mono_set
        (Set.uIcc_subset_Icc t₀.2 t.2)).intervalIntegrable
      rw [iterate_succ_apply', iterate_succ_apply']
      rw [hP, hP, dist_eq_norm, add_sub_add_left_eq_sub,
        ← intervalIntegral.integral_sub huInt hvInt]
      calc
        ‖∫ s in t₀.1..t.1,
            g ((P^[n]) u) s -
              g ((P^[n]) v) s‖ ≤
            ∫ s in Set.uIoc t₀.1 t.1,
              ((K : ℝ) ^ (n + 1) * |s - t₀.1| ^ n /
                n.factorial) * dist u v := by
          rw [intervalIntegral.norm_intervalIntegral_eq]
          apply MeasureTheory.norm_integral_le_of_norm_le
            (Continuous.integrableOn_uIoc (by fun_prop))
          apply ae_restrict_mem measurableSet_Ioc |>.mono
          intro s hs
          have hsI : s ∈ Set.Icc a b :=
            subset_trans Set.uIoc_subset_uIcc
              (Set.uIcc_subset_Icc t₀.2 t.2) hs
          calc
            ‖g ((P^[n]) u) s -
                g ((P^[n]) v) s‖ ≤
                (K : ℝ) *
                  dist (((P^[n]) u) ⟨s, hsI⟩)
                    (((P^[n]) v) ⟨s, hsI⟩) :=
              hK _ _ ⟨s, hsI⟩
            _ ≤ (K : ℝ) *
                ((((K : ℝ) * |s - t₀.1|) ^ n / n.factorial) *
                  dist u v) := by
              gcongr
              exact hn ⟨s, hsI⟩
            _ = (((K : ℝ) ^ (n + 1) * |s - t₀.1| ^ n /
                n.factorial) * dist u v) := by ring
        _ ≤ (((K : ℝ) * |t.1 - t₀.1|) ^ (n + 1) /
              (n + 1).factorial) * dist u v := by
          apply le_of_abs_le
          rw [← intervalIntegral.abs_intervalIntegral_eq,
            intervalIntegral.integral_mul_const,
            intervalIntegral.integral_div,
            intervalIntegral.integral_const_mul, abs_mul, abs_div,
            abs_mul, intervalIntegral.abs_intervalIntegral_eq,
            integral_pow_abs_sub_uIoc, abs_div, abs_pow, abs_pow,
            abs_dist, NNReal.abs_eq, abs_abs, mul_div, div_div,
            ← abs_mul, ← Nat.cast_succ, ← Nat.cast_mul,
            ← Nat.factorial_succ, Nat.abs_cast, ← mul_pow]

omit [CompleteSpace E] in
/-- Taking the supremum over the interval gives the uniform factorial bound. -/
theorem dist_iterate_volterra_le
    {a b : ℝ} (t₀ : Icc a b)
    (P : C(Set.Icc a b, E) → C(Set.Icc a b, E))
    (g : C(Set.Icc a b, E) → ℝ → E) (x₀ : E) (K : NNReal)
    (hg : ∀ u, IntegrableOn (g u) (Icc a b) volume)
    (hP : ∀ u (t : Set.Icc a b), P u t = x₀ + ∫ s in t₀.1..t.1, g u s)
    (hK : ∀ u v (t : Set.Icc a b),
      ‖g u t - g v t‖ ≤ (K : ℝ) * dist (u t) (v t))
    (u v : C(Set.Icc a b, E)) (n : ℕ) :
    dist ((P^[n]) u) ((P^[n]) v) ≤
      (((K : ℝ) * (b - a)) ^ n / n.factorial) * dist u v := by
  have hab : a ≤ b := t₀.2.1.trans t₀.2.2
  rw [ContinuousMap.dist_le (by positivity)]
  intro t
  apply le_trans (dist_iterate_volterra_apply_le t₀ P g x₀ K hg hP hK u v n t)
  gcongr
  exact abs_le.mpr ⟨by linarith [t.2.1, t₀.2.2], by linarith [t.2.2, t₀.2.1]⟩

omit [CompleteSpace E] in
/-- A factorial denominator eventually beats every fixed interval length. -/
theorem exists_contractingWith_iterate_volterra
    {a b : ℝ} (t₀ : Icc a b)
    (P : C(Set.Icc a b, E) → C(Set.Icc a b, E))
    (g : C(Set.Icc a b, E) → ℝ → E) (x₀ : E) (K : NNReal)
    (hg : ∀ u, IntegrableOn (g u) (Icc a b) volume)
    (hP : ∀ u (t : Set.Icc a b), P u t = x₀ + ∫ s in t₀.1..t.1, g u s)
    (hK : ∀ u v (t : Set.Icc a b),
      ‖g u t - g v t‖ ≤ (K : ℝ) * dist (u t) (v t))
    : ∃ (n : ℕ) (C : NNReal), ContractingWith C (P^[n]) := by
  have hab : a ≤ b := t₀.2.1.trans t₀.2.2
  obtain ⟨n, hn⟩ :=
    FloorSemiring.tendsto_pow_div_factorial_atTop ((K : ℝ) * (b - a))
      |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have hnonneg : 0 ≤ (((K : ℝ) * (b - a)) ^ n / n.factorial) := by positivity
  let C : NNReal := ⟨((K : ℝ) * (b - a)) ^ n / n.factorial, hnonneg⟩
  refine ⟨n, C, hn, LipschitzWith.of_dist_le_mul ?_⟩
  intro u v
  exact dist_iterate_volterra_le t₀ P g x₀ K hg hP hK u v n

/-- The continuous-curve space is complete, so a contracting iterate supplies
one and only one fixed point of the Volterra operator itself. -/
theorem existsUnique_isFixedPt_volterra
    {a b : ℝ} (t₀ : Icc a b)
    (P : C(Set.Icc a b, E) → C(Set.Icc a b, E))
    (g : C(Set.Icc a b, E) → ℝ → E) (x₀ : E) (K : NNReal)
    (hg : ∀ u, IntegrableOn (g u) (Icc a b) volume)
    (hP : ∀ u (t : Set.Icc a b), P u t = x₀ + ∫ s in t₀.1..t.1, g u s)
    (hK : ∀ u v (t : Set.Icc a b),
      ‖g u t - g v t‖ ≤ (K : ℝ) * dist (u t) (v t))
    : ∃! u : C(Set.Icc a b, E), IsFixedPt P u := by
  obtain ⟨n, C, hPn⟩ := exists_contractingWith_iterate_volterra t₀ P g x₀ K hg hP hK
  let u := ContractingWith.fixedPoint (P^[n]) hPn
  have hu : IsFixedPt P u := hPn.isFixedPt_fixedPoint_iterate
  refine ⟨u, hu, ?_⟩
  intro v hv
  exact hPn.fixedPoint_unique' (hv.iterate n) hPn.fixedPoint_isFixedPt

end PDE.Analysis.ODE
