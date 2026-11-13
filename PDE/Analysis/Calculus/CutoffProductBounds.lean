/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Derivative bounds after a smooth cutoff

Equality on the positive half-line determines derivatives at its endpoint
by continuity. With the product rule, equality with `(1 - g) * q` there
controls the endpoint jets of the product. The estimates retain arbitrary
bounds for the factor `q`.

## Main results

* `iteratedDeriv_eq_on_Ici_of_eqOn_Ioi`: `Cⁿ` functions equal on `(a, ∞)` have equal `n`-th
  derivatives on `[a, ∞)`.
* `deriv_deriv_fun_mul_of_contDiff`: the second derivative of a product of two `C²` functions.
* `abs_deriv_cutoff_product_le`: if `k = (1 - g) q` on `(0, ∞)`, `|1 - g| ≤ 1`, `|g'| ≤ ε`,
  `|q| ≤ A` and `|q'| ≤ B` at `x ≥ 0`, then `|k'(x)| ≤ ε A + B`.
* `abs_deriv_deriv_cutoff_product_le`: with moreover `|g'| ≤ D`, `|g''| ≤ E` and `|q''| ≤ C`,
  `|k''(x)| ≤ E A + 2 D B + C`.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

/-- Equality of smooth functions on an open half-line extends to their endpoint jets. -/
theorem iteratedDeriv_eq_on_Ici_of_eqOn_Ioi {n : ℕ} {f g : ℝ → ℝ} {a : ℝ}
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (hfg : Set.EqOn f g (Set.Ioi a)) :
    Set.EqOn (iteratedDeriv n f) (iteratedDeriv n g) (Set.Ici a) := by
  simpa only [closure_Ioi] using
    (hfg.iteratedDeriv_of_isOpen isOpen_Ioi n).closure
      (hf.continuous_iteratedDeriv n le_rfl) (hg.continuous_iteratedDeriv n le_rfl)

/-- The second derivative of a product of two `C²` functions. -/
theorem deriv_deriv_fun_mul_of_contDiff {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : ℝ) :
    deriv (deriv (fun y ↦ f y * g y)) x =
      deriv (deriv f) x * g x + 2 * deriv f x * deriv g x +
        f x * deriv (deriv g) x := by
  have h := iteratedDeriv_fun_mul (n := 2) (x := x) hf.contDiffAt hg.contDiffAt
  norm_num [Finset.sum_range_succ, Nat.choose, iteratedDeriv_succ, iteratedDeriv_one] at h
  linarith

/-- A small transition slope perturbs the derivative bound by at most `ε * A`. -/
theorem abs_deriv_cutoff_product_le {k q g : ℝ → ℝ} {A B ε x : ℝ}
    (hk : ContDiff ℝ 1 k) (hq : ContDiff ℝ 1 q) (hg : ContDiff ℝ 1 g)
    (heq : Set.EqOn k (fun t ↦ (1 - g t) * q t) (Set.Ioi 0))
    (hx : 0 ≤ x) (hg₀ : |1 - g x| ≤ 1) (hg₁ : |deriv g x| ≤ ε)
    (hq₀ : |q x| ≤ A) (hq₁ : |deriv q x| ≤ B) :
    |deriv k x| ≤ ε * A + B := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans hg₁
  have hj := iteratedDeriv_eq_on_Ici_of_eqOn_Ioi hk
    ((contDiff_const.sub hg).mul hq) heq hx
  have hfirst : deriv k x = -deriv g x * q x + (1 - g x) * deriv q x := by
    simpa only [iteratedDeriv_one,
      deriv_fun_mul (((hg.differentiable (by norm_num)) x).const_sub 1)
        ((hq.differentiable (by norm_num)) x), deriv_const_sub] using hj
  rw [hfirst]
  calc
    _ ≤ |deriv g x| * |q x| + |1 - g x| * |deriv q x| := by
      simpa only [abs_mul, abs_neg] using
        abs_add_le (-deriv g x * q x) ((1 - g x) * deriv q x)
    _ ≤ ε * A + 1 * B := by gcongr
    _ = _ := by rw [one_mul]

/-- Separate first- and second-derivative budgets for the transition give an explicit
second derivative bound. -/
theorem abs_deriv_deriv_cutoff_product_le {k q g : ℝ → ℝ} {A B C D E x : ℝ}
    (hk : ContDiff ℝ 2 k) (hq : ContDiff ℝ 2 q) (hg : ContDiff ℝ 2 g)
    (heq : Set.EqOn k (fun t ↦ (1 - g t) * q t) (Set.Ioi 0))
    (hx : 0 ≤ x) (hg₀ : |1 - g x| ≤ 1) (hg₁ : |deriv g x| ≤ D)
    (hg₂ : |deriv (deriv g) x| ≤ E)
    (hq₀ : |q x| ≤ A) (hq₁ : |deriv q x| ≤ B)
    (hq₂ : |deriv (deriv q) x| ≤ C) :
    |deriv (deriv k) x| ≤ E * A + 2 * D * B + C := by
  have hD : 0 ≤ D := (abs_nonneg _).trans hg₁
  have hE : 0 ≤ E := (abs_nonneg _).trans hg₂
  have hj := iteratedDeriv_eq_on_Ici_of_eqOn_Ioi hk
    ((contDiff_const.sub hg).mul hq) heq hx
  have hsecond : deriv (deriv k) x =
      -deriv (deriv g) x * q x + 2 * (-deriv g x) * deriv q x +
        (1 - g x) * deriv (deriv q) x := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero,
      deriv_deriv_fun_mul_of_contDiff (contDiff_const.sub hg) hq,
      deriv_const_sub', deriv.fun_neg] using hj
  rw [hsecond]
  calc
    _ ≤ |deriv (deriv g) x| * |q x| + 2 * |deriv g x| * |deriv q x| +
        |1 - g x| * |deriv (deriv q) x| := by
      simpa only [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using
        (abs_add_le (-deriv (deriv g) x * q x + 2 * (-deriv g x) * deriv q x)
          ((1 - g x) * deriv (deriv q) x)).trans
          (add_le_add (abs_add_le (-deriv (deriv g) x * q x)
            (2 * (-deriv g x) * deriv q x)) le_rfl)
    _ ≤ E * A + 2 * D * B + 1 * C := by gcongr
    _ = _ := by rw [one_mul]

end PDE.Analysis
