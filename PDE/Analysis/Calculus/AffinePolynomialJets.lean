/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Derivatives of a function from a polynomial on an affine cell

If a polynomial `P` represents a `Cⁿ` function `g` on a cell `[a, a + h]` through the affine
coordinate, `P(t) = g(a + h t)` for `t ∈ [0, 1]`, then the derivatives of order `j ≤ n` agree on
the closed cell, on the open cell by differentiating the identity and at the ends by continuity.
The coefficients of `P⁽ʲ⁾` are those of `P` multiplied by descending factorials
(`Polynomial.coeff_iterate_derivative`).

## Main results

* `iteratedDeriv_affine`: the `j`-th derivative of `t ↦ g (a + h t)` is `hʲ g⁽ʲ⁾(a + h t)` for a
  `Cⁿ` function `g` and `j ≤ n`.
* `eval_iterate_derivative_eq_of_affine`: `P⁽ʲ⁾(t) = hʲ g⁽ʲ⁾(a + h t)` on the closed cell
  `t ∈ [0, 1]`.
-/

@[expose] public section

namespace PDE.Analysis

open Polynomial Set
open scoped Topology

/-- For a `Cⁿ` function `g` and `j ≤ n`, the `j`-th derivative of `t ↦ g (a + h t)` is
`hʲ g⁽ʲ⁾(a + h t)`. -/
theorem iteratedDeriv_affine {g : ℝ → ℝ} {n : ℕ} (hg : ContDiff ℝ n g) (a h : ℝ) {j : ℕ}
    (hj : j ≤ n) (t : ℝ) :
    iteratedDeriv j (fun t ↦ g (a + h * t)) t = h ^ j * iteratedDeriv j g (a + h * t) := by
  rw [iteratedDeriv_comp_const_mul (f := fun z ↦ g (a + z))
      ((hg.of_le (mod_cast hj)).comp (contDiff_const.add contDiff_id)) h,
    iteratedDeriv_comp_const_add]

/-- **The derivatives of a polynomial representation on a closed affine cell.** -/
theorem eval_iterate_derivative_eq_of_affine {g : ℝ → ℝ} {n : ℕ} (hg : ContDiff ℝ n g) {a h : ℝ}
    {P : ℝ[X]} (hP : ∀ t ∈ Icc (0 : ℝ) 1, P.eval t = g (a + h * t)) {j : ℕ} (hj : j ≤ n) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (derivative^[j] P).eval t = h ^ j * iteratedDeriv j g (a + h * t) := by
  have hpoly : ∀ y, iteratedDeriv j (fun t ↦ P.eval t) y = (derivative^[j] P).eval y := by
    intro y
    induction j generalizing y with
    | zero => simp
    | succ j ih =>
      rw [iteratedDeriv_succ]
      have : iteratedDeriv j (fun t ↦ P.eval t) = fun y ↦ (derivative^[j] P).eval y :=
        funext fun y ↦ ih (by omega) y
      rw [this, Polynomial.deriv, Function.iterate_succ_apply']
  have hopen : EqOn (fun t ↦ (derivative^[j] P).eval t)
      (fun t ↦ h ^ j * iteratedDeriv j g (a + h * t)) (Ioo 0 1) := fun y hy ↦ by
    have hev : (fun t ↦ P.eval t) =ᶠ[𝓝 y] fun t ↦ g (a + h * t) := by
      filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz
      exact hP z ⟨hz.1.le, hz.2.le⟩
    simp only
    rw [← hpoly, hev.iteratedDeriv_eq, iteratedDeriv_affine hg a h hj]
  have hcont : Continuous fun t ↦ h ^ j * iteratedDeriv j g (a + h * t) :=
    continuous_const.mul ((hg.continuous_iteratedDeriv j (by exact_mod_cast hj)).comp
      (continuous_const.add (continuous_const.mul continuous_id)))
  have hclosed := hopen.closure (derivative^[j] P).continuous hcont
  rw [closure_Ioo (show (0 : ℝ) ≠ 1 by norm_num)] at hclosed
  exact hclosed ht

end PDE.Analysis
