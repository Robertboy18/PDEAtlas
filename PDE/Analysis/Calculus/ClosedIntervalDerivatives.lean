/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Equality of derivatives on a closed interval

Equality on the interior identifies ordinary derivatives there. Their
continuity extends that equality to both endpoints of a nondegenerate
interval. Polynomial evaluation is smooth, so the identities apply to the
polynomial branches of a piecewise function.

## Main results

* `iteratedDeriv_eqOn_Icc`: `Cⁿ` functions equal on a closed interval have equal derivatives
  through order `n` on it.
* `deriv_deriv_eqOn_Icc`: `C²` functions equal on a closed interval have equal second
  derivatives on it.
* `contDiff_polynomial_eval`: evaluation of a real polynomial is smooth of every order.
-/

@[expose] public section

namespace PDE.Analysis

/-- Equal `Cⁿ` functions have equal derivatives through order `n` on a closed interval. -/
theorem iteratedDeriv_eqOn_Icc {f g : ℝ → ℝ} {a b : ℝ} {n m : ℕ}
    (hab : a < b) (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (heq : Set.EqOn f g (Set.Icc a b)) (hmn : m ≤ n) :
    Set.EqOn (iteratedDeriv m f) (iteratedDeriv m g) (Set.Icc a b) := by
  have hopen := heq.mono Set.Ioo_subset_Icc_self
  have hderiv := hopen.iteratedDeriv_of_isOpen isOpen_Ioo m
  have hclosed := hderiv.closure
    (hf.continuous_iteratedDeriv m (by exact_mod_cast hmn))
    (hg.continuous_iteratedDeriv m (by exact_mod_cast hmn))
  rwa [closure_Ioo hab.ne] at hclosed

/-- Equality of `C²` functions on a closed interval includes their ordinary second derivatives. -/
theorem deriv_deriv_eqOn_Icc {f g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (heq : Set.EqOn f g (Set.Icc a b)) :
    Set.EqOn (deriv (deriv f)) (deriv (deriv g)) (Set.Icc a b) := by
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
    iteratedDeriv_eqOn_Icc hab hf hg heq (le_refl 2)

/-- Evaluation of a real polynomial has every order of smoothness. -/
theorem contDiff_polynomial_eval (p : Polynomial ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun x ↦ p.eval x) := by
  simpa using p.contDiff_aeval (𝕜 := ℝ) n

end PDE.Analysis
