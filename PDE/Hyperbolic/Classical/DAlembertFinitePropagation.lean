/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.DAlembert.Formula
import Mathlib.Tactic.Positivity.Finset

/-!
# Finite propagation for d'Alembert's formula

The one-dimensional wave representation depends only on data in the
backward characteristic interval. Consequently compactly supported initial
data remain inside the corresponding forward cone. Evans, §2.4.1, notes this finite propagation
speed for d'Alembert's formula (8) in Remark (iii) after Theorem 2.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.1, equation (8) and Remark (iii) after Theorem 2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace WaveEquation

/--
If the initial displacement and velocity vanish outside `[-R, R]`, then
d'Alembert's formula vanishes outside `[-R - t, R + t]` at every
nonnegative time `t`.
-/
theorem dAlembertFormula_eq_zero_outside_expandingInterval {g h : ℝ → ℝ} {R x t : ℝ} (ht : 0 ≤ t)
    (hg : Function.support g ⊆ Set.Icc (-R) R) (hh : Function.support h ⊆ Set.Icc (-R) R)
    (hx : x ∉ Set.Icc (-(R + t)) (R + t)) :
    dAlembertFormula g h x t = 0 := by
  have hxCases : x < -(R + t) ∨ R + t < x := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using hx
  apply dAlembertFormula_eq_zero_of_vanishes_on_domainOfDependence ht
  · intro y hy
    by_contra hgy
    have hySupport : y ∈ Function.support g := hgy
    have hyData := hg hySupport
    rcases hxCases with hxLeft | hxRight
    · have : y < -R := by linarith [hy.2]
      exact (not_lt_of_ge hyData.1) this
    · have : R < y := by linarith [hy.1]
      exact (not_lt_of_ge hyData.2) this
  · intro y hy
    by_contra hhy
    have hySupport : y ∈ Function.support h := hhy
    have hyData := hh hySupport
    rcases hxCases with hxLeft | hxRight
    · have : y < -R := by linarith [hy.2]
      exact (not_lt_of_ge hyData.1) this
    · have : R < y := by linarith [hy.1]
      exact (not_lt_of_ge hyData.2) this

/--
Finite propagation in support form: at nonnegative time `t`, the support of
the d'Alembert solution is contained in the initial support interval enlarged
by distance `t`.
-/
theorem support_dAlembertFormula_subset_expandingInterval {g h : ℝ → ℝ} {R t : ℝ} (ht : 0 ≤ t)
    (hg : Function.support g ⊆ Set.Icc (-R) R) (hh : Function.support h ⊆ Set.Icc (-R) R) :
    Function.support (fun x ↦ dAlembertFormula g h x t) ⊆ Set.Icc (-(R + t)) (R + t) := by
  intro x hx
  by_contra hxOutside
  exact hx (dAlembertFormula_eq_zero_outside_expandingInterval ht hg hh hxOutside)

end WaveEquation
