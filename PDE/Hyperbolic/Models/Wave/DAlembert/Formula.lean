/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import PDE.Common.Euclidean
import Mathlib.Tactic.Positivity.Finset

/-!
# D'Alembert formula for the one-dimensional wave equation

We define the one-dimensional representation formula

`u(x, t) = ½ (g(x + t) + g(x - t)) + ½ ∫_{x-t}^{x+t} h(y) dy`

(Evans, §2.4.1, d'Alembert's formula (8)), prove its domain-of-dependence
identities, and verify its initial displacement. Its derivatives and the
classical-solution theorem are in `DAlembert.Derivatives` and
`DAlembert.ClassicalSolution`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.1, equation (8).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace WaveEquation

open PDE.Common
open scoped Interval

/-- The right-hand side of d'Alembert's formula for the one-dimensional wave equation. -/
noncomputable def dAlembertFormula (g h : ℝ → ℝ) (x t : ℝ) : ℝ :=
  (1/2) * (g (x + t) + g (x - t)) +
  (1/2) * ∫ y in x - t..x + t, h y

/--
Domain of dependence for the one-dimensional wave equation (Evans, §2.4.1, formula (8)).

At nonnegative time `t`, d'Alembert's solution at `(x,t)` only uses the
initial displacement and velocity on the closed interval
`[x-t,x+t]`.  Therefore two data sets agreeing on that interval produce the
same value at `(x,t)`.

This is the pointwise finite-propagation statement behind the backward
characteristic cone.
-/
theorem dAlembertFormula_eq_of_eqOn_domainOfDependence {g₁ g₂ h₁ h₂ : ℝ → ℝ} {x t : ℝ} (ht : 0 ≤ t)
    (hg : Set.EqOn g₁ g₂ (Set.Icc (x - t) (x + t)))
    (hh : Set.EqOn h₁ h₂ (Set.Icc (x - t) (x + t))) :
    dAlembertFormula g₁ h₁ x t = dAlembertFormula g₂ h₂ x t := by
  have hends : x - t ≤ x + t := by linarith
  have hxsub : x - t ∈ Set.Icc (x - t) (x + t) := ⟨le_rfl, hends⟩
  have hxadd : x + t ∈ Set.Icc (x - t) (x + t) := ⟨hends, le_rfl⟩
  have hint : (∫ y in x - t..x + t, h₁ y) = ∫ y in x - t..x + t, h₂ y :=
    intervalIntegral.integral_congr fun y hy ↦ hh (by simpa [Set.uIcc_of_le hends] using hy)
  simp only [dAlembertFormula]
  rw [hg hxadd, hg hxsub, hint]

/--
Finite speed of propagation for d'Alembert's formula.

If both initial data vanish throughout the backward domain of dependence
`[x-t,x+t]`, then the wave value at `(x,t)` vanishes.  Equivalently, a
disturbance initially supported away from this interval cannot reach
`(x,t)`.
-/
theorem dAlembertFormula_eq_zero_of_vanishes_on_domainOfDependence {g h : ℝ → ℝ} {x t : ℝ}
    (ht : 0 ≤ t) (hg : ∀ y ∈ Set.Icc (x - t) (x + t), g y = 0)
    (hh : ∀ y ∈ Set.Icc (x - t) (x + t), h y = 0) :
    dAlembertFormula g h x t = 0 := by
  have heq := dAlembertFormula_eq_of_eqOn_domainOfDependence (g₁ := g) (g₂ := fun _ ↦ 0)
      (h₁ := h) (h₂ := fun _ ↦ 0) ht (fun y hy ↦ hg y hy) (fun y hy ↦ hh y hy)
  simpa [dAlembertFormula] using heq

/-- The one-dimensional d'Alembert solution (8) of Evans, §2.4.1, as a spacetime field. -/
noncomputable def dAlembertSolution1D
    (g h : ℝ^1 → ℝ) :
    ℝ^2 → ℝ :=
  fun xt ↦
    dAlembertFormula
      (fun x₁ ↦ g (EuclideanSpace.single (0 : Fin 1) x₁))
      (fun x₁ ↦ h (EuclideanSpace.single (0 : Fin 1) x₁))
      (xt 1) (xt 0)

/-- D'Alembert's formula attains its initial displacement without regularity assumptions. -/
theorem dAlembert_satisfies_initial_pos (g h : ℝ^1 → ℝ) (x0 : ℝ^1) :
    dAlembertSolution1D g h (timeSpaceCons 0 x0) = g x0 := by
  have hx : EuclideanSpace.single (0 : Fin 1) (x0 0) = x0 := by
    ext i
    fin_cases i
    simp
  have hspace : timeSpaceCons 0 x0 (1 : Fin 2) = x0 0 := timeSpaceCons_succ 0 x0 (0 : Fin 1)
  simp only [dAlembertSolution1D, dAlembertFormula, one_div, Fin.isValue, hspace,
    timeSpaceCons_zero, add_zero, hx, sub_zero, intervalIntegral.integral_same, mul_zero]
  ring

end WaveEquation
