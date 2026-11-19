/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Calculus

/-!
# The Korteweg–de Vries equation

We use the convention `u_t + a u u_x + b u_xxx = 0`, with time in coordinate `0`
and space in coordinate `1`. The coefficient-six normalization `a = 6`, `b = 1` is the form
(4) of Evans, §4.2.1(b); `a = b = 1` is another choice.
Positive dispersion and positive nonlinearity give positive solitary waves moving
to the right. Keeping both coefficients explicit also records the sign convention.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.2.1(b), equation (4).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace KdVEquation

/-- The KdV residual, using Fréchet coordinate derivatives on spacetime. -/
noncomputable def residual (nonlinearity dispersion : ℝ) (u : ℝ^2 → ℝ) (p : ℝ^2) : ℝ :=
  (∂[(0 : Fin 2)] u) p + nonlinearity * u p * (∂[(1 : Fin 2)] u) p +
    dispersion * (∂[(1 : Fin 2)] (∂[(1 : Fin 2)] (∂[(1 : Fin 2)] u))) p

/-- A globally defined classical KdV solution. Joint `C³` regularity ensures that
the time derivative and all three spatial derivatives in the equation exist. -/
structure IsSolution (nonlinearity dispersion : ℝ) (u : ℝ^2 → ℝ) : Prop where
  regularity : ContDiff ℝ 3 u
  equation : ∀ p, residual nonlinearity dispersion u p = 0

end KdVEquation
