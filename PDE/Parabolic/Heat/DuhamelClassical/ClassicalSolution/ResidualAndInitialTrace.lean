/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Duhamel.Equation
import PDE.Parabolic.Heat.DuhamelClassical.ClassicalSolution.Regularity

/-!
# The forced heat residual and initial trace

Duhamel's formula solves `∂ₜ u - Δu = f` at positive time and approaches zero uniformly
in space as time decreases to zero. These are consequences of the shared classical
regularity theorem, which also proves the derivatives appearing in the equation exist.

The uniform limit is retained alongside the initial value: assigning `u(x, 0) = 0`
alone does not assert convergence to the initial data.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.1, Theorem 2(ii)-(iii).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (laplacian)

namespace HeatEquation

open PDE.Common

variable {n : ℕ}

/-- The Duhamel solution has the forced heat residual, zero initial value, and a spatially
uniform zero initial trace. Here the source is globally `C²` and compactly supported. -/
theorem nonhomogeneousSolution_forced_heat_residual_and_initial_trace
    (f : ℝ^(n + 1) → ℝ)
    (hf2 : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (∀ (x : ℝ^n) (t : ℝ), 0 < t →
      deriv (fun τ ↦ nonhomogeneousSolution (n := n) f x τ) t -
          laplacian (n := n)
            (fun x' ↦ nonhomogeneousSolution (n := n) f x' t) x =
        f (timeSpaceCons (n := n) t x)) ∧
    (∀ x : ℝ^n,
      nonhomogeneousSolution (n := n) f x 0 = 0) ∧
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ (x : ℝ^n) (t : ℝ),
          0 < t → t < δ →
            |nonhomogeneousSolution (n := n) f x t| < ε := by
  exact (nonhomogeneousSolution_regularity_classical f hf2 hfc).2.2.2.2

end HeatEquation
