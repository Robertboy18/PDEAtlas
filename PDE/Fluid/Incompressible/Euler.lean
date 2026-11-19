/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.Operators

/-!
# Pointwise incompressible Euler residual

The Euler momentum residual `eulerMomentumResidual n u p f = Dₜᵘu + ∇p - f`, built from the
operators of `PDE.Fluid.Incompressible.Operators`, and its zero form
`eulerMomentumResidual_eq_zero_iff`.

This is the momentum equation of the incompressible Euler equations in Majda and Bertozzi,
Section 1.1, with a forcing term.

## References

* A. J. Majda and A. L. Bertozzi, *Vorticity and Incompressible Flow*, Cambridge Texts in Applied
  Mathematics 27, Cambridge University Press, 2001, Chapter 1, Section 1.1.
  <https://doi.org/10.1017/CBO9780511613203>
-/

@[expose] public section

open PDE (spatialGradient)

namespace IncompressibleFlow

open EuclideanSpace

set_option linter.missingDocs true

noncomputable section

/-- Euler momentum residual `Dₜᵘu + ∇p - f`. -/
def eulerMomentumResidual (n : ℕ)
    (u : ℝ^(n + 1) → ℝ^n) (p : ℝ^(n + 1) → ℝ)
    (f : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) : ℝ^n :=
  materialDerivative n u u x + spatialGradient p x - f x

/-- A zero Euler residual is exactly the pointwise Euler momentum equation. -/
theorem eulerMomentumResidual_eq_zero_iff
    (n : ℕ) (u : ℝ^(n + 1) → ℝ^n) (p : ℝ^(n + 1) → ℝ)
    (f : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) :
    eulerMomentumResidual n u p f x = 0 ↔
      materialDerivative n u u x + spatialGradient p x = f x := by
  unfold eulerMomentumResidual
  exact sub_eq_zero

end

end IncompressibleFlow
