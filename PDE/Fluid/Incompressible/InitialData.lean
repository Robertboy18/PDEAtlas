/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.Operators

/-!
# Initial-value data for incompressible flow

`InitialValueData` bundles a forcing term with a distributionally divergence-free initial
velocity; it is shared by the Euler and Navier–Stokes initial-value problems.
`zeroInitialValueData` is the zero datum.

The Euler and Navier–Stokes equations are those of Majda and Bertozzi, Chapter 1. Fefferman's
initial condition (3) takes a smooth divergence-free datum and his forcing satisfies the decay
condition (5); here the datum is only distributionally divergence-free and the forcing is
arbitrary.

## References

* A. J. Majda and A. L. Bertozzi, *Vorticity and Incompressible Flow*, Cambridge Texts in Applied
  Mathematics 27, Cambridge University Press, 2001, Chapter 1.
  <https://doi.org/10.1017/CBO9780511613203>
* C. L. Fefferman, "Existence and smoothness of the Navier–Stokes equation", official problem
  description of the Clay Mathematics Institute, equation (3) and condition (5), p. 1.
  <https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf>
-/

@[expose] public section

namespace IncompressibleFlow

open EuclideanSpace

set_option linter.missingDocs true

/-- Data common to an incompressible initial-value problem on `ℝ^n`. -/
structure InitialValueData (n : ℕ) where
  /-- External spacetime force. -/
  forcing : ℝ^(n + 1) → ℝ^n
  /-- Prescribed velocity at time zero. -/
  initialVelocity : ℝ^n → ℝ^n
  /-- Distributional incompressibility of the prescribed initial velocity. -/
  initialVelocity_distributionallyDivergenceFree :
    DistributionallyDivergenceFree initialVelocity

/-- Zero forcing and zero initial velocity. -/
def zeroInitialValueData (n : ℕ) : InitialValueData n where
  forcing := fun _ ↦ 0
  initialVelocity := fun _ ↦ 0
  initialVelocity_distributionallyDivergenceFree :=
    distributionallyDivergenceFree_zero n

end IncompressibleFlow
