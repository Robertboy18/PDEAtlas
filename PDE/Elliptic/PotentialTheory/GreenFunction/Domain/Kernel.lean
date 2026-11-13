/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution
public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Gradient

/-!
# The domain Green kernel from a corrector

We define the Green kernel `greenKernel x φ y = Φ(y - x) - φ(y)` with pole `x`, where `Φ` is
`fundamentalSolution n` and `φ` is a corrector. When `φ` solves Evans's corrector problem (26),
harmonic in the domain with boundary values `Φ(y - x)`, this is Green's function for the region as
defined in Evans's §2.2.4(a). The gradient `greenKernelGradient` subtracts the continuous closure
gradient of the corrector, so the same field supplies the interior formula and the signed boundary
flux. The definitions impose no harmonicity or boundary conditions; the representation theorems
state those hypotheses explicitly.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.4(a), the corrector problem (26) and the definition of
  Green's function for the region `U`, p. 34.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public noncomputable section

namespace PotentialTheory.GreenFunction.Domain

open SobolevSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The fundamental solution with pole `x`, minus the corrector `φ`. -/
def greenKernel (x : ℝ^n) (φ : ℝ^n → ℝ) (y : ℝ^n) : ℝ :=
  fundamentalSolution n (y - x) - φ y

/-- The gradient of the pole kernel minus the continuous closure gradient of
its corrector. The pole itself is excluded when identifying this field with
an analytic derivative. -/
def greenKernelGradient (x : ℝ^n) {φ : ℝ^n → ℝ}
    (hφ : ContDiffUpToBoundary 1 φ Ω) (y : ℝ^n) : ℝ^n :=
  ∇ (fun z ↦ fundamentalSolution n (z - x)) y - hφ.completedGradient y

end PotentialTheory.GreenFunction.Domain
