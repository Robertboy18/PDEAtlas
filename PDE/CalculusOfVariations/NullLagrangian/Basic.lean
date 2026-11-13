/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Jacobian.Basic
public import Mathlib.Analysis.Matrix.Normed

/-!
# Classical null Lagrangians

For a density `L(P,z,x)`, the Euler–Lagrange expression is minus the divergence of the
gradient-entry derivative plus the value derivative. Both derivatives below are
Fréchet derivatives with the other variables frozen. Matrix rows index components and
columns index spatial directions.

The expression is the left side of the Euler–Lagrange system in Evans, §8.1.4(a), (16),
and a null Lagrangian has it equal to zero for every smooth map, as in the definition of
§8.1.4(b). Since `fderiv` is totalized, applications prove differentiability of the density
separately.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.1.4(a), system (16), and §8.1.4(b), Definition.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open scoped Matrix.Norms.Elementwise ContDiff

namespace PDE.CalculusOfVariations

variable {n m : ℕ}

/-- The classical Euler–Lagrange expression in component `k`, with sign `-div + D_z`. -/
def classicalEulerLagrange
    (L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ)
    (u : ℝ^n → ℝ^m) (x : ℝ^n) (k : Fin m) : ℝ :=
  -(∑ i, (∂[i]
      (fun y ↦ fderiv ℝ (fun P ↦ L P (u y) y) (Analysis.jacobianMatrix u y)
        (Matrix.single k i 1))) x) +
    fderiv ℝ (fun z ↦ L (Analysis.jacobianMatrix u x) z x) (u x)
      (EuclideanSpace.single k (1 : ℝ))

/-- The classical null-Lagrangian property: every smooth map satisfies the
Euler–Lagrange system throughout the domain. Smoothness of the density is stated separately. -/
def IsNullLagrangianOn (Ω : Set (ℝ^n))
    (L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ) : Prop :=
  ∀ (u : ℝ^n → ℝ^m), ContDiffOn ℝ ∞ u Ω →
    ∀ x ∈ Ω, ∀ k, classicalEulerLagrange L u x k = 0

end PDE.CalculusOfVariations
