/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.Noether.Current

/-!
# Locality of variational expressions

The density, momentum, Euler–Lagrange expression, and Noether current depend only
on the germ of the field. These identities let a locally constructed transformed
field replace the original one without choosing a smooth extension outside the domain.
They use locality of derivatives and require no regularity assumptions.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Elementwise Topology

namespace PDE.CalculusOfVariations.Noether

open Analysis

variable {n m : ℕ} {L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ}
  {u w v : ℝ^n → ℝ^m} {X : ℝ^n → ℝ^n} {x : ℝ^n}

/-- Fields with the same germ have the same evaluated density. -/
theorem fieldDensity_eq_of_eventuallyEq (h : u =ᶠ[𝓝 x] w) :
    fieldDensity L u x = fieldDensity L w x := by
  unfold fieldDensity
  rw [jacobianMatrix_eq_of_eventuallyEq h, h.eq_of_nhds]

/-- The conjugate momentum depends only on the germ of the field. -/
theorem momentum_eq_of_eventuallyEq (h : u =ᶠ[𝓝 x] w) (k : Fin m) (i : Fin n) :
    momentum L u k i x = momentum L w k i x := by
  unfold momentum
  rw [jacobianMatrix_eq_of_eventuallyEq h, h.eq_of_nhds]

/-- The classical Euler–Lagrange expression depends only on the field germ,
including the derivatives of its momentum. -/
theorem classicalEulerLagrange_eq_of_eventuallyEq (h : u =ᶠ[𝓝 x] w) (k : Fin m) :
    classicalEulerLagrange L u x k = classicalEulerLagrange L w x k := by
  have hp (i : Fin n) : momentum L u k i =ᶠ[𝓝 x] momentum L w k i := by
    filter_upwards [h.eventuallyEq_nhds] with y hy
    exact momentum_eq_of_eventuallyEq hy k i
  have hdp (i : Fin n) :
      (∂[i] (momentum L u k i)) x = (∂[i] (momentum L w k i)) x :=
    ((hp i).partialDeriv i).eq_of_nhds
  unfold momentum at hdp
  unfold classicalEulerLagrange
  simp only [hdp, jacobianMatrix_eq_of_eventuallyEq h, h.eq_of_nhds]

/-- With the generators fixed, the current depends only on the field germ. -/
theorem noetherCurrent_eq_of_eventuallyEq (h : u =ᶠ[𝓝 x] w) :
    noetherCurrent L u v X x = noetherCurrent L w v X x := by
  unfold noetherCurrent
  simp only [momentum_eq_of_eventuallyEq h, fieldDensity_eq_of_eventuallyEq h]

end PDE.CalculusOfVariations.Noether
