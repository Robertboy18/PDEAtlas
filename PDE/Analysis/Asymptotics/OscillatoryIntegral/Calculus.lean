/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Asymptotics.OscillatoryIntegral
public import PDE.FDeriv.PartialDeriv

/-!
# Coordinate derivatives of oscillatory phases

At every point where the phase `φ` is differentiable, the coordinate derivative of
`y ↦ osc ξ (φ y) = exp (i ξ φ y)` is `∂ᵢφ • (i ξ exp (i ξ φ))`.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

variable {n : ℕ}

/-- The chain rule for a coordinate derivative of a nonlinear oscillation. -/
theorem partialDeriv_osc_comp {φ : ℝ^n → ℝ} {x : ℝ^n}
    (hφ : DifferentiableAt ℝ φ x) (ξ : ℝ) (i : Fin n) :
    (∂[i] (fun y ↦ osc ξ (φ y))) x =
      (∂[i] φ) x • ((ξ : ℂ) * Complex.I * osc ξ (φ x)) := by
  have h := (hasDerivAt_osc ξ (φ x)).hasFDerivAt.comp x hφ.hasFDerivAt
  change fderiv ℝ ((osc ξ) ∘ φ) x (EuclideanSpace.single i 1) = _
  rw [h.fderiv]
  rfl

end PDE.Analysis
