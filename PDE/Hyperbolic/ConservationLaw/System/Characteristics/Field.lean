/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.ODE.Basic
public import PDE.Hyperbolic.ConservationLaw.System.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Characteristic fields and Riemann invariants

A characteristic field chooses a nonzero eigenvector and its speed at each
state. The selected vectors need not be smooth; regularity of a local
selection is proved where a curve is constructed.
Riemann invariants, genuine nonlinearity and linear degeneracy use the
Fréchet derivatives of the speed and invariant.

A characteristic field is one pair `(λ_k, r_k)` of the notation (24)-(25) of Evans, §11.1.2,
without the strict hyperbolicity that Evans assumes there. Genuine nonlinearity and linear
degeneracy are the definitions (11)-(12) of Evans, §11.2.1. The constancy of the speed along
integral curves of a linearly degenerate field is the first step of the proof of Theorem 3 in
Evans, §11.2.3. Riemann invariants are defined by the condition (2') of Evans, §11.3.1, which
Evans states for systems of two equations, and their constancy along integral curves is (3)
there.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.1.2, notation (24)-(25); §11.2.1, definitions
  (11)-(12); §11.2.3, proof of Theorem 3; §11.3.1, definition of Riemann invariants and
  (2')-(3).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

variable {m : ℕ}

/-- A right characteristic field of a system flux. -/
structure CharacteristicField (flux : ℝ^m → ℝ^m) where
  /-- The flux is differentiable, so `fderiv ℝ flux` is its Jacobian at every state. -/
  flux_differentiable : Differentiable ℝ flux
  /-- Characteristic speed. -/
  speed : ℝ^m → ℝ
  /-- Right eigenvector field. -/
  rightEigenvector : ℝ^m → ℝ^m
  /-- The selected vectors are nonzero eigenvectors of the flux Jacobian. -/
  eigenvector : ∀ state,
    Module.End.HasEigenvector (fderiv ℝ flux state).toLinearMap
      (speed state) (rightEigenvector state)

/-- The autonomous ODE vector field associated with a characteristic field. -/
def CharacteristicField.vectorField
    {flux : ℝ^m → ℝ^m} (C : CharacteristicField flux)
    (_ : ℝ) : ℝ^m → ℝ^m :=
  C.rightEigenvector

/-- A scalar function is a Riemann invariant for a characteristic field when
its differential annihilates that field. -/
def CharacteristicField.IsRiemannInvariant
    {flux : ℝ^m → ℝ^m} (C : CharacteristicField flux)
    (invariant : ℝ^m → ℝ) : Prop :=
  Differentiable ℝ invariant ∧
    ∀ state,
      fderiv ℝ invariant state (C.rightEigenvector state) = 0

/-- The derivative of a Riemann invariant vanishes along an integral curve. -/
theorem CharacteristicField.IsRiemannInvariant.deriv_comp_eq_zero {flux : ℝ^m → ℝ^m}
    {C : CharacteristicField flux} {curve : ℝ → ℝ^m} {invariant : ℝ^m → ℝ} {s : ℝ}
    (hIntegral : IsIntegralCurve curve C.vectorField)
    (hInvariant : C.IsRiemannInvariant invariant) :
    deriv (invariant ∘ curve) s = 0 := by
  rw [fderiv_comp_deriv s (hInvariant.1 (curve s))
    (hIntegral s).differentiableAt, (hIntegral s).deriv]
  exact hInvariant.2 (curve s)

/-- A Riemann invariant is constant along a global integral curve. -/
theorem CharacteristicField.IsRiemannInvariant.eq_on_integralCurve {flux : ℝ^m → ℝ^m}
    {C : CharacteristicField flux} {curve : ℝ → ℝ^m} {invariant : ℝ^m → ℝ}
    (hIntegral : IsIntegralCurve curve C.vectorField) (hInvariant : C.IsRiemannInvariant invariant)
    (s₁ s₂ : ℝ) :
    invariant (curve s₁) = invariant (curve s₂) := by
  have hcurve : Differentiable ℝ curve := fun s ↦ (hIntegral s).differentiableAt
  apply is_const_of_deriv_eq_zero (hInvariant.1.comp hcurve)
  intro s
  exact hInvariant.deriv_comp_eq_zero hIntegral

/-! ## Characteristic-field classes -/

/-- A characteristic field is linearly degenerate when its speed is a
Riemann invariant for its own right eigenvector field. -/
def CharacteristicField.IsLinearlyDegenerate
    {flux : ℝ^m → ℝ^m} (C : CharacteristicField flux) : Prop :=
  C.IsRiemannInvariant C.speed

/-- A characteristic field is genuinely nonlinear at a state when its speed
is differentiable there and has nonzero derivative in the
right-eigenvector direction. -/
def CharacteristicField.IsGenuinelyNonlinearAt
    {flux : ℝ^m → ℝ^m} (C : CharacteristicField flux)
    (state : ℝ^m) : Prop :=
  DifferentiableAt ℝ C.speed state ∧
    fderiv ℝ C.speed state (C.rightEigenvector state) ≠ 0

/-- Genuine nonlinearity at every state. -/
def CharacteristicField.IsGenuinelyNonlinear
    {flux : ℝ^m → ℝ^m} (C : CharacteristicField flux) : Prop :=
  ∀ state, C.IsGenuinelyNonlinearAt state

/-- The characteristic speed is constant along every integral curve of a
linearly degenerate field. -/
theorem CharacteristicField.IsLinearlyDegenerate.speed_eq_on_integralCurve {flux : ℝ^m → ℝ^m}
    {C : CharacteristicField flux} {curve : ℝ → ℝ^m} (hdegenerate : C.IsLinearlyDegenerate)
    (hintegral : IsIntegralCurve curve C.vectorField) (s₁ s₂ : ℝ) :
    C.speed (curve s₁) = C.speed (curve s₂) :=
  hdegenerate.eq_on_integralCurve hintegral s₁ s₂

end PDE.Hyperbolic.ConservationLaw.System
