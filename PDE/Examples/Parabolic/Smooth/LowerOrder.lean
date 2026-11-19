/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Regularity.Autonomous.Full.Smooth.Compatibility.InitialValues
public import PDE.Spaces.Sobolev.Calculus.Differentiation.LocalSobolev
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# A smooth parabolic example with drift and signed potential

For `Lz = -z'' + z' + xz`, the function `u(t,x) = exp(t) (1 - x²)` solves the
equation `uₜ + Lu = f` with forcing `f = exp(t) (3 - x - x² - x³)`. Every recursively derived
initial value equals the initial profile and vanishes at `x = ±1`. The forcing
itself need not vanish there. The computer algebra system checks all closed-form
derivatives and residuals. The coefficients are smooth on any bounded spatial set, and
the calculation uses no existence or regularity theorem.
-/

@[expose] public noncomputable section

namespace PDE.Examples.Parabolic.Smooth.LowerOrder

open Set PDE.Common SobolevSpace SobolevSpace.GraphSpace.BoundaryRegularity
open PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.Smooth

/-- The principal coefficient is one, the drift is one, and the potential is `x`. -/
def coefficients {Ω : Set (ℝ^1)} (hbounded : Bornology.IsBounded Ω) :
    SmoothFullCoefficients 1 Ω where
  principal := fun _ _ _ ↦ 1
  drift := fun _ _ ↦ 1
  potential := fun x ↦ x 0
  principal_smooth := fun _ _ _ ↦ ContDiffUpToBoundary.const 1
  drift_smooth := fun _ _ ↦ ContDiffUpToBoundary.const 1
  potential_smooth := fun r ↦
    contDiffUpToBoundary_of_contDiffOn isOpen_univ
      (show ContDiff ℝ r (fun x : ℝ^1 ↦ x 0) from by cas).contDiffOn
      hbounded.isCompact_closure (subset_univ _)

/-- A nonstationary smooth function with homogeneous endpoint values. -/
def solution (p : SpaceTime 1) : ℝ :=
  Real.exp (p 0) * (1 - p 1 ^ 2)

/-- The forcing includes the first- and zeroth-order terms of the operator. -/
def forcing (p : SpaceTime 1) : ℝ :=
  Real.exp (p 0) * (3 - p 1 - p 1 ^ 2 - p 1 ^ 3)

/-- The time derivative is the solution itself. -/
theorem partialDeriv_solution (p : SpaceTime 1) :
    (∂[0] solution) p = solution p := by
  cas

/-- Every forcing time derivative equals the original forcing. -/
theorem partialDeriv_forcing (p : SpaceTime 1) :
    (∂[0] forcing) p = forcing p := by
  cas

/-- The solution is jointly smooth of every order. -/
theorem contDiff_solution (r : ℕ) : ContDiff ℝ r solution := by
  cas

/-- The forcing is jointly smooth of every order. -/
theorem contDiff_forcing (r : ℕ) : ContDiff ℝ r forcing := by
  cas

/-- Applied to the solution, the spatial operator gives `exp(t) (2 - x - x³)`; both
lower-order terms contribute. -/
theorem classicalLoad_solution {Ω : Set (ℝ^1)} (hbounded : Bornology.IsBounded Ω)
    (t : ℝ) (x : ℝ^1) :
    (coefficients hbounded).classicalLoad (fun y ↦ solution (timeSpaceCons t y)) x =
      Real.exp t * (2 - x 0 - x 0 ^ 3) := by
  unfold SmoothFullCoefficients.classicalLoad coefficients
  simp only [Fin.sum_univ_one, one_mul]
  unfold solution
  simp only [show (1 : Fin 2) = (0 : Fin 1).succ from rfl,
    timeSpaceCons_zero, timeSpaceCons_succ]
  cas

/-- The function solves `uₜ + Lu = f`, with drift one and the sign-changing potential `x`. -/
theorem equation {Ω : Set (ℝ^1)} (hbounded : Bornology.IsBounded Ω)
    (t : ℝ) (x : ℝ^1) :
    (∂[0] solution) (timeSpaceCons t x) +
        (coefficients hbounded).classicalLoad (fun y ↦ solution (timeSpaceCons t y)) x =
      forcing (timeSpaceCons t x) := by
  rw [partialDeriv_solution, classicalLoad_solution]
  unfold solution forcing
  simp only [show (1 : Fin 2) = (0 : Fin 1).succ from rfl,
    timeSpaceCons_zero, timeSpaceCons_succ]
  cas

/-- The forcing hierarchy consists of the time derivatives of the forcing. -/
theorem iteratedPartialDeriv_forcing (j : ℕ) :
    iteratedPartialDeriv (List.replicate j 0) forcing = forcing := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [List.replicate_succ, iteratedPartialDeriv, ih]
    exact funext partialDeriv_forcing

/-- Every recursively derived initial value, at any initial time `a`, equals the profile
at time `a`. -/
theorem initialValue_eq {Ω : Set (ℝ^1)} (hbounded : Bornology.IsBounded Ω)
    (a : ℝ) (j : ℕ) :
    initialValue (coefficients hbounded)
        (fun k x ↦ iteratedPartialDeriv (List.replicate k 0) forcing (timeSpaceCons a x))
        (fun x ↦ solution (timeSpaceCons a x)) j =
      fun x ↦ solution (timeSpaceCons a x) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [initialValue, ih]
    funext x
    rw [iteratedPartialDeriv_forcing, ← equation hbounded a x, partialDeriv_solution]
    exact add_sub_cancel_right _ _

/-- The initial profile and every derived value vanish at both endpoints. -/
theorem initialValue_eq_zero {Ω : Set (ℝ^1)} (hbounded : Bornology.IsBounded Ω)
    (a : ℝ) (j : ℕ) (x : ℝ^1) (hx : x 0 = -1 ∨ x 0 = 1) :
    initialValue (coefficients hbounded)
        (fun k y ↦ iteratedPartialDeriv (List.replicate k 0) forcing (timeSpaceCons a y))
        (fun y ↦ solution (timeSpaceCons a y)) j x = 0 := by
  rw [initialValue_eq]
  unfold solution
  simp only [show (1 : Fin 2) = (0 : Fin 1).succ from rfl,
    timeSpaceCons_zero, timeSpaceCons_succ]
  rcases hx with hx | hx <;> rw [hx] <;> cas

/-- Homogeneous solution compatibility does not require vanishing forcing at the boundary. -/
theorem forcing_left_endpoint (t : ℝ) (x : ℝ^1) (hx : x 0 = -1) :
    forcing (timeSpaceCons t x) = 4 * Real.exp t := by
  unfold forcing
  simp only [show (1 : Fin 2) = (0 : Fin 1).succ from rfl,
    timeSpaceCons_zero, timeSpaceCons_succ, hx]
  cas

end PDE.Examples.Parabolic.Smooth.LowerOrder
