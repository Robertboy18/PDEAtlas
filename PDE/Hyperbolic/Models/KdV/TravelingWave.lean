/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.KdV.Equation
public import PDE.Representations.Similarity.Pointwise
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Nonlinear traveling waves for KdV

For a `C³` profile, the traveling wave `u(t,x) = f(x - c t)` solves KdV precisely
when `b f''' + (a f - c) f' = 0`. We compute its coordinate derivatives.
We also obtain solutions from the integrated profile equation
`b f'' = c f - a f² / 2 + A` by differentiating it with Mathlib's scalar calculus.
The integration constant is arbitrary.
-/

@[expose] public section

namespace KdVEquation

open PDE.Representations.Similarity

/-- The spatial derivative of a differentiable traveling wave is its translated derivative. -/
theorem travelingWave1D_space_derivative {profile : ℝ → ℝ}
    (hprofile : Differentiable ℝ profile) (speed : ℝ) :
    (∂[(1 : Fin 2)] (travelingWave1D profile speed)) = travelingWave1D (deriv profile) speed := by
  funext p
  unfold travelingWave1D
  rw [PDE.partialDeriv_comp_real (1 : Fin 2) (hprofile _) (by cas)]
  have hphase : (∂[(1 : Fin 2)] (fun q : ℝ^2 ↦ q 1 - speed * q 0)) p = 1 := by
    cas
  rw [hphase, one_mul]

/-- The time derivative of a traveling wave is minus its speed times the profile derivative. -/
theorem travelingWave1D_time_derivative {profile : ℝ → ℝ}
    (hprofile : Differentiable ℝ profile) (speed : ℝ) (p : ℝ^2) :
    (∂[(0 : Fin 2)] (travelingWave1D profile speed)) p =
      -speed * deriv profile (p 1 - speed * p 0) := by
  unfold travelingWave1D
  rw [PDE.partialDeriv_comp_real (0 : Fin 2) (hprofile _) (by cas)]
  have hphase : (∂[(0 : Fin 2)] (fun q : ℝ^2 ↦ q 1 - speed * q 0)) p = -speed := by
    cas
  rw [hphase]

/-- A `C³` traveling wave has the expected third spatial derivative. -/
theorem travelingWave1D_third_space_derivative {profile : ℝ → ℝ}
    (hprofile : ContDiff ℝ 3 profile) (speed : ℝ) :
    (∂[(1 : Fin 2)] (∂[(1 : Fin 2)] (∂[(1 : Fin 2)] (travelingWave1D profile speed)))) =
      travelingWave1D (deriv (deriv (deriv profile))) speed := by
  have hfirst : ContDiff ℝ 2 (deriv profile) := hprofile.deriv'
  have hsecond : ContDiff ℝ 1 (deriv (deriv profile)) := hfirst.deriv'
  rw [travelingWave1D_space_derivative (hprofile.differentiable (by norm_num)),
    travelingWave1D_space_derivative (hfirst.differentiable (by norm_num)),
    travelingWave1D_space_derivative (hsecond.differentiable (by norm_num))]

/-- The KdV PDE reduces to its third-order nonlinear profile ODE. -/
theorem residual_travelingWave1D {profile : ℝ → ℝ}
    (hprofile : ContDiff ℝ 3 profile) (nonlinearity dispersion speed : ℝ) (p : ℝ^2) :
    residual nonlinearity dispersion (travelingWave1D profile speed) p =
      dispersion * deriv (deriv (deriv profile)) (p 1 - speed * p 0) +
      (nonlinearity * profile (p 1 - speed * p 0) - speed) * deriv profile (p 1 - speed * p 0) := by
  unfold residual
  rw [travelingWave1D_time_derivative (hprofile.differentiable (by norm_num)),
    travelingWave1D_third_space_derivative hprofile,
    travelingWave1D_space_derivative (hprofile.differentiable (by norm_num))]
  unfold travelingWave1D
  ring

/-- The nonlinear profile ODE is necessary and sufficient for a `C³` traveling wave
to be a classical KdV solution on all spacetime. -/
theorem travelingWave1D_isSolution_iff {profile : ℝ → ℝ}
    (hprofile : ContDiff ℝ 3 profile) (nonlinearity dispersion speed : ℝ) :
    IsSolution nonlinearity dispersion (travelingWave1D profile speed) ↔ ∀ z, dispersion * deriv
      (deriv (deriv profile)) z + (nonlinearity * profile z - speed) * deriv profile z = 0 := by
  constructor
  · intro h z
    have hz := h.equation !₂[0, z]
    simpa [residual_travelingWave1D hprofile] using hz
  · intro h
    refine ⟨?_, fun p ↦ (residual_travelingWave1D hprofile _ _ _ p).trans (h _)⟩
    unfold travelingWave1D
    exact hprofile.comp (by fun_prop)

/-- Differentiating the integrated profile equation produces the third-order ODE and hence a
classical traveling-wave solution. -/
theorem travelingWave1D_isSolution_of_profile_ode {profile : ℝ → ℝ}
    (hprofile : ContDiff ℝ 3 profile) (nonlinearity dispersion speed constant : ℝ)
    (hode : ∀ z, dispersion * deriv (deriv profile) z =
      speed * profile z - nonlinearity / 2 * profile z ^ 2 + constant) :
    IsSolution nonlinearity dispersion (travelingWave1D profile speed) := by
  refine (travelingWave1D_isSolution_iff hprofile _ _ _).2 fun z ↦ ?_
  have hfirst : ContDiff ℝ 2 (deriv profile) := hprofile.deriv'
  have hsecond : ContDiff ℝ 1 (deriv (deriv profile)) := hfirst.deriv'
  have hp := (hprofile.differentiable (by norm_num) z).hasDerivAt
  have hleft := (hsecond.differentiable (by norm_num) z).hasDerivAt.const_mul dispersion
  have hright := ((hp.const_mul speed).sub
    ((hp.pow 2).const_mul (nonlinearity / 2))).add_const constant
  have heq := hleft.deriv.symm.trans
    ((congrArg (fun f : ℝ → ℝ ↦ deriv f z) (funext hode)).trans hright.deriv)
  dsimp at heq
  nlinarith [heq]

end KdVEquation
