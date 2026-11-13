/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Control.InitialValue
public import PDE.Examples.Hyperbolic.HamiltonJacobi.Control.UnattainedMinimum

/-!
# A viscosity solution whose Hamiltonian infimum is not attained

With control space `[0, 1]`, zero dynamics and the running cost `endpointJumpCost`,
no control attains the infimum defining the Hamiltonian. The control value still
solves the initial-value problem for that infimum, which is the zero Hamiltonian.
-/

@[expose] public noncomputable section

open Set
open HamiltonJacobi

namespace PDE.Examples.HamiltonJacobi.Control

/-- With zero dynamics and zero terminal cost, the control value of the jump cost is a
viscosity solution of the initial-value problem with zero Hamiltonian and zero datum. -/
theorem jumpCost_value_isViscosityInitialSolution :
    IsViscosityInitialSolution (fun _ _ : ℝ ↦ 0) (fun _ : ℝ ↦ 0)
      (controlInitialValue (fun _ : ℝ ↦ fun _ : Icc (0 : ℝ) 1 ↦ (0 : ℝ))
        continuous_const 0 0 (fun _ ↦ LipschitzWith.const 0) (fun _ _ ↦ by simp)
        endpointJumpCost (fun _ ↦ 0)) := by
  have hsol := isViscosityInitialSolution_controlInitialValue
    (fun _ : ℝ ↦ fun _ : Icc (0 : ℝ) 1 ↦ (0 : ℝ)) continuous_const
    0 0 (fun _ ↦ LipschitzWith.const 0) (fun _ _ ↦ by simp)
    endpointJumpCost measurable_endpointJumpCost 1 0 abs_jumpCost_le endpointJumpCost_lipschitz
    (fun _ ↦ 0) 0 0 (fun _ ↦ by simp) (LipschitzWith.const 0)
  have hH : controlHamiltonian
      (fun _ : ℝ ↦ fun _ : Icc (0 : ℝ) 1 ↦ (0 : ℝ)) endpointJumpCost =
      fun _ _ ↦ (0 : ℝ) := by
    funext p x
    exact controlHamiltonian_endpointJumpCost p x
  simpa only [hH] using hsol

end PDE.Examples.HamiltonJacobi.Control
