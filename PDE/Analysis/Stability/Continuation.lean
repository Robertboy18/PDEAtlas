/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Stability.ModulatedNonlinear
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Positivity.Finset
import PDE.Analysis.Evolution.ODE.FiniteContinuation

/-!
# Stable continuation from invariant local solutions

A nonlinear energy estimate gives an inward-pointing norm ball, and the finite-continuation
theorem then extends solutions. A local well-posedness theorem for the model must show that
local trajectories exist and preserve that ball; this hypothesis is
`UniformLocalInvariantEvolution`. Given it, local trajectories glue across an arbitrary finite
partition, with no global-existence assumption.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Stability

open scoped RealInnerProductSpace

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A positive radius at which the validated nonlinear energy field points strictly inward. -/
abbrev TrappingBallCertificate
    (estimate : ModulatedEnergyEstimate H) :=
  {radius : ℝ //
    0 < radius ∧
      estimate.residualBound <
        estimate.effectiveDecay radius * radius}

namespace TrappingBallCertificate

variable {estimate : ModulatedEnergyEstimate H}

/-- Radius of the perturbation ball. -/
abbrev radius (certificate : TrappingBallCertificate estimate) : ℝ :=
  certificate.1

/-- The trapping radius is positive. -/
theorem radius_pos (certificate : TrappingBallCertificate estimate) :
    0 < certificate.radius :=
  certificate.2.1

/-- Residual forcing is smaller than the available decay at the boundary. -/
theorem residual_margin (certificate : TrappingBallCertificate estimate) :
    estimate.residualBound <
      estimate.effectiveDecay certificate.radius * certificate.radius :=
  certificate.2.2

/-- The certificate proves strict inward pointing on every boundary state. -/
theorem inward_on_boundary
    (certificate : TrappingBallCertificate estimate)
    {perturbation : H}
    (hboundary : ‖perturbation‖ = certificate.radius) :
    ⟪estimate.vectorField perturbation, perturbation⟫ < 0 :=
  estimate.pairing_vectorField_lt_zero_on_sphere
    certificate.residual_margin hboundary

end TrappingBallCertificate

/-- Uniform local solutions that preserve a certified perturbation ball.

The preservation field is where strict inward pointing and local well-posedness of the model
give viability of the closed ball. The trajectory is required only on one interval of the fixed
step length. The step is not required to be positive; at `step = 0` the structure carries no
content and the continuation theorems below reach only the trivial interval. -/
structure UniformLocalInvariantEvolution
    (estimate : ModulatedEnergyEstimate H)
    (certificate : TrappingBallCertificate estimate) where
  /-- Uniform continuation step. -/
  step : NNReal
  /-- Every state in the certified ball starts a local solution that remains in the ball. -/
  local_solution :
    ∀ (start : ℝ) (initial : H),
      ‖initial‖ ≤ certificate.radius →
        ∃ trajectory : ℝ → H,
          trajectory start = initial ∧
          (∀ time ∈ Set.Icc start (start + (step : ℝ)),
            HasDerivWithinAt trajectory
              (estimate.vectorField (trajectory time))
              (Set.Icc start (start + (step : ℝ))) time) ∧
          ∀ time ∈ Set.Icc start (start + (step : ℝ)),
            ‖trajectory time‖ ≤ certificate.radius

namespace UniformLocalInvariantEvolution

variable {estimate : ModulatedEnergyEstimate H}
  {certificate : TrappingBallCertificate estimate}

/-- The continuation step is nonnegative. -/
theorem step_nonneg
    (evolution : UniformLocalInvariantEvolution estimate certificate) :
    0 ≤ (evolution.step : ℝ) :=
  NNReal.coe_nonneg evolution.step

/-- Glue uniformly available invariant local solutions over a finite arithmetic partition. -/
theorem exists_trajectory_on_Icc
    (evolution : UniformLocalInvariantEvolution estimate certificate)
    {a b : ℝ}
    (cells : ℕ) (hcells : 0 < cells)
    (hendpoint : a + (cells : ℝ) * (evolution.step : ℝ) = b)
    (initial : H)
    (hinitial : ‖initial‖ ≤ certificate.radius) :
    ∃ trajectory : ℝ → H,
      trajectory a = initial ∧
      (∀ time ∈ Set.Icc a b,
        HasDerivWithinAt trajectory
          (estimate.vectorField (trajectory time))
          (Set.Icc a b) time) ∧
      ∀ time ∈ Set.Icc a b,
        ‖trajectory time‖ ≤ certificate.radius := by
  obtain ⟨trajectory, hinitialValue, hequation, hbound⟩ :=
    PDE.Analysis.Evolution.exists_ode_solution_Icc_of_partition_of_energy_bound
      (fun _time ↦ estimate.vectorField)
      (fun state : H ↦ ‖state‖)
      evolution.step_nonneg cells hcells hendpoint initial hinitial
      (by
        intro cell hcell state hstate
        let start : ℝ := a + (cell : ℝ) * (evolution.step : ℝ)
        obtain ⟨trajectory, hinitialLocal, hequationLocal, hboundLocal⟩ :=
          evolution.local_solution start state hstate
        refine ⟨trajectory, ?_, ?_, ?_⟩
        · simpa [start] using hinitialLocal
        · intro time htime
          have htimeLocal :
              time ∈ Set.Icc start (start + (evolution.step : ℝ)) := by
            simpa [start, Nat.cast_add, add_mul, add_assoc] using htime
          have hderivative := hequationLocal time htimeLocal
          simpa [start, Nat.cast_add, add_mul, add_assoc] using hderivative
        · intro time htime
          have htimeLocal :
              time ∈ Set.Icc start (start + (evolution.step : ℝ)) := by
            simpa [start, Nat.cast_add, add_mul, add_assoc] using htime
          exact hboundLocal time htimeLocal)
  exact ⟨trajectory, hinitialValue, by
      intro time htime
      simpa using hequation time htime, hbound⟩

end UniformLocalInvariantEvolution

end PDE.Analysis.Stability
