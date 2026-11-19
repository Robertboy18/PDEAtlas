/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Control.DynamicProgramming
public import PDE.Examples.Hyperbolic.HamiltonJacobi.Control.UnattainedMinimum
public import PDE.Hyperbolic.HamiltonJacobi.Control.MeasurableValue

/-!
# Dynamic programming with a discontinuous control cost

The control `a ∈ [0, 1]` is the velocity. The running cost is `endpointJumpCost`,
which equals `a` for `a > 0` and jumps up to one at `a = 0`, and the terminal cost is
the absolute value. Dynamic programming holds at every cut `a ≤ c ≤ b`, endpoints
included, although no control minimizes the pointwise Hamiltonian at covector zero
(`endpointJumpCost_has_no_minimum`).
-/

@[expose] public noncomputable section

open Function MeasureTheory Set
open HamiltonJacobi PDE.Examples.HamiltonJacobi.Control

namespace PDE.Examples.HamiltonJacobi.Control.JumpDynamics

/-- The velocity is the control, independently of the state. -/
def velocity (_ : ℝ) (a : Icc (0 : ℝ) 1) : ℝ := a

/-- The dynamics are jointly continuous. -/
theorem continuous_velocity : Continuous (fun p : ℝ × Icc (0 : ℝ) 1 ↦ velocity p.1 p.2) :=
  continuous_subtype_val.comp continuous_snd

/-- The dynamics have zero state-Lipschitz constant. -/
theorem lipschitz_velocity (a : Icc (0 : ℝ) 1) : LipschitzWith 0 (fun x ↦ velocity x a) :=
  LipschitzWith.const _

/-- The dynamics have speed at most one. -/
theorem norm_velocity_le (x : ℝ) (a : Icc (0 : ℝ) 1) : ‖velocity x a‖ ≤ (1 : NNReal) := by
  simpa only [velocity, Real.norm_eq_abs, abs_of_nonneg a.property.1, NNReal.coe_one]
    using a.property.2

local notation "X" => controlResponse velocity continuous_velocity 0 1
  lipschitz_velocity norm_velocity_le
local notation "R" => controlRunningCost velocity continuous_velocity 0 1
  lipschitz_velocity norm_velocity_le endpointJumpCost
local notation "V" => controlValue velocity continuous_velocity 0 1
  lipschitz_velocity norm_velocity_le endpointJumpCost

/-- The jump cost is integrable along the trajectory of every measurable control. -/
theorem intervalIntegrable_jumpCost {a b : ℝ} (hab : a ≤ b)
    (α : ControlOn (Icc (0 : ℝ) 1) a b) (x : ℝ) :
    IntervalIntegrable (fun t ↦ endpointJumpCost (X hab α x t) (α.1 t)) volume a b := by
  exact HamiltonJacobi.intervalIntegrable_control_runningCost
    velocity continuous_velocity 0 1 lipschitz_velocity norm_velocity_le
    endpointJumpCost measurable_endpointJumpCost 1 abs_jumpCost_le hab α x

/-- Dynamic programming for the jump cost at every cut. -/
theorem dynamic_programming_jumpCost {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) (x : ℝ) :
    V abs (hac.trans hcb) x =
      sInf (range (fun α : ControlOn (Icc (0 : ℝ) 1) a c ↦
        R hac α x + V abs hcb (X hac α x c))) := by
  let : Nonempty (Icc (0 : ℝ) 1) := ⟨⟨0, le_rfl, zero_le_one⟩⟩
  exact HamiltonJacobi.control_value_dynamic_programming
    velocity continuous_velocity 0 1 lipschitz_velocity norm_velocity_le
    endpointJumpCost measurable_endpointJumpCost 1 abs_jumpCost_le abs
    ⟨0, by rintro _ ⟨y, rfl⟩; exact abs_nonneg y⟩ hac hcb x

/-- In the dynamic programming identity the prefix controls may be taken Borel
measurable. -/
theorem dynamic_programming_jumpCost_measurable {a b c : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b) (x : ℝ) :
    V abs (hac.trans hcb) x =
      sInf (range (fun α : {α : ℝ → Icc (0 : ℝ) 1 // Measurable α} ↦
        let β : ControlOn (Icc (0 : ℝ) 1) a c :=
          ⟨α.1, α.2.stronglyMeasurable.aestronglyMeasurable⟩
        R hac β x + V abs hcb (X hac β x c))) := by
  rw [dynamic_programming_jumpCost hac hcb x]
  exact congrArg sInf (range_control_cost_eq_range_measurable
    velocity continuous_velocity 0 1 lipschitz_velocity norm_velocity_le
    endpointJumpCost (V abs hcb) hac x)

end PDE.Examples.HamiltonJacobi.Control.JumpDynamics
