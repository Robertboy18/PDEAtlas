/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.DynamicRescaling.Scales
public import PDE.Analysis.Evolution.ODE.PhysicalClock

/-!
# Recovering rescaled time from physical time

The clock constructed from continuous rates is strictly increasing. We choose
its inverse on its range and use the inverse function theorem to differentiate
it there. Only values on the range of the clock are used. In particular, if the
physical clock has a finite supremum, that supremum is not in its range.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace DeGregorio.DynamicRescalingData

/-- Rescaled time at a point in the physical clock's range. The total function
has unspecified values off that range. -/
def rescaledTime (data : DynamicRescalingData) : ℝ → ℝ :=
  Function.invFun data.physicalTime

/-- The integral clock `τ ↦ ∫₀^τ Cω` is strictly increasing on all of `ℝ`. -/
theorem physicalTime_ofRates_strictMono
    (cl : ℝ → ℝ) {cw : ℝ → ℝ} (hcw : Continuous cw) :
    StrictMono (ofRates cl cw).physicalTime :=
  strictMono_of_hasDerivAt_pos
    (fun τ ↦ (physicalTime_ofRates_hasStrictDerivAt cl hcw τ).hasDerivAt)
    (vorticityScale_ofRates_pos cl cw)

/-- Inverting the constructed clock recovers every rescaled time. -/
@[simp]
theorem rescaledTime_ofRates_physicalTime
    (cl : ℝ → ℝ) {cw : ℝ → ℝ} (hcw : Continuous cw) (τ : ℝ) :
    (ofRates cl cw).rescaledTime ((ofRates cl cw).physicalTime τ) = τ :=
  PDE.Analysis.Evolution.ODE.leftInverse_invFun_of_hasDerivAt_pos
    (fun s ↦ (physicalTime_ofRates_hasStrictDerivAt cl hcw s).hasDerivAt)
    (vorticityScale_ofRates_pos cl cw) τ

/-- The inverse clock preserves the initial time. -/
@[simp]
theorem rescaledTime_ofRates_zero
    (cl : ℝ → ℝ) {cw : ℝ → ℝ} (hcw : Continuous cw) :
    (ofRates cl cw).rescaledTime 0 = 0 := by
  simpa only [physicalTime_ofRates_zero] using
    rescaledTime_ofRates_physicalTime cl hcw 0

/-- On the clock's range, the inverse clock has strict derivative `Cω(τ)⁻¹` at `t(τ)`. -/
theorem rescaledTime_ofRates_hasStrictDerivAt
    (cl : ℝ → ℝ) {cw : ℝ → ℝ} (hcw : Continuous cw) (τ : ℝ) :
    HasStrictDerivAt (ofRates cl cw).rescaledTime
      ((ofRates cl cw).vorticityScale τ)⁻¹ ((ofRates cl cw).physicalTime τ) :=
  PDE.Analysis.Evolution.ODE.hasStrictDerivAt_invFun_of_hasStrictDerivAt_pos
    (physicalTime_ofRates_hasStrictDerivAt cl hcw) (vorticityScale_ofRates_pos cl cw) τ

end DeGregorio.DynamicRescalingData
