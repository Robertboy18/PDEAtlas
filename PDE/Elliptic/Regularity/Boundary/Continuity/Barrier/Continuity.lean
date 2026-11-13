/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.Continuity.Barrier.Estimates

/-!
# Continuity of the angular barrier at its vertex

The separate terms in the formula contain negative powers when the radial
exponent is small. Their angular factors nevertheless give a barrier bounded
by a constant times `r^a`. For `a > 0` this proves continuity at the vertex.
-/

@[expose] public noncomputable section

namespace PDE.Elliptic.BoundaryContinuity

open Filter
open scoped Topology

variable {n : ℕ}

/-- The value at the singular vertex is zero for a positive radial exponent. -/
@[simp]
theorem angularPowerBarrier_zero {a : ℝ} (ha : 0 < a) (N : ℝ^n) :
    angularPowerBarrier a N 0 = 0 := by
  simp [angularPowerBarrier, Real.zero_rpow ha.ne']

/-- The angular barrier is continuous on the whole ambient space, including
its vertex. No differentiability at the vertex is asserted. -/
theorem continuous_angularPowerBarrier {a : ℝ} (ha : 0 < a)
    {N : ℝ^n} (hN : ‖N‖ = 1) :
    Continuous (angularPowerBarrier a N) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    rw [ContinuousAt, angularPowerBarrier_zero ha]
    apply squeeze_zero_norm (a := fun y : ℝ^n ↦ 3 * ‖y‖ ^ a)
    · intro y
      by_cases hy : y = 0
      · subst y
        simp [angularPowerBarrier_zero ha, Real.zero_rpow ha.ne']
      · have hb := angularPowerBarrier_bounds a hN hy
        have hb0 : 0 ≤ angularPowerBarrier a N y :=
          (mul_nonneg (by norm_num) (Real.rpow_nonneg (norm_nonneg _) _)).trans hb.1
        simpa only [Real.norm_eq_abs, abs_of_nonneg hb0] using hb.2
    · have hcont : Continuous (fun y : ℝ^n ↦ 3 * ‖y‖ ^ a) :=
        continuous_const.mul (continuous_norm.rpow_const (fun _ ↦ Or.inr ha.le))
      simpa only [norm_zero, Real.zero_rpow ha.ne', mul_zero] using hcont.tendsto 0
  · exact (angularPowerBarrier_contDiffAt a N (k := 1) hx).continuousAt

end PDE.Elliptic.BoundaryContinuity
