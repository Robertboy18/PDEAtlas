/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.Instances.Real.Lemmas
import CAS.ExactTactic

/-!
# Scaling a seventh-power reaction on shrinking cylinders

With spatial volume proportional to `s^18` and time length `k*s^9`, an initial
level `1/(2*s^2)` gives a reaction-square lower bound proportional to `1/s`.
The positive coefficient remains after absorbing the squared trace cost.
-/

@[expose] public section

open Filter
open scoped Topology

namespace PDE.Analysis

/-- The powers in the shrinking-cylinder estimate leave exactly one inverse
power of the spatial scale. -/
theorem seventh_power_cylinder_lower_bound_eq
    (c K k : ℝ) {s : ℝ} (hs : s ≠ 0) :
    ((1 / (2 * s ^ 2)) ^ 7) ^ 2 *
        (k * s ^ 9 * (c * s ^ 18) - K ^ 2 * (k * s ^ 9) ^ 3) =
      (k * (c - K ^ 2 * k ^ 2) / 16384) / s := by
  cas using hs

/-- After absorbing the trace cost, the reaction-square lower bound diverges
as the cylinder shrinks to the initial spatial singularity. -/
theorem tendsto_seventh_power_cylinder_lower_bound
    {c K k : ℝ} (hk : 0 < k) (hcost : K ^ 2 * k ^ 2 < c) :
    Tendsto (fun s : ℝ ↦ ((1 / (2 * s ^ 2)) ^ 7) ^ 2 *
      (k * s ^ 9 * (c * s ^ 18) - K ^ 2 * (k * s ^ 9) ^ 3))
      (𝓝[>] 0) atTop := by
  have hc : 0 < k * (c - K ^ 2 * k ^ 2) / 16384 :=
    div_pos (mul_pos hk (sub_pos.mpr hcost)) (by norm_num)
  have hlim := tendsto_inv_nhdsGT_zero.const_mul_atTop hc
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [seventh_power_cylinder_lower_bound_eq c K k hs.ne']
  exact (div_eq_mul_inv _ _).symm

end PDE.Analysis
