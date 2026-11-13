/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean

/-!
# Basic properties of the Euclidean heat kernel

The Gaussian heat kernel `fundamentalSolutionHeat` and its shifted form, both extended by zero to
`t ≤ 0`, and positivity of the kernel at positive time.

For `t > 0` this is the fundamental solution `Φ` of Evans's §2.3.1(a). Evans sets `Φ = 0` for
`t < 0` and leaves `t = 0` out of the definition; the value zero there makes the function total.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.1(a), the definition of the fundamental solution, p. 46.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HeatEquation

open scoped Pointwise
open PDE.Common

variable {n : ℕ}

/-! ## Definition and positivity -/

/-- Heat kernel, zero-extended to `t ≤ 0`.

For `t > 0` this is `(4πt)^(-n/2) exp(-‖x‖² / (4t))`. -/
noncomputable def fundamentalSolutionHeat (x : ℝ^n) (t : ℝ) : ℝ :=
  if t ≤ 0 then 0
  else (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-(‖x‖ ^ 2 / (4 * t)))

/-- Shifted heat kernel `Γ(x-y,t-s)`, with the same zero-extension convention when `t ≤ s`. -/
noncomputable def shiftedFundamentalSolutionHeat
    (x y : ℝ^n) (t s : ℝ) : ℝ :=
  fundamentalSolutionHeat (x - y) (t - s)

/-- The heat kernel is strictly positive at every positive time. -/
theorem fundamentalSolutionHeat_pos (x : ℝ^n) (t : ℝ) (ht : 0 < t) :
    0 < fundamentalSolutionHeat x t := by
  unfold fundamentalSolutionHeat
  rw [ite_eq_right (not_le.mpr ht)]
  apply mul_pos
  · apply Real.rpow_pos_of_pos
    apply mul_pos
    · apply mul_pos
      · norm_num
      · exact Real.pi_pos
    · exact ht
  · exact Real.exp_pos _

end HeatEquation
