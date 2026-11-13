/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Kernel.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
import CAS.ExactTactic

/-!
# Time differentiation of the Euclidean heat kernel

For fixed `x` and `t > 0` the heat kernel `Φ(x, t) = (4πt)^(-n/2) exp(-‖x‖² / (4t))` satisfies

`∂ₜΦ = (‖x‖² / (4t²) - n / (2t)) Φ`.

The coefficient is the logarithmic derivative of `t ↦ Φ(x, t)`: the prefactor `(4πt)^(-n/2)`
contributes `-n / (2t)` and the exponential contributes `‖x‖² / (4t²)`. This is the time half
of the verification that `Φ` solves the heat equation (Evans, PDE, §2.3.1); the spatial half is
`laplacian_fundamentalSolutionHeat`, and the two are combined in
`PDE.Parabolic.Heat.Kernel.Equation`.

## Main results

* `fundamentalSolutionHeat_deriv_t`: the closed form of `deriv (fun s => Φ(x, s)) t` for `t > 0`.
* `differentiableAt_fundamentalSolutionHeat_time`: differentiability of `s ↦ Φ(x, s)` at every
  `t > 0`.

## Implementation notes

`fundamentalSolutionHeat` is zero-extended to `t ≤ 0`, so `s ↦ Φ(x, s)` is not differentiable
across `s = 0` in general. Both results are proved by replacing the kernel with its Gaussian
branch on a neighbourhood of `t`, which is legitimate because `t > 0` is an open condition. The
derivative of the branch is checked by the CAS; the factored form of the coefficient uses the one
real-power identity `(4πt)^(-n/2 - 1) = (4πt)^(-n/2) / (4πt)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.1, definition of the fundamental solution.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HeatEquation

open scoped Pointwise
open PDE.Common

variable {n : ℕ}

/-! ## Positive-time differentiation -/

/-- Time derivative of the heat kernel for `t > 0`. Near `t` the kernel agrees with its Gaussian
branch, whose derivative is checked by the CAS; the positivity of `4πt` is the analytic
condition of the real power. -/
theorem fundamentalSolutionHeat_deriv_t (x : ℝ^n) (t : ℝ) (ht : 0 < t) :
    deriv (fun s ↦ fundamentalSolutionHeat (n := n) x s) t =
      (‖x‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)) * fundamentalSolutionHeat (n := n) x t := by
  have hgt_pos : 0 < 4 * Real.pi * t := by positivity
  -- Work with the `t > 0` branch of the definition via an eventual-equality near `t`.
  have hbranch :
      (fun s ↦ fundamentalSolutionHeat (n := n) x s) =ᶠ[nhds t]
        (fun s ↦
          (4 * Real.pi * s) ^ (-(n : ℝ) / 2) * Real.exp (-(‖x‖ ^ 2 / (4 * s)))) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    simp [fundamentalSolutionHeat, not_le_of_gt hs, mul_comm]
  rw [hbranch.deriv_eq, fundamentalSolutionHeat, ite_eq_right (not_le_of_gt ht)]
  cas using hgt_pos

section TimeDerivative

/-- For fixed `x`, the map `s ↦ Φ(x, s)` is differentiable at every positive time. Near `t > 0`
the kernel agrees with the product of the real power `(4πs)^(-n/2)` and `exp(-‖x‖² / (4s))`,
whose differentiability at `t` is checked by the CAS. -/
theorem differentiableAt_fundamentalSolutionHeat_time
    (x : ℝ^n) (t : ℝ) (ht : 0 < t) :
    DifferentiableAt ℝ (fun s ↦ fundamentalSolutionHeat (n := n) x s) t := by
  have hgt_pos : 0 < 4 * Real.pi * t := by positivity
  have hbranch :
      (fun s ↦ fundamentalSolutionHeat (n := n) x s) =ᶠ[nhds t]
        fun s ↦ (4 * Real.pi * s) ^ (-(n : ℝ) / 2) * Real.exp (-(‖x‖ ^ 2 / (4 * s))) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    simp [fundamentalSolutionHeat, not_le_of_gt hs, mul_comm]
  refine hbranch.differentiableAt_iff.2 ?_
  cas using hgt_pos

end TimeDerivative

end HeatEquation
