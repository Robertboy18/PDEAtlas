/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Operators
public import PDE.Parabolic.Heat.InitialValue
import PDE.Parabolic.Heat.ConvolutionSpace.SpatialDerivatives
import PDE.Parabolic.Heat.ConvolutionTime

/-!
# The heat equation for the initial-data convolution

For bounded continuous initial data `g`, the positive-time derivative formulas in time and space
combine to give `uₜ - Δu = 0` for `t > 0`, part (ii) of Evans's §2.3.1(b), Theorem 1. As in his
(10), both derivatives pass through the convolution and the kernel identity `∂ₜΓ = ΔΓ` makes the
residual vanish.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.1(b), Theorem 1 (Solution of initial-value problem) and
  step 1 of its proof, (10), p. 47.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (laplacian)

namespace HeatEquation

open scoped Pointwise
open PDE.Common

variable {n : ℕ}


/-- Part (ii) of Evans's §2.3.1(b), Theorem 1: the initial-data convolution solves `uₜ = Δu`.

For bounded continuous initial data, the time derivative and every second spatial derivative may
be passed through the Gaussian convolution. The pointwise kernel identity `∂ₜΓ = ΔΓ` then gives
`uₜ = Δu` at every positive time. -/
theorem deriv_initialValueSolution_time_eq_laplacian
    (g : ℝ^n → ℝ) (x : ℝ^n)
    (t : ℝ) (ht : 0 < t)
    (hg_cont : Continuous g) (hg_bdd : ∃ M, ∀ y, |g y| ≤ M) :
    deriv (fun s ↦ initialValueSolution (n := n) g x s) t =
      laplacian (n := n)
        (fun x' ↦ initialValueSolution (n := n) g x' t) x := by
  have htime :=
    (hasDerivAt_initialValueSolution_time (n := n) g x t ht hg_cont hg_bdd).deriv
  have hlap := laplacian_heatKernel_convolution (n := n) g x t ht hg_cont hg_bdd
  have hlap' :
      laplacian (n := n)
          (fun x' ↦ initialValueSolution (n := n) g x' t) x =
        ∫ y : ℝ^n,
          g y * laplacian (n := n)
            (fun z : ℝ^n ↦ fundamentalSolutionHeat (n := n) z t)
            (x - y) := by
    simpa [initialValueSolution, not_le_of_gt ht] using hlap
  rw [htime, hlap']
  refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ fun y ↦ ?_)
  change ((‖x - y‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)) *
      fundamentalSolutionHeat (n := n) (x - y) t) * g y =
    g y * laplacian (n := n)
      (fun z : ℝ^n ↦ fundamentalSolutionHeat (n := n) z t) (x - y)
  rw [laplacian_fundamentalSolutionHeat (n := n) (x - y) t ht]
  ring

/-- Evans's (10) in §2.3.1(b): the heat residual of the heat-kernel convolution vanishes at
positive time. -/
theorem initialValueSolution_positive_time_residual_zero
    (g : ℝ^n → ℝ) (x : ℝ^n)
    (t : ℝ) (ht : 0 < t)
    (hg_cont : Continuous g) (hg_bdd : ∃ M, ∀ y, |g y| ≤ M) :
    deriv (fun s ↦ initialValueSolution (n := n) g x s) t -
      laplacian (n := n)
        (fun x' ↦ initialValueSolution (n := n) g x' t) x = 0 := by
  rw [deriv_initialValueSolution_time_eq_laplacian
    (n := n) g x t ht hg_cont hg_bdd]
  ring

end HeatEquation
