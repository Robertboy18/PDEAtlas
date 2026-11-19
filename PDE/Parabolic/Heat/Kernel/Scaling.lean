/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Kernel.Basic
import CAS.ExactTactic

/-!
# Parabolic scaling of the heat kernel

The heat kernel is invariant under parabolic scaling: `Γ(a • x, a²t) = a⁻ⁿ Γ(x, t)` for `a, t > 0`.
Evans's §2.3.1(a) derives the fundamental solution by looking for solutions invariant under the
dilation scaling `u(x, t) ↦ λ^α u(λ^β x, λt)`; the kernel is the one with `α = n/2` and `β = 1/2`,
and the identity is that invariance with `λ = a²`. His §4.2.2 repeats the computation for the porous
medium equation.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.1(a), the dilation scaling and (4)-(7), pp. 45-46, and
  §4.2.2, (28), p. 185.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HeatEquation

/-- The heat kernel obeys the parabolic scaling
`Γ(a • x, a²t) = a⁻ⁿ Γ(x, t)` for positive `a` and `t`. -/
theorem fundamentalSolutionHeat_scaling
    {n : ℕ} (x : ℝ^n) (t a : ℝ) (ht : 0 < t) (ha : 0 < a) :
    fundamentalSolutionHeat (n := n) (a • x) (a ^ 2 * t) =
      a ^ (-(n : ℝ)) * fundamentalSolutionHeat (n := n) x t := by
  have ha2 : 0 < a ^ (2 : ℕ) := by
    simpa [pow_two] using (mul_pos ha ha)
  have ht' : 0 < a ^ 2 * t := mul_pos ha2 ht
  rw [fundamentalSolutionHeat, fundamentalSolutionHeat,
    ite_eq_right (not_le_of_gt ht'), ite_eq_right (not_le_of_gt ht)]
  have hnormsq : ‖a • x‖ ^ 2 = a ^ 2 * ‖x‖ ^ 2 := by
    have h := congrArg (fun r : ℝ ↦ r ^ 2) (norm_smul a x)
    simpa [Real.norm_eq_abs, abs_of_pos ha, pow_two, mul_assoc, mul_left_comm, mul_comm] using h
  have hquot : ‖a • x‖ ^ 2 / (4 * (a ^ 2 * t)) = ‖x‖ ^ 2 / (4 * t) := by
    rw [hnormsq]
    cas
  have hpref :
      (4 * Real.pi * (a ^ 2 * t)) ^ (-(n : ℝ) / 2) =
        a ^ (-(n : ℝ)) * (4 * Real.pi * t) ^ (-(n : ℝ) / 2) := by
    cas
  rw [hpref]
  have hexp :
      Real.exp (-(‖a • x‖ ^ 2 / (4 * (a ^ 2 * t)))) =
        Real.exp (-(‖x‖ ^ 2 / (4 * t))) := by
    simp [hquot]
  rw [hexp]
  simp [mul_assoc]

end HeatEquation
