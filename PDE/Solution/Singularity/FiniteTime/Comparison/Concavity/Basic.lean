/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Differential inequalities for the concavity method

The local scalar calculations behind the concavity method.
If `I' = P` and `I` is positive, the concavity inequality

`(1 + a) P² ≤ I (P' - b)`

implies the Riccati inequality `a (P / I)² ≤ (P / I)'` when `b ≥ 0`.
The forcing bound `b ≤ P'` follows when `a ≥ 0`; this second implication
does not require `I' = P`. These are steps of the concavity method of Levine's proof of
Theorem I (1974); `Concavity.RightEndpoint` explains the correspondence.

## References

* H. A. Levine, "Instability and nonexistence of global solutions to nonlinear wave equations
  of the form `P u_tt = -A u + F(u)`", *Trans. Amer. Math. Soc.* 192 (1974), 1-21, proof of
  Theorem I, (II-2)-(II-4).
  <https://doi.org/10.1090/S0002-9947-1974-0344697-2>
-/

@[expose] public section

namespace PDE.Solution.Singularity.FiniteTime.Concavity

/-- Differentiate the logarithmic momentum `P / I` when the mass satisfies
`I' = P`. -/
theorem deriv_momentum_div_mass
    {I P : ℝ → ℝ} {t : ℝ}
    (hI : HasDerivAt I (P t) t)
    (hP : DifferentiableAt ℝ P t)
    (hpos : 0 < I t) :
    deriv (fun s ↦ P s / I s) t =
      (deriv P t * I t - P t * P t) / I t ^ 2 := by
  rw [deriv_fun_div hP hI.differentiableAt hpos.ne', hI.deriv]

/-- With nonnegative forcing coefficient `b`, the concavity inequality implies
the Riccati lower bound for the derivative of the logarithmic momentum `P / I`. -/
theorem mul_sq_le_deriv_momentum_div_mass
    {I P : ℝ → ℝ} {a b t : ℝ}
    (hb : 0 ≤ b)
    (hI : HasDerivAt I (P t) t)
    (hP : DifferentiableAt ℝ P t)
    (hpos : 0 < I t)
    (hconcavity :
      (1 + a) * P t ^ 2 ≤ I t * (deriv P t - b)) :
    a * (P t / I t) ^ 2 ≤ deriv (fun s ↦ P s / I s) t := by
  rw [deriv_momentum_div_mass hI hP hpos, div_pow, ← mul_div_assoc]
  apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hpos)).2
  have hbI : 0 ≤ I t * b := mul_nonneg hpos.le hb
  nlinarith [hconcavity]

/-- For `a ≥ 0` and positive mass, the concavity inequality forces the momentum
derivative to dominate the forcing coefficient. -/
theorem le_momentum_deriv_of_concavity
    {I P : ℝ → ℝ} {a b t : ℝ}
    (ha : 0 ≤ a) (hpos : 0 < I t)
    (hconcavity :
      (1 + a) * P t ^ 2 ≤ I t * (deriv P t - b)) :
    b ≤ deriv P t := by
  have hleft : 0 ≤ (1 + a) * P t ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have hright : 0 ≤ I t * (deriv P t - b) :=
    hleft.trans hconcavity
  nlinarith

end PDE.Solution.Singularity.FiniteTime.Concavity
