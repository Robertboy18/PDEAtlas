/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS
public import PDE.Symbolic.Command.CAS.PDESolve

/-!
# Transport, heat and wave equations in one space dimension

`#cas [pdesolve u t x, conditions] equation` solves the classical linear problems whose solution is
a formula: transport by characteristics, the heat and wave equations on `[0, L]` with zero boundary
values by separation of variables for finite sine sums as data, and the wave equation on the line by
d'Alembert's formula. The commands at the end of this file run in the build, each inside
`#guard_msgs`, which checks its report.

The outputs are `sin (x - 2t)`; `e ^ (-t) e ^ (x + t)`; `e ^ (-2t) sin x + 3 e ^ (-8t) sin (2x)`;
`2 e ^ (-π ^ 2 t) sin (π x) - e ^ (-9 π ^ 2 t) sin (3 π x)`; `cos (2 π t) sin (π x)`;
`cos t sin x + sin (2t) sin (2x) / 2`; `(cos (x + t) + cos (x - t)) / 2`; and
`(e ^ (-(x + 3t) ^ 2) + e ^ (-(x - 3t) ^ 2)) / 2 + ((x + 3t) ^ 2 / 2 - (x - 3t) ^ 2 / 2) / 6`. The
first theorem is

`∀ (u : ℝ → ℝ → ℝ), Differentiable ℝ (Function.uncurry u) → (((∀ (t x : ℝ), deriv (fun s => u s x)`
`t + 2 * deriv (fun y => u t y) x = 0) ∧ ∀ (x : ℝ), u 0 x = Real.sin x) ↔ ∀ (t x : ℝ), u t x =`
`Real.sin (x - 2 * t))`,

and the third is the conjunction of `∀ (u : ℝ → ℝ → ℝ), (∀ (t x : ℝ), u t x =`
`Real.exp (-(2 * t)) * Real.sin x + 3 * Real.exp (-(8 * t)) * Real.sin (2 * x)) → (∀ (t x : ℝ),`
`deriv (fun s => u s x) t = 2 * deriv (fun y => deriv (fun r => u t r) y) x) ∧ (∀ (t : ℝ),`
`u t 0 = 0) ∧ (∀ (t : ℝ), u t Real.pi = 0) ∧ ∀ (x : ℝ), u 0 x = Real.sin x + 3 * Real.sin (2 * x)`
and of the uniqueness `∀ (u : ℝ → ℝ → ℝ), ContDiff ℝ 2 (Function.uncurry u) → (∀ t > 0,`
`∀ x ∈ Set.Ioo 0 Real.pi, …) → (∀ t ≥ 0, u t 0 = 0) → (∀ t ≥ 0, u t Real.pi = 0) →`
`(∀ x ∈ Set.Icc 0 Real.pi, u 0 x = …) → ∀ t ≥ 0, ∀ x ∈ Set.Icc 0 Real.pi, u t x = …`, from the
energy method. The eight
commands take 3 s. Initial data that are not finite sine sums, such as `x ^ 2` on `[0, π]`, are
refused, since their solution is an infinite series.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/--
info: #cas [pdesolve u t x, u 0 x = sin x]
Domain: t, x ∈ ℝ
Input (transport equation): (u_t + 2 * u_x = 0)
Output (characteristics): u(t, x) = Real.sin (x - 2 * t)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] The solution, and every differentiable solution has this form
        Proposition: ∀ (u : ℝ → ℝ → ℝ),
          Differentiable ℝ (Function.uncurry u) →
            (((∀ (t x : ℝ), deriv (fun s ↦ u s x) t + 2 * deriv (fun y ↦ u t y) x = 0) ∧
                ∀ (x : ℝ), u 0 x = Real.sin x) ↔
              ∀ (t x : ℝ), u t x = Real.sin (x - 2 * t))
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [pdesolve u t x, u 0 x = sin x] (u_t + 2 * u_x = 0)

/--
info: #cas [pdesolve u t x, u 0 x = exp x]
Domain: t, x ∈ ℝ
Input (transport equation): (u_t - u_x + u = 0)
Output (characteristics): u(t, x) = Real.exp (-t) * Real.exp (x + t)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [pdesolve u t x, u 0 x = exp x] (u_t - u_x + u = 0)

/--
info: #cas [pdesolve u t x, u 0 x = sin x + 3 * sin (2 * x), u t 0 = 0, u t pi = 0]
Domain: x ∈ [0, L], Dirichlet boundary values
Input (heat equation): (u_t = 2 * u_xx)
Output (separation of variables): u(t, x) = Real.exp (-(2 * t)) * Real.sin x + 3 * Real.exp (-(8 *
t)) * Real.sin (2 * x)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [pdesolve u t x, u 0 x = sin x + 3 * sin (2 * x), u t 0 = 0, u t pi = 0] (u_t = 2 * u_xx)

/--
info: #cas [pdesolve u t x, u 0 x = 2 * sin (pi * x) - sin (3 * pi * x), u t 0 = 0, u t 1 = 0]
Domain: x ∈ [0, L], Dirichlet boundary values
Input (heat equation): (u_t = u_xx)
Output (separation of variables): u(t, x) = 2 * Real.exp (-(Real.pi ^ 2 * t)) * Real.sin (Real.pi *
x) -
  Real.exp (-((3 * Real.pi) ^ 2 * t)) * Real.sin (3 * Real.pi * x)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [pdesolve u t x, u 0 x = 2 * sin (pi * x) - sin (3 * pi * x), u t 0 = 0, u t 1 = 0]
  (u_t = u_xx)

/--
info: #cas [pdesolve u t x, u 0 x = sin (pi * x), u_t 0 x = 0, u t 0 = 0, u t 1 = 0]
Domain: x ∈ [0, L], Dirichlet boundary values
Input (wave equation): (u_tt = 4 * u_xx)
Output (separation of variables): u(t, x) = Real.cos (2 * Real.pi * t) * Real.sin (Real.pi * x)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [pdesolve u t x, u 0 x = sin (pi * x), u_t 0 x = 0, u t 0 = 0, u t 1 = 0] (u_tt = 4 * u_xx)

/--
info: #cas [pdesolve u t x, u 0 x = sin x, u_t 0 x = sin (2 * x), u t 0 = 0, u t pi = 0]
Domain: x ∈ [0, L], Dirichlet boundary values
Input (wave equation): (u_tt = u_xx)
Output (separation of variables): u(t, x) = Real.cos t * Real.sin x + 1 / 2 * Real.sin (2 * t) *
Real.sin (2 * x)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [pdesolve u t x, u 0 x = sin x, u_t 0 x = sin (2 * x), u t 0 = 0, u t pi = 0]
  (u_tt = u_xx)

/--
info: #cas [pdesolve u t x, u 0 x = cos x, u_t 0 x = 0]
Domain: t, x ∈ ℝ
Input (wave equation): (u_tt = u_xx)
Output (d'Alembert's formula): u(t, x) = (Real.cos (x + t) + Real.cos (x - t)) / 2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [pdesolve u t x, u 0 x = cos x, u_t 0 x = 0] (u_tt = u_xx)

/--
info: #cas [pdesolve u t x, u 0 x = exp (-x ^ 2), u_t 0 x = x]
Domain: t, x ∈ ℝ
Input (wave equation): (u_tt = 9 * u_xx)
Output (d'Alembert's formula): u(t, x) = (Real.exp (-(x + 3 * t) ^ 2) + Real.exp (-(x - 3 * t) ^ 2))
/ 2 +
  (1 / 2 * (x + 3 * t) ^ 2 - 1 / 2 * (x - 3 * t) ^ 2) / 6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [pdesolve u t x, u 0 x = exp (-x ^ 2), u_t 0 x = x] (u_tt = 9 * u_xx)

