/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS
public import PDE.Symbolic.Command.CAS.PDESolve

/-!
# Commands from the SymLean documentation

Commands from the documentation of SymLean that no other example file runs. Each runs in the
build inside `#guard_msgs`, which checks its report.

The refusals check the error message: a non-constant coefficient, a primitive that is not
elementary, an initial value that is not a finite sine sum, a limit that needs a further
expansion and a sum without a hypergeometric closed form.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/--
info: #cas [derive x]
Domain: x ∈ ℝ
Input (scalar ℝ): (2 * x)
Output (scalar ℝ): 2

[CAS.Command.details] More details
  Variables: x
  [CAS.Command.computation] Analytic domain conditions
    Raw checked nonzero requirements: (none)
    Raw checked positivity requirements: (none)
  [CAS.Command.computation] Partial derivative in x
    [CAS.Command.computation] 1. Apply symbolic differentiation rules
      raw result: 0*x + 2*1
    [CAS.Command.computation] 2. Normalize the symbolic derivative unconditionally
      normalized result: 2
    [CAS.Command.computation] 3. Apply checked side-conditioned cleanup
      displayed result: 2
      additional nonzero requirements: (none)
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Derivative of the input
        Proposition: ∀ (x : ℝ), HasDerivAt (fun x ↦ 2 * x) 2 x
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.hasDerivAt_of_displayRoute
      [CAS.explanation.checkedStep] Partial derivative in x: indexed rules compute Expr.diff
        Proposition: (CAS.Verified.Expr.DiffDerivation.build 0 ((CAS.Verified.Expr.nat 2).mul
𝕏[0])).rawDerivative =
          CAS.Verified.Expr.diff 0 ((CAS.Verified.Expr.nat 2).mul 𝕏[0])
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.rawDerivative_eq_diff
      [CAS.explanation.checkedStep] Partial derivative in x: normalization preserves evaluation
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.eval ρ
              (CAS.Verified.Expr.DiffDerivation.build 0 ((CAS.Verified.Expr.nat 2).mul
𝕏[0])).simplifiedDerivative =
            CAS.Verified.Expr.eval ρ
              (CAS.Verified.Expr.DiffDerivation.build 0 ((CAS.Verified.Expr.nat 2).mul
𝕏[0])).rawDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.eval_simplifiedDerivative_eq_rawDerivative
      [CAS.explanation.checkedStep] Partial derivative in x: side-conditioned display normalization
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ
              (CAS.Command.displayDerivativeRoute
                  (CAS.Verified.Expr.DiffDerivation.build 0 ((CAS.Verified.Expr.nat 2).mul
𝕏[0]))).nonzero →
            CAS.Verified.Expr.eval ρ
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0 ((CAS.Verified.Expr.nat 2).mul
𝕏[0]))).rhs =
              CAS.Verified.Expr.eval ρ
                (CAS.Verified.Expr.DiffDerivation.build 0 ((CAS.Verified.Expr.nat 2).mul
𝕏[0])).simplifiedDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.displayDerivativeRoute_sound
      [CAS.explanation.checkedStep] Partial derivative in x: analytic semantics of the displayed
result
        Proposition: ∀ (x : ℝ^1),
          CAS.Verified.Expr.ValidAt x.ofLp ((CAS.Verified.Expr.nat 2).mul 𝕏[0]) →
            CAS.Verified.Expr.Alg.SideHolds x.ofLp
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0 ((CAS.Verified.Expr.nat 2).mul
𝕏[0]))).nonzero →
              (fderiv ℝ (fun y ↦ CAS.Verified.Expr.eval y.ofLp ((CAS.Verified.Expr.nat 2).mul 𝕏[0]))
x)
                  (EuclideanSpace.single 0 1) =
                CAS.Verified.Expr.eval x.ofLp
                  (CAS.Command.displayDerivativeRoute
                      (CAS.Verified.Expr.DiffDerivation.build 0 ((CAS.Verified.Expr.nat 2).mul
𝕏[0]))).rhs
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.fderiv_apply_single_eq_eval_displayDerivative
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [derive x] (2 * x)

/--
info: #cas [derive]
Domain: (x, a, b) ∈ ℝ^3
Input (scalar ℝ): a * x + b
Output (scalar ℝ): a

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [derive] (fun x : ℝ ↦ a * x + b)

/--
info: #cas [factor]
Domain: x ∈ ℝ
Input (scalar ℝ): (x ^ 3 - x)
Output (scalar ℝ): x*(x - 1)*(x + 1)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [factor] (x ^ 3 - x)

/--
info: #cas [integrate x]
Domain: x ∈ ℝ
Input (scalar ℝ): (x * sin (x ^ 2))
Output (scalar ℝ; antiderivative): -(1/2*cos(x^2))

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [integrate x] (x * sin (x ^ 2))

/--
info: #cas [integrate]
Domain: x ∈ ℝ
Input (scalar ℝ): 2
Output (scalar ℝ; antiderivative): 2*x

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [integrate] (fun x : ℝ ↦ 2)

/--
info: #cas [enclose x in [-1 / 10, 1 / 10]]
Domain: x ∈ [-1/10, 1/10] ⊆ ℝ
Input (scalar map ℝ → ℝ): (cos x)
Output (certified interval in ℝ): [0.995004, 1]
Upper bound: 1
Absolute bound: 1
Center and radius: ≈0.997502 ± 0.002498

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [enclose x in [-1 / 10, 1 / 10]] (cos x)

/--
info: #cas (prec := 16) [enclose]
Domain: closed real expression
Input (scalar ℝ): (sqrt 2)
Output (certified interval in ℝ): [92681/65536, 46341/32768]
Upper bound: 46341/32768
Absolute bound: 46341/32768
Center and radius: 185363/131072 ± 1/131072

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (prec := 16) [enclose] (sqrt 2)

/--
info: #cas [solve x]
Domain: x ∈ ℝ
Input (real relation): (x ^ 2 = 1)
Output (equivalent real solution predicate): x = 1 ∨ x = -1

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [solve x] (x ^ 2 = 1)

/--
info: #cas [reduce x]
Domain: x ∈ ℝ
Input (real relation): (-2 * x + 3 ≤ 7)
Output (equivalent real solution predicate): x ≥ -2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [reduce x] (-2 * x + 3 ≤ 7)

/--
info: #cas [roots x]
Domain: x ∈ ℝ
Input (polynomial equation): (x ^ 5 - x - 1 = 0)
Output (the only real solution, by 20 decimals, truncated): 1.16730397826141868425

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [roots x] (x ^ 5 - x - 1 = 0)

/--
info: #cas [dsolve y x]
Domain: x ∈ ℝ
Input (linear equation of order 2 with constant coefficients): (y'' + 3 * y' + 2 * y = exp x)
Output (order 2, characteristic roots: -1, -2): y(x) = exp(x)*1/6 + c₁*exp(-x) + c₂*exp(-(2*x))

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [dsolve y x] (y'' + 3 * y' + 2 * y = exp x)

/--
info: #cas [pdesolve u t x, u 0 x = sin x, u t 0 = 0, u t pi = 0]
Domain: x ∈ [0, L], Dirichlet boundary values
Input (heat equation): (u_t = u_xx)
Output (separation of variables): u(t, x) = Real.exp (-t) * Real.sin x

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [pdesolve u t x, u 0 x = sin x, u t 0 = 0, u t pi = 0] (u_t = u_xx)

/--
info: #cas [derive x]
Domain: x ∈ ℝ
Input (scalar ℝ): (x ^ 3)
Output (scalar ℝ): 3*x^2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [derive x] (x ^ 3)

/--
info: #cas [derive x]
Domain: (x, a, b) ∈ ℝ^3
Input (scalar ℝ): (a * x + b)
Output (scalar ℝ): a

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [derive x] (a * x + b)

/--
info: #cas [solve x]
Domain: x ∈ ℝ
Input (real relation): (x ^ 2 + 1 = 0)
Output (equivalent real solution predicate): False

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [solve x] (x ^ 2 + 1 = 0)

/--
info: #cas [solve x]
Domain: x ∈ ℝ
Input (real relation): (x = x)
Output (equivalent real solution predicate): True

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [solve x] (x = x)

/--
info: #cas [derive]
Domain: x ∈ ℝ
Input (scalar ℝ): 2 * x
Output (scalar ℝ): 2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [derive] (fun x : ℝ ↦ 2 * x)

/--
info: #cas [derive]
Domain: (x, a, b) ∈ ℝ^3
Input (scalar ℝ): a * x + b
Output (scalar ℝ): a

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [derive] (fun x ↦ a * x + b)

/--
info: #cas [derive]
Domain: x ∈ ℝ
Input (scalar ℝ): 7
Output (scalar ℝ): 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [derive] (fun x ↦ 7)

/--
info: #cas [fullSimplify depth]
Domain: x ∈ ℝ
Input (scalar ℝ): (sin (2*x) - 2*sin x*cos x)
Output (scalar ℝ): 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [fullSimplify depth] (sin (2*x) - 2*sin x*cos x)

/--
info: #cas [fullSimplify]
Domain: x ∈ ℝ
Input (scalar ℝ): (x^3 - x)
Output (scalar ℝ): x^3 - x

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [fullSimplify] (x^3 - x)

/--
info: #cas [factor]
Domain: x ∈ ℝ
Input (scalar ℝ): (x^4 - 5*x^2 + 4)
Output (scalar ℝ): (x - 1)*(x + 1)*(x - 2)*(x + 2)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [factor] (x^4 - 5*x^2 + 4)

/--
info: #cas [factor]
Domain: x ∈ ℝ
Input (scalar ℝ): (x^2 + 1)
Output (scalar ℝ): x^2 + 1

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [factor] (x^2 + 1)

/--
error: limit: no route proved the limit at ∞.
Asymptotic comparison:
  limit: log of an argument that is not equivalent to a positive power
Substitution x = 1 / t:
  limit: the expression is not built from x by field operations and functions of arguments with
a finite limit
-/
#guard_msgs in
#cas [limit x → ∞] (log (exp x + 1) - x)

/--
error: sum: Gosper's algorithm finds no closed form in hypergeometric terms for this summand
-/
#guard_msgs in
#cas [sum k 1 n] (1 / k)

/--
error: dsolve: the coefficient of the derivative of order 0 is not a rational constant
-/
#guard_msgs in
#cas [dsolve y x] (y'' + x*y = 0)

/--
error: dsolve: the checked integrator found no primitive of e ^ P times the right side
-/
#guard_msgs in
#cas [dsolve y x] (y' + x*y = 1)

/--
error: pdesolve: the initial value must be a finite sum of terms b sin (ω x)
-/
#guard_msgs in
#cas [pdesolve u t x, u 0 x = x ^ 2, u t 0 = 0, u t pi = 0] (u_t = u_xx)

