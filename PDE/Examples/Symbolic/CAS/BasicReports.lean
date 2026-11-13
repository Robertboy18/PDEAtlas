/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS
public import PDE.Symbolic.Command.CAS.Laplacian

/-!
# Reports of the basic `#cas` commands

The basic `#cas` commands that the SymLean manual quotes, for `simplify`, `derive`, `grad`,
`laplacian`, `integrate` and `enclose`, each run inside `#guard_msgs`, which checks its InfoView
report. `CAS.Examples.Basic` in SymLean describes the
calculator and states the `cas` tactic examples.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/--
info: #cas [simplify]
Domain: x ∈ ℝ
Input (scalar ℝ): ((x + 0) * 1)
Output (scalar ℝ): x

[CAS.Command.details] More details
  Variables: x
  [CAS.Command.computation] Checked symbolic computation
    Raw checked nonzero requirements: (none)
    Guarantee: these assumptions justify conditional rewrites and preserve real evaluation
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Identity with the simplified form
        Proposition: ∀ (x : ℝ), (x + 0) * 1 = x
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.eq_of_simplifyFinDisplayRoute
      [CAS.explanation.checkedStep] Simplification under generated rewrite assumptions
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ
              ((𝕏[0].add (CAS.Verified.Expr.nat 0)).mul (CAS.Verified.Expr.nat
1)).simplifyFinDisplayRoute.nonzero →
            CAS.Verified.Expr.eval ρ
                ((𝕏[0].add (CAS.Verified.Expr.nat 0)).mul (CAS.Verified.Expr.nat
1)).simplifyFinDisplayRoute.rhs =
              CAS.Verified.Expr.eval ρ
                ((𝕏[0].add (CAS.Verified.Expr.nat 0)).mul (CAS.Verified.Expr.nat
1)).simplifyFinDisplayRoute.lhs
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.SideClaimRoute.sound
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] pre-normalization: deep-factor-cancel: attempted
        side-conditioned
      [CAS.explanation.plannerStep] pre-normalization: inverse-elementary: attempted
        side-conditioned
      [CAS.explanation.plannerStep] pre-normalization: real-power: attempted
        side-conditioned
      [CAS.explanation.plannerStep] base normalization: structural: attempted
        checked
      [CAS.explanation.plannerStep] base normalization: trig: attempted
        checked
      [CAS.explanation.plannerStep] base normalization: algebra: attempted
        checked
      [CAS.explanation.plannerStep] base normalization: factor-common: attempted
        checked
      [CAS.explanation.plannerStep] post-normalization: inverse-elementary: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: real-power: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: fraction-normal-form: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: rational-side: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: sqrt-square: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: sqrt-numeral: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: sqrt-product-collect: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: common-add-factor: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: deep-factor-cancel: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: unit-ratio: attempted
        side-conditioned
      [CAS.explanation.plannerStep] direct: univariate-rational-canonical: attempted
        side-conditioned
-/
#guard_msgs in
#cas [simplify] ((x + 0) * 1)

/--
info: #cas [simplify]
Domain: x ∈ ℝ
Input (scalar ℝ): ((x ^ 4 - 1) / (x ^ 2 - 1))
Output (scalar ℝ): x^2 + 1
Conditions: x^2 - 1 ≠ 0

[CAS.Command.details] More details
  Variables: x
  [CAS.Command.computation] Checked symbolic computation
    Raw checked nonzero requirements: x^2 - 1
    Guarantee: these assumptions justify conditional rewrites and preserve real evaluation
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Identity with the simplified form
        Proposition: ∀ (x : ℝ), x * x - 1 ≠ 0 → (x ^ 4 - 1) / (x ^ 2 - 1) = x ^ 2 + 1
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.eq_of_simplifyFinDisplayRoute
      [CAS.explanation.checkedStep] Simplification under generated rewrite assumptions
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ
              (((𝕏[0].pow 4).sub (CAS.Verified.Expr.nat 1)).div
                    ((𝕏[0].pow 2).sub (CAS.Verified.Expr.nat 1))).simplifyFinDisplayRoute.nonzero →
            CAS.Verified.Expr.eval ρ
                (((𝕏[0].pow 4).sub (CAS.Verified.Expr.nat 1)).div
                      ((𝕏[0].pow 2).sub (CAS.Verified.Expr.nat 1))).simplifyFinDisplayRoute.rhs =
              CAS.Verified.Expr.eval ρ
                (((𝕏[0].pow 4).sub (CAS.Verified.Expr.nat 1)).div
                      ((𝕏[0].pow 2).sub (CAS.Verified.Expr.nat 1))).simplifyFinDisplayRoute.lhs
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.SideClaimRoute.sound
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] pre-normalization: deep-factor-cancel: attempted
        side-conditioned
      [CAS.explanation.plannerStep] pre-normalization: inverse-elementary: attempted
        side-conditioned
      [CAS.explanation.plannerStep] pre-normalization: real-power: attempted
        side-conditioned
      [CAS.explanation.plannerStep] base normalization: structural: attempted
        checked
      [CAS.explanation.plannerStep] base normalization: trig: attempted
        checked
      [CAS.explanation.plannerStep] base normalization: algebra: attempted
        checked
      [CAS.explanation.plannerStep] base normalization: factor-common: attempted
        checked
      [CAS.explanation.plannerStep] post-normalization: inverse-elementary: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: real-power: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: fraction-normal-form: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: rational-side: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: sqrt-square: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: sqrt-numeral: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: sqrt-product-collect: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: common-add-factor: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: deep-factor-cancel: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: unit-ratio: attempted
        side-conditioned
      [CAS.explanation.plannerStep] direct: univariate-rational-canonical: attempted
        side-conditioned
-/
#guard_msgs in
#cas [simplify] ((x ^ 4 - 1) / (x ^ 2 - 1))

/--
info: #cas [derive x]
Domain: (x, y) ∈ ℝ^2
Input (scalar ℝ): (sin (x * y))
Output (scalar ℝ): cos(x*y)*y

[CAS.Command.details] More details
  Variables: x, y
  [CAS.Command.computation] Analytic domain conditions
    Raw checked nonzero requirements: (none)
    Raw checked positivity requirements: (none)
  [CAS.Command.computation] Partial derivative in x
    [CAS.Command.computation] 1. Apply symbolic differentiation rules
      raw result: cos(x*y)*(1*y + x*0)
    [CAS.Command.computation] 2. Normalize the symbolic derivative unconditionally
      normalized result: cos(x*y)*y
    [CAS.Command.computation] 3. Apply checked side-conditioned cleanup
      displayed result: cos(x*y)*y
      additional nonzero requirements: (none)
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Derivative of the input
        Proposition: ∀ (x y : ℝ), HasDerivAt (fun x ↦ Real.sin (x * y)) (Real.cos (x * y) * y) x
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.hasDerivAt_of_displayRoute
      [CAS.explanation.checkedStep] Partial derivative in x: indexed rules compute Expr.diff
        Proposition: (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].mul 𝕏[1]).sin).rawDerivative =
          CAS.Verified.Expr.diff 0 (𝕏[0].mul 𝕏[1]).sin
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.rawDerivative_eq_diff
      [CAS.explanation.checkedStep] Partial derivative in x: normalization preserves evaluation
        Proposition: ∀ (ρ : Fin 2 → ℝ),
          CAS.Verified.Expr.eval ρ (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].mul
𝕏[1]).sin).simplifiedDerivative =
            CAS.Verified.Expr.eval ρ (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].mul
𝕏[1]).sin).rawDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.eval_simplifiedDerivative_eq_rawDerivative
      [CAS.explanation.checkedStep] Partial derivative in x: side-conditioned display normalization
        Proposition: ∀ (ρ : Fin 2 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ
              (CAS.Command.displayDerivativeRoute
                  (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].mul 𝕏[1]).sin)).nonzero →
            CAS.Verified.Expr.eval ρ
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].mul 𝕏[1]).sin)).rhs =
              CAS.Verified.Expr.eval ρ
                (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].mul 𝕏[1]).sin).simplifiedDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.displayDerivativeRoute_sound
      [CAS.explanation.checkedStep] Partial derivative in x: analytic semantics of the displayed
result
        Proposition: ∀ (x : ℝ^2),
          CAS.Verified.Expr.ValidAt x.ofLp (𝕏[0].mul 𝕏[1]).sin →
            CAS.Verified.Expr.Alg.SideHolds x.ofLp
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].mul 𝕏[1]).sin)).nonzero →
              (fderiv ℝ (fun y ↦ CAS.Verified.Expr.eval y.ofLp (𝕏[0].mul 𝕏[1]).sin) x)
(EuclideanSpace.single 0 1) =
                CAS.Verified.Expr.eval x.ofLp
                  (CAS.Command.displayDerivativeRoute
                      (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].mul 𝕏[1]).sin)).rhs
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.fderiv_apply_single_eq_eval_displayDerivative
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [derive x] (sin (x * y))

/--
info: #cas [derive x]
Domain: x ∈ ℝ
Input (scalar ℝ): (x ^ (-2))
Output (scalar ℝ): -(2/x^3)
Conditions: x ≠ 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [derive x] (x ^ (-2))

/--
info: #cas [derive x]
Domain: x ∈ ℝ
Input (scalar ℝ): (sqrt (2 * x + 2))
Output (scalar ℝ): 1/sqrt(2*x + 2)
Conditions: x + 1 > 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [derive x] (sqrt (2 * x + 2))

/--
info: #cas [derive x]
Domain: x ∈ ℝ
Input (scalar ℝ): (arcsin x)
Output (scalar ℝ): 1/sqrt(1 - x^2)
Conditions: x + 1 ≠ 0; x - 1 ≠ 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [derive x] (arcsin x)

/--
info: #cas [grad x, y]
Domain: (x, y) ∈ ℝ^2
Input (scalar ℝ): (sin (x * y))
Output (vector ℝ^2; order x, y): (cos(x*y)*y, cos(x*y)*x)

[CAS.Command.details] More details
  Variables and component order: x, y
  [CAS.Command.computation] Analytic domain conditions
    Raw checked nonzero requirements: (none)
    Raw checked positivity requirements: (none)
  [CAS.Command.computation] Checked gradient computation
    [CAS.Command.computation] Gradient component ∂_x
      Output: cos(x*y)*y
      [CAS.Command.computation] Partial derivative in x
        [CAS.Command.computation] 1. Apply symbolic differentiation rules
          raw result: cos(x*y)*(1*y + x*0)
        [CAS.Command.computation] 2. Normalize the symbolic derivative unconditionally
          normalized result: cos(x*y)*y
        [CAS.Command.computation] 3. Apply checked side-conditioned cleanup
          displayed result: cos(x*y)*y
          additional nonzero requirements: (none)
    [CAS.Command.computation] Gradient component ∂_y
      Output: cos(x*y)*x
      [CAS.Command.computation] Partial derivative in y
        [CAS.Command.computation] 1. Apply symbolic differentiation rules
          raw result: cos(x*y)*(0*y + x*1)
        [CAS.Command.computation] 2. Normalize the symbolic derivative unconditionally
          normalized result: cos(x*y)*x
        [CAS.Command.computation] 3. Apply checked side-conditioned cleanup
          displayed result: cos(x*y)*x
          additional nonzero requirements: (none)
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Gradient of the input
        Proposition: ∀ (x y : ℝ),
          HasGradientAt (fun p ↦ Real.sin (p.ofLp 0 * p.ofLp 1)) !₂[Real.cos (x * y) * y, Real.cos
(x * y) * x] !₂[x, y]
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.hasGradientAt_of_closedGradient
      [CAS.explanation.checkedStep] Gradient component ∂_x: indexed rules compute Expr.diff
        Proposition: (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].mul 𝕏[1]).sin).rawDerivative =
          CAS.Verified.Expr.diff 0 (𝕏[0].mul 𝕏[1]).sin
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.rawDerivative_eq_diff
      [CAS.explanation.checkedStep] Gradient component ∂_x: normalization preserves evaluation
        Proposition: ∀ (ρ : Fin 2 → ℝ),
          CAS.Verified.Expr.eval ρ (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].mul
𝕏[1]).sin).simplifiedDerivative =
            CAS.Verified.Expr.eval ρ (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].mul
𝕏[1]).sin).rawDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.eval_simplifiedDerivative_eq_rawDerivative
      [CAS.explanation.checkedStep] Gradient component ∂_x: side-conditioned display normalization
        Proposition: ∀ (ρ : Fin 2 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ
              (CAS.Command.displayDerivativeRoute
                  (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].mul 𝕏[1]).sin)).nonzero →
            CAS.Verified.Expr.eval ρ
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].mul 𝕏[1]).sin)).rhs =
              CAS.Verified.Expr.eval ρ
                (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].mul 𝕏[1]).sin).simplifiedDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.displayDerivativeRoute_sound
      [CAS.explanation.checkedStep] Gradient component ∂_x: analytic semantics of the displayed
result
        Proposition: ∀ (x : ℝ^2),
          CAS.Verified.Expr.ValidAt x.ofLp (𝕏[0].mul 𝕏[1]).sin →
            CAS.Verified.Expr.Alg.SideHolds x.ofLp
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].mul 𝕏[1]).sin)).nonzero →
              (fderiv ℝ (fun y ↦ CAS.Verified.Expr.eval y.ofLp (𝕏[0].mul 𝕏[1]).sin) x)
(EuclideanSpace.single 0 1) =
                CAS.Verified.Expr.eval x.ofLp
                  (CAS.Command.displayDerivativeRoute
                      (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].mul 𝕏[1]).sin)).rhs
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.fderiv_apply_single_eq_eval_displayDerivative
      [CAS.explanation.checkedStep] Gradient component ∂_y: indexed rules compute Expr.diff
        Proposition: (CAS.Verified.Expr.DiffDerivation.build 1 (𝕏[0].mul 𝕏[1]).sin).rawDerivative =
          CAS.Verified.Expr.diff 1 (𝕏[0].mul 𝕏[1]).sin
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.rawDerivative_eq_diff
      [CAS.explanation.checkedStep] Gradient component ∂_y: normalization preserves evaluation
        Proposition: ∀ (ρ : Fin 2 → ℝ),
          CAS.Verified.Expr.eval ρ (CAS.Verified.Expr.DiffDerivation.build 1 (𝕏[0].mul
𝕏[1]).sin).simplifiedDerivative =
            CAS.Verified.Expr.eval ρ (CAS.Verified.Expr.DiffDerivation.build 1 (𝕏[0].mul
𝕏[1]).sin).rawDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.eval_simplifiedDerivative_eq_rawDerivative
      [CAS.explanation.checkedStep] Gradient component ∂_y: side-conditioned display normalization
        Proposition: ∀ (ρ : Fin 2 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ
              (CAS.Command.displayDerivativeRoute
                  (CAS.Verified.Expr.DiffDerivation.build 1 (𝕏[0].mul 𝕏[1]).sin)).nonzero →
            CAS.Verified.Expr.eval ρ
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 1 (𝕏[0].mul 𝕏[1]).sin)).rhs =
              CAS.Verified.Expr.eval ρ
                (CAS.Verified.Expr.DiffDerivation.build 1 (𝕏[0].mul 𝕏[1]).sin).simplifiedDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.displayDerivativeRoute_sound
      [CAS.explanation.checkedStep] Gradient component ∂_y: analytic semantics of the displayed
result
        Proposition: ∀ (x : ℝ^2),
          CAS.Verified.Expr.ValidAt x.ofLp (𝕏[0].mul 𝕏[1]).sin →
            CAS.Verified.Expr.Alg.SideHolds x.ofLp
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 1 (𝕏[0].mul 𝕏[1]).sin)).nonzero →
              (fderiv ℝ (fun y ↦ CAS.Verified.Expr.eval y.ofLp (𝕏[0].mul 𝕏[1]).sin) x)
(EuclideanSpace.single 1 1) =
                CAS.Verified.Expr.eval x.ofLp
                  (CAS.Command.displayDerivativeRoute
                      (CAS.Verified.Expr.DiffDerivation.build 1 (𝕏[0].mul 𝕏[1]).sin)).rhs
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.fderiv_apply_single_eq_eval_displayDerivative
      [CAS.explanation.checkedStep] Analytic gradient assembly
        Proposition: ∀ (x : ℝ^2),
          CAS.Verified.Expr.ValidAt x.ofLp (𝕏[0].mul 𝕏[1]).sin →
            (WithLp.toLp 2 fun i ↦ CAS.Verified.Expr.eval x.ofLp ((∇ₛ (𝕏[0].mul 𝕏[1]).sin) i)) =
              gradient (fun y ↦ CAS.Verified.Expr.eval y.ofLp (𝕏[0].mul 𝕏[1]).sin) x
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.closedGradient_eval_eq_gradient
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [grad x, y] (sin (x * y))

/--
info: #cas [laplacian x, y]
Domain: (x, y) ∈ ℝ^2
Input (scalar ℝ): (x ^ 2 + y ^ 2)
Output (scalar ℝ): 4

[CAS.Command.details] More details
  Variables: x, y
  [CAS.Command.computation] Analytic domain conditions
    Raw checked nonzero requirements: (none)
    Raw checked positivity requirements: (none)
  [CAS.Command.computation] Checked coordinate computations
    [CAS.Command.computation] Second partial ∂_x∂_x
      [CAS.Command.computation] Partial derivative in x
        [CAS.Command.computation] 1. Apply symbolic differentiation rules
          raw result: 2*x^1*1 + 2*y^1*0
        [CAS.Command.computation] 2. Normalize the symbolic derivative unconditionally
          normalized result: 2*x
        [CAS.Command.computation] 3. Apply checked side-conditioned cleanup
          displayed result: 2*x
          additional nonzero requirements: (none)
      [CAS.Command.computation] Partial derivative in x
        [CAS.Command.computation] 1. Apply symbolic differentiation rules
          raw result: (0*x^1 + 2*1*x^0*1)*1 + 2*x^1*0 + (0*y^1 + 2*1*y^0*0)*0 + 2*y^1*0
        [CAS.Command.computation] 2. Normalize the symbolic derivative unconditionally
          normalized result: 2
        [CAS.Command.computation] 3. Apply checked side-conditioned cleanup
          displayed result: 2
          additional nonzero requirements: (none)
      summand: 2
    [CAS.Command.computation] Second partial ∂_y∂_y
      [CAS.Command.computation] Partial derivative in y
        [CAS.Command.computation] 1. Apply symbolic differentiation rules
          raw result: 2*x^1*0 + 2*y^1*1
        [CAS.Command.computation] 2. Normalize the symbolic derivative unconditionally
          normalized result: 2*y
        [CAS.Command.computation] 3. Apply checked side-conditioned cleanup
          displayed result: 2*y
          additional nonzero requirements: (none)
      [CAS.Command.computation] Partial derivative in y
        [CAS.Command.computation] 1. Apply symbolic differentiation rules
          raw result: (0*x^1 + 2*1*x^0*0)*0 + 2*x^1*0 + (0*y^1 + 2*1*y^0*1)*1 + 2*y^1*0
        [CAS.Command.computation] 2. Normalize the symbolic derivative unconditionally
          normalized result: 2
        [CAS.Command.computation] 3. Apply checked side-conditioned cleanup
          displayed result: 2
          additional nonzero requirements: (none)
      summand: 2
  [CAS.Command.computation] Sum and normalize the diagonal second partials
    Summands: 2, 2
    Normalized sum: 4
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] First partial in x: indexed rules compute Expr.diff
        Proposition: (CAS.Verified.Expr.DiffDerivation.build 0 ((𝕏[0].pow 2).add (𝕏[1].pow
2))).rawDerivative =
          CAS.Verified.Expr.diff 0 ((𝕏[0].pow 2).add (𝕏[1].pow 2))
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.rawDerivative_eq_diff
      [CAS.explanation.checkedStep] First partial in x: normalization preserves evaluation
        Proposition: ∀ (ρ : Fin 2 → ℝ),
          CAS.Verified.Expr.eval ρ
              (CAS.Verified.Expr.DiffDerivation.build 0 ((𝕏[0].pow 2).add (𝕏[1].pow
2))).simplifiedDerivative =
            CAS.Verified.Expr.eval ρ
              (CAS.Verified.Expr.DiffDerivation.build 0 ((𝕏[0].pow 2).add (𝕏[1].pow
2))).rawDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.eval_simplifiedDerivative_eq_rawDerivative
      [CAS.explanation.checkedStep] First partial in x: side-conditioned display normalization
        Proposition: ∀ (ρ : Fin 2 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ
              (CAS.Command.displayDerivativeRoute
                  (CAS.Verified.Expr.DiffDerivation.build 0 ((𝕏[0].pow 2).add (𝕏[1].pow
2)))).nonzero →
            CAS.Verified.Expr.eval ρ
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0 ((𝕏[0].pow 2).add (𝕏[1].pow 2)))).rhs
=
              CAS.Verified.Expr.eval ρ
                (CAS.Verified.Expr.DiffDerivation.build 0 ((𝕏[0].pow 2).add (𝕏[1].pow
2))).simplifiedDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.displayDerivativeRoute_sound
      [CAS.explanation.checkedStep] First partial in x: analytic semantics of the displayed result
        Proposition: ∀ (x : ℝ^2),
          CAS.Verified.Expr.ValidAt x.ofLp ((𝕏[0].pow 2).add (𝕏[1].pow 2)) →
            CAS.Verified.Expr.Alg.SideHolds x.ofLp
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0 ((𝕏[0].pow 2).add (𝕏[1].pow
2)))).nonzero →
              (fderiv ℝ (fun y ↦ CAS.Verified.Expr.eval y.ofLp ((𝕏[0].pow 2).add (𝕏[1].pow 2))) x)
                  (EuclideanSpace.single 0 1) =
                CAS.Verified.Expr.eval x.ofLp
                  (CAS.Command.displayDerivativeRoute
                      (CAS.Verified.Expr.DiffDerivation.build 0 ((𝕏[0].pow 2).add (𝕏[1].pow
2)))).rhs
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.fderiv_apply_single_eq_eval_displayDerivative
      [CAS.explanation.checkedStep] Second partial in x: indexed rules compute Expr.diff
        Proposition: (CAS.Verified.Expr.DiffDerivation.build 0
              ((((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 1)).mul (CAS.Verified.Expr.nat 1)).add
                (((CAS.Verified.Expr.nat 2).mul (𝕏[1].pow 1)).mul (CAS.Verified.Expr.nat
0)))).rawDerivative =
          CAS.Verified.Expr.diff 0
            ((((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 1)).mul (CAS.Verified.Expr.nat 1)).add
              (((CAS.Verified.Expr.nat 2).mul (𝕏[1].pow 1)).mul (CAS.Verified.Expr.nat 0)))
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.rawDerivative_eq_diff
      [CAS.explanation.checkedStep] Second partial in x: normalization preserves evaluation
        Proposition: ∀ (ρ : Fin 2 → ℝ),
          CAS.Verified.Expr.eval ρ
              (CAS.Verified.Expr.DiffDerivation.build 0
                  ((((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 1)).mul (CAS.Verified.Expr.nat 1)).add
                    (((CAS.Verified.Expr.nat 2).mul (𝕏[1].pow 1)).mul
                      (CAS.Verified.Expr.nat 0)))).simplifiedDerivative =
            CAS.Verified.Expr.eval ρ
              (CAS.Verified.Expr.DiffDerivation.build 0
                  ((((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 1)).mul (CAS.Verified.Expr.nat 1)).add
                    (((CAS.Verified.Expr.nat 2).mul (𝕏[1].pow 1)).mul (CAS.Verified.Expr.nat
0)))).rawDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.eval_simplifiedDerivative_eq_rawDerivative
      [CAS.explanation.checkedStep] Second partial in x: side-conditioned display normalization
        Proposition: ∀ (ρ : Fin 2 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ
              (CAS.Command.displayDerivativeRoute
                  (CAS.Verified.Expr.DiffDerivation.build 0
                    ((((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 1)).mul (CAS.Verified.Expr.nat
1)).add
                      (((CAS.Verified.Expr.nat 2).mul (𝕏[1].pow 1)).mul (CAS.Verified.Expr.nat
0))))).nonzero →
            CAS.Verified.Expr.eval ρ
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0
                      ((((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 1)).mul (CAS.Verified.Expr.nat
1)).add
                        (((CAS.Verified.Expr.nat 2).mul (𝕏[1].pow 1)).mul (CAS.Verified.Expr.nat
0))))).rhs =
              CAS.Verified.Expr.eval ρ
                (CAS.Verified.Expr.DiffDerivation.build 0
                    ((((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 1)).mul (CAS.Verified.Expr.nat
1)).add
                      (((CAS.Verified.Expr.nat 2).mul (𝕏[1].pow 1)).mul
                        (CAS.Verified.Expr.nat 0)))).simplifiedDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.displayDerivativeRoute_sound
      [CAS.explanation.checkedStep] Second partial in x: analytic semantics of the displayed result
        Proposition: ∀ (x : ℝ^2),
          CAS.Verified.Expr.ValidAt x.ofLp
              ((((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 1)).mul (CAS.Verified.Expr.nat 1)).add
                (((CAS.Verified.Expr.nat 2).mul (𝕏[1].pow 1)).mul (CAS.Verified.Expr.nat 0))) →
            CAS.Verified.Expr.Alg.SideHolds x.ofLp
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0
                      ((((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 1)).mul (CAS.Verified.Expr.nat
1)).add
                        (((CAS.Verified.Expr.nat 2).mul (𝕏[1].pow 1)).mul (CAS.Verified.Expr.nat
0))))).nonzero →
              (fderiv ℝ
                    (fun y ↦
                      CAS.Verified.Expr.eval y.ofLp
                        ((((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 1)).mul (CAS.Verified.Expr.nat
1)).add
                          (((CAS.Verified.Expr.nat 2).mul (𝕏[1].pow 1)).mul (CAS.Verified.Expr.nat
0))))
                    x)
                  (EuclideanSpace.single 0 1) =
                CAS.Verified.Expr.eval x.ofLp
                  (CAS.Command.displayDerivativeRoute
                      (CAS.Verified.Expr.DiffDerivation.build 0
                        ((((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 1)).mul (CAS.Verified.Expr.nat
1)).add
                          (((CAS.Verified.Expr.nat 2).mul (𝕏[1].pow 1)).mul (CAS.Verified.Expr.nat
0))))).rhs
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.fderiv_apply_single_eq_eval_displayDerivative
      [CAS.explanation.checkedStep] First partial in y: indexed rules compute Expr.diff
        Proposition: (CAS.Verified.Expr.DiffDerivation.build 1 ((𝕏[0].pow 2).add (𝕏[1].pow
2))).rawDerivative =
          CAS.Verified.Expr.diff 1 ((𝕏[0].pow 2).add (𝕏[1].pow 2))
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.rawDerivative_eq_diff
      [CAS.explanation.checkedStep] First partial in y: normalization preserves evaluation
        Proposition: ∀ (ρ : Fin 2 → ℝ),
          CAS.Verified.Expr.eval ρ
              (CAS.Verified.Expr.DiffDerivation.build 1 ((𝕏[0].pow 2).add (𝕏[1].pow
2))).simplifiedDerivative =
            CAS.Verified.Expr.eval ρ
              (CAS.Verified.Expr.DiffDerivation.build 1 ((𝕏[0].pow 2).add (𝕏[1].pow
2))).rawDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.eval_simplifiedDerivative_eq_rawDerivative
      [CAS.explanation.checkedStep] First partial in y: side-conditioned display normalization
        Proposition: ∀ (ρ : Fin 2 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ
              (CAS.Command.displayDerivativeRoute
                  (CAS.Verified.Expr.DiffDerivation.build 1 ((𝕏[0].pow 2).add (𝕏[1].pow
2)))).nonzero →
            CAS.Verified.Expr.eval ρ
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 1 ((𝕏[0].pow 2).add (𝕏[1].pow 2)))).rhs
=
              CAS.Verified.Expr.eval ρ
                (CAS.Verified.Expr.DiffDerivation.build 1 ((𝕏[0].pow 2).add (𝕏[1].pow
2))).simplifiedDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.displayDerivativeRoute_sound
      [CAS.explanation.checkedStep] First partial in y: analytic semantics of the displayed result
        Proposition: ∀ (x : ℝ^2),
          CAS.Verified.Expr.ValidAt x.ofLp ((𝕏[0].pow 2).add (𝕏[1].pow 2)) →
            CAS.Verified.Expr.Alg.SideHolds x.ofLp
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 1 ((𝕏[0].pow 2).add (𝕏[1].pow
2)))).nonzero →
              (fderiv ℝ (fun y ↦ CAS.Verified.Expr.eval y.ofLp ((𝕏[0].pow 2).add (𝕏[1].pow 2))) x)
                  (EuclideanSpace.single 1 1) =
                CAS.Verified.Expr.eval x.ofLp
                  (CAS.Command.displayDerivativeRoute
                      (CAS.Verified.Expr.DiffDerivation.build 1 ((𝕏[0].pow 2).add (𝕏[1].pow
2)))).rhs
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.fderiv_apply_single_eq_eval_displayDerivative
      [CAS.explanation.checkedStep] Second partial in y: indexed rules compute Expr.diff
        Proposition: (CAS.Verified.Expr.DiffDerivation.build 1
              ((((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 1)).mul (CAS.Verified.Expr.nat 0)).add
                (((CAS.Verified.Expr.nat 2).mul (𝕏[1].pow 1)).mul (CAS.Verified.Expr.nat
1)))).rawDerivative =
          CAS.Verified.Expr.diff 1
            ((((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 1)).mul (CAS.Verified.Expr.nat 0)).add
              (((CAS.Verified.Expr.nat 2).mul (𝕏[1].pow 1)).mul (CAS.Verified.Expr.nat 1)))
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.rawDerivative_eq_diff
      [CAS.explanation.checkedStep] Second partial in y: normalization preserves evaluation
        Proposition: ∀ (ρ : Fin 2 → ℝ),
          CAS.Verified.Expr.eval ρ
              (CAS.Verified.Expr.DiffDerivation.build 1
                  ((((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 1)).mul (CAS.Verified.Expr.nat 0)).add
                    (((CAS.Verified.Expr.nat 2).mul (𝕏[1].pow 1)).mul
                      (CAS.Verified.Expr.nat 1)))).simplifiedDerivative =
            CAS.Verified.Expr.eval ρ
              (CAS.Verified.Expr.DiffDerivation.build 1
                  ((((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 1)).mul (CAS.Verified.Expr.nat 0)).add
                    (((CAS.Verified.Expr.nat 2).mul (𝕏[1].pow 1)).mul (CAS.Verified.Expr.nat
1)))).rawDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.eval_simplifiedDerivative_eq_rawDerivative
      [CAS.explanation.checkedStep] Second partial in y: side-conditioned display normalization
        Proposition: ∀ (ρ : Fin 2 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ
              (CAS.Command.displayDerivativeRoute
                  (CAS.Verified.Expr.DiffDerivation.build 1
                    ((((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 1)).mul (CAS.Verified.Expr.nat
0)).add
                      (((CAS.Verified.Expr.nat 2).mul (𝕏[1].pow 1)).mul (CAS.Verified.Expr.nat
1))))).nonzero →
            CAS.Verified.Expr.eval ρ
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 1
                      ((((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 1)).mul (CAS.Verified.Expr.nat
0)).add
                        (((CAS.Verified.Expr.nat 2).mul (𝕏[1].pow 1)).mul (CAS.Verified.Expr.nat
1))))).rhs =
              CAS.Verified.Expr.eval ρ
                (CAS.Verified.Expr.DiffDerivation.build 1
                    ((((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 1)).mul (CAS.Verified.Expr.nat
0)).add
                      (((CAS.Verified.Expr.nat 2).mul (𝕏[1].pow 1)).mul
                        (CAS.Verified.Expr.nat 1)))).simplifiedDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.displayDerivativeRoute_sound
      [CAS.explanation.checkedStep] Second partial in y: analytic semantics of the displayed result
        Proposition: ∀ (x : ℝ^2),
          CAS.Verified.Expr.ValidAt x.ofLp
              ((((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 1)).mul (CAS.Verified.Expr.nat 0)).add
                (((CAS.Verified.Expr.nat 2).mul (𝕏[1].pow 1)).mul (CAS.Verified.Expr.nat 1))) →
            CAS.Verified.Expr.Alg.SideHolds x.ofLp
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 1
                      ((((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 1)).mul (CAS.Verified.Expr.nat
0)).add
                        (((CAS.Verified.Expr.nat 2).mul (𝕏[1].pow 1)).mul (CAS.Verified.Expr.nat
1))))).nonzero →
              (fderiv ℝ
                    (fun y ↦
                      CAS.Verified.Expr.eval y.ofLp
                        ((((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 1)).mul (CAS.Verified.Expr.nat
0)).add
                          (((CAS.Verified.Expr.nat 2).mul (𝕏[1].pow 1)).mul (CAS.Verified.Expr.nat
1))))
                    x)
                  (EuclideanSpace.single 1 1) =
                CAS.Verified.Expr.eval x.ofLp
                  (CAS.Command.displayDerivativeRoute
                      (CAS.Verified.Expr.DiffDerivation.build 1
                        ((((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 1)).mul (CAS.Verified.Expr.nat
0)).add
                          (((CAS.Verified.Expr.nat 2).mul (𝕏[1].pow 1)).mul (CAS.Verified.Expr.nat
1))))).rhs
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.fderiv_apply_single_eq_eval_displayDerivative
      [CAS.explanation.checkedStep] Analytic Laplacian assembly
        Proposition: ∀ (x : ℝ^2),
          CAS.Verified.Expr.ValidAt x.ofLp ((𝕏[0].pow 2).add (𝕏[1].pow 2)) →
            (∀ (i : Fin 2),
                CAS.Verified.Expr.ValidAt x.ofLp (CAS.Verified.Expr.diff i ((𝕏[0].pow 2).add
(𝕏[1].pow 2)))) →
              CAS.Verified.Expr.eval x.ofLp (Δₛ ((𝕏[0].pow 2).add (𝕏[1].pow 2))) =
                PDE.laplacian (fun y ↦ CAS.Verified.Expr.eval y.ofLp ((𝕏[0].pow 2).add (𝕏[1].pow
2))) x
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.closedLaplacian_eval_eq_laplacian
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [laplacian x, y] (x ^ 2 + y ^ 2)

/--
info: #cas [integrate]
Domain: x ∈ ℝ
Input (scalar ℝ): (sin x)
Output (scalar ℝ; antiderivative): -cos(x)

[CAS.Command.details] More details
  Variables: x
  [CAS.Command.computation] Checked antiderivative computation
    [CAS.Command.computation] 1. Differentiate the proposed primitive
      Raw derivative: -(-sin(x)*1)
    [CAS.Command.computation] 2. Form the derivative residual
      Raw residual: -(-sin(x)*1) - sin(x)
      Definition: CAS.IntegrationCheck.residual
    [CAS.Command.computation] 3. Check the residual normal form
      Checked residual normal form: 0
      Certificate condition: checked residual normal form = 0
    [CAS.Command.computation] 4. Record analytic domain requirements
      Certificate nonzero requirements (compacted): (none)
      Certificate positivity requirements (compacted): (none)
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Integral of the input
        Proposition: ∀ (a b : ℝ), ∫ (x : ℝ) in a..b, Real.sin x = -Real.cos b + Real.cos a
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.IntegrationCheck.AntiderivativeCert.intervalIntegral_eq_sub_of_line
      [CAS.explanation.checkedStep] Primitive derivative in x: indexed rules compute Expr.diff
        Proposition: (CAS.Verified.Expr.DiffDerivation.build 0 𝕏[0].cos.neg).rawDerivative =
          CAS.Verified.Expr.diff 0 𝕏[0].cos.neg
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.rawDerivative_eq_diff
      [CAS.explanation.checkedStep] Primitive derivative in x: normalization preserves evaluation
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.eval ρ (CAS.Verified.Expr.DiffDerivation.build 0
𝕏[0].cos.neg).simplifiedDerivative =
            CAS.Verified.Expr.eval ρ (CAS.Verified.Expr.DiffDerivation.build 0
𝕏[0].cos.neg).rawDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.eval_simplifiedDerivative_eq_rawDerivative
      [CAS.explanation.checkedStep] Primitive derivative in x: side-conditioned display
normalization
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ
              (CAS.Command.displayDerivativeRoute (CAS.Verified.Expr.DiffDerivation.build 0
𝕏[0].cos.neg)).nonzero →
            CAS.Verified.Expr.eval ρ
                (CAS.Command.displayDerivativeRoute (CAS.Verified.Expr.DiffDerivation.build 0
𝕏[0].cos.neg)).rhs =
              CAS.Verified.Expr.eval ρ (CAS.Verified.Expr.DiffDerivation.build 0
𝕏[0].cos.neg).simplifiedDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.displayDerivativeRoute_sound
      [CAS.explanation.checkedStep] Primitive derivative in x: analytic semantics of the displayed
result
        Proposition: ∀ (x : ℝ^1),
          CAS.Verified.Expr.ValidAt x.ofLp 𝕏[0].cos.neg →
            CAS.Verified.Expr.Alg.SideHolds x.ofLp
                (CAS.Command.displayDerivativeRoute (CAS.Verified.Expr.DiffDerivation.build 0
𝕏[0].cos.neg)).nonzero →
              (fderiv ℝ (fun y ↦ CAS.Verified.Expr.eval y.ofLp 𝕏[0].cos.neg) x)
(EuclideanSpace.single 0 1) =
                CAS.Verified.Expr.eval x.ofLp
                  (CAS.Command.displayDerivativeRoute (CAS.Verified.Expr.DiffDerivation.build 0
𝕏[0].cos.neg)).rhs
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.fderiv_apply_single_eq_eval_displayDerivative
      [CAS.explanation.checkedStep] Residual route reaches zero
        Proposition: (CAS.IntegrationCheck.route 0 𝕏[0].sin
              { candidate := 𝕏[0].cos.neg, routeZero := ⋯ }.candidate).rhs =
          0
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.IntegrationCheck.AntiderivativeCert.routeZero
      [CAS.explanation.checkedStep] Symbolic antiderivative identity under the displayed
requirements
        Proposition: ∀ (x : ℝ^1),
          { candidate := 𝕏[0].cos.neg, routeZero := ⋯ }.requirements.Holds x.ofLp →
            CAS.Verified.Expr.eval x.ofLp
                (CAS.Verified.Expr.diff 0 { candidate := 𝕏[0].cos.neg, routeZero := ⋯ }.candidate) =
              CAS.Verified.Expr.eval x.ofLp 𝕏[0].sin
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.IntegrationCheck.AntiderivativeCert.eval_diff_eq
      [CAS.explanation.checkedStep] Coordinate-line derivative theorem
        Proposition: ∀ (x : ℝ^1) (t : ℝ),
          { candidate := 𝕏[0].cos.neg, routeZero := ⋯ }.requirements.Holds
              (x.ofLp + t • (EuclideanSpace.single 0 1).ofLp) →
            HasDerivAt
              (fun s ↦
                CAS.Verified.Expr.eval (x + s • EuclideanSpace.single 0 1).ofLp
                  { candidate := 𝕏[0].cos.neg, routeZero := ⋯ }.candidate)
              (CAS.Verified.Expr.eval (x + t • EuclideanSpace.single 0 1).ofLp 𝕏[0].sin) t
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.IntegrationCheck.AntiderivativeCert.hasDerivAt_eval_add_smul_single
      [CAS.explanation.checkedStep] Coordinate-line fundamental theorem of calculus
        Proposition: ∀ (x : ℝ^1) (a b : ℝ),
          (∀ t ∈ Set.uIcc a b,
              { candidate := 𝕏[0].cos.neg, routeZero := ⋯ }.requirements.Holds
                (x.ofLp + t • (EuclideanSpace.single 0 1).ofLp)) →
            ∫ (t : ℝ) in a..b, CAS.Verified.Expr.eval (x + t • EuclideanSpace.single 0 1).ofLp
𝕏[0].sin =
              CAS.Verified.Expr.eval (x + b • EuclideanSpace.single 0 1).ofLp
                  { candidate := 𝕏[0].cos.neg, routeZero := ⋯ }.candidate -
                CAS.Verified.Expr.eval (x + a • EuclideanSpace.single 0 1).ofLp
                  { candidate := 𝕏[0].cos.neg, routeZero := ⋯ }.candidate
        Validation: proof term checked by the kernel against this proposition
        Theorem:
CAS.IntegrationCheck.AntiderivativeCert.intervalIntegral_eq_sub_eval_add_smul_single
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] direct: ordered-sparse-polynomial: attempted
        checked
      [CAS.explanation.plannerStep] direct: pythagorean: attempted
        checked
      [CAS.explanation.plannerStep] direct: algebra: attempted
        checked
      [CAS.explanation.plannerStep] direct: pythagorean: attempted
        checked
      [CAS.explanation.plannerStep] direct: algebra: attempted
        checked
-/
#guard_msgs (info, substring := true) in
#cas [integrate] (sin x)

/--
info: #cas [integrate x]
Domain: x ∈ ℝ
Input (scalar ℝ): (sin x ^ 4)
Output (scalar ℝ; antiderivative): 3/8*x - 5/8*sin(x)*cos(x) + 1/4*sin(x)*cos(x)^3

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [integrate x] (sin x ^ 4)

/--
info: #cas [integrate x]
Domain: x ∈ ℝ
Input (scalar ℝ): (atan x)
Output (scalar ℝ; antiderivative): x*atan(x) - 1/2*log(1 + x^2)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [integrate x] (atan x)

/--
info: #cas [integrate x]
Domain: x ∈ ℝ
Input (scalar ℝ): (arccos x)
Output (scalar ℝ; antiderivative): x*acos(x) - sqrt(1 - x^2)
Conditions: x + 1 ≠ 0; x - 1 ≠ 0; 1 - x^2 > 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [integrate x] (arccos x)

/--
info: #cas [integrate x]
Domain: x ∈ ℝ
Input (scalar ℝ): (1 / sqrt (1 - x ^ 2))
Output (scalar ℝ; antiderivative): asin(x)
Conditions: x + 1 ≠ 0; x - 1 ≠ 0; 1 - x^2 > 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [integrate x] (1 / sqrt (1 - x ^ 2))

set_option linter.style.longLine false in
/--
info: #cas [integrate x]
Domain: x ∈ ℝ
Input (scalar ℝ): (1 / sin (2 * x) ^ 2)
Output (scalar ℝ; antiderivative): -(1/2/(sin(2*x)/cos(2*x)))
Conditions: sin(2*x) ≠ 0; cos(2*x) ≠ 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [integrate x] (1 / sin (2 * x) ^ 2)

/--
info: #cas [integrate x]
Domain: x ∈ ℝ
Input (scalar ℝ): (1 / (x * log x))
Output (scalar ℝ; antiderivative): log(log(x))
Conditions: x ≠ 0; log(x) ≠ 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [integrate x] (1 / (x * log x))

/--
info: #cas [integrate x]
Domain: (x, a, b) ∈ ℝ^3
Input (scalar ℝ): ((a * x + b) / (1 + x ^ 2))
Output (scalar ℝ; antiderivative): a*1/2*log(x^2 + 1) + b*atan(x)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [integrate x] ((a * x + b) / (1 + x ^ 2))

/--
info: #cas [integrate]
Domain: x ∈ ℝ
Input (scalar ℝ): (sin x) ^ 3 * (cos x) ^ 2
Output (scalar ℝ; antiderivative): -(1/3*cos(x)^3) + 1/5*cos(x)^5

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [integrate] (fun x ↦ (sin x) ^ 3 * (cos x) ^ 2)

/--
info: #cas [enclose x in [0, 1]]
Domain: x ∈ [0, 1] ⊆ ℝ
Input (scalar map ℝ → ℝ): (x / (1 + x))
Output (certified interval in ℝ): [0, 1/2]
Upper bound: 1/2
Absolute bound: 1/2
Center and radius: 1/4 ± 1/4

[CAS.Command.details] More details
  Coordinates: x
  Certified domain: x ∈ [0, 1] ⊆ ℝ
  [CAS.Command.computation] Certified numerical guarantee
    Guarantee: the input lies in the output interval throughout the box
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Enclosure of the input
        Proposition: ∀ x ∈ Set.Icc 0 1, 0 ≤ x / (1 + x) ∧ x / (1 + x) ≤ 1 / 2
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Tactic.BoxInequality.mem_of_enclosedOn_box
      [CAS.explanation.checkedStep] Upper bound of the input
        Proposition: ∀ x ∈ Set.Icc 0 1, x / (1 + x) ≤ 1 / 2
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Tactic.BoxInequality.le_of_boundOn_box
      [CAS.explanation.checkedStep] Absolute bound of the input
        Proposition: ∀ x ∈ Set.Icc 0 1, |x / (1 + x)| ≤ 1 / 2
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Tactic.BoxInequality.abs_le_of_boundOn_abs_box
      [CAS.explanation.checkedStep] Center and radius of the input
        Proposition: ∀ x ∈ Set.Icc 0 1, |x / (1 + x) - 1 / 4| ≤ 1 / 4
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Tactic.BoxInequality.abs_sub_le_of_approxOn_box
      [CAS.explanation.checkedStep] Certified enclosure
        Proposition: CAS.Certificate.EnclosedOn (CAS.Exact.exprFn (𝕏[0].div ((CAS.Verified.Expr.nat
1).add 𝕏[0])))
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦
            [CAS.Continuum.RationalInterval.ofBounds 0 1 ⋯].get coordinate)
          (↑0 / ↑1) (↑1 / ↑2)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.enclosedOn_of_interval_eq
      [CAS.explanation.checkedStep] Certified upper bound
        Proposition: CAS.Certificate.BoundOn (CAS.Exact.exprFn (𝕏[0].div ((CAS.Verified.Expr.nat
1).add 𝕏[0])))
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦
            [CAS.Continuum.RationalInterval.ofBounds 0 1 ⋯].get coordinate)
          (↑1 / ↑2)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.boundOn_of_interval_eq
      [CAS.explanation.checkedStep] Certified absolute bound
        Proposition: CAS.Certificate.BoundOn
          (fun x ↦ |CAS.Exact.exprFn (𝕏[0].div ((CAS.Verified.Expr.nat 1).add 𝕏[0])) x|)
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦
            [CAS.Continuum.RationalInterval.ofBounds 0 1 ⋯].get coordinate)
          (↑1 / ↑2)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.boundOn_abs_of_interval_eq
      [CAS.explanation.checkedStep] Certified center and radius
        Proposition: CAS.Certificate.ApproxOn (CAS.Exact.exprFn (𝕏[0].div ((CAS.Verified.Expr.nat
1).add 𝕏[0])))
          (fun x ↦ ↑1 / ↑4)
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦
            [CAS.Continuum.RationalInterval.ofBounds 0 1 ⋯].get coordinate)
          (↑1 / ↑4)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.approxOn_center_of_interval_eq
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] increasing endpoint range: succeeded
      [CAS.explanation.plannerStep] positive reciprocal range: succeeded
        used by 2 local enclosure routes
      [CAS.explanation.plannerStep] exact normalization: succeeded
-/
#guard_msgs in
#cas [enclose x in [0, 1]] (x / (1 + x))

/--
info: #cas [enclose x in [0, 1]]
Domain: x ∈ [0, 1] ⊆ ℝ
Input (scalar map ℝ → ℝ): (sin x)
Output (certified interval in ℝ): [0, 0.841471]
Upper bound: 0.841471
Absolute bound: 0.841471
Center and radius: ≈0.420735 ± 0.420736

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [enclose x in [0, 1]] (sin x)

/--
info: #cas [enclose x in [10, 1001 / 100]]
Domain: x ∈ [10, 1001/100] ⊆ ℝ
Input (scalar map ℝ → ℝ): (sin x)
Output (certified interval in ℝ): [-0.552385, -0.544021]
Upper bound: -0.544021
Absolute bound: 0.552385
Center and radius: ≈-0.548203 ± 0.004182

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [enclose x in [10, 1001 / 100]] (sin x)

/--
info: #cas [enclose x in [0, 1]]
Domain: x ∈ [0, 1] ⊆ ℝ
Input (scalar map ℝ → ℝ): (sin x ^ 2 + cos x ^ 2)
Output (certified interval in ℝ): [1, 1]
Upper bound: 1
Absolute bound: 1
Center and radius: 1 ± 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [enclose x in [0, 1]] (sin x ^ 2 + cos x ^ 2)

/--
info: #cas [enclose x in [9 / 10, 11 / 10]]
Domain: x ∈ [9/10, 11/10] ⊆ ℝ
Input (scalar map ℝ → ℝ): (x * exp (-x))
Output (certified interval in ℝ): [0.356443, 0.379316]
Upper bound: 0.379316
Absolute bound: 0.379316
Center and radius: ≈0.367879 ± 0.011437

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [enclose x in [9 / 10, 11 / 10]] (x * exp (-x))

set_option linter.style.longLine false in
/--
info: #cas (prec := 40) [enclose x in [0, 1]]
Domain: x ∈ [0, 1] ⊆ ℝ
Input (scalar map ℝ → ℝ): (exp x)
Output (certified interval in ℝ): [1, 2.718282]
Upper bound: 2.718282
Absolute bound: 2.718282
Center and radius: ≈1.859140 ± 0.859142

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (prec := 40) [enclose x in [0, 1]] (exp x)

/--
info: #cas [enclose x in [-5, 5]]
Domain: x ∈ [-5, 5] ⊆ ℝ
Input (scalar map ℝ → ℝ): (tanh x)
Output (certified interval in ℝ): [-0.999910, 0.999910]
Upper bound: 0.999910
Absolute bound: 0.999910
Center and radius: ≈-0.000001 ± 0.999911

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [enclose x in [-5, 5]] (tanh x)

/--
info: #cas [enclose x in [-2, 1]]
Domain: x ∈ [-2, 1] ⊆ ℝ
Input (scalar map ℝ → ℝ): (|x|)
Output (certified interval in ℝ): [0, 2]
Upper bound: 2
Absolute bound: 2
Center and radius: 1 ± 1

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [enclose x in [-2, 1]] (|x|)

/--
info: #cas [enclose x in [-1 / 2, 1 / 2]]
Domain: x ∈ [-1/2, 1/2] ⊆ ℝ
Input (scalar map ℝ → ℝ): (arcsin x)
Output (certified interval in ℝ): [-0.523599, 0.523599]
Upper bound: 0.523599
Absolute bound: 0.523599
Center and radius: 0 ± 0.523599

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [enclose x in [-1 / 2, 1 / 2]] (arcsin x)

/--
info: #cas [enclose x in [0, 1], y in [2, 3]]
Domain: x ∈ [0, 1], y ∈ [2, 3] ⊆ ℝ^2
Input (scalar map ℝ^2 → ℝ): (x * y)
Output (certified interval in ℝ): [0, 3]
Upper bound: 3
Absolute bound: 3
Center and radius: 3/2 ± 3/2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [enclose x in [0, 1], y in [2, 3]] (x * y)

/--
info: #cas [enclose x in [0, 1]]
Domain: x ∈ [0, 1] ⊆ ℝ
Input (scalar map ℝ → ℝ): (x - 2)
Output (certified interval in ℝ): [-2, -1]
Upper bound: -1
Absolute bound: 2
Center and radius: -3/2 ± 1/2

[CAS.Command.details] More details
  Coordinates: x
  Certified domain: x ∈ [0, 1] ⊆ ℝ
  [CAS.Command.computation] Certified numerical guarantee
    Guarantee: the input lies in the output interval throughout the box
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Enclosure of the input
        Proposition: ∀ x ∈ Set.Icc 0 1, -2 ≤ x - 2 ∧ x - 2 ≤ -1
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Tactic.BoxInequality.mem_of_enclosedOn_box
      [CAS.explanation.checkedStep] Upper bound of the input
        Proposition: ∀ x ∈ Set.Icc 0 1, x - 2 ≤ -1
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Tactic.BoxInequality.le_of_boundOn_box
      [CAS.explanation.checkedStep] Absolute bound of the input
        Proposition: ∀ x ∈ Set.Icc 0 1, |x - 2| ≤ 2
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Tactic.BoxInequality.abs_le_of_boundOn_abs_box
      [CAS.explanation.checkedStep] Center and radius of the input
        Proposition: ∀ x ∈ Set.Icc 0 1, |x - 2 + 3 / 2| ≤ 1 / 2
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Tactic.BoxInequality.abs_sub_le_of_approxOn_box
      [CAS.explanation.checkedStep] Certified enclosure
        Proposition: CAS.Certificate.EnclosedOn (CAS.Exact.exprFn (𝕏[0].sub (CAS.Verified.Expr.nat
2)))
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦
            [CAS.Continuum.RationalInterval.ofBounds 0 1 ⋯].get coordinate)
          (↑(-2) / ↑1) (↑(-1) / ↑1)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.enclosedOn_of_interval_eq
      [CAS.explanation.checkedStep] Certified upper bound
        Proposition: CAS.Certificate.BoundOn (CAS.Exact.exprFn (𝕏[0].sub (CAS.Verified.Expr.nat 2)))
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦
            [CAS.Continuum.RationalInterval.ofBounds 0 1 ⋯].get coordinate)
          (↑(-1) / ↑1)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.boundOn_of_interval_eq
      [CAS.explanation.checkedStep] Certified absolute bound
        Proposition: CAS.Certificate.BoundOn (fun x ↦ |CAS.Exact.exprFn (𝕏[0].sub
(CAS.Verified.Expr.nat 2)) x|)
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦
            [CAS.Continuum.RationalInterval.ofBounds 0 1 ⋯].get coordinate)
          (↑2 / ↑1)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.boundOn_abs_of_interval_eq
      [CAS.explanation.checkedStep] Certified center and radius
        Proposition: CAS.Certificate.ApproxOn (CAS.Exact.exprFn (𝕏[0].sub (CAS.Verified.Expr.nat
2)))
          (fun x ↦ ↑(-3) / ↑2)
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦
            [CAS.Continuum.RationalInterval.ofBounds 0 1 ⋯].get coordinate)
          (↑1 / ↑2)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.approxOn_center_of_interval_eq
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [enclose x in [0, 1]] (x - 2)

/--
info: #cas [enclose x in [0, 1]]
Domain: x ∈ [0, 1] ⊆ ℝ
Input (scalar map ℝ → ℝ): (x ^ 2 + x)
Output (certified interval in ℝ): [0, 2]
Upper bound: 2
Absolute bound: 2
Center and radius: 1 ± 1

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [enclose x in [0, 1]] (x ^ 2 + x)

