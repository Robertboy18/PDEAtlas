/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Symbolic.Calculus.Operators
public meta import PDE.Symbolic.Calculus.Operators
public import CAS.Command.Differential
public meta import CAS.Command.Differential

/-!
# Laplacian reports for `#cas`

The command `#cas [laplacian x, y, ...] e` logs an InfoView report of the coordinate Laplacian
`PDE.laplacian` of `e` in exactly the listed coordinate space. It reuses the scalar derivative
computation of `#cas [derive]` for the first and second partial in each coordinate and validates
the diagonal-sum assembly theorem `closedLaplacian_eval_eq_laplacian`.

`partialDeriv_eq_eval_displayDerivative` restates the evidence theorem of `#cas [derive]`,
`fderiv_apply_single_eq_eval_displayDerivative`, with the coordinate derivative `∂[i]`.
-/

public meta section

namespace CAS.Command

open Lean Elab Command Meta
open CAS.Command.InfoView
open CAS.Tactic.Explanation

/-- The displayed expression equals the coordinate derivative when the input is
analytically valid and the display route's nonzero conditions hold at the point. -/
theorem partialDeriv_eq_eval_displayDerivative {n : Nat}
    {coordinate : Fin n} {input output : Verified.Expr (Fin n)}
    (derivation : Verified.Expr.DiffDerivation coordinate input output) :
    ∀ (x : ℝ^n), input.ValidAt x →
      Verified.Expr.Alg.SideHolds x.ofLp (displayDerivativeRoute derivation).nonzero →
        (∂[coordinate] (fun y : ℝ^n ↦ input.eval y.ofLp)) x =
          (displayDerivativeRoute derivation).rhs.eval x.ofLp :=
  fderiv_apply_single_eq_eval_displayDerivative derivation

private def laplacianAssemblyEvidence {n : Nat}
    (input : Verified.Expr (Fin n)) : MetaM UncheckedExplanationStep := do
  let inputTerm ← quoteVerifiedExpr input
  let proof :=
    mkAppN (.const ``Verified.Expr.closedLaplacian_eval_eq_laplacian [])
      #[Lean.toExpr n, inputTerm]
  proofStep "Analytic Laplacian assembly"
    ``Verified.Expr.closedLaplacian_eval_eq_laplacian proof

/-- Compute the coordinate Laplacian and emit its checked analytic report. -/
def logLaplacian (ref : Syntax) (reified : ReifiedExpr) : CommandElabM Unit := do
  let coordinates := List.finRange reified.names.length
  let components := coordinates.map fun coordinate ↦
    let name := reified.names.get coordinate
    let first := Verified.Expr.DiffDerivation.build coordinate reified.expr
    let second := Verified.Expr.DiffDerivation.build coordinate (reified.expr.diff coordinate)
    computationNode s!"Second partial ∂_{renderName name}∂_{renderName name}" #[
      derivativeComputation reified name first,
      derivativeComputation reified name second,
      m!"summand: {renderExpr reified second.simplifiedDerivative}"
    ]
  let secondPartials :=
    coordinates.map fun coordinate ↦
      (reified.expr.diff coordinate).closedPartial coordinate
  let result := reified.expr.closedLaplacian
  let requirements := laplacianRequirements reified.expr
  let report ← liftTermElabM do
    let mut steps := #[]
    for coordinate in coordinates do
      let name := reified.names.get coordinate
      steps := steps ++
        (← derivativeEvidence s!"First partial in {renderName name}"
          coordinate reified.expr)
      steps := steps ++
        (← derivativeEvidence s!"Second partial in {renderName name}"
          coordinate (reified.expr.diff coordinate))
    steps := steps.push (← laplacianAssemblyEvidence reified.expr)
    evidenceReportMessage steps
  logReport ref {
    domain := renderRealDomain reified.names
    input := reified.render
    inputType := "scalar ℝ"
    output := renderExpr reified result
    outputType := "scalar ℝ"
    conditions? := renderConditions reified requirements
  } #[
    m!"Variables: {renderNames reified.names}",
    requirementsComputation reified "Analytic domain conditions" requirements,
    computationNode "Checked coordinate computations" components.toArray,
    computationNode "Sum and normalize the diagonal second partials" #[
      m!"Summands: {renderExprList reified secondPartials}",
      m!"Normalized sum: {renderExpr reified result}"
    ],
    report
  ]

end CAS.Command

namespace CAS.Command

open Lean Elab Command

/-- Compute the symbolic Laplacian in exactly the listed coordinate space. -/
syntax (name := casLaplacianCommand) "#cas" "[" &"laplacian" ident,* "]" term : command

elab_rules : command
  | `(#cas [laplacian $names:ident,*] $expr:term) => do
      let declared := names.getElems.toList.map TSyntax.getId
      let reified ← parseExact expr declared
      logLaplacian expr reified

end CAS.Command
