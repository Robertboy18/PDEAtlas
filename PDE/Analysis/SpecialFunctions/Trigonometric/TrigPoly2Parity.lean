/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2Calculus
public meta import Lean.Elab.Tactic

/-!
# A tactic for the parities of trigonometric tables

`trig_parity` proves a goal `TrigPoly2.ParityAtβ a e p` or `TrigPoly2.ParityAtθ a e p`, with `a`
equal to `0` or `π / 2`, for a table `p` built by sums, differences, scalar multiples, products,
padding, partial derivatives and quotients by `sin` from the coordinate tables and from tables
whose parities are hypotheses in the context. It reads the operation at the head of the table and
applies the corresponding closure rule, so the sign of every product and derivative is computed
rather than searched for. The remaining side goals (sign equations between booleans, degree
inequalities and the support conditions of the quotients) are closed by `rfl`, `omega` and
`assumption`.
-/

public meta section

open Lean Meta Elab Tactic

namespace PDE.Analysis.TrigPoly2

/-- Whether an expression is the numeral `0`. -/
private def isZeroNumeral (a : Expr) : Bool :=
  a.isAppOfArity ``OfNat.ofNat 3 && (a.getArg! 1).rawNatLit? == some 0

/-- One closure step on the main goal. -/
private def trigParityStep : TacticM Unit := withMainContext do
  let tgt := (← whnfR (← instantiateMVars (← getMainTarget))).cleanupAnnotations
  let some n := tgt.getAppFn.constName? | evalTactic (← `(tactic| first | rfl | omega | assumption))
  if n != ``ParityAtβ && n != ``ParityAtθ then
    evalTactic (← `(tactic| first | rfl | omega | assumption))
    return
  let isβ := n == ``ParityAtβ
  let args := tgt.getAppArgs
  let a := args[args.size - 3]!
  let p := (← instantiateMVars args[args.size - 1]!).cleanupAnnotations
  let zero := isZeroNumeral a
  let tac ← match p.getAppFn.constName? with
  | some ``HAdd.hAdd =>
    if isβ then `(tactic| apply ParityAtβ.add) else `(tactic| apply ParityAtθ.add)
  | some ``HSub.hSub =>
    if isβ then `(tactic| apply ParityAtβ.sub) else `(tactic| apply ParityAtθ.sub)
  | some ``HSMul.hSMul =>
    if isβ then `(tactic| apply ParityAtβ.smul) else `(tactic| apply ParityAtθ.smul)
  | some ``TrigPoly2.mul =>
    if isβ then `(tactic| apply ParityAtβ.mul) else `(tactic| apply ParityAtθ.mul)
  | some ``TrigPoly2.resize =>
    if isβ then `(tactic| apply ParityAtβ.resize) else `(tactic| apply ParityAtθ.resize)
  | some ``TrigPoly2.dβ =>
    if isβ then `(tactic| apply ParityAtβ.dβ) else `(tactic| apply ParityAtθ.dβ)
  | some ``TrigPoly2.dθ =>
    if isβ then `(tactic| apply ParityAtβ.dθ) else `(tactic| apply ParityAtθ.dθ)
  | some ``TrigPoly2.divSinβ =>
    if isβ then
      if zero then `(tactic| exact parityAtβ_zero_divSinβ _)
      else `(tactic| apply ParityAtβ.divSinβ_pi_div_two)
    else `(tactic| apply ParityAtθ.divSinβ)
  | some ``TrigPoly2.divSinθ =>
    if isβ then `(tactic| apply ParityAtβ.divSinθ)
    else if zero then `(tactic| exact parityAtθ_zero_divSinθ _)
    else `(tactic| apply ParityAtθ.divSinθ_pi_div_two)
  | some ``OfNat.ofNat =>
    if isβ then `(tactic| exact parityAtβ_zero_table _ _)
    else `(tactic| exact parityAtθ_zero_table _ _)
  | some ``TrigPoly2.sinβ =>
    if isβ then
      if zero then `(tactic| exact parityAtβ_zero_sinβ)
      else `(tactic| exact parityAtβ_pi_div_two_sinβ)
    else `(tactic| exact parityAtθ_sinβ _)
  | some ``TrigPoly2.cosβ =>
    if isβ then
      if zero then `(tactic| exact parityAtβ_zero_cosβ)
      else `(tactic| exact parityAtβ_pi_div_two_cosβ)
    else `(tactic| exact parityAtθ_cosβ _)
  | some ``TrigPoly2.sinθ =>
    if isβ then `(tactic| exact parityAtβ_sinθ _)
    else if zero then `(tactic| exact parityAtθ_zero_sinθ)
    else `(tactic| exact parityAtθ_pi_div_two_sinθ)
  | some ``TrigPoly2.cosθ =>
    if isβ then `(tactic| exact parityAtβ_cosθ _)
    else if zero then `(tactic| exact parityAtθ_zero_cosθ)
    else `(tactic| exact parityAtθ_pi_div_two_cosθ)
  | _ => `(tactic| with_reducible assumption)
  evalTactic tac

/-- Proves `ParityAtβ a e p` or `ParityAtθ a e p` (`a = 0` or `a = π / 2`) for a table `p` built
from the coordinate tables and from tables with parity hypotheses in the context by sums,
differences, scalar multiples, products, padding, partial derivatives and quotients by `sin`. -/
elab (name := trigParity) "trig_parity" : tactic => do
  let rec loop (fuel : Nat) : TacticM Unit := do
    match fuel with
    | 0 => throwError "trig_parity: too many steps"
    | fuel + 1 =>
      if (← getGoals).isEmpty then return
      trigParityStep
      loop fuel
  loop 100000

end PDE.Analysis.TrigPoly2
