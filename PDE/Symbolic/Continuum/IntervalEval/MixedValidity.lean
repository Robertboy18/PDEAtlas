/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Symbolic.Calculus.MixedDerivatives
public import CAS.Continuum.IntervalEval.Validity

/-!
# Checked analytic domains for mixed derivatives

`validMixedOn?` proves `expr.ValidMixedAt word` at every point of a registry chart by checking
each intermediate derivative of the mixed derivative word with `validOn?`, which covers all
denominator and branch conditions. The word follows `Expr.mixedDiff`: its head is the outermost
derivative. If one level fails, the whole word is rejected.

The empty word needs no analytic domain certificate because it does not
differentiate the expression. Successful range evaluation is a separate check.
-/

@[expose] public section

namespace CAS.Continuum.RationalInterval.CertifiedEvalRegistry

open CAS.Verified

/-- Compile the analytic validity of every expression differentiated by a mixed
word on one chart. No domain condition is inferred from the final value range. -/
noncomputable def validMixedOn? {α : Type} {n : ℕ}
    {s : Set α} {ρ : α → ℝ^n}
    (registry : CertifiedEvalRegistry s (fun x i ↦ ρ x i))
    (expr : Expr (Fin n)) :
    (word : List (Fin n)) →
      Option (CertificateRoute (∀ x, x ∈ s → expr.ValidMixedAt word (ρ x)))
  | [] =>
      some { cert := by intro _x _hx; trivial }
  | _ :: rest =>
      match registry.validMixedOn? expr rest, registry.validOn? (expr.mixedDiff rest) with
      | some tail, some head =>
          some
            { steps := tail.steps ++ head.steps
              cert := by
                intro x hx
                exact ⟨tail.cert x hx, head.cert x hx⟩ }
      | _, _ => none

attribute [inherit_doc validMixedOn?]
  validMixedOn?.eq_1 validMixedOn?.eq_2 validMixedOn?.eq_def

end CAS.Continuum.RationalInterval.CertifiedEvalRegistry
