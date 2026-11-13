/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Symbolic.Calculus.MixedDerivatives
public import PDE.Symbolic.Calculus.ParameterEmbeddingOperators

/-!
# Mixed derivatives with fixed real parameters

For `expr : Expr (Fin (n + k))` evaluated along `paramEmbed c`, a mixed derivative along a
word of the first `n` coordinates is the symbolic derivative along the corresponding word
of embedded coordinates (`iteratedPartialDeriv_eval_paramEmbed`). The parameters are
never differentiated.
-/

@[expose] public section

namespace CAS.Verified.Expr

open PDE
open scoped Topology

/--
A mixed derivative in the first `n` coordinates commutes with fixing the parameter
coordinates. The parameters are arbitrary real numbers and are never differentiated.
-/
theorem iteratedPartialDeriv_eval_paramEmbed {n k : ℕ}
    (expr : Expr (Fin (n + k))) (parameters : Fin k → ℝ)
    (indices : List (Fin n)) (x : ℝ^n)
    (hvalid : expr.ValidMixedAt (indices.map (Fin.castAdd k)) (paramEmbed parameters x)) :
    iteratedPartialDeriv indices
      (fun y : ℝ^n ↦ expr.eval (paramEmbed parameters y)) x =
        (expr.mixedDiff (indices.map (Fin.castAdd k))).eval (paramEmbed parameters x) := by
  induction indices generalizing x with
  | nil => rfl
  | cons i rest ih =>
      have heq :
          (fun y : ℝ^n ↦ iteratedPartialDeriv rest
            (fun q : ℝ^n ↦ expr.eval (paramEmbed parameters q)) y) =ᶠ[𝓝 x]
          fun y ↦ (expr.mixedDiff (rest.map (Fin.castAdd k))).eval
            (paramEmbed parameters y) := by
        filter_upwards [(hasFDerivAt_paramEmbed parameters x).continuousAt.tendsto.eventually
          hvalid.1.eventually] with y hy
        exact ih y hy
      exact (partialDeriv_congr_nhds i heq).trans
        (partialDeriv_eval_paramEmbed_eq
          (expr.mixedDiff (rest.map (Fin.castAdd k))) parameters x i (Fin.castAdd k i)
          rfl hvalid.2)

end CAS.Verified.Expr
