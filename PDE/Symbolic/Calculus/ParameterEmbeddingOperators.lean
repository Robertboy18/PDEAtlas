/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.Calculus.ParameterEmbedding
public import PDE.FDeriv.Calculus

/-!
# PDE derivatives along parameter embeddings

For `expr : Expr (Fin (n + k))` evaluated along `paramEmbed c`, the coordinate derivative
(`partialDeriv_eval_paramEmbed_eq`), the repeated coordinate derivative
(`partialDeriv_partialDeriv_eval_paramEmbed_eq`), and the Laplacian
(`laplacian_eval_paramEmbed_eq`) are evaluations of symbolic derivatives in the embedded
coordinates. Validity at the evaluation point suffices, since it persists on a
neighbourhood.
-/

@[expose] public section

namespace CAS

open PDE
open scoped BigOperators Topology

namespace Verified.Expr

variable {n k : ℕ}

/-- The coordinate partial derivative of an embedded checked expression is the evaluated
symbolic partial derivative with respect to the corresponding embedded coordinate. -/
theorem partialDeriv_eval_paramEmbed_eq (expr : Verified.Expr (Fin (n + k)))
    (c : Fin k → ℝ) (p : ℝ^n) (i : Fin n) (i' : Fin (n + k)) (hi : (i' : ℕ) = i)
    (h : expr.ValidAt (paramEmbed c p)) :
    (∂[i] (fun q : ℝ^n ↦ expr.eval (paramEmbed c q))) p =
      (expr.diff i').eval (paramEmbed c p) := by
  have hi' : i' = Fin.castAdd k i := Fin.ext (by simpa using hi)
  subst hi'
  unfold partialDeriv
  rw [(hasFDerivAt_eval_paramEmbed expr c p h).fderiv, ContinuousLinearMap.comp_apply,
    paramEmbedL_single]
  exact symbolicFDeriv_apply_single_eq_diff_eval expr (paramEmbed c p) (Fin.castAdd k i)

/-- A repeated coordinate partial derivative of an embedded checked expression is the
evaluation of the twice-differentiated symbolic expression. Only validity at the point is
required, because validity persists on a neighbourhood. -/
theorem partialDeriv_partialDeriv_eval_paramEmbed_eq (expr : Verified.Expr (Fin (n + k)))
    (c : Fin k → ℝ) (p : ℝ^n) (i j : Fin n) (i' j' : Fin (n + k))
    (hi : (i' : ℕ) = i) (hj : (j' : ℕ) = j)
    (h0 : expr.ValidAt (paramEmbed c p)) (h1 : (expr.diff j').ValidAt (paramEmbed c p)) :
    (∂[i]
        (fun q : ℝ^n ↦ (∂[j] (fun r : ℝ^n ↦ expr.eval (paramEmbed c r))) q)) p =
      ((expr.diff j').diff i').eval (paramEmbed c p) := by
  have hEq :
      (fun q : ℝ^n ↦ (∂[j] (fun r : ℝ^n ↦ expr.eval (paramEmbed c r))) q) =ᶠ[𝓝 p]
        fun q : ℝ^n ↦ (expr.diff j').eval (paramEmbed c q) := by
    filter_upwards [eventually_validAt_paramEmbed expr c p h0] with q hq
    exact partialDeriv_eval_paramEmbed_eq expr c q j j' hj hq
  rw [partialDeriv_congr_nhds i hEq]
  exact partialDeriv_eval_paramEmbed_eq (expr.diff j') c p i i' hi h1

/-- The coordinate Laplacian of an embedded checked expression is the sum of its evaluated
second symbolic derivatives, given validity of the expression and of its first symbolic
derivatives at the point. -/
theorem laplacian_eval_paramEmbed_eq (expr : Verified.Expr (Fin (n + k)))
    (c : Fin k → ℝ) (p : ℝ^n)
    (h0 : expr.ValidAt (paramEmbed c p))
    (h1 : ∀ i : Fin n, (expr.diff (Fin.castAdd k i)).ValidAt (paramEmbed c p)) :
    laplacian (fun q : ℝ^n ↦ expr.eval (paramEmbed c q)) p =
      ∑ i : Fin n,
        ((expr.diff (Fin.castAdd k i)).diff (Fin.castAdd k i)).eval (paramEmbed c p) := by
  unfold laplacian
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact partialDeriv_partialDeriv_eval_paramEmbed_eq expr c p i i _ _ (by simp) (by simp)
    h0 (h1 i)

end Verified.Expr

end CAS
