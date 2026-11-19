/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.SpaceTime
public import PDE.Symbolic.Calculus.EuclideanOperators

/-!
# Spatial slices of symbolic spacetime expressions

The heat operator `HeatEquation.heatOperator` takes the Laplacian of the fixed-time slice
`y ↦ u(t, y)` as a function on `ℝ^2`, while the symbolic residual of a spacetime expression
`expr : Verified.Expr (Fin 3)` is computed from spacetime partial derivatives in coordinates
`1` and `2`. The two agree: at a point `p = (t, x, y)`,

`Δ_y (expr.eval (t, ·)) (x, y) = ∂₁ (expr.diff 1).eval p + ∂₂ (expr.diff 2).eval p`.

The right-hand side mixes one symbolic derivative (`expr.diff i`) with one analytic
`partialDeriv`, because the certified residual checkers return their result in that form.
With this identity, the Gaussian and polynomial examples turn a symbolic
residual certificate into the heat equation.

## Main results

* `laplacian_timeSpaceCons_slice2_eval_eq`: the slice-Laplacian identity above.

## Implementation notes

The symbolic derivative `expr.diff i` equals the analytic derivative only where `expr` is
valid (all denominators, logarithms, and powers are in their domains). The theorem therefore
assumes validity of `expr` and of its first symbolic derivatives along the whole slice
`{t} × ℝ^2`, not only at `p`, since the outer derivative needs the inner identity on a
neighbourhood. Both hypotheses are discharged by `symbolic_assumptions` in the applications.
-/

@[expose] public section

open PDE (partialDeriv laplacian)

namespace HeatEquation.Symbolic.Space2

open PDE.Common
open CAS
open scoped CAS

noncomputable section

/-! ### Euclidean spatial-slice bridge -/

/--
For verified symbolic expressions in spacetime `(t,x,y)`, the Euclidean spatial
Laplacian of the fixed-time slice is the sum of spacetime second partials in
coordinates `1` and `2`.
-/
theorem laplacian_timeSpaceCons_slice2_eval_eq
    (expr : Verified.Expr (Fin 3)) (p : ℝ^3)
    (h0 : ∀ y : ℝ^2,
      expr.ValidAt (PDE.Common.timeSpaceCons (n := 2) (p 0) y))
    (h1 : ∀ (i : Fin 2) (y : ℝ^2),
      (expr.diff i.succ).ValidAt (PDE.Common.timeSpaceCons (n := 2) (p 0) y)) :
    laplacian (n := 2)
        (fun y : ℝ^2 ↦
          expr.eval (PDE.Common.timeSpaceCons (n := 2) (p 0) y))
        (spatialPartCLM 2 p) =
      (∂[(1 : Fin 3)]
          (fun q : ℝ^3 ↦ (expr.diff (1 : Fin 3)).eval q)) p +
        (∂[(2 : Fin 3)]
          (fun q : ℝ^3 ↦ (expr.diff (2 : Fin 3)).eval q)) p := by
  have hterm (i : Fin 2) :
      (∂[i] (fun y : ℝ^2 ↦ (∂[i] (fun z : ℝ^2 ↦
          expr.eval (PDE.Common.timeSpaceCons (n := 2) (p 0) z))) y)) (spatialPartCLM 2 p) =
        (∂[i.succ] (fun q : ℝ^3 ↦ (expr.diff i.succ).eval q)) p := by
    have hinner : (fun y : ℝ^2 ↦ (∂[i] (fun z : ℝ^2 ↦
        expr.eval (PDE.Common.timeSpaceCons (n := 2) (p 0) z))) y) =
          fun y ↦ (expr.diff i.succ).eval (PDE.Common.timeSpaceCons (n := 2) (p 0) y) :=
      funext fun y ↦ (PDE.partialDeriv_timeSpaceCons_spatial i (fun q ↦ expr.eval q) (p 0) y
        (expr.hasFDerivAt_eval _ (h0 y)).differentiableAt).trans
          (expr.partialDeriv_eval_eq _ i.succ (h0 y))
    rw [hinner, PDE.partialDeriv_timeSpaceCons_spatial i _ (p 0) _
      ((expr.diff i.succ).hasFDerivAt_eval _ (h1 i _)).differentiableAt,
      timeSpaceCons_spatialPartCLM]
  unfold laplacian
  simp only [Fin.sum_univ_two, hterm, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]

end

end HeatEquation.Symbolic.Space2
