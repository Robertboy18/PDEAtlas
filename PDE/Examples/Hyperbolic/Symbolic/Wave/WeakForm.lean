/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Symbolic.Calculus.WeakFormIntegrands
public import PDE.Examples.Hyperbolic.Symbolic.Transport.RightMovingSine

/-!
# The weak wave integrand of the traveling sine wave

The weak form of `u_tt - Δu = f` against a test function `v` has pointwise integrand
`u_tt v + ∇u · ∇v - f v`. For the traveling profile `u(t, x) = sin(x - t)`, source `f = 0`
and the constant test function `v = 1`, the gradient term carries `∇v = 0`, so the integrand
reduces to `u_tt = -sin(x - t)`. The reduction holds symbolically and pointwise in terms
of Euclidean partial derivatives.

The first symbolic coordinate `x` is time and the second `y` is space, matching
`PDE.Examples.Hyperbolic.Symbolic.Wave.TravelingSine`.

## Main results

* `travelingWave1DWeakResidual`: the difference between the symbolic weak integrand
  `waveWeakResidualIntegrand x [y] u 0 1` and the expected closed form `-sin(y - x)`.
* `travelingWave1D_weak_integrand_residual_bound`: the residual has uniform bound `0`.
* `travelingWave1D_weak_integrand_eval_eq_euclidean_derivatives`: the symbolic integrand
  evaluates to the coordinate formula in Euclidean partials.
* `travelingWave1D_weak_integrand_eval_eq_expected`: the integrand equals `-sin(x - t)`
  pointwise.
-/

@[expose] public section

namespace WaveEquation.Symbolic

open TransportEquation.Symbolic (rightMovingSineAnsatz)

open CAS
open CAS.Certificate
open CAS.Euclid2
open scoped CAS

noncomputable section

/--
Residual of the weak-wave integrand identity for `u(t,x) = sin(x-t)` and `v = 1`.

The weak integrand `u_tt v + u_x v_x - f v` is compared with its closed form
`-sin(x-t)`, so this expression vanishes identically.
-/
def travelingWave1DWeakResidual : Verified.Expr (Fin 2) :=
  waveWeakResidualIntegrand
      x [y] rightMovingSineAnsatz
      (0 : Verified.Expr (Fin 2)) (1 : Verified.Expr (Fin 2)) -
    (-(.sin (y - x : Verified.Expr (Fin 2))) : Verified.Expr (Fin 2))

/-- The residual `travelingWave1DWeakResidual` is bounded by `0` on all of spacetime. -/
theorem travelingWave1D_weak_integrand_residual_bound :
    ResidualBound
      (Exact.exprFn travelingWave1DWeakResidual)
      Set.univ
      0 := by
  cas

/-- The weak integrand in terms of Euclidean partial derivatives. -/
theorem travelingWave1D_weak_integrand_eval_eq_euclidean_derivatives
    (p : ℝ^2) :
    (waveWeakResidualIntegrand
        x [y] rightMovingSineAnsatz
        (0 : Verified.Expr (Fin 2)) (1 : Verified.Expr (Fin 2))).eval p =
      (∂[x.idx]
          (fun q : ℝ^2 ↦
            (Verified.Expr.closedPartial x.idx rightMovingSineAnsatz).eval q)) p *
        (1 : Verified.Expr (Fin 2)).eval p +
      ([y].map fun coord ↦
        (∂[coord.idx]
            (fun q : ℝ^2 ↦ rightMovingSineAnsatz.eval q)) p *
          (∂[coord.idx]
            (fun q : ℝ^2 ↦ (1 : Verified.Expr (Fin 2)).eval q)) p).sum -
      (0 : Verified.Expr (Fin 2)).eval p * (1 : Verified.Expr (Fin 2)).eval p := by
  exact waveWeakResidualIntegrand_eval_eq_time2_mul_add_spatial_sum_sub
    (t := x) (spatial := [y]) (u := rightMovingSineAnsatz)
    (f := (0 : Verified.Expr (Fin 2))) (v := (1 : Verified.Expr (Fin 2))) (p := p)
    (by symbolic_assumptions) (by symbolic_assumptions) (by symbolic_assumptions)

/-- The second time derivative of `sin(x - t)` is `-sin(x - t)`. -/
private theorem travelingWave1D_timeSecond_closedPartial_eval
    (p : ℝ^2) :
      (Verified.Expr.diff x.idx
        (Verified.Expr.closedPartial x.idx rightMovingSineAnsatz) : Verified.Expr (Fin 2)).eval p =
      (-(.sin
          (y - x : Verified.Expr (Fin 2))) : Verified.Expr (Fin 2)).eval p := by
  unfold rightMovingSineAnsatz
  cas

/-- The weak integrand equals `-sin(x - t)`. -/
theorem travelingWave1D_weak_integrand_eval_eq_expected
    (p : ℝ^2) :
    (waveWeakResidualIntegrand
        x [y] rightMovingSineAnsatz
        (0 : Verified.Expr (Fin 2)) (1 : Verified.Expr (Fin 2))).eval p =
      (-(.sin
          (y - x : Verified.Expr (Fin 2))) : Verified.Expr (Fin 2)).eval p := by
  rw [travelingWave1D_weak_integrand_eval_eq_euclidean_derivatives]
  have htvalid :
      (Verified.Expr.closedPartial x.idx
        rightMovingSineAnsatz : Verified.Expr (Fin 2)).ValidAt p := by
    unfold rightMovingSineAnsatz
    symbolic_assumptions
  have htt := Verified.Expr.partialDeriv_eval_eq
    (expr := (Verified.Expr.closedPartial x.idx rightMovingSineAnsatz : Verified.Expr (Fin 2)))
    (x := p) (i := x.idx) htvalid
  rw [htt]
  rw [travelingWave1D_timeSecond_closedPartial_eval]
  simp [Verified.Expr.eval]

end

end WaveEquation.Symbolic
