/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.Hyperbolic.Symbolic.Transport.RightMovingSine
public import PDE.Symbolic.Calculus.PointwiseResidualSemantics

/-!
# Transport residuals in vector and integral form

The unit spacetime vector `(1, 1)` annihilates the gradient of `sin(x - t)`, so the
transport integrand vanishes, both as a symbolic expression and as the advective
derivative, and its integral over every set `Ω ⊆ ℝ^2` is zero.
-/

@[expose] public section

open PDE (advectiveDerivative)

namespace TransportEquation.Symbolic

open CAS
open CAS.Certificate
open CAS.Euclid2
open scoped CAS
open MeasureTheory

noncomputable section

/-- Constant spacetime transport vector `(1,1)`, giving `∂ₜ + ∂ₓ`. -/
def unitTransportVector2 : Fin 2 → Verified.Expr (Fin 2) :=
  ![(1 : Verified.Expr (Fin 2)), (1 : Verified.Expr (Fin 2))]

/-- Symbolic transport residual `(1,1) · ∇sin(x-t)`. -/
def rightMovingSineTransportResidual : Verified.Expr (Fin 2) :=
  transportResidualIntegrand
    unitTransportVector2 rightMovingSineAnsatz (0 : Verified.Expr (Fin 2))

/-- The transport integrand vanishes uniformly. -/
theorem rightMovingSine_transport_residual_bound :
    ResidualBound (Exact.exprFn rightMovingSineTransportResidual) Set.univ 0 := by
  cas

private theorem rightMovingSineTransportResidual_eqOn_zero :
    Set.EqOn
      (Exact.exprFn rightMovingSineTransportResidual)
      Exact.zeroFn
      Set.univ :=
  eqOn_zero_of_residualBound_zero rightMovingSine_transport_residual_bound

/-- Pointwise identity `(1,1) · ∇sin(x-t) = 0`. -/
theorem rightMovingSine_transport_residual_eval_zero
    (p : ℝ^2) :
    (transportResidualIntegrand
      unitTransportVector2 rightMovingSineAnsatz (0 : Verified.Expr (Fin 2))).eval p = 0 := by
  simpa [rightMovingSineTransportResidual, Exact.exprFn, Exact.zeroFn] using
    rightMovingSineTransportResidual_eqOn_zero (Set.mem_univ p)

/-- The symbolic residual evaluates to the analytic advection operator. -/
theorem rightMovingSine_transport_eval_eq_advectiveDerivative
    (p : ℝ^2) :
    (transportResidualIntegrand
      unitTransportVector2 rightMovingSineAnsatz (0 : Verified.Expr (Fin 2))).eval p =
      advectiveDerivative
        (fun q : ℝ^2 ↦
          WithLp.toLp 2 (fun i : Fin 2 ↦ (unitTransportVector2 i).eval q))
        (fun q : ℝ^2 ↦ rightMovingSineAnsatz.eval q) p := by
  simpa using transportResidualIntegrand_eval_eq_advectiveDerivative_sub
    (b := unitTransportVector2) (u := rightMovingSineAnsatz)
    (f := (0 : Verified.Expr (Fin 2))) (x := p)
    (by
      unfold rightMovingSineAnsatz
      symbolic_assumptions)

/--
The transport residual integrates to zero on every set `Ω`.
-/
theorem rightMovingSine_transport_integral_zero
    (Ω : Set (ℝ^2)) :
    (∫ q in Ω,
      (transportResidualIntegrand
        unitTransportVector2 rightMovingSineAnsatz (0 : Verified.Expr (Fin 2))).eval q) = 0 := by
  calc
    (∫ q in Ω,
      (transportResidualIntegrand
        unitTransportVector2 rightMovingSineAnsatz (0 : Verified.Expr (Fin 2))).eval q) =
        ∫ _q in Ω, (0 : ℝ) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with q
          exact rightMovingSine_transport_residual_eval_zero q
    _ = 0 := by simp

/-- The symbolic residual integral agrees with the integral of analytic advection. -/
theorem rightMovingSine_transport_integral_eq_advectiveDerivative
    (Ω : Set (ℝ^2)) :
    (∫ q in Ω,
      (transportResidualIntegrand
        unitTransportVector2 rightMovingSineAnsatz (0 : Verified.Expr (Fin 2))).eval q) =
      ∫ q in Ω,
        advectiveDerivative
          (fun r : ℝ^2 ↦
            WithLp.toLp 2 (fun i : Fin 2 ↦ (unitTransportVector2 i).eval r))
          (fun r : ℝ^2 ↦ rightMovingSineAnsatz.eval r) q := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with q
  exact rightMovingSine_transport_eval_eq_advectiveDerivative q

/-- Analytic advection integrates to zero on any domain. -/
theorem rightMovingSine_transport_advectiveDerivative_integral_zero
    (Ω : Set (ℝ^2)) :
    (∫ q in Ω,
      advectiveDerivative
        (fun r : ℝ^2 ↦
          WithLp.toLp 2 (fun i : Fin 2 ↦ (unitTransportVector2 i).eval r))
        (fun r : ℝ^2 ↦ rightMovingSineAnsatz.eval r) q) = 0 := by
  rw [← rightMovingSine_transport_integral_eq_advectiveDerivative Ω]
  exact rightMovingSine_transport_integral_zero Ω
end

end TransportEquation.Symbolic
