/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Burgers.ColeHopf.Symbolic
public import PDE.Symbolic.ClosedForm.Tactic.Residual
public import CAS.ExactTactic
public import PDE.Hyperbolic.ConservationLaw.Burgers.ColeHopf
public import PDE.Parabolic.Symbolic.Heat.Equations

/-!
# A nonconstant Cole–Hopf profile

The positive heat profile `exp(t + x) + exp(t - x)` produces an explicit nonconstant velocity
under the unit-viscosity Cole–Hopf transform. It is an elementary instance of Evans, §4.4.1(b),
not an example stated in the text. Positivity proves that the transform denominator
never vanishes. Checked symbolic residuals then establish the heat equation and the transform
identity, while the analytic evaluation lemmas identify the result with the ordinary Cole–Hopf
transform.

The reflected syntax is used only to certify this explicit representation; the resulting
pointwise theorem is stated for the ordinary real-valued transform.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.4.1(b), equations (5)-(10).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace BurgersEquation.ColeHopf

open HeatEquation.Symbolic.Space1 (heat1DEquation)

open CAS
open CAS.Euclid2

noncomputable section

/--
A nonconstant heat profile built from two heat exponentials:
`v(t,x)=exp(t+x)+exp(t-x)`.

This is an elementary exponential form of the classical hyperbolic-tangent
Cole–Hopf profile.
-/
def coleHopfTwoExpProfile : Verified.Expr (Fin 2) :=
  .exp (x + y : Verified.Expr (Fin 2)) +
    .exp (x - y : Verified.Expr (Fin 2))

/-- The corresponding nonconstant unit-viscosity Cole–Hopf velocity. -/
def coleHopfTwoExpVelocity : Verified.Expr (Fin 2) :=
  -2 *
    (.exp (x + y : Verified.Expr (Fin 2)) -
      .exp (x - y : Verified.Expr (Fin 2))) /
      (.exp (x + y : Verified.Expr (Fin 2)) +
        .exp (x - y : Verified.Expr (Fin 2)))

/-- The heat-equation residual of the two-exponential profile. -/
def coleHopfTwoExpHeatResidual : Verified.Expr (Fin 2) :=
  Scalar.residual heat1DEquation coleHopfTwoExpProfile

/-- The symbolic transform evaluates to the explicit velocity at every point. -/
private theorem coleHopfTwoExp_transform_eval_eq_velocity (p : ℝ^2) :
    (coleHopfUnitTransformExpr coleHopfTwoExpProfile).eval p = coleHopfTwoExpVelocity.eval p := by
  cas

/-- The two-exponential Cole–Hopf denominator is positive everywhere. -/
theorem coleHopfTwoExpProfile_pos (p : ℝ^2) :
    0 < coleHopfTwoExpProfile.eval p := by
  simpa [coleHopfTwoExpProfile, Verified.Expr.eval]
    using add_pos (Real.exp_pos (p 0 + p 1)) (Real.exp_pos (p 0 - p 1))

/-- The checked closed-form heat residual is identically zero. -/
theorem coleHopfTwoExpProfile_closed_residual_eq_zero :
    Set.EqOn (Exact.exprFn coleHopfTwoExpHeatResidual) Exact.zeroFn Set.univ := by
  cas

/-- Analytic derivative-domain side conditions for the two-exponential profile. -/
private theorem coleHopfTwoExpHeat_analytic_side_condition (p : ℝ^2) (_hp : p ∈ Set.univ) :
    DiffExpr.AnalyticSideCondition (Scalar.ansatz coleHopfTwoExpProfile) p
    heat1DEquation.residual := by
  symbolic_residual

/-- The interpreted profile satisfies the ordinary analytic heat residual everywhere. -/
theorem coleHopfTwoExpHeat_analytic_residual_eq_zero :
    ∀ p, p ∈ Set.univ → DiffExpr.Equation.analyticResidual (Scalar.ansatz coleHopfTwoExpProfile) p
      heat1DEquation = 0 := by
  intro p hp
  have hclosed :
      (Scalar.residual heat1DEquation coleHopfTwoExpProfile).eval p = 0 := by
    simpa [coleHopfTwoExpHeatResidual, Exact.exprFn, Exact.zeroFn] using
      coleHopfTwoExpProfile_closed_residual_eq_zero hp
  exact DiffExpr.Equation.analyticResidual_eq_zero_of_closedResidualVanishesAt
    hclosed (coleHopfTwoExpHeat_analytic_side_condition p hp)

/--
The ordinary `coleHopfTransform` agrees pointwise with the symbolic transform
of the two-exponential heat profile.
-/
theorem coleHopfTwoExpTransform_eq_symbolic_transform (p : ℝ^2) :
    BurgersEquation.ColeHopf.coleHopfTransform 1 (fun q : ℝ^2 ↦ coleHopfTwoExpProfile.eval q) p =
      (coleHopfUnitTransformExpr coleHopfTwoExpProfile).eval p := by
  simp only [coleHopfTransform, mul_one, Fin.isValue, Fin.succ_zero_eq_one,
    neg_mul, coleHopfUnitTransformExpr, Verified.Expr.eval_div_operator,
    Verified.Expr.eval, Nat.cast_ofNat]
  rw [Verified.Expr.partialDeriv_eval_eq]
  symbolic_assumptions

/-- The Cole–Hopf transform gives the explicit nonconstant velocity. -/
theorem coleHopfTwoExpTransform_eq_velocity (p : ℝ^2) :
    BurgersEquation.ColeHopf.coleHopfTransform 1 (fun q : ℝ^2 ↦ coleHopfTwoExpProfile.eval q) p =
      coleHopfTwoExpVelocity.eval p := by
  rw [coleHopfTwoExpTransform_eq_symbolic_transform]
  exact coleHopfTwoExp_transform_eval_eq_velocity p

end

end BurgersEquation.ColeHopf
