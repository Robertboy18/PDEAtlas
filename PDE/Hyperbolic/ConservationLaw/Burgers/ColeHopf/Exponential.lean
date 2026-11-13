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
# Exponential Cole–Hopf profile

The heat profile `v(t, x) = exp(t + x)` has unit-viscosity Cole–Hopf transform
`u = -2`. It is an elementary instance of Evans, §4.4.1(b), with `a = 1`, not an example stated
in the text. The profile, transformed velocity, and residuals are represented by
`Verified.Expr (Fin 2)`. Exact symbolic certificates, checked by the `cas` tactic of SymLean, our
computer algebra system for Lean, prove the reflected identities, and the analytic evaluation of
`Verified.Expr` identifies the reflected derivative with LeanPDE's ordinary Euclidean partial
derivative.

The final theorem, `coleHopfExpTransform_solves_unit_burgers`, is stated using the ordinary
Cole–Hopf transform and viscous Burgers residual from `BurgersEquation.ColeHopf`. The symbolic
calculation therefore proves a statement about the ordinary Burgers equation.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.4.1(b), equations (5)-(10).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv)

namespace BurgersEquation.ColeHopf

open HeatEquation.Symbolic.Space1 (heat1DEquation)

open CAS
open CAS.Euclid2

noncomputable section

/--
The heat profile `v(t,x)=exp(t+x)`.

As in the other two-dimensional symbolic PDE files, symbolic `x` is the
time coordinate and symbolic `y` is the spatial coordinate.
-/
def coleHopfExpProfile : Verified.Expr (Fin 2) :=
  .exp (y + x : Verified.Expr (Fin 2))

/-- The constant velocity produced by the unit-viscosity Cole–Hopf transform. -/
def coleHopfExpVelocity : Verified.Expr (Fin 2) :=
  -(2 : Verified.Expr (Fin 2))

/-- The heat-equation residual of `exp(t + x)`. -/
def coleHopfExpHeatResidual : Verified.Expr (Fin 2) :=
  Scalar.residual heat1DEquation coleHopfExpProfile

/-- Positivity of the exponential heat profile on all spacetime. -/
theorem coleHopfExpProfile_pos (p : ℝ^2) :
    0 < coleHopfExpProfile.eval p := by
  simpa [coleHopfExpProfile, Verified.Expr.eval, Verified.Expr.SymVar.expr]
    using Real.exp_pos (p 1 + p 0)

/-- The checked closed-form heat residual of `exp(t+x)` is identically zero. -/
theorem coleHopfExpProfile_closed_residual_eq_zero :
    Set.EqOn (Exact.exprFn coleHopfExpHeatResidual) Exact.zeroFn Set.univ := by
  cas

/-- Pointwise closed-form Cole–Hopf calculation `-2 ∂ₓ exp(t+x) / exp(t+x) = -2`, checked by
`cas`. -/
theorem coleHopfExp_transform_eval_eq_velocity (p : ℝ^2) :
    (coleHopfUnitTransformExpr coleHopfExpProfile).eval p = coleHopfExpVelocity.eval p := by
  cas

/-- Analytic derivative-domain side conditions for the heat profile. -/
private theorem coleHopfExpHeat_analytic_side_condition (p : ℝ^2) (_hp : p ∈ Set.univ) :
    DiffExpr.AnalyticSideCondition (Scalar.ansatz coleHopfExpProfile) p
    heat1DEquation.residual := by
  symbolic_residual

/-- Analytic residual form of the heat check for `exp(t+x)`. -/
theorem coleHopfExpHeat_analytic_residual_eq_zero :
    ∀ p, p ∈ Set.univ → DiffExpr.Equation.analyticResidual (Scalar.ansatz coleHopfExpProfile) p
      heat1DEquation = 0 := by
  intro p hp
  have hclosed :
      (Scalar.residual heat1DEquation coleHopfExpProfile).eval p = 0 := by
    simpa [coleHopfExpHeatResidual, Exact.exprFn, Exact.zeroFn] using
      coleHopfExpProfile_closed_residual_eq_zero hp
  exact DiffExpr.Equation.analyticResidual_eq_zero_of_closedResidualVanishesAt
    hclosed (coleHopfExpHeat_analytic_side_condition p hp)

/-! ## Ordinary Cole–Hopf transform -/

/--
The symbolic unit-viscosity expression agrees pointwise with
`BurgersEquation.ColeHopf.coleHopfTransform` applied to the interpreted profile.
-/
theorem coleHopfTransform_eq_symbolic_transform (p : ℝ^2) :
    BurgersEquation.ColeHopf.coleHopfTransform 1 (fun q : ℝ^2 ↦ coleHopfExpProfile.eval q) p =
      (coleHopfUnitTransformExpr coleHopfExpProfile).eval p := by
  simp only [coleHopfTransform, mul_one, Fin.isValue, Fin.succ_zero_eq_one,
    neg_mul, coleHopfUnitTransformExpr, Verified.Expr.eval_div_operator,
    Verified.Expr.eval, Nat.cast_ofNat]
  rw [Verified.Expr.partialDeriv_eval_eq]
  symbolic_assumptions

/-- The Cole–Hopf transform of `exp(t+x)` is the constant velocity `-2`. -/
theorem coleHopfTransform_eq_velocity (p : ℝ^2) :
    BurgersEquation.ColeHopf.coleHopfTransform 1 (fun q : ℝ^2 ↦ coleHopfExpProfile.eval q) p =
      coleHopfExpVelocity.eval p := by
  rw [coleHopfTransform_eq_symbolic_transform]
  exact coleHopfExp_transform_eval_eq_velocity p

/--
The transformed exponential profile solves the unit-viscosity Burgers equation.

The proof uses the checked closed-form identity as a rewrite into
the constant velocity field, then closes the ordinary `viscousBurgersResidual`
goal by the Euclidean calculus lemmas for constants.
-/
theorem coleHopfExpTransform_solves_unit_burgers :
    BurgersEquation.ColeHopf.SolvesViscousBurgersOn 1 Set.univ
      (BurgersEquation.ColeHopf.coleHopfTransform 1 (fun q : ℝ^2 ↦ coleHopfExpProfile.eval q)) := by
  have hfun : BurgersEquation.ColeHopf.coleHopfTransform 1
          (fun q : ℝ^2 ↦ coleHopfExpProfile.eval q) =
        fun q : ℝ^2 ↦ coleHopfExpVelocity.eval q := by
    funext q
    exact coleHopfTransform_eq_velocity q
  constructor
  · intro p _hp
    rw [hfun]
    change ContDiffAt ℝ 2 (fun _ : ℝ^2 ↦ (-2 : ℝ)) p
    fun_prop
  · intro p _hp
    rw [hfun]
    simp [BurgersEquation.ColeHopf.viscousBurgersResidual, coleHopfExpVelocity,
      Verified.Expr.eval, partialDeriv]


end

end BurgersEquation.ColeHopf
