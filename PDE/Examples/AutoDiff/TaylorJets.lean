/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.AutoDiff.Jet.Expression
public import PDE.AutoDiff.Jet.Interval

/-!
# Multivariate formal-jet examples

These examples use named finite index types rather than `Fin n`. They demonstrate the main
interfaces of the higher-order jet layer:

* compilation of a mixed multivariate symbolic expression;
* a typed first-order calculus certificate for a Euclidean expression;
* extraction of a vector residual and its output-first Jacobian;
* a fourth-order normalized exponential coefficient; and
* certified interval residual and Jacobian data for validated nonlinear solvers.

The interval example stops at the enclosure. The general Krawczyk checker accepts this kind of
data once the finite-dimensional coordinate bridge is supplied.
-/

@[expose] public section

namespace PDE.Examples.TaylorJets

open PDE.AutoDiff
open CAS
open CAS.Continuum

noncomputable section

/-- Named variables used to show that jets are not restricted to `Fin n`. -/
inductive Variable where
  | x
  | y
deriving DecidableEq

instance : Fintype Variable where
  elems := {.x, .y}
  complete i := by
    cases i <;> simp

/-- Two components of the example residual map. -/
inductive ResidualIndex where
  | first
  | second
deriving DecidableEq

instance : Fintype ResidualIndex where
  elems := {.first, .second}
  complete i := by
    cases i <;> simp

/-- The base point `(x, y) = (0, 2)`. -/
def point : Variable → ℝ
  | .x => 0
  | .y => 2

/-- The symbolic `x` coordinate. -/
def xExpr : Verified.Expr Variable :=
  .var .x

/-- The symbolic `y` coordinate. -/
def yExpr : Verified.Expr Variable :=
  .var .y

/-- A polynomial containing both pure and mixed multivariate terms. -/
def mixedPolynomial : Verified.Expr Variable :=
  xExpr ^ 2 * yExpr + xExpr * yExpr ^ 2

/-- The compiled jet recovers the `x` derivative of the mixed polynomial at `point`. -/
theorem mixedPolynomial_firstCoefficient_x :
    Jet.firstCoefficient Variable.x
        (mixedPolynomial.toJet (order := 3) point) = 4 := by
  rw [Verified.Expr.firstCoefficient_toJet _ _ _ (by omega)]
  norm_num [mixedPolynomial, xExpr, yExpr, point]

/-!
Analytic coordinate derivatives use the Euclidean index type `Fin n`, so the semantic
certificate for a compiled formal jet is stated for an expression over `Fin 1`.
-/

/-- The one-dimensional exponential expression used for the calculus bridge example. -/
def euclideanExponential : Verified.Expr (Fin 1) :=
  .exp (.var 0)

/--
The compiled first-order formal jet represents the value and the derivative of the
exponential expression at the origin.
-/
theorem euclideanExponential_representsFirstOrderAt :
    Jet.RepresentsFirstOrderAt
      (euclideanExponential.toJet (order := 1) (0 : ℝ^1))
      (fun y : ℝ^1 ↦ euclideanExponential.eval y) 0 := by
  exact Verified.Expr.toJet_representsFirstOrderAt
    euclideanExponential (0 : ℝ^1) (by omega) (by
      simp [euclideanExponential])

/-- A two-component polynomial residual with a nonsingular Jacobian at `point`. -/
def residualExpr : ResidualIndex → Verified.Expr Variable
  | .first => xExpr ^ 2 + yExpr - 2
  | .second => xExpr * yExpr

/-- Second-order jets of the residual components at `point`. -/
def residualJets : ResidualIndex → Jet Variable ℝ 2 :=
  fun k ↦ (residualExpr k).toJet point

/-- Both residual components vanish at `point`. -/
theorem residual_values :
    Jet.values residualJets = fun _ ↦ 0 := by
  funext k
  cases k <;>
    norm_num [Jet.values, residualJets, residualExpr, point, xExpr, yExpr]

/-- The exact output-first Jacobian of the residual map at `point`. -/
def residualJacobian : ResidualIndex → Variable → ℝ
  | .first, .x => 0
  | .first, .y => 1
  | .second, .x => 2
  | .second, .y => 0

/-- Jet extraction computes the expected residual Jacobian. -/
theorem residual_jacobian :
    Jet.jacobian residualJets = residualJacobian := by
  funext k i
  cases k <;> cases i <;>
    simp only [Jet.jacobian_apply, residualJets] <;>
    rw [Verified.Expr.firstCoefficient_toJet _ _ _ (by omega)] <;>
    simp [residualExpr, residualJacobian, point, xExpr, yExpr]

/-- The exponential expression in the named `x` coordinate. -/
def exponentialExpr : Verified.Expr Variable :=
  .exp xExpr

/-- The fourth-order exponential jet at `point`. -/
def exponentialJet : Jet Variable ℝ 4 :=
  exponentialExpr.toJet point

/--
The formal coefficient of `x⁴` is `exp(0) / 4! = 1/24`. The compiler supplies normalized
symbolic coefficients, so the proof is an algebraic coefficient calculation.
-/
theorem exponentialJet_fourthCoefficient :
    Jet.coefficient (Finsupp.single Variable.x 4) exponentialJet = 1 / 24 := by
  change
    Jet.coefficient (Finsupp.single Variable.x 4)
        (Jet.compose
          (Verified.Expr.normalizedCoefficient
            (.exp (.var (0 : Fin 1))) 0)
          (Jet.coordinate point Variable.x)) =
      1 / 24
  rw [Jet.coefficient_compose_coordinate _ _ _ (by omega)]
  norm_num [Verified.Expr.normalizedCoefficient, Verified.Expr.iteratedDiff,
    Nat.factorial]

/-- A rational box around `point`. -/
def inputBox : Variable → RationalInterval
  | .x => RationalInterval.ofBounds (-1 / 10) (1 / 10) (by norm_num)
  | .y => RationalInterval.ofBounds (19 / 10) (21 / 10) (by norm_num)

/-- Exact first-order residual jets based at an arbitrary point in `inputBox`. -/
def exactResidualJets (q : Variable → ℝ) :
    ResidualIndex → Jet Variable ℝ 1
  | .first =>
      Jet.coordinate q .x * Jet.coordinate q .x +
        Jet.coordinate q .y - Jet.constant 2
  | .second =>
      Jet.coordinate q .x * Jet.coordinate q .y

/-- Interval first-order residual jets over the whole input box. -/
def intervalResidualJets : ResidualIndex → IntervalJet Variable 1
  | .first =>
      IntervalJet.sub
        (IntervalJet.add
          (IntervalJet.mul
            (IntervalJet.coordinate inputBox .x)
            (IntervalJet.coordinate inputBox .x))
          (IntervalJet.coordinate inputBox .y))
        (IntervalJet.constant 2)
  | .second =>
      IntervalJet.mul
        (IntervalJet.coordinate inputBox .x)
        (IntervalJet.coordinate inputBox .y)

/-- Every interval residual jet encloses its exact jet at every point of `inputBox`. -/
theorem intervalResidualJets_enclose
    {q : Variable → ℝ}
    (hq : ∀ i, (inputBox i).MemReal (q i)) :
    ∀ k, IntervalJet.Encloses (intervalResidualJets k) (exactResidualJets q k) := by
  intro k
  cases k
  · exact IntervalJet.sub_encloses
      (IntervalJet.add_encloses
        (IntervalJet.mul_encloses
          (IntervalJet.coordinate_encloses hq .x)
          (IntervalJet.coordinate_encloses hq .x))
        (IntervalJet.coordinate_encloses hq .y))
      (IntervalJet.constant_encloses 2)
  · exact IntervalJet.mul_encloses
      (IntervalJet.coordinate_encloses hq .x)
      (IntervalJet.coordinate_encloses hq .y)

/--
The interval values and Jacobian entries contain the exact residual data throughout the box.

This is the certified input expected by an interval-Newton or Krawczyk inclusion test.
-/
theorem intervalResidual_values_jacobian_mem
    {q : Variable → ℝ}
    (hq : ∀ i, (inputBox i).MemReal (q i)) :
    (∀ k, (IntervalJet.values intervalResidualJets k).MemReal
      (Jet.values (exactResidualJets q) k)) ∧
      (∀ k i, (IntervalJet.jacobian intervalResidualJets k i).MemReal
        (Jet.jacobian (exactResidualJets q) k i)) := by
  exact IntervalJet.values_jacobian_mem
    (intervalResidualJets_enclose hq) (by omega)

end

end PDE.Examples.TaylorJets
