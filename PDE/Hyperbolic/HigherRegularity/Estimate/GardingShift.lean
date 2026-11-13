/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.LaxMilgram
public import PDE.Analysis.Evolution.Gelfand.Triple
import Mathlib.Tactic.Positivity.Finset

/-!
# Gårding shift for nonsymmetric wave operators

The autonomous spatial operator is a symmetric uniformly elliptic principal
part plus lower-order terms, which need not be symmetric.  Their mixed
`H¹ × L²` bound produces a Gårding inequality, and adding a sufficiently large
mass term makes the complete operator coercive. This abstracts the energy estimate (ii) of
Evans, §6.2.2, Theorem 2, where the lower-order terms are absorbed by Cauchy's inequality with
`ε`. It should not be confused with the distinct `H²` estimate (59) in Evans, §7.2.3.

We prove this functional-analytic step on a Gelfand triple.  If

`B = A + R`,

`A(v,v) >= c ‖v‖_V²`, and

`|R(v,w)| <= L_R ‖v‖_V ‖Jw‖_H`,

then

`(c/2) ‖v‖_V² <= B(v,v) + (L_R²/(2c)) ‖Jv‖_H²`.

Consequently `B + μ J*J` is coercive for `μ = L_R²/(2c)`. The final theorem identifies
an unshifted weak solution with the Lax-Milgram solution of this shifted problem after
adding the corresponding mass term to the load. This shift is needed before applying
higher elliptic regularity to the nonsymmetric wave equation.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.2.2, Theorem 2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace Hyperbolic.HigherRegularity

open PDE.Analysis.Evolution
open PDE.Analysis.Variational

variable {V H : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/--
The canonical mass shift dictated by the mixed lower-order estimate.

The normalization is chosen so that Young's inequality spends exactly half
of the principal coercivity:

`L_R ‖v‖_V ‖Jv‖_H
  <= (c/2) ‖v‖_V² + nonsymmetricGardingShift c L_R ‖Jv‖_H²`.
-/
noncomputable def nonsymmetricGardingShift (c LR : ℝ) : ℝ :=
  LR ^ 2 / (2 * c)

/-- The canonical nonsymmetric Gårding shift is nonnegative. -/
theorem nonsymmetricGardingShift_nonneg {c LR : ℝ} (hc : 0 < c) :
    0 ≤ nonsymmetricGardingShift c LR := by
  unfold nonsymmetricGardingShift
  positivity

/--
Young's inequality in the exact normalization used by the nonsymmetric
Gårding estimate.
-/
theorem mixedLowerOrder_young {c LR x y : ℝ} (hc : 0 < c) :
    LR * x * y ≤ c / 2 * x ^ 2 + nonsymmetricGardingShift c LR * y ^ 2 := by
  have hsquare : 0 ≤ (c * x - LR * y) ^ 2 := sq_nonneg _
  unfold nonsymmetricGardingShift
  have hc0 : c ≠ 0 := ne_of_gt hc
  field_simp [hc0]
  nlinarith

/--
Abstract Gelfand-triple Gårding estimate.

Only the principal operator is symmetric and coercive.  The complete
operator `A + R` may be nonsymmetric.  The mixed `V × H` estimate on `R`
is absorbed by Young's inequality, leaving a pivot-mass loss.
-/
theorem nonsymmetric_garding (T : GelfandTriple (V := V) (H := H)) (A R : V →L[ℝ] StrongDual ℝ V)
    {c LR : ℝ} (hc : 0 < c) (hcoercive : ∀ v : V, c * ‖v‖ ^ 2 ≤ A v v)
    (hRbound : ∀ v w : V, |R v w| ≤ LR * ‖v‖ * ‖T.inclusion w‖) (v : V) :
    c / 2 * ‖v‖ ^ 2 ≤ (A + R) v v + nonsymmetricGardingShift c LR * ‖T.inclusion v‖ ^ 2 := by
  have hRlower : -(LR * ‖v‖ * ‖T.inclusion v‖) ≤ R v v :=
    (neg_le_neg (hRbound v v)).trans (neg_abs_le (R v v))
  have hyoung := mixedLowerOrder_young (c := c) (LR := LR) (x := ‖v‖) (y := ‖T.inclusion v‖) hc
  have hA := hcoercive v
  simp only [add_apply] at *
  linarith

/--
The shifted complete operator

`A + R + μ J*J`

on the energy space of a Gelfand triple.
-/
noncomputable def shiftedNonsymmetricOperator
    (T : GelfandTriple (V := V) (H := H))
    (A R : V →L[ℝ] StrongDual ℝ V)
    (mu : ℝ) :
    V →L[ℝ] StrongDual ℝ V :=
  A + R + mu • T.energyToDual

/--
Evaluating the shifted operator: the mass term `μ J*J` contributes
`μ ⟨Ju, Jv⟩_H`, the pivot inner product of the two energy vectors.
-/
@[simp]
theorem shiftedNonsymmetricOperator_apply (T : GelfandTriple (V := V) (H := H))
    (A R : V →L[ℝ] StrongDual ℝ V) (mu : ℝ) (u v : V) :
    shiftedNonsymmetricOperator T A R mu u v =
      (A + R) u v + mu * inner ℝ (T.inclusion u) (T.inclusion v) := by
  simp [shiftedNonsymmetricOperator, GelfandTriple.energyToDual_apply]

/--
The canonical mass shift makes the complete nonsymmetric operator
coercive. This is derived from `nonsymmetric_garding`.
-/
theorem shiftedNonsymmetricOperator_isCoercive (T : GelfandTriple (V := V) (H := H))
    (A R : V →L[ℝ] StrongDual ℝ V) {c LR : ℝ} (hc : 0 < c)
    (hcoercive : ∀ v : V, c * ‖v‖ ^ 2 ≤ A v v)
    (hRbound : ∀ v w : V, |R v w| ≤ LR * ‖v‖ * ‖T.inclusion w‖) :
    @IsCoercive V inferInstance inferInstance
      (shiftedNonsymmetricOperator T A R (nonsymmetricGardingShift c LR)) := by
  refine ⟨c / 2, div_pos hc (by norm_num), fun v ↦ ?_⟩
  have hg := nonsymmetric_garding T A R hc hcoercive hRbound v
  simpa [shiftedNonsymmetricOperator_apply, real_inner_self_eq_norm_sq, pow_two, mul_assoc] using hg

/--
The weak equation and the Gårding estimate control the energy norm by the
dual load and the pivot norm.

This is the lower-order estimate used when the mass term is not part of the
original PDE.  It is intentionally stated before taking square roots, so no
sign or division information is lost.
-/
theorem weakSolution_energy_estimate (T : GelfandTriple (V := V) (H := H))
    (A R : V →L[ℝ] StrongDual ℝ V) {c LR : ℝ} (hc : 0 < c)
    (hcoercive : ∀ v : V, c * ‖v‖ ^ 2 ≤ A v v)
    (hRbound : ∀ v w : V, |R v w| ≤ LR * ‖v‖ * ‖T.inclusion w‖) (ell : StrongDual ℝ V) (u : V)
    (hu : IsWeakSolution (A + R) ell u) :
    c / 4 * ‖u‖ ^ 2 ≤ ‖ell‖ ^ 2 / c + nonsymmetricGardingShift c LR * ‖T.inclusion u‖ ^ 2 := by
  have hg := nonsymmetric_garding T A R hc hcoercive hRbound u
  have hdual : ell u ≤ ‖ell‖ * ‖u‖ :=
    (le_abs_self (ell u)).trans (ContinuousLinearMap.le_opNorm ell u)
  have heq : (A + R) u u = ell u := hu u
  have hyoung : ‖ell‖ * ‖u‖ ≤
        c / 4 * ‖u‖ ^ 2 + ‖ell‖ ^ 2 / c := by
    have hsquare : 0 ≤ (c * ‖u‖ - 2 * ‖ell‖) ^ 2 := sq_nonneg _
    have hc0 : c ≠ 0 := ne_of_gt hc
    field_simp [hc0]
    nlinarith
  rw [heq] at hg
  linarith

/--
An unshifted weak solution is exactly the Lax-Milgram solution of the
canonically shifted problem with the corrected load

`ell + μ J*J u`.

Nonsymmetric elliptic lifting uses this identity. It is proved from the
original weak equation and shifted coercivity.
-/
theorem weakSolution_eq_shiftedSolve (T : GelfandTriple (V := V) (H := H))
    (A R : V →L[ℝ] StrongDual ℝ V) {c LR : ℝ} (hc : 0 < c)
    (hcoercive : ∀ v : V, c * ‖v‖ ^ 2 ≤ A v v)
    (hRbound : ∀ v w : V, |R v w| ≤ LR * ‖v‖ * ‖T.inclusion w‖) (ell : StrongDual ℝ V) (u : V)
    [CompleteSpace V] (hu : IsWeakSolution (A + R) ell u) :
    u = solveCLM (shiftedNonsymmetricOperator T A R (nonsymmetricGardingShift c LR))
      (shiftedNonsymmetricOperator_isCoercive T A R hc hcoercive hRbound)
      (ell + nonsymmetricGardingShift c LR • T.energyToDual u) := by
  let mu := nonsymmetricGardingShift c LR
  let Bmu := shiftedNonsymmetricOperator T A R mu
  let hBmu : @IsCoercive V inferInstance inferInstance Bmu := shiftedNonsymmetricOperator_isCoercive
      T A R hc hcoercive hRbound
  have huShifted : IsWeakSolution
        Bmu (ell + mu • T.energyToDual u) u := by
    intro v
    rw [show Bmu u v = (A + R) u v +
        mu * inner ℝ (T.inclusion u) (T.inclusion v) by
      exact shiftedNonsymmetricOperator_apply T A R mu u v]
    rw [hu v]
    simp [GelfandTriple.energyToDual_apply]
  exact IsWeakSolution.unique Bmu hBmu (ell + mu • T.energyToDual u) huShifted
      (solveCLM.isWeakSolution Bmu hBmu _)

end Hyperbolic.HigherRegularity
