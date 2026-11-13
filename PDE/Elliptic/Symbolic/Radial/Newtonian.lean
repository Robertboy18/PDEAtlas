/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution
public import PDE.FDeriv.Euclidean.Laplacian
public import CAS.ClosedForm.Expression.Radial
public import CAS.ClosedForm.Scalar.Models
public import CAS.Tactic.Assumptions
public import CAS.Exact.ExpressionSideConditions
import Mathlib.Analysis.InnerProductSpace.Calculus
public import PDE.Symbolic.ClosedForm.Differential.Equation

/-!
# The symbolic Newtonian radial core

The Newtonian potential `x ↦ 1 / ‖x‖` is harmonic on `ℝ^3 ∖ {0}`; multiplied by
`1 / (4π) = 1 / (3 · α(3))`, with `α(3)` the volume of the unit ball, it is the fundamental
solution of Laplace's equation in three dimensions (Evans, PDE, §2.2.1). We represent
the core `1 / sqrt(x² + y² + z²)` as a `Verified.Expr`, prove that it evaluates to `‖p‖⁻¹`,
and establish its harmonicity off the origin. That harmonicity is the case `k = 1`, `n = 3`
of the general inverse-distance-power formula `EuclideanLaplacian.laplacian_inv_dist_pow`, so
no separate Laplacian calculation is done here; the symbolic residual theorems follow
by transporting the analytic fact through the validity side conditions. The expression language
and the `symbolic_assumptions` tactic, which discharges the validity condition of the core, come
from SymLean.

The normalization constant is kept out of `newtonianCore3D` so the nonconstant
radial factor can be studied on its own; the relation to `PotentialTheory.fundamentalSolution 3`
is recorded as a separate identity.

## Main results

* `puncturedSpace3D`: the domain `ℝ^3 ∖ {0}`.
* `newtonianCore3D_eval_eq_inv_norm`: the symbolic core evaluates to `‖p‖⁻¹`.
* `laplacian_inv_norm3_zero_of_ne_zero`, `laplacian_newtonianCore3D_of_ne_zero`:
  harmonicity of `1 / ‖x‖` off the origin, analytically and for the symbolic expression.
* `fundamentalSolution_three_eq_scaled_newtonianCore3D`: the analytic fundamental solution is
  the core times `1 / ((3 - 2) · 3 · α(3))`.
* `newtonianCore3D_harmonic_on_punctured`, `newtonianCore3D_analytic_residual_zero_of_ne_zero`:
  the symbolic and analytic Laplace residuals vanish on the punctured space.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.1, the radial equation (5), the fundamental solution
  (6) and its harmonicity off the origin, p. 22.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (laplacian)

namespace LaplacianEquation.Symbolic

open CAS
open scoped CAS

noncomputable section

/-! ## Three-dimensional punctured domain -/

/-- The punctured three-dimensional space, used for radial fundamental-solution checks. -/
def puncturedSpace3D : Set (ℝ^3) := {p | p ≠ 0}

/-! ## Three-dimensional Newtonian radial core -/

/-- The three-dimensional Newtonian radial core `1 / sqrt(x²+y²+z²)`.

This is the symbolic expression underlying the classical Laplace fundamental solution away from
the pole. The normalization constant is omitted here so that the
nonconstant radial factor can be studied separately. -/
def newtonianCore3D : Verified.Expr (Fin 3) :=
  (1 : Verified.Expr (Fin 3)) / CAS.radius3

/--
The symbolic Newtonian core is exactly the analytic radial core `1 / ‖p‖`.

It differs from `PotentialTheory.fundamentalSolution 3`, which also carries the
Evans/Poisson normalization constant `1 / (((3:ℝ)-2) * 3 * PDE.Analysis.unitBallVolume 3)`.
-/
theorem newtonianCore3D_eval_eq_inv_norm (p : ℝ^3) :
    newtonianCore3D.eval p = ‖p‖⁻¹ := by
  simp [newtonianCore3D, div_eq_mul_inv]

/-- The Newtonian core is `C²` away from the pole.

The proof works locally with the equal analytic function `x ↦ ‖x‖⁻¹`, whose
smoothness follows from smoothness of the norm away from zero and inversion.
-/
theorem newtonianCore3D_contDiffAt_of_ne_zero
    (p : ℝ^3) (hp : p ∈ puncturedSpace3D) :
    ContDiffAt ℝ 2 (fun q : ℝ^3 ↦ newtonianCore3D.eval q) p := by
  have hp0 : p ≠ 0 := by
    change p ≠ 0 at hp
    exact hp
  have hnorm_ne : ‖p‖ ≠ 0 := norm_ne_zero_iff.2 hp0
  have hnorm : ContDiffAt ℝ 2 (norm : ℝ^3 → ℝ) p :=
    contDiffAt_norm (𝕜 := ℝ) hp0
  have hcore :
      (fun q : ℝ^3 ↦ newtonianCore3D.eval q) = fun q : ℝ^3 ↦ ‖q‖⁻¹ := by
    funext q
    exact newtonianCore3D_eval_eq_inv_norm q
  rw [hcore]
  exact hnorm.inv hnorm_ne

/-- The analytic radial core `1 / ‖x‖` is harmonic away from the origin in `ℝ^3`: the case
`k = 1`, `n = 3` of `EuclideanLaplacian.laplacian_inv_dist_pow`, where the coefficient
`k (k + 2 - n)` vanishes. -/
theorem laplacian_inv_norm3_zero_of_ne_zero
    (p : ℝ^3) (hp : p ≠ 0) :
    laplacian (fun q : ℝ^3 ↦ ‖q‖⁻¹) p = 0 := by
  have h :=
    EuclideanLaplacian.laplacian_inv_dist_pow (n := 3) (k := 1) (x := p) (y := 0) hp
  simpa [dist_zero_right] using h

/-- The symbolic Newtonian core has zero analytic Laplacian on punctured `ℝ^3`. -/
theorem laplacian_newtonianCore3D_of_ne_zero
    (p : ℝ^3) (hp : p ∈ puncturedSpace3D) :
    laplacian
      (fun q : ℝ^3 ↦ newtonianCore3D.eval q) p = 0 := by
  have hp0 : p ≠ 0 := by
    change p ≠ 0 at hp
    exact hp
  simpa only [newtonianCore3D_eval_eq_inv_norm] using
    laplacian_inv_norm3_zero_of_ne_zero p hp0

/--
Relation to the analytic three-dimensional fundamental solution.

The Evans/Poisson fundamental solution is the Newtonian radial core multiplied
by its dimension-dependent normalization constant.
-/
theorem fundamentalSolution_three_eq_scaled_newtonianCore3D (p : ℝ^3) :
    PotentialTheory.fundamentalSolution 3 p =
      (1 / (((3 : ℝ) - 2) * (3 : ℝ) * PDE.Analysis.unitBallVolume 3)) *
        newtonianCore3D.eval p := by
  rw [newtonianCore3D_eval_eq_inv_norm]
  by_cases hp : p = 0
  · subst p
    simp [PotentialTheory.fundamentalSolution]
  · simp [PotentialTheory.fundamentalSolution, hp]
    ring

/-- The Newtonian core `1/r` is valid on punctured `ℝ^3`. -/
private theorem newtonianCore3D_validAt_of_ne_zero
    (p : ℝ^3) (hp : p ∈ puncturedSpace3D) :
    newtonianCore3D.ValidAt p := by
  have hnorm_pos : 0 < ‖p‖ := norm_pos_iff.2 hp
  have hpos : 0 < CAS.radiusSq3.eval p := by
    simpa using sq_pos_of_pos hnorm_pos
  have hr : CAS.radius3.eval p ≠ 0 := by
    simpa using hnorm_pos.ne'
  unfold newtonianCore3D CAS.radius3 CAS.radiusSq3
  symbolic_assumptions

/-- The first derivatives of the Newtonian core `1/r` are valid on punctured `ℝ^3`. -/
private theorem newtonianCore3D_diff_validAt_of_ne_zero
    (p : ℝ^3) (hp : p ∈ puncturedSpace3D) :
    ∀ i : Fin 3, (newtonianCore3D.diff i).ValidAt p := by
  have hnorm_pos : 0 < ‖p‖ := norm_pos_iff.2 hp
  have hnorm_sq :
      ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 := by
    simpa [Fin.sum_univ_three, add_assoc] using EuclideanSpace.real_norm_sq_eq p
  have hsum_pos : 0 < (p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 := by
    rw [← hnorm_sq]
    exact sq_pos_of_pos hnorm_pos
  have hsqrt_ne :
      Real.sqrt ((p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2) ≠ 0 :=
    Real.sqrt_ne_zero'.2 hsum_pos
  intro coord
  fin_cases coord <;>
    simp [newtonianCore3D, CAS.radius3, CAS.radiusSq3,
      Verified.Expr.ValidAt, Verified.Expr.diff, Verified.Expr.eval,
      Verified.Expr.SymVar.expr, hsum_pos, hsqrt_ne]

/-- Closed symbolic residual for the Newtonian radial core under the three-dimensional Laplacian. -/
def newtonianCore3DResidual : Verified.Expr (Fin 3) :=
  Scalar.laplaceResidual newtonianCore3D

/-- Pointwise symbolic residual theorem for the Newtonian core off the pole. -/
theorem newtonianCore3DResidual_eval_eq_zero_of_ne_zero
    (p : ℝ^3) (hp : p ∈ puncturedSpace3D) :
    newtonianCore3DResidual.eval p = 0 := by
  have h0 : newtonianCore3D.ValidAt p :=
    newtonianCore3D_validAt_of_ne_zero p hp
  have h1 : ∀ i : Fin 3, (newtonianCore3D.diff i).ValidAt p :=
    newtonianCore3D_diff_validAt_of_ne_zero p hp
  have hlap := laplacian_newtonianCore3D_of_ne_zero p hp
  have hclosed :=
    Verified.Expr.closedLaplacian_eval_eq_laplacian
      (expr := newtonianCore3D) (x := p) h0 h1
  rw [← hclosed] at hlap
  simpa [newtonianCore3DResidual, Scalar.laplaceResidual,
    Scalar.residual, Scalar.laplace, DiffExpr.Lap, Scalar.u,
    DiffExpr.Equation.closedResidual, DiffExpr.Equation.residual, DiffExpr.lower] using hlap

/-- The Newtonian core `1/r` has zero symbolic Laplace residual away from the pole. -/
theorem newtonianCore3D_harmonic_on_punctured :
    Set.EqOn (Exact.exprFn newtonianCore3DResidual) Exact.zeroFn puncturedSpace3D := by
  intro p hp
  have hzero := newtonianCore3DResidual_eval_eq_zero_of_ne_zero p hp
  simpa [Exact.exprFn, Exact.zeroFn] using hzero

/-- Analytic side conditions for the Newtonian-core Laplace residual off the pole. -/
private theorem newtonianCore3D_analytic_side_condition_of_ne_zero
    (p : ℝ^3) (hp : p ∈ puncturedSpace3D) :
    DiffExpr.AnalyticSideCondition
      (Scalar.ansatz newtonianCore3D) p (Scalar.laplace (n := 3)).residual := by
  have h0 : newtonianCore3D.ValidAt p :=
    newtonianCore3D_validAt_of_ne_zero p hp
  have h1 : ∀ i : Fin 3, (newtonianCore3D.diff i).ValidAt p :=
    newtonianCore3D_diff_validAt_of_ne_zero p hp
  simp [DiffExpr.AnalyticSideCondition, DiffExpr.lower, DiffExpr.Lap,
    Scalar.laplace, DiffExpr.Equation.residual, Scalar.u,
    Scalar.ansatz, h0, h1]

/-- Analytic residual theorem for the Newtonian core `1/r` on punctured `ℝ^3`. -/
theorem newtonianCore3D_analytic_residual_zero_of_ne_zero
    (p : ℝ^3) (hp : p ∈ puncturedSpace3D) :
    DiffExpr.Equation.analyticResidual
      (Scalar.ansatz newtonianCore3D) p (Scalar.laplace (n := 3)) = 0 := by
  have hclosed :
      (Scalar.residual (Scalar.laplace (n := 3)) newtonianCore3D).eval p = 0 := by
    simpa [Exact.exprFn, Exact.zeroFn, newtonianCore3DResidual,
      Scalar.laplaceResidual] using
      newtonianCore3D_harmonic_on_punctured hp
  exact DiffExpr.Equation.analyticResidual_eq_zero_of_closedResidualVanishesAt hclosed
    (newtonianCore3D_analytic_side_condition_of_ne_zero p hp)
end

end LaplacianEquation.Symbolic
