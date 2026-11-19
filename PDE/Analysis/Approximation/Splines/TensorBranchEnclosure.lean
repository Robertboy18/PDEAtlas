/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Approximation.Splines.BranchHorner
public import CAS.Continuum.IntervalEval.Soundness

/-!
# Checked polynomial replay for rational tensor spline branches

The exact knot and coefficient arrays determine the expression being checked.
A supplied polynomial may replace the Cox–de Boor expression only after exact
normalization verifies their identity. Interval evaluation then encloses the
spline on its active knot rectangle, starting only from coordinate bounds.
-/

@[expose] public section

namespace CAS.Splines

open CAS.Verified CAS.Continuum

/-- A finite expression sum, with explicit zero for an empty family. -/
def exprRangeSum {ι : Type*} (terms : ℕ → Expr ι) : ℕ → Expr ι
  | 0 => .nat 0
  | count + 1 => .add (exprRangeSum terms count) (terms count)

/-- The finite expression sum evaluates to the finite real sum. -/
theorem exprRangeSum_eval {ι : Type*} (terms : ℕ → Expr ι) (count : ℕ) (ρ : ι → ℝ) :
    (exprRangeSum terms count).eval ρ = ∑ i ∈ Finset.range count, (terms i).eval ρ := by
  induction count with
  | zero => simp [exprRangeSum, Expr.eval]
  | succ count ih => simp [exprRangeSum, Expr.eval, Finset.sum_range_succ, ih]

/-- Exact symbolic tensor branch from rational knots and coefficients. -/
def tensorBranchExpr {ι : Type*} (qx qy : ℕ → ℚ) (vx vy : ι)
    (cellX cellY degreeX degreeY rows cols : ℕ) (coefficient : ℕ → ℕ → ℚ) : Expr ι :=
  exprRangeSum (fun i ↦ .mul (branchExpr qx vx cellX degreeX i)
    (exprRangeSum (fun j ↦ .mul (branchExpr qy vy cellY degreeY j)
      (Expr.mkRatConst (coefficient i j))) cols)) rows

/-- The finite tensor spline with rational coefficients. -/
noncomputable def rationalTensorSpline (kx ky : KnotSequence)
    (degreeX degreeY rows cols : ℕ) (coefficient : ℕ → ℕ → ℚ) (x y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range rows, coxDeBoorBasis kx degreeX i x *
    ∑ j ∈ Finset.range cols, coxDeBoorBasis ky degreeY j y * coefficient i j

/-- On an active rectangle the exact expression equals the tensor spline. -/
theorem tensorBranchExpr_eval {ι : Type*} (qx qy : ℕ → ℚ) (vx vy : ι) (ρ : ι → ℝ)
    (kx ky : KnotSequence) (hxknots : ∀ i, kx i = (qx i : ℝ))
    (hyknots : ∀ i, ky i = (qy i : ℝ))
    (cellX cellY degreeX degreeY rows cols : ℕ) (coefficient : ℕ → ℕ → ℚ)
    (hx : ρ vx ∈ Set.Ico (kx cellX) (kx (cellX + 1)))
    (hy : ρ vy ∈ Set.Ico (ky cellY) (ky (cellY + 1))) :
    (tensorBranchExpr qx qy vx vy cellX cellY degreeX degreeY rows cols coefficient).eval ρ =
      rationalTensorSpline kx ky degreeX degreeY rows cols coefficient (ρ vx) (ρ vy) := by
  simp only [tensorBranchExpr, exprRangeSum_eval, Expr.eval,
    branchExpr_eval qx vx ρ kx hxknots, branchExpr_eval qy vy ρ ky hyknots,
    Expr.eval_mkRatConst, rationalTensorSpline,
    coxDeBoorBasis_eq_branch kx cellX degreeX _ hx,
    coxDeBoorBasis_eq_branch ky cellY degreeY _ hy]

/-- Checked normalization and rational interval evaluation enclose the spline.
The hypotheses are executable certificate checks, exact data identification,
and coordinate-cell membership; no spline-value enclosure is assumed. -/
theorem rationalTensorSpline_enclosed_of_polynomial_replay
    {n : ℕ} (qx qy : ℕ → ℚ) (vx vy : Fin n) (ρ : Fin n → ℝ)
    (kx ky : KnotSequence) (hxknots : ∀ i, kx i = (qx i : ℝ))
    (hyknots : ∀ i, ky i = (qy i : ℝ))
    (cellX cellY degreeX degreeY rows cols : ℕ) (coefficient : ℕ → ℕ → ℚ)
    (polynomial : Expr (Fin n)) (env : Fin n → RationalInterval) (output : RationalInterval)
    (hidentity : polynomialIdentityCheck
      (tensorBranchExpr qx qy vx vy cellX cellY degreeX degreeY rows cols coefficient)
      polynomial = true)
    (heval : RationalInterval.evalPolynomial env polynomial = some output)
    (henv : ∀ i, (env i).MemReal (ρ i))
    (hx : ρ vx ∈ Set.Ico (kx cellX) (kx (cellX + 1)))
    (hy : ρ vy ∈ Set.Ico (ky cellY) (ky (cellY + 1))) :
    output.MemReal
      (rationalTensorSpline kx ky degreeX degreeY rows cols coefficient (ρ vx) (ρ vy)) := by
  have hvalue := polynomialIdentityCheck_sound _ _ hidentity (WithLp.toLp 2 ρ)
  have hmem := RationalInterval.intervalExprBackend_verifiedExprOps.eval_sound env ρ henv _ _ heval
  change output.MemReal _ at hmem
  rw [← hvalue, tensorBranchExpr_eval qx qy vx vy ρ kx ky hxknots hyknots
    cellX cellY degreeX degreeY rows cols coefficient hx hy] at hmem
  exact hmem

end CAS.Splines
