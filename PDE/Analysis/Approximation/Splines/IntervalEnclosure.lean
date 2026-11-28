/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/
module

public import PDE.Analysis.Approximation.Splines.SecondDerivatives
public import CAS.Expr.FloatLib
public import FloatLib.Numerics.Enclosure.Expression.StandardProof
public import CAS.Expr.SmartConstructors

/-!
# Executable enclosures of rational spline branches

Exact rational knot differences and their totalized reciprocals are embedded as
constants. Thus repeated knots contribute zero weights, matching Cox–de Boor
semantics, without asking the interval evaluator to divide by an interval containing
zero. The only input enclosure is the coordinate box; knot data are identified by
exact equalities. Derivative expressions describe the polynomial extension.

A successful replay of any expression encloses its value (`eval_enclosed_of_replay`), for every
backend that is sound with the real functions of FloatLib's standard calls. The translation
`Expr.toFloatLib` writes `π`, `x ^ y` and `e` as those calls and keeps the value of every
expression, so the lemma has no condition on the expression. FloatLib's exact rational backend
has no calls of its own and is such a backend. The statements for a branch, its two derivatives
and the basis are this lemma at the branch expressions.
-/

@[expose] public section
namespace CAS.Splines
open CAS.Verified

/-- Left affine weight with its exact rational reciprocal precomputed. -/
def leftBlendExpr {ι : Type*} (q : ℕ → ℚ) (v : ι) (degree index : ℕ) : Expr ι :=
  .mul (.sub (.var v) (Expr.mkRatConst (q index)))
    (Expr.mkRatConst ((q (index + degree + 1) - q index)⁻¹))

/-- Right affine weight with its exact rational reciprocal precomputed. -/
def rightBlendExpr {ι : Type*} (q : ℕ → ℚ) (v : ι) (degree index : ℕ) : Expr ι :=
  .mul (.sub (Expr.mkRatConst (q (index + degree + 2))) (.var v))
    (Expr.mkRatConst ((q (index + degree + 2) - q (index + 1))⁻¹))

/-- Exact expression for a polynomial branch of a rational-knot basis. -/
def branchExpr {ι : Type*} (q : ℕ → ℚ) (v : ι) (cell : ℕ) : ℕ → ℕ → Expr ι
  | 0, index => if index = cell then .nat 1 else .nat 0
  | degree + 1, index => .add
      (.mul (leftBlendExpr q v degree index) (branchExpr q v cell degree index))
      (.mul (rightBlendExpr q v degree index) (branchExpr q v cell degree (index + 1)))

/-- Product-rule expression for the first derivative of a branch. -/
def branchDerivativeExpr {ι : Type*} (q : ℕ → ℚ) (v : ι) (cell : ℕ) : ℕ → ℕ → Expr ι
  | 0, _ => .nat 0
  | degree + 1, index => .add
      (.add
        (.mul (Expr.mkRatConst (1 / (q (index + degree + 1) - q index)))
          (branchExpr q v cell degree index))
        (.mul (leftBlendExpr q v degree index)
          (branchDerivativeExpr q v cell degree index)))
      (.add
        (.mul (Expr.mkRatConst (-1 / (q (index + degree + 2) - q (index + 1))))
          (branchExpr q v cell degree (index + 1)))
        (.mul (rightBlendExpr q v degree index)
          (branchDerivativeExpr q v cell degree (index + 1))))

/-- Product-rule expression for the second derivative of a branch. -/
def branchSecondDerivativeExpr {ι : Type*} (q : ℕ → ℚ) (v : ι) (cell : ℕ) : ℕ → ℕ → Expr ι
  | 0, _ => .nat 0
  | degree + 1, index => .add
      (.add
        (.mul (leftBlendExpr q v degree index)
          (branchSecondDerivativeExpr q v cell degree index))
        (.mul (Expr.mkRatConst (2 * (1 / (q (index + degree + 1) - q index))))
          (branchDerivativeExpr q v cell degree index)))
      (.add
        (.mul (rightBlendExpr q v degree index)
          (branchSecondDerivativeExpr q v cell degree (index + 1)))
        (.mul (Expr.mkRatConst (2 * (-1 / (q (index + degree + 2) - q (index + 1)))))
          (branchDerivativeExpr q v cell degree (index + 1))))

/-- Expression weights agree with the real spline weights. -/
theorem leftBlendExpr_eval {ι : Type*} (q : ℕ → ℚ) (v : ι) (ρ : ι → ℝ)
    (knots : KnotSequence) (hknots : ∀ i, knots i = (q i : ℝ)) (degree index : ℕ) :
    (leftBlendExpr q v degree index).eval ρ = leftBlendWeight knots degree index (ρ v) := by
  simp [leftBlendExpr, Expr.eval, leftBlendWeight, hknots, div_eq_mul_inv]

/-- Expression weights agree with the real spline weights. -/
theorem rightBlendExpr_eval {ι : Type*} (q : ℕ → ℚ) (v : ι) (ρ : ι → ℝ)
    (knots : KnotSequence) (hknots : ∀ i, knots i = (q i : ℝ)) (degree index : ℕ) :
    (rightBlendExpr q v degree index).eval ρ = rightBlendWeight knots degree index (ρ v) := by
  simp [rightBlendExpr, Expr.eval, rightBlendWeight, hknots, div_eq_mul_inv]

/-- An exact rational branch expression evaluates to the real Cox–de Boor branch. -/
theorem branchExpr_eval {ι : Type*} (q : ℕ → ℚ) (v : ι) (ρ : ι → ℝ)
    (knots : KnotSequence) (hknots : ∀ i, knots i = (q i : ℝ))
    (cell degree index : ℕ) :
    (branchExpr q v cell degree index).eval ρ = coxDeBoorBranch knots cell degree index (ρ v) := by
  induction degree generalizing index with
  | zero => simp [branchExpr, coxDeBoorBranch]; split <;> simp [Expr.eval]
  | succ degree ih =>
      simp only [branchExpr, Expr.eval, leftBlendExpr_eval q v ρ knots hknots,
        rightBlendExpr_eval q v ρ knots hknots, ih, coxDeBoorBranch]

/-- The derivative expression denotes the derivative of the branch. -/
theorem branchDerivativeExpr_eval {ι : Type*} (q : ℕ → ℚ) (v : ι) (ρ : ι → ℝ)
    (knots : KnotSequence) (hknots : ∀ i, knots i = (q i : ℝ))
    (cell degree index : ℕ) :
    (branchDerivativeExpr q v cell degree index).eval ρ =
      coxDeBoorBranchDerivative knots cell degree index (ρ v) := by
  induction degree generalizing index with
  | zero => simp [branchDerivativeExpr, Expr.eval, coxDeBoorBranchDerivative]
  | succ degree ih =>
      simp [branchDerivativeExpr, Expr.eval, leftBlendExpr_eval q v ρ knots hknots,
        rightBlendExpr_eval q v ρ knots hknots, branchExpr_eval q v ρ knots hknots,
        ih, coxDeBoorBranchDerivative, leftBlendWeightDerivative,
        rightBlendWeightDerivative, hknots]

/-- The second derivative expression has the real branch's second derivative semantics. -/
theorem branchSecondDerivativeExpr_eval {ι : Type*} (q : ℕ → ℚ) (v : ι) (ρ : ι → ℝ)
    (knots : KnotSequence) (hknots : ∀ i, knots i = (q i : ℝ))
    (cell degree index : ℕ) :
    (branchSecondDerivativeExpr q v cell degree index).eval ρ =
      coxDeBoorBranchSecondDerivative knots cell degree index (ρ v) := by
  induction degree generalizing index with
  | zero => simp [branchSecondDerivativeExpr, Expr.eval, coxDeBoorBranchSecondDerivative]
  | succ degree ih =>
      simp [branchSecondDerivativeExpr, Expr.eval, leftBlendExpr_eval q v ρ knots hknots,
        rightBlendExpr_eval q v ρ knots hknots, branchDerivativeExpr_eval q v ρ knots hknots,
        ih, coxDeBoorBranchSecondDerivative, leftBlendWeightDerivative,
        rightBlendWeightDerivative, hknots]

/-- A successful FloatLib replay of an expression, with every variable read from one input
interval that contains `x`, encloses the value of the expression at `x`. This holds for every
backend that is sound with the real functions of FloatLib's standard calls, which the translation
writes for `π`, `x ^ y` and `e`. A sound backend without calls of its own is one
(`Backend.Sound.of_noCalls`), and so is a sound backend with the standard calls added
(`Backend.withExtensions_sound`). -/
theorem eval_enclosed_of_replay {α ι : Type*}
    (B : FloatLib.Numerics.Interval.Backend α)
    (hB : B.Sound (FloatLib.Numerics.Interval.extensionValues
      FloatLib.Numerics.Interval.Backend.Standard.functions))
    (expr : Expr ι) (input output : FloatLib.Numerics.Interval α)
    (hcheck : (expr.toFloatLib (fun _ ↦ 0)).eval? B (fun _ ↦ some input) = some output)
    {x : ℝ} (hx : input.ContainsReal B.decode x) :
    output.ContainsReal B.decode (expr.eval fun _ ↦ x) := by
  have h := FloatLib.Numerics.Interval.Expr.containsReal_eval? _ hB
    (values := fun _ ↦ x) (fun _ _ hi ↦ (Option.some.inj hi) ▸ hx) hcheck
  rwa [Expr.eval_toFloatLib _ _ (fun _ ↦ x) _ (fun _ ↦ rfl)] at h

/-- A successful FloatLib replay of a branch encloses the basis value on the active cell, for
every backend that is sound with the real functions of FloatLib's standard calls. -/
theorem basis_enclosed_of_branch_replay {α : Type*}
    (B : FloatLib.Numerics.Interval.Backend α)
    (hB : B.Sound (FloatLib.Numerics.Interval.extensionValues
      FloatLib.Numerics.Interval.Backend.Standard.functions))
    (q : ℕ → ℚ) (knots : KnotSequence)
    (hknots : ∀ i, knots i = (q i : ℝ)) (cell degree index : ℕ)
    (input output : FloatLib.Numerics.Interval α)
    (hcheck : ((branchExpr q () cell degree index).toFloatLib (fun _ ↦ 0)).eval?
      B (fun _ ↦ some input) = some output)
    {x : ℝ} (hx : input.ContainsReal B.decode x)
    (hcell : x ∈ Set.Ico (knots cell) (knots (cell + 1))) :
    output.ContainsReal B.decode (coxDeBoorBasis knots degree index x) := by
  have h := eval_enclosed_of_replay B hB _ input output hcheck hx
  rw [branchExpr_eval q () (fun _ ↦ x) knots hknots] at h
  rwa [coxDeBoorBasis_eq_branch knots cell degree index hcell]

/-- FloatLib's exact rational backend has no calls of its own, so it is sound with the real
functions of the standard calls as well. -/
private theorem rational_sound_standard :
    FloatLib.Numerics.Interval.Backend.Sound FloatLib.Numerics.Interval.Backend.rational
      (FloatLib.Numerics.Interval.extensionValues
        FloatLib.Numerics.Interval.Backend.Standard.functions) :=
  FloatLib.Numerics.Interval.Backend.Sound.of_noCalls
    FloatLib.Numerics.Interval.Backend.rational_sound fun _ _ ↦ rfl

/-- Exact rational FloatLib evaluation of a branch encloses its real value. -/
theorem branch_enclosed_of_rational_replay (q : ℕ → ℚ) (knots : KnotSequence)
    (hknots : ∀ i, knots i = (q i : ℝ)) (cell degree index : ℕ)
    (input output : FloatLib.Numerics.Interval ℚ)
    (hcheck : ((branchExpr q () cell degree index).toFloatLib (fun _ ↦ 0)).eval?
      (.rational) (fun _ ↦ some input) = some output)
    {x : ℝ} (hx : input.ContainsReal some x) :
    output.ContainsReal some (coxDeBoorBranch knots cell degree index x) := by
  have h := eval_enclosed_of_replay _ rational_sound_standard _ input output hcheck hx
  rw [branchExpr_eval q () (fun _ ↦ x) knots hknots] at h
  exact h

/-- Exact rational FloatLib evaluation encloses the branch's first derivative. -/
theorem branch_derivative_enclosed_of_rational_replay (q : ℕ → ℚ) (knots : KnotSequence)
    (hknots : ∀ i, knots i = (q i : ℝ)) (cell degree index : ℕ)
    (input output : FloatLib.Numerics.Interval ℚ)
    (hcheck : ((branchDerivativeExpr q () cell degree index).toFloatLib (fun _ ↦ 0)).eval?
      (.rational) (fun _ ↦ some input) = some output)
    {x : ℝ} (hx : input.ContainsReal some x) :
    output.ContainsReal some (coxDeBoorBranchDerivative knots cell degree index x) := by
  have h := eval_enclosed_of_replay _ rational_sound_standard _ input output hcheck hx
  rw [branchDerivativeExpr_eval q () (fun _ ↦ x) knots hknots] at h
  exact h

/-- Exact rational FloatLib evaluation encloses the branch's second derivative. -/
theorem branch_second_derivative_enclosed_of_rational_replay (q : ℕ → ℚ) (knots : KnotSequence)
    (hknots : ∀ i, knots i = (q i : ℝ)) (cell degree index : ℕ)
    (input output : FloatLib.Numerics.Interval ℚ)
    (hcheck : ((branchSecondDerivativeExpr q () cell degree index).toFloatLib (fun _ ↦ 0)).eval?
      (.rational) (fun _ ↦ some input) = some output)
    {x : ℝ} (hx : input.ContainsReal some x) :
    output.ContainsReal some (coxDeBoorBranchSecondDerivative knots cell degree index x) := by
  have h := eval_enclosed_of_replay _ rational_sound_standard _ input output hcheck hx
  rw [branchSecondDerivativeExpr_eval q () (fun _ ↦ x) knots hknots] at h
  exact h

/-- Inside an active cell, FloatLib replay encloses the derivative of the basis. -/
theorem basis_derivative_enclosed_of_rational_replay (q : ℕ → ℚ) (knots : KnotSequence)
    (hknots : ∀ i, knots i = (q i : ℝ)) (cell degree index : ℕ)
    (input output : FloatLib.Numerics.Interval ℚ)
    (hcheck : ((branchDerivativeExpr q () cell degree index).toFloatLib (fun _ ↦ 0)).eval?
      (.rational) (fun _ ↦ some input) = some output)
    {x : ℝ} (hx : input.ContainsReal some x)
    (hcell : x ∈ Set.Ioo (knots cell) (knots (cell + 1))) :
    output.ContainsReal some (deriv (coxDeBoorBasis knots degree index) x) := by
  rw [(hasDerivAt_coxDeBoorBasis_of_mem_Ioo knots cell degree index hcell).deriv,
    coxDeBoorBasisDerivative_eq_branchDerivative knots cell degree index ⟨hcell.1.le, hcell.2⟩]
  exact branch_derivative_enclosed_of_rational_replay q knots hknots cell degree index
    input output hcheck hx

end CAS.Splines
