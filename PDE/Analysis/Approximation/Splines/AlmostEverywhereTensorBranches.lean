/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Approximation.Splines.AlmostEverywhereCells
public import PDE.Analysis.Approximation.Splines.TensorBranchEnclosure
public import CAS.Calculus.Smoothness

/-!
# Tensor branches on the almost-everywhere cell cover

Each finite tensor has a finite family of polynomial expressions: its interior
cell polynomials and the zero expression outside its support span. Open-piece
membership gives equality on an ambient neighborhood, including after continuous
coordinate substitution. The identities follow from Cox–de Boor evaluation and
support; no branch equality or smoothness at a knot is assumed.
-/

@[expose] public section

namespace CAS.Splines

open Filter Set CAS.Verified
open scoped Topology

private theorem mkRatConst_validAt {ι : Type*} (c : ℚ) (ρ : ι → ℝ) :
    (Expr.mkRatConst c).ValidAt ρ := by
  simp only [Expr.mkRatConst, Expr.mkIntConst]
  split_ifs <;> simp [Expr.ValidAt]

/-- A rational branch polynomial is valid everywhere, even when a repeated knot
makes an exact rational blend coefficient zero. No variable denominator occurs. -/
theorem branchExpr_validAt {ι : Type*} (knots : ℕ → ℚ) (v : ι)
    (cell degree index : ℕ) (ρ : ι → ℝ) :
    (branchExpr knots v cell degree index).ValidAt ρ := by
  induction degree generalizing index with
  | zero =>
      simp only [branchExpr]
      split <;> trivial
  | succ degree ih =>
      simp [branchExpr, leftBlendExpr, rightBlendExpr, Expr.ValidAt, mkRatConst_validAt, ih]

/-- A finite expression sum is valid whenever its contributing terms are valid. -/
theorem exprRangeSum_validAt {ι : Type*} (terms : ℕ → Expr ι) (count : ℕ) (ρ : ι → ℝ)
    (hterms : ∀ i < count, (terms i).ValidAt ρ) :
    (exprRangeSum terms count).ValidAt ρ := by
  induction count with
  | zero => trivial
  | succ count ih =>
      exact ⟨ih (fun i hi ↦ hterms i (Nat.lt_succ_of_lt hi)),
        hterms count (Nat.lt_succ_self count)⟩

/-- Every raw tensor branch is a globally valid polynomial expression. -/
theorem tensorBranchExpr_validAt {ι : Type*} (qx qy : ℕ → ℚ) (vx vy : ι)
    (cellX cellY px py rows cols : ℕ) (coefficient : ℕ → ℕ → ℚ) (ρ : ι → ℝ) :
    (tensorBranchExpr qx qy vx vy cellX cellY px py rows cols coefficient).ValidAt ρ := by
  apply exprRangeSum_validAt
  intro i _
  refine ⟨branchExpr_validAt qx vx cellX px i ρ, ?_⟩
  apply exprRangeSum_validAt
  intro j _
  exact ⟨branchExpr_validAt qy vy cellY py j ρ, mkRatConst_validAt (coefficient i j) ρ⟩

/-- A basis in a finite prefix vanishes outside the closed span containing every
support in that prefix. Repeated knots and a zero-length prefix are allowed. -/
theorem coxDeBoorBasis_eq_zero_of_mem_exterior (knots : KnotSequence)
    (degree count index : ℕ) (hindex : index < count) {x : ℝ}
    (hx : x ∈ knotPiece knots (count + degree) none) :
    coxDeBoorBasis knots degree index x = 0 := by
  have hout : x < knots 0 ∨ knots (count + degree) < x := by
    simpa only [knotPiece, mem_compl_iff, mem_Icc, not_and_or, not_le] using hx
  rcases hout with hleft | hright
  · exact coxDeBoorBasis_eq_zero_of_lt_left knots degree index
      (hleft.trans_le (knots.monotone (Nat.zero_le index)))
  · exact coxDeBoorBasis_eq_zero_of_right_le knots degree index
      ((knots.monotone (by omega : index + degree + 1 ≤ count + degree)).trans
        hright.le)

/-- If either coordinate is exterior to the complete finite support span, the
finite tensor is zero. -/
theorem rationalTensorSpline_eq_zero_of_mem_exterior (kx ky : KnotSequence)
    (px py rows cols : ℕ) (coefficient : ℕ → ℕ → ℚ) {x y : ℝ}
    (hout : x ∈ knotPiece kx (rows + px) none ∨ y ∈ knotPiece ky (cols + py) none) :
    rationalTensorSpline kx ky px py rows cols coefficient x y = 0 := by
  unfold rationalTensorSpline
  apply Finset.sum_eq_zero
  intro i hi
  rcases hout with hx | hy
  · rw [coxDeBoorBasis_eq_zero_of_mem_exterior kx px rows i (Finset.mem_range.mp hi) hx,
      zero_mul]
  · have hzero : (∑ j ∈ Finset.range cols,
        coxDeBoorBasis ky py j y * (coefficient i j : ℝ)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [coxDeBoorBasis_eq_zero_of_mem_exterior ky py cols j (Finset.mem_range.mp hj) hy,
        zero_mul]
    rw [hzero, mul_zero]

/-- A finite family of exact expressions for the complete tensor cover. An
exterior piece in either coordinate selects zero; interior pieces select the
existing Cox–de Boor branch expression. -/
def tensorPieceExpr (qx qy : ℕ → ℚ) (px py rows cols : ℕ)
    (coefficient : ℕ → ℕ → ℚ)
    (cellX : Option (Fin (rows + px))) (cellY : Option (Fin (cols + py))) : Expr (Fin 2) :=
  match cellX, cellY with
  | some x, some y =>
      tensorBranchExpr qx qy (0 : Fin 2) 1 x y px py rows cols coefficient
  | _, _ => .rat 0 1

/-- Every expression in the complete finite piece family is valid everywhere. -/
theorem tensorPieceExpr_validAt (qx qy : ℕ → ℚ) (px py rows cols : ℕ)
    (coefficient : ℕ → ℕ → ℚ)
    (cellX : Option (Fin (rows + px))) (cellY : Option (Fin (cols + py)))
    (ρ : Fin 2 → ℝ) :
    (tensorPieceExpr qx qy px py rows cols coefficient cellX cellY).ValidAt ρ := by
  cases cellX <;> cases cellY <;>
    simp [tensorPieceExpr, Expr.ValidAt, tensorBranchExpr_validAt]

/-- A piece expression is smooth of every order, including analytic order.
This is regularity of the individual polynomial expression, not of the assembled
spline across its knots. -/
theorem contDiff_tensorPieceExpr_eval {m : WithTop ℕ∞}
    (qx qy : ℕ → ℚ) (px py rows cols : ℕ) (coefficient : ℕ → ℕ → ℚ)
    (cellX : Option (Fin (rows + px))) (cellY : Option (Fin (cols + py))) :
    ContDiff ℝ m (fun q : ℝ^2 ↦
      (tensorPieceExpr qx qy px py rows cols coefficient cellX cellY).eval q) :=
  contDiff_iff_contDiffAt.mpr fun q ↦
    Expr.contDiffAt_eval _ q (tensorPieceExpr_validAt qx qy px py rows cols coefficient
      cellX cellY q)

/-- The finite expression agrees with the tensor at every point of its
open piece, including the exterior pieces. -/
theorem tensorPieceExpr_eval (qx qy : ℕ → ℚ) (kx ky : KnotSequence)
    (hxknots : ∀ i, kx i = (qx i : ℝ))
    (hyknots : ∀ i, ky i = (qy i : ℝ))
    (px py rows cols : ℕ) (coefficient : ℕ → ℕ → ℚ)
    (cellX : Option (Fin (rows + px))) (cellY : Option (Fin (cols + py)))
    (ρ : Fin 2 → ℝ)
    (hx : ρ 0 ∈ knotPiece kx (rows + px) cellX)
    (hy : ρ 1 ∈ knotPiece ky (cols + py) cellY) :
    (tensorPieceExpr qx qy px py rows cols coefficient cellX cellY).eval ρ =
      rationalTensorSpline kx ky px py rows cols coefficient (ρ 0) (ρ 1) := by
  cases cellX with
  | none =>
      rw [rationalTensorSpline_eq_zero_of_mem_exterior kx ky px py rows cols coefficient
        (Or.inl hx)]
      simp [tensorPieceExpr, Expr.eval]
  | some x =>
      cases cellY with
      | none =>
          rw [rationalTensorSpline_eq_zero_of_mem_exterior kx ky px py rows cols coefficient
            (Or.inr hy)]
          simp [tensorPieceExpr, Expr.eval]
      | some y =>
          exact tensorBranchExpr_eval qx qy (0 : Fin 2) 1 ρ kx ky hxknots hyknots
            x y px py rows cols coefficient ⟨hx.1.le, hx.2⟩ ⟨hy.1.le, hy.2⟩

/-- Open-piece geometry gives the tensor identity on a full neighborhood
after any continuous coordinate substitution. This supplies source germs, rather
than merely pointwise values or assumed branch identities. -/
theorem rationalTensorSpline_eventuallyEq_tensorPieceExpr {α : Type*} [TopologicalSpace α]
    (qx qy : ℕ → ℚ) (kx ky : KnotSequence)
    (hxknots : ∀ i, kx i = (qx i : ℝ))
    (hyknots : ∀ i, ky i = (qy i : ℝ))
    (px py rows cols : ℕ) (coefficient : ℕ → ℕ → ℚ)
    (cellX : Option (Fin (rows + px))) (cellY : Option (Fin (cols + py)))
    (x y : α → ℝ) (hcx : Continuous x) (hcy : Continuous y) {p : α}
    (hx : x p ∈ knotPiece kx (rows + px) cellX)
    (hy : y p ∈ knotPiece ky (cols + py) cellY) :
    (fun q ↦ rationalTensorSpline kx ky px py rows cols coefficient (x q) (y q)) =ᶠ[𝓝 p]
      fun q ↦ (tensorPieceExpr qx qy px py rows cols coefficient cellX cellY).eval
        ![x q, y q] := by
  filter_upwards [((isOpen_knotPiece kx (rows + px) cellX).preimage hcx).mem_nhds hx,
    ((isOpen_knotPiece ky (cols + py) cellY).preimage hcy).mem_nhds hy] with q hqx hqy
  exact (tensorPieceExpr_eval qx qy kx ky hxknots hyknots px py rows cols coefficient
    cellX cellY ![x q, y q] hqx hqy).symm

end CAS.Splines
