/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Matrix.Normed

/-!
# The derivative of the determinant

The determinant is a continuous alternating function of its rows. Its differential replaces
one row at a time by the corresponding perturbation. Cramer's linear map then identifies
the coefficient of entry `(k,i)` with `adjugate P i k`: the cofactor matrix is the transpose
of the adjugate. None of these identities requires an invertible matrix.
-/

@[expose] public section

noncomputable section

open scoped Matrix.Norms.Elementwise

namespace PDE.Analysis.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The determinant, bundled with its alternating multilinearity and continuity in the rows. -/
def detContinuousAlternating : (ι → ℝ) [⋀^ι]→L[ℝ] ℝ :=
  { Matrix.detRowAlternating with cont := continuous_id.matrix_det }

/-- Evaluating the alternating determinant on the rows gives the usual matrix determinant. -/
@[simp] theorem detContinuousAlternating_apply (P : Matrix ι ι ℝ) :
    detContinuousAlternating P = P.det := rfl

/-- The differential of the determinant obtained by replacing one row at a time. -/
def detDerivative (P : Matrix ι ι ℝ) : Matrix ι ι ℝ →L[ℝ] ℝ :=
  detContinuousAlternating.toContinuousMultilinearMap.linearDeriv P

/-- The determinant has this derivative at every matrix, including singular matrices. -/
theorem hasFDerivAt_det (P : Matrix ι ι ℝ) :
    HasFDerivAt Matrix.det (detDerivative P) P :=
  detContinuousAlternating.hasFDerivAt P

/-- The determinant is smooth at every order, as a continuous multilinear map in its rows. -/
theorem contDiff_det {r : WithTop ℕ∞} :
    ContDiff ℝ r (Matrix.det : Matrix ι ι ℝ → ℝ) := by
  change ContDiff ℝ r (detContinuousAlternating (ι := ι) : (ι → ι → ℝ) → ℝ)
  exact (detContinuousAlternating (ι := ι)).toContinuousMultilinearMap.contDiff

/-- The differential pairs a perturbation with the cofactor matrix, entry by entry. -/
theorem detDerivative_apply (P H : Matrix ι ι ℝ) :
    detDerivative P H = ∑ k, ∑ i, P.adjugate i k * H k i := by
  change detContinuousAlternating.toContinuousMultilinearMap.linearDeriv
    (fun k i ↦ P k i) (fun k i ↦ H k i) = _
  rw [ContinuousMultilinearMap.linearDeriv_apply]
  change ∑ k, (P.updateRow k (H k)).det = _
  apply Finset.sum_congr rfl
  intro k _
  rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec,
    ← Matrix.adjugate_transpose]
  rfl

/-- The Fréchet derivative is the cofactor contraction at every matrix. -/
theorem fderiv_det_apply (P H : Matrix ι ι ℝ) :
    fderiv ℝ Matrix.det P H = ∑ k, ∑ i, P.adjugate i k * H k i := by
  rw [(hasFDerivAt_det P).fderiv, detDerivative_apply]

/-- Differentiating the determinant in entry `(k,i)` gives row `k`, column `i` of the cofactor. -/
theorem fderiv_det_single (P : Matrix ι ι ℝ) (k i : ι) :
    fderiv ℝ Matrix.det P (Matrix.single k i 1) = P.adjugate i k := by
  simp [fderiv_det_apply, Matrix.single_apply, ite_and]

/-- A cofactor entry is the determinant with the corresponding column replaced by a basis vector.
The tuple on the right lists columns, so the determinant is evaluated on the transpose. -/
theorem adjugate_eq_det_update_column (P : Matrix ι ι ℝ) (k i : ι) :
    P.adjugate i k =
      detContinuousAlternating (Function.update P.transpose i (Pi.single k 1)) := by
  change P.adjugate i k = (P.transpose.updateRow i (Pi.single k 1)).det
  rw [← Matrix.adjugate_apply, ← Matrix.adjugate_transpose]
  rfl

end PDE.Analysis.Matrix
