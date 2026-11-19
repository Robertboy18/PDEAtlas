/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Determinants bounded by positive traces

Each eigenvalue of a positive semidefinite matrix is bounded by the sum of the
eigenvalues. Multiplication gives the coarse bound `det A ≤ (trace A)^n`.
The same estimate for a positive linear map follows in an orthonormal basis.
The constant is not sharp: the arithmetic-geometric mean inequality gives
`(trace A / n)^n`.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

/-- The determinant of a positive semidefinite matrix is bounded by a power of
its trace, including the empty matrix convention. -/
theorem det_le_trace_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    A.det ≤ A.trace ^ Fintype.card ι := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues, hA.isHermitian.trace_eq_sum_eigenvalues]
  calc
    ∏ i, hA.isHermitian.eigenvalues i ≤ ∏ _ : ι, ∑ i, hA.isHermitian.eigenvalues i := by
      apply Finset.prod_le_prod₀
      · exact fun i _ ↦ hA.eigenvalues_nonneg i
      · intro i _
        exact Finset.single_le_sum (fun j _ ↦ hA.eigenvalues_nonneg j) (Finset.mem_univ i)
    _ = (∑ i, hA.isHermitian.eigenvalues i) ^ Fintype.card ι := by simp

/-- The Jacobian determinant of a positive linear map is nonnegative. -/
theorem det_nonneg_of_isPositive {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {A : E →ₗ[ℝ] E} (hA : A.IsPositive) :
    0 ≤ A.det := by
  classical
  let b := stdOrthonormalBasis ℝ E
  have hmatrix := (LinearMap.posSemidef_toMatrix_iff b).mpr hA
  simpa only [LinearMap.det_toMatrix] using hmatrix.det_nonneg

/-- Positive linear maps satisfy the same trace bound independently of a chosen basis. -/
theorem det_le_trace_pow_of_isPositive {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {A : E →ₗ[ℝ] E} (hA : A.IsPositive) :
    A.det ≤ LinearMap.trace ℝ E A ^ Module.finrank ℝ E := by
  classical
  let b := stdOrthonormalBasis ℝ E
  have hmatrix := (LinearMap.posSemidef_toMatrix_iff b).mpr hA
  simpa only [LinearMap.det_toMatrix, LinearMap.trace_eq_matrix_trace ℝ b.toBasis,
    Fintype.card_fin] using det_le_trace_pow hmatrix

/-- A bound on a weighted positive trace plus a nonnegative scalar controls
their determinant product, also when the operator acts on a zero-dimensional
space. This coarse estimate avoids dividing by the dimension. -/
theorem abs_det_mul_le_of_trace_add_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {A : E →ₗ[ℝ] E} {α s F : ℝ} (hA : A.IsPositive) (hα : 0 < α) (hs : 0 ≤ s)
    (hbound : α * LinearMap.trace ℝ E A + s ≤ F) :
    |A.det * s| ≤ (F / α) ^ Module.finrank ℝ E * F := by
  have htrace := hA.trace_nonneg
  have hsF : s ≤ F := le_trans
    (le_add_of_nonneg_left (mul_nonneg hα.le htrace)) hbound
  have hF : 0 ≤ F := hs.trans hsF
  have htrF : LinearMap.trace ℝ E A ≤ F / α :=
    (le_div_iff₀ hα).mpr (by nlinarith)
  rw [abs_of_nonneg (mul_nonneg (det_nonneg_of_isPositive hA) hs)]
  exact mul_le_mul
    ((det_le_trace_pow_of_isPositive hA).trans
      (pow_le_pow_left₀ htrace htrF (Module.finrank ℝ E)))
    hsF hs (pow_nonneg (div_nonneg hF hα.le) _)

end PDE.Analysis
