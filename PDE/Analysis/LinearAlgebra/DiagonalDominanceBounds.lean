/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.LinearAlgebra.DiagonalDominance
public import Mathlib.Analysis.Matrix.Normed

/-!
# Sup-norm residual bounds from row diagonal dominance

A positive lower bound `δ` for every row's diagonal-dominance margin gives
`‖x‖∞ ≤ ‖A x‖∞ / δ`. Applying this to an approximate solution minus an exact
solution bounds the error using the exact residual of the approximate vector.
The proof selects a component of maximal modulus and uses the triangle inequality.

Function-space norms below are Mathlib's finite-product sup norms.
The matrix inverse norm is explicitly the induced sup norm, using
`Matrix.Norms.Operator`.
-/

@[expose] public section

namespace PDE.Analysis

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [NormedField K]

/-- A component of maximal modulus supplies a lower bound on one residual component. -/
theorem exists_row_margin_mul_norm_le [Nonempty ι] (A : Matrix ι ι K) (x : ι → K) :
    ∃ i, (‖A i i‖ - ∑ j ∈ Finset.univ.erase i, ‖A i j‖) * ‖x‖ ≤ ‖A.mulVec x i‖ := by
  obtain ⟨i, _, hmax⟩ :=
    Finset.exists_max_image Finset.univ (fun j ↦ ‖x j‖) Finset.univ_nonempty
  have hxnorm : ‖x‖ = ‖x i‖ :=
    le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      (fun j ↦ hmax j (Finset.mem_univ j))) (norm_le_pi_norm x i)
  have hdiag :
      A i i * x i = A.mulVec x i - ∑ j ∈ Finset.univ.erase i, A i j * x j := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [Matrix.mulVec, dotProduct, add_comm] using
      Finset.sum_erase_add Finset.univ (fun j ↦ A i j * x j) (Finset.mem_univ i)
  have hbound : ‖A i i‖ * ‖x i‖ ≤
      ‖A.mulVec x i‖ + (∑ j ∈ Finset.univ.erase i, ‖A i j‖) * ‖x i‖ := by
    calc
      ‖A i i‖ * ‖x i‖ = ‖A i i * x i‖ := (norm_mul _ _).symm
      _ ≤ ‖A.mulVec x i‖ + ‖∑ j ∈ Finset.univ.erase i, A i j * x j‖ := by
        rw [hdiag]
        exact norm_sub_le _ _
      _ ≤ ‖A.mulVec x i‖ + ∑ j ∈ Finset.univ.erase i, ‖A i j * x j‖ :=
        add_le_add le_rfl (norm_sum_le _ _)
      _ ≤ ‖A.mulVec x i‖ + (∑ j ∈ Finset.univ.erase i, ‖A i j‖) * ‖x i‖ := by
        rw [Finset.sum_mul]
        apply add_le_add le_rfl
        exact Finset.sum_le_sum fun j _ ↦ by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hmax j (Finset.mem_univ j)) (norm_nonneg _)
  refine ⟨i, ?_⟩
  rw [hxnorm, sub_mul]
  exact sub_le_iff_le_add.mpr hbound

/-- A common lower bound on all row margins gives a coercivity bound in the sup norm. -/
theorem row_margin_mul_norm_le (A : Matrix ι ι K) (δ : ℝ)
    (hmargin : ∀ i, δ ≤ ‖A i i‖ - ∑ j ∈ Finset.univ.erase i, ‖A i j‖) (x : ι → K) :
    δ * ‖x‖ ≤ ‖A.mulVec x‖ := by
  cases isEmpty_or_nonempty ι
  · have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]
  obtain ⟨i, hi⟩ := exists_row_margin_mul_norm_le A x
  calc
    δ * ‖x‖ ≤ (‖A i i‖ - ∑ j ∈ Finset.univ.erase i, ‖A i j‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_right (hmargin i) (norm_nonneg _)
    _ ≤ ‖A.mulVec x i‖ := hi
    _ ≤ ‖A.mulVec x‖ := norm_le_pi_norm _ _

/-- Residual bounds scaled by each positive row margin avoid replacing all
row margins by their common minimum. -/
theorem norm_le_of_row_residual_bounds (A : Matrix ι ι K) (margin : ι → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hpositive : ∀ i, 0 < margin i)
    (hmargin : ∀ i, margin i ≤ ‖A i i‖ - ∑ j ∈ Finset.univ.erase i, ‖A i j‖)
    (x : ι → K) (hresidual : ∀ i, ‖A.mulVec x i‖ ≤ margin i * ε) :
    ‖x‖ ≤ ε := by
  cases isEmpty_or_nonempty ι
  · have hx : x = 0 := Subsingleton.elim _ _
    simpa only [hx, norm_zero] using hε
  obtain ⟨i, hi⟩ := exists_row_margin_mul_norm_le A x
  apply (mul_le_mul_iff_right₀ (hpositive i)).mp
  have hbound : margin i * ‖x‖ ≤ margin i * ε :=
    (mul_le_mul_of_nonneg_right (hmargin i) (norm_nonneg _)).trans
      (hi.trans (hresidual i))
  simpa only [mul_comm] using hbound

/-- A positive common row margin bounds the solution norm by the residual norm. -/
theorem norm_le_mulVec_norm_div (A : Matrix ι ι K) (δ : ℝ) (hδ : 0 < δ)
    (hmargin : ∀ i, δ ≤ ‖A i i‖ - ∑ j ∈ Finset.univ.erase i, ‖A i j‖) (x : ι → K) :
    ‖x‖ ≤ ‖A.mulVec x‖ / δ := by
  apply (le_div_iff₀ hδ).mpr
  simpa only [mul_comm] using row_margin_mul_norm_le A δ hmargin x

/-- The exact residual of an arbitrary approximate vector bounds its distance
from any exact solution. There is no hypothesis on how the approximate vector was produced. -/
theorem norm_sub_le_residual_div (A : Matrix ι ι K) (δ : ℝ) (hδ : 0 < δ)
    (hmargin : ∀ i, δ ≤ ‖A i i‖ - ∑ j ∈ Finset.univ.erase i, ‖A i j‖)
    (b exact approximate : ι → K) (hexact : A.mulVec exact = b) :
    ‖approximate - exact‖ ≤ ‖A.mulVec approximate - b‖ / δ := by
  simpa only [Matrix.mulVec_sub, hexact] using
    norm_le_mulVec_norm_div A δ hδ hmargin (approximate - exact)

/-- Certified componentwise residual bounds give a sup-norm error bound. -/
theorem norm_sub_le_of_residual_bounds (A : Matrix ι ι K) (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hmargin : ∀ i, δ ≤ ‖A i i‖ - ∑ j ∈ Finset.univ.erase i, ‖A i j‖)
    (b exact approximate : ι → K) (hexact : A.mulVec exact = b)
    (hresidual : ∀ i, ‖A.mulVec approximate i - b i‖ ≤ ε) :
    ‖approximate - exact‖ ≤ ε / δ := by
  apply (norm_sub_le_residual_div A δ hδ hmargin b exact approximate hexact).trans
  exact div_le_div_of_nonneg_right
    ((pi_norm_le_iff_of_nonneg hε).mpr hresidual) hδ.le

/-- Separate residual budgets for individual rows certify the error directly. -/
theorem norm_sub_le_of_row_residual_bounds (A : Matrix ι ι K) (margin : ι → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hpositive : ∀ i, 0 < margin i)
    (hmargin : ∀ i, margin i ≤ ‖A i i‖ - ∑ j ∈ Finset.univ.erase i, ‖A i j‖)
    (b exact approximate : ι → K) (hexact : A.mulVec exact = b)
    (hresidual : ∀ i, ‖A.mulVec approximate i - b i‖ ≤ margin i * ε) :
    ‖approximate - exact‖ ≤ ε := by
  apply norm_le_of_row_residual_bounds A margin ε hε hpositive hmargin
  intro i
  simpa only [Matrix.mulVec_sub, hexact, Pi.sub_apply] using hresidual i

/-- The action of the inverse has sup norm at most the reciprocal row margin. -/
theorem norm_inv_mulVec_le (A : Matrix ι ι K) (δ : ℝ) (hδ : 0 < δ)
    (hmargin : ∀ i, δ ≤ ‖A i i‖ - ∑ j ∈ Finset.univ.erase i, ‖A i j‖) (b : ι → K) :
    ‖A⁻¹.mulVec b‖ ≤ ‖b‖ / δ := by
  have hdet : A.det ≠ 0 := det_ne_zero_of_sum_row_lt_diag fun i ↦
    sub_pos.mp (hδ.trans_le (hmargin i))
  have hinverse : A.mulVec (A⁻¹.mulVec b) = b := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hdet)]
    exact Matrix.one_mulVec b
  simpa only [hinverse] using norm_le_mulVec_norm_div A δ hδ hmargin (A⁻¹.mulVec b)

open scoped Matrix.Norms.Operator in
/-- The inverse's induced sup norm is at most the reciprocal row margin. -/
theorem inverse_opNorm_le (A : Matrix ι ι ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hmargin : ∀ i, δ ≤ ‖A i i‖ - ∑ j ∈ Finset.univ.erase i, ‖A i j‖) :
    ‖A⁻¹‖ ≤ 1 / δ := by
  rw [Matrix.linfty_opNorm_eq_opNorm]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro b
  simpa only [ContinuousLinearMap.coe_mk', Matrix.coe_mulVecLin, one_div, div_eq_mul_inv,
    mul_comm, mul_one] using norm_inv_mulVec_le A δ hδ hmargin b

end PDE.Analysis
