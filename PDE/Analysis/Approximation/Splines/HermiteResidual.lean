/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Numerics.Certificates.LinearSystem
public import PDE.Analysis.Approximation.Splines.HermiteSystem
import CAS.ExactTactic

/-!
# A posteriori certificates for exact Hermite slopes

The matrix from `HermiteSystem` has row margins `1` at both endpoints and
`hL + hR` at an interior knot. Its smallest margin is positive on every
strict finite mesh. The sup norm of an approximate slope vector minus the
unique exact slope vector is bounded by its exact residual norm divided
by that smallest margin.

Individual residual bounds scaled by these row margins certify a target
error directly. The final residual includes any error in the prescribed last
slope.

The matrix, nodal values, final derivative, and residual all use exact real
arithmetic; a binary64 vector enters through its exact real values.
-/

@[expose] public section

noncomputable section

namespace CAS.Splines.HermiteSlopeSystem

variable {n : ℕ}

/-- The dominance margins of the natural-left, prescribed-right slope matrix. -/
def rowMargin (mesh : StrictKnotMesh (n + 2)) : Fin (n + 3) → ℝ :=
  Fin.cases 1 (Fin.lastCases 1 fun i : Fin (n + 1) ↦
    width mesh i.castSucc + width mesh i.succ)

/-- The left row has diagonal `2` and a single off-diagonal entry `1`. -/
@[simp] theorem rowMargin_zero (mesh : StrictKnotMesh (n + 2)) :
    rowMargin mesh 0 = 1 := by
  simp [rowMargin]

/-- The interior margin is the sum of the two neighboring panel widths. -/
@[simp] theorem rowMargin_interior (mesh : StrictKnotMesh (n + 2)) (i : Fin (n + 1)) :
    rowMargin mesh i.castSucc.succ = width mesh i.castSucc + width mesh i.succ := by
  simp [rowMargin]

/-- The prescribed final derivative row has diagonal `1` and no off-diagonal entries. -/
@[simp] theorem rowMargin_last (mesh : StrictKnotMesh (n + 2)) :
    rowMargin mesh (Fin.last (n + 2)) = 1 := by
  change rowMargin mesh (Fin.last (n + 1)).succ = _
  simp only [rowMargin, Fin.cases_succ, Fin.lastCases_last]

/-- Positive panel widths make every concrete row margin positive. -/
theorem rowMargin_pos (mesh : StrictKnotMesh (n + 2)) (i : Fin (n + 3)) :
    0 < rowMargin mesh i := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rw [rowMargin_zero]
    norm_num
  · refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · rw [Fin.succ_last, rowMargin_last]
      norm_num
    · rw [rowMargin_interior]
      exact add_pos (width_pos mesh k.castSucc) (width_pos mesh k.succ)

/-- The explicit margin function equals the matrix's diagonal modulus minus
the sum of all off-diagonal moduli, including the boundary rows. -/
theorem rowMargin_eq (mesh : StrictKnotMesh (n + 2)) (i : Fin (n + 3)) :
    rowMargin mesh i =
      ‖matrix mesh i i‖ - ∑ j ∈ Finset.univ.erase i, ‖matrix mesh i j‖ := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rw [rowMargin_zero, matrix_zero]
    have hnonneg (j : Fin (n + 3)) :
        0 ≤ (Pi.single 0 2 + Pi.single 1 1 : Fin (n + 3) → ℝ) j := by
      simp only [Pi.add_apply, Pi.single_apply]
      positivity
    simp_rw [Real.norm_of_nonneg (hnonneg _)]
    norm_num [Pi.add_apply, Pi.single_apply, Finset.sum_add_distrib, Finset.sum_ite_eq']
  · refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · rw [Fin.succ_last, rowMargin_last, matrix_last]
      simp [Pi.single_apply, apply_ite, Finset.sum_ite_eq']
    · rw [rowMargin_interior, matrix_interior]
      have hp : k.castSucc.castSucc ≠ k.castSucc.succ := by
        intro heq
        have := congrArg Fin.val heq
        simp only [Fin.val_castSucc, Fin.val_succ] at this
        omega
      have hn : k.succ.succ ≠ k.castSucc.succ := by
        intro heq
        have := congrArg Fin.val heq
        simp only [Fin.val_castSucc, Fin.val_succ] at this
        omega
      have hL := (width_pos mesh k.castSucc).le
      have hR := (width_pos mesh k.succ).le
      have hnonneg (j : Fin (n + 3)) :
          0 ≤ (Pi.single k.castSucc.castSucc (width mesh k.succ) +
            Pi.single k.castSucc.succ (2 * (width mesh k.castSucc + width mesh k.succ)) +
            Pi.single k.succ.succ (width mesh k.castSucc) : Fin (n + 3) → ℝ) j := by
        simp only [Pi.add_apply, Pi.single_apply]
        positivity
      simp_rw [Real.norm_of_nonneg (hnonneg _)]
      simp only [Pi.add_apply, Pi.single_apply, Finset.sum_add_distrib,
        Finset.sum_ite_eq', Finset.mem_erase, Finset.mem_univ, and_true, ne_eq,
        hp, hn, Ne.symm hp, Ne.symm hn, not_false_eq_true, ite_true, ite_false,
        not_true_eq_false, add_zero, zero_add]
      cas

/-- The smallest exact row margin of the finite slope matrix. -/
def minimumMargin (mesh : StrictKnotMesh (n + 2)) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (rowMargin mesh)

/-- Every strict finite mesh gives a strictly positive smallest row margin. -/
theorem minimumMargin_pos (mesh : StrictKnotMesh (n + 2)) :
    0 < minimumMargin mesh :=
  (Finset.lt_inf'_iff Finset.univ_nonempty).mpr fun i _ ↦ rowMargin_pos mesh i

/-- The smallest margin is a lower bound for each matrix row. -/
theorem minimumMargin_le (mesh : StrictKnotMesh (n + 2)) (i : Fin (n + 3)) :
    minimumMargin mesh ≤
      ‖matrix mesh i i‖ - ∑ j ∈ Finset.univ.erase i, ‖matrix mesh i j‖ := by
  rw [← rowMargin_eq]
  exact Finset.inf'_le (rowMargin mesh) (Finset.mem_univ i)

/-- The exact linear residual of a candidate slope vector, including both endpoint rows. -/
def residual (mesh : StrictKnotMesh (n + 2)) (value : Fin (n + 3) → ℝ)
    (finalSlope : ℝ) (approximate : Fin (n + 3) → ℝ) : Fin (n + 3) → ℝ :=
  (matrix mesh).mulVec approximate - rightHandSide mesh value finalSlope

/-- The left residual is the defect in the natural curvature equation. -/
@[simp] theorem residual_zero (mesh : StrictKnotMesh (n + 2))
    (value approximate : Fin (n + 3) → ℝ) (finalSlope : ℝ) :
    residual mesh value finalSlope approximate 0 =
      2 * approximate 0 + approximate 1 - 3 * (value 1 - value 0) / width mesh 0 := by
  simp [residual]

/-- An interior residual needs only three candidate slopes and three nodal values,
so an interval certificate need not evaluate a full matrix-vector product. -/
@[simp] theorem residual_interior (mesh : StrictKnotMesh (n + 2))
    (value approximate : Fin (n + 3) → ℝ) (finalSlope : ℝ) (i : Fin (n + 1)) :
    residual mesh value finalSlope approximate i.castSucc.succ =
      width mesh i.succ * approximate i.castSucc.castSucc +
        2 * (width mesh i.castSucc + width mesh i.succ) * approximate i.castSucc.succ +
        width mesh i.castSucc * approximate i.succ.succ -
        3 * (width mesh i.succ *
            (value i.castSucc.succ - value i.castSucc.castSucc) / width mesh i.castSucc +
          width mesh i.castSucc *
            (value i.succ.succ - value i.castSucc.succ) / width mesh i.succ) := by
  simp [residual]

/-- The final residual records the defect in the prescribed endpoint derivative. -/
@[simp] theorem residual_last (mesh : StrictKnotMesh (n + 2))
    (value approximate : Fin (n + 3) → ℝ) (finalSlope : ℝ) :
    residual mesh value finalSlope approximate (Fin.last (n + 2)) =
      approximate (Fin.last (n + 2)) - finalSlope := by
  simp [residual]

/-- An exact residual bounds the distance from the unique exact C² slope vector. -/
theorem slope_error_le_residual_div (mesh : StrictKnotMesh (n + 2))
    (value approximate : Fin (n + 3) → ℝ) (finalSlope : ℝ) :
    ‖approximate - slopes mesh value finalSlope‖ ≤
      ‖residual mesh value finalSlope approximate‖ / minimumMargin mesh := by
  exact PDE.Analysis.norm_sub_le_residual_div (matrix mesh) (minimumMargin mesh)
    (minimumMargin_pos mesh) (minimumMargin_le mesh) (rightHandSide mesh value finalSlope)
    (slopes mesh value finalSlope) approximate
    ((solution_iff mesh value _ finalSlope).mpr (slopes_conditions mesh value finalSlope))

/-- Componentwise certified residual errors give an explicit uniform slope error. -/
theorem slope_error_le_of_residual_bounds (mesh : StrictKnotMesh (n + 2))
    (value approximate : Fin (n + 3) → ℝ) (finalSlope ε : ℝ) (hε : 0 ≤ ε)
    (hresidual : ∀ i, ‖residual mesh value finalSlope approximate i‖ ≤ ε) :
    ‖approximate - slopes mesh value finalSlope‖ ≤ ε / minimumMargin mesh := by
  apply (slope_error_le_residual_div mesh value approximate finalSlope).trans
  exact div_le_div_of_nonneg_right ((pi_norm_le_iff_of_nonneg hε).mpr hresidual)
    (minimumMargin_pos mesh).le

/-- Individual row budgets retain the exact margins instead of using their minimum. -/
theorem slope_error_le_of_row_residual_bounds (mesh : StrictKnotMesh (n + 2))
    (value approximate : Fin (n + 3) → ℝ) (finalSlope ε : ℝ) (hε : 0 ≤ ε)
    (hresidual : ∀ i,
      ‖residual mesh value finalSlope approximate i‖ ≤ rowMargin mesh i * ε) :
    ‖approximate - slopes mesh value finalSlope‖ ≤ ε := by
  apply PDE.Analysis.norm_sub_le_of_row_residual_bounds (matrix mesh) (rowMargin mesh) ε
    hε (rowMargin_pos mesh) (fun i ↦ (rowMargin_eq mesh i).le)
    (rightHandSide mesh value finalSlope) (slopes mesh value finalSlope) approximate
    ((solution_iff mesh value _ finalSlope).mpr (slopes_conditions mesh value finalSlope))
  exact hresidual

open scoped Matrix.Norms.Operator in
/-- The inverse slope matrix has induced sup norm at most the reciprocal minimum margin. -/
theorem inverse_opNorm_le (mesh : StrictKnotMesh (n + 2)) :
    ‖(matrix mesh)⁻¹‖ ≤ 1 / minimumMargin mesh :=
  PDE.Analysis.inverse_opNorm_le (matrix mesh) (minimumMargin mesh)
    (minimumMargin_pos mesh) (minimumMargin_le mesh)

/-- On an exact uniform mesh the smallest margin is `min 1 (2*h)`. -/
theorem minimumMargin_eq_uniform (mesh : StrictKnotMesh (n + 2)) (h : ℝ)
    (hmesh : ∀ i, width mesh i = h) :
    minimumMargin mesh = min 1 (2 * h) := by
  apply le_antisymm
  · apply le_min
    · have hi : minimumMargin mesh ≤ rowMargin mesh 0 :=
        Finset.inf'_le (rowMargin mesh) (Finset.mem_univ (0 : Fin (n + 3)))
      simpa only [rowMargin_zero] using hi
    · have hi : minimumMargin mesh ≤ rowMargin mesh (0 : Fin (n + 1)).castSucc.succ :=
        Finset.inf'_le (rowMargin mesh) (Finset.mem_univ (0 : Fin (n + 1)).castSucc.succ)
      simpa only [rowMargin_interior, hmesh, two_mul] using hi
  · apply Finset.le_inf'
    intro i _
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rw [rowMargin_zero]
      exact min_le_left _ _
    · refine Fin.lastCases ?_ (fun k ↦ ?_) j
      · rw [Fin.succ_last, rowMargin_last]
        exact min_le_left _ _
      · rw [rowMargin_interior, hmesh, hmesh, ← two_mul]
        exact min_le_right _ _

/-- On a uniform grid, the slope error is bounded by the residual of the approximate slopes. -/
theorem uniform_slope_error_le (mesh : StrictKnotMesh (n + 2))
    (value approximate : Fin (n + 3) → ℝ) (h : ℝ) (hmesh : ∀ i, width mesh i = h) :
    ‖approximate - slopes mesh value (backwardDifference value h)‖ ≤
      ‖residual mesh value (backwardDifference value h) approximate‖ / min 1 (2 * h) := by
  simpa only [minimumMargin_eq_uniform mesh h hmesh] using
    slope_error_le_residual_div mesh value approximate (backwardDifference value h)

/-- Integer samples on any finite sequence, interpreted at a common denominator. -/
noncomputable abbrev realVector {k : ℕ} (D : ℕ) (v : ℕ → ℤ) : Fin k → ℝ :=
  CAS.Numerics.rationalVector D (fun i ↦ v i.val)

/-- Integer residual for a uniform Hermite mesh of width `p/q`.
The last row is multiplied by `2*p` to keep the backward difference integral. -/
def uniformIntegerResidual (n p q : ℕ) (v m : ℕ → ℤ) (i : ℕ) : ℤ :=
  if i = 0 then p * (2 * m 0 + m 1) - 3 * q * (v 1 - v 0)
  else if i = n + 2 then
    2 * p * m (n + 2) - q * (3 * v (n + 2) - 4 * v (n + 1) + v n)
  else p * (m (i - 1) + 4 * m i + m (i + 1)) - 3 * q * (v (i + 1) - v (i - 1))

/-- Integer dominance margins in the same normalization as the checked rows. -/
def uniformIntegerMargin (p : ℕ) (i : ℕ) : ℤ :=
  if i = 0 then p else 2 * p

/-- Row scales connecting the integer checker to the exact Hermite system. -/
def uniformRowScale (n p q : ℕ) (i : ℕ) : ℝ :=
  if i = 0 then p else if i = n + 2 then 2 * p else q

/-- Integer rows decode to exact residuals on any mesh with positive rational uniform width. -/
theorem residual_eq_uniformInteger (mesh : StrictKnotMesh (n + 2)) (p q D : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hD : 0 < D)
    (hmesh : ∀ i, width mesh i = (p : ℝ) / q) (v m : ℕ → ℤ) (i : Fin (n + 3)) :
    residual mesh (realVector D v) (backwardDifference (n := n) (realVector D v) ((p : ℝ) / q))
        (realVector D m) i =
      (uniformIntegerResidual n p q v m i.val : ℝ) / D / uniformRowScale n p q i.val := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rw [residual_zero, hmesh]
    simp only [Fin.val_zero, uniformIntegerResidual, uniformRowScale, ite_true,
      realVector, CAS.Numerics.rationalVector, Fin.val_one,
      Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
    cas using [hpR, hqR, hDR]
  · refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · rw [Fin.succ_last, residual_last]
      simp only [Fin.val_last, uniformIntegerResidual, uniformRowScale,
        show n + 2 ≠ 0 by omega, ite_false, ite_true, realVector,
        CAS.Numerics.rationalVector, backwardDifference, Fin.val_castSucc,
        Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
      cas using [hpR, hqR, hDR]
    · rw [residual_interior, hmesh, hmesh]
      have hfirst : k.val + 1 ≠ 0 := by omega
      have hlast : k.val + 1 ≠ n + 2 := by have := k.isLt; omega
      simp only [Fin.val_succ, Fin.val_castSucc, uniformIntegerResidual, uniformRowScale,
        hfirst, hlast, ite_false, Nat.add_sub_cancel_right, realVector,
        CAS.Numerics.rationalVector, Int.cast_sub, Int.cast_add,
        Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
      cas using [hpR, hqR, hDR]

/-- Checked integer rows bound the error against exact Hermite slopes for any nodal data.
The nodal values may come from rounding, quadrature, a solver, or an exact construction;
only their proved agreement with the integer samples is needed. -/
theorem slope_error_of_integer_rows (mesh : StrictKnotMesh (n + 2)) (p q D B : ℕ)
    (hD : 0 < D)
    (hmesh : ∀ i, width mesh i = (p : ℝ) / q) (v m : ℕ → ℤ)
    (value : Fin (n + 3) → ℝ) (hvalue : ∀ i, value i = realVector D v i)
    (hrows : ∀ i : Fin (n + 3),
      |uniformIntegerResidual n p q v m i.val| ≤ uniformIntegerMargin p i.val * B) :
    ‖realVector D m - slopes mesh value (backwardDifference value ((p : ℝ) / q))‖ ≤
      (B : ℝ) / D := by
  -- a strict mesh has positive widths, so `p / q > 0` forces `p, q > 0`
  have hpq : (0 : ℝ) < (p : ℝ) / q := hmesh 0 ▸ width_pos mesh 0
  have hp : 0 < p := Nat.pos_of_ne_zero fun h ↦ by simp [h] at hpq
  have hq : 0 < q := Nat.pos_of_ne_zero fun h ↦ by simp [h] at hpq
  rw [funext hvalue]
  let finalSlope := backwardDifference (n := n) (realVector D v) ((p : ℝ) / q)
  refine CAS.Numerics.norm_sub_le_of_integer_rows
    (matrix mesh) (rowMargin mesh) (rightHandSide mesh (realVector D v) finalSlope)
    (slopes mesh (realVector D v) finalSlope) (realVector D m)
    ((solution_iff mesh (realVector D v) _ finalSlope).mpr
      (slopes_conditions mesh (realVector D v) finalSlope))
    D B hD (fun i ↦ uniformIntegerResidual n p q v m i.val)
    (fun i ↦ uniformIntegerMargin p i.val) (fun i ↦ uniformRowScale n p q i.val)
    ?_ (rowMargin_pos mesh) (fun i ↦ (rowMargin_eq mesh i).le) ?_ ?_ hrows
  · intro i
    unfold uniformRowScale
    split_ifs <;> positivity
  · intro i
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [uniformIntegerMargin, uniformRowScale, hpR]
    · refine Fin.lastCases ?_ (fun k ↦ ?_) j
      · rw [Fin.succ_last, rowMargin_last]
        simp [uniformIntegerMargin, uniformRowScale, hpR]
      · rw [rowMargin_interior, hmesh, hmesh]
        have hfirst : k.val + 1 ≠ 0 := by omega
        have hlast : k.val + 1 ≠ n + 2 := by have := k.isLt; omega
        simp only [uniformIntegerMargin, uniformRowScale, Fin.val_castSucc, Fin.val_succ,
          hfirst, hlast, ite_false, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
        ring
  · intro i
    exact residual_eq_uniformInteger mesh p q D hp hq hD hmesh v m i

end CAS.Splines.HermiteSlopeSystem
