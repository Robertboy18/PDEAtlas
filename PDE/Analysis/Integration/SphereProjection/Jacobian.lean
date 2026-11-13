/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.SphereProjection.Coordinates
public import PDE.Analysis.Calculus.Jacobian.Determinant
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Signed Jacobian of the hemisphere radial chart

The derivative has a scalar diagonal block and one extra row and column.
The Schur complement is the reciprocal hemisphere height. The determinant
is positive on both hemispheres and contains the absolute radial power.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

variable {n : ℕ}

private theorem jacobian_hemisphere_castSucc_castSucc {p : ℝ^(n + 1)}
    (hp : p ∈ hemisphereRadialDomain) (i j : Fin n) :
    jacobianMatrix hemisphereRadialMap p i.castSucc j.castSucc =
      |p (Fin.last n)| * if i = j then 1 else 0 := by
  change fderiv ℝ (fun q ↦ hemisphereRadialMap q i.castSucc) p
    (EuclideanSpace.single j.castSucc 1) = _
  simp only [hemisphereRadialMap_castSucc]
  rw [(((PiLp.hasFDerivAt_apply 2 p (Fin.last n)).abs hp.2.2).fun_mul
    (PiLp.hasFDerivAt_apply 2 p i.castSucc)).fderiv]
  simp [eq_comm]

private theorem jacobian_hemisphere_castSucc_last {p : ℝ^(n + 1)}
    (hp : p ∈ hemisphereRadialDomain) (i : Fin n) :
    jacobianMatrix hemisphereRadialMap p i.castSucc (Fin.last n) =
      (SignType.sign (p (Fin.last n)) : ℝ) * p i.castSucc := by
  change fderiv ℝ (fun q ↦ hemisphereRadialMap q i.castSucc) p
    (EuclideanSpace.single (Fin.last n) 1) = _
  simp only [hemisphereRadialMap_castSucc]
  rw [(((PiLp.hasFDerivAt_apply 2 p (Fin.last n)).abs hp.2.2).fun_mul
    (PiLp.hasFDerivAt_apply 2 p i.castSucc)).fderiv]
  simp [mul_comm]

private theorem jacobian_hemisphere_last_castSucc {p : ℝ^(n + 1)}
    (hp : p ∈ hemisphereRadialDomain) (j : Fin n) :
    jacobianMatrix hemisphereRadialMap p (Fin.last n) j.castSucc =
      -(p (Fin.last n) / √(1 - ‖coordinateProjection p‖ ^ 2)) *
        p j.castSucc := by
  change fderiv ℝ (fun q ↦ hemisphereRadialMap q (Fin.last n)) p
    (EuclideanSpace.single j.castSucc 1) = _
  simp only [hemisphereRadialMap_last]
  have hs := ((hasFDerivAt_const (x := p) (c := (1 : ℝ))).fun_sub
    coordinateProjection.hasFDerivAt.norm_sq).sqrt (sub_pos.2 hp.1).ne'
  rw [((PiLp.hasFDerivAt_apply 2 p (Fin.last n)).fun_mul hs).fderiv]
  simp [innerSL_apply_apply, EuclideanSpace.inner_single_right]
  ring

private theorem jacobian_hemisphere_last_last {p : ℝ^(n + 1)}
    (hp : p ∈ hemisphereRadialDomain) :
    jacobianMatrix hemisphereRadialMap p (Fin.last n) (Fin.last n) =
      √(1 - ‖coordinateProjection p‖ ^ 2) := by
  change fderiv ℝ (fun q ↦ hemisphereRadialMap q (Fin.last n)) p
    (EuclideanSpace.single (Fin.last n) 1) = _
  simp only [hemisphereRadialMap_last]
  have hs := ((hasFDerivAt_const (x := p) (c := (1 : ℝ))).fun_sub
    coordinateProjection.hasFDerivAt.norm_sq).sqrt (sub_pos.2 hp.1).ne'
  rw [((PiLp.hasFDerivAt_apply 2 p (Fin.last n)).fun_mul hs).fderiv]
  simp

/-- The derivative in the retained-coordinate and last-coordinate blocks. -/
theorem jacobianMatrix_hemisphereRadialMap_blocks {p : ℝ^(n + 1)}
    (hp : p ∈ hemisphereRadialDomain) :
    (jacobianMatrix hemisphereRadialMap p).submatrix
        (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)) finSumFinEquiv =
      Matrix.fromBlocks (|p (Fin.last n)| • (1 : Matrix (Fin n) (Fin n) ℝ))
        (Matrix.of fun i (_ : Fin 1) ↦ (SignType.sign (p (Fin.last n)) : ℝ) * p i.castSucc)
        (Matrix.of fun (_ : Fin 1) j ↦
          -(p (Fin.last n) / √(1 - ‖coordinateProjection p‖ ^ 2)) * p j.castSucc)
        (Matrix.of fun (_ _ : Fin 1) ↦ √(1 - ‖coordinateProjection p‖ ^ 2)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · change jacobianMatrix hemisphereRadialMap p i.castSucc j.castSucc = _
    simpa [Matrix.smul_apply, Matrix.one_apply] using
      jacobian_hemisphere_castSucc_castSucc hp i j
  · fin_cases j
    exact jacobian_hemisphere_castSucc_last hp i
  · fin_cases i
    exact jacobian_hemisphere_last_castSucc hp j
  · fin_cases i
    fin_cases j
    exact jacobian_hemisphere_last_last hp

/-- The radial chart has a positive signed Jacobian on both hemispheres. -/
theorem det_fderiv_hemisphereRadialMap {p : ℝ^(n + 1)} (hp : p ∈ hemisphereRadialDomain) :
    (fderiv ℝ hemisphereRadialMap p).det =
      |p (Fin.last n)| ^ n / √(1 - ‖coordinateProjection p‖ ^ 2) := by
  let r := p (Fin.last n)
  let a := √(1 - ‖coordinateProjection p‖ ^ 2)
  have hr : r ≠ 0 := hp.2.2
  have ha : 0 < a := hemisphereRadialDomain_sqrt_pos hp
  have ha₂ : a ^ 2 = 1 - ‖coordinateProjection p‖ ^ 2 :=
    Real.sq_sqrt (sub_nonneg.2 hp.1.le)
  let B : Matrix (Fin n) (Fin 1) ℝ := Matrix.of fun i _ ↦ p i.castSucc / r
  let C : Matrix (Fin 1) (Fin n) ℝ := Matrix.of fun _ j ↦ -(r / a) * p j.castSucc
  let D : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of fun _ _ ↦ a
  have hCB : C * B = Matrix.of (fun (_ _ : Fin 1) ↦ -(‖coordinateProjection p‖ ^ 2 / a)) := by
    ext i j
    simp only [Matrix.mul_apply, B, C, Matrix.of_apply]
    calc
      _ = ∑ k : Fin n, -(p k.castSucc ^ 2) / a := by
        apply Finset.sum_congr rfl
        intro k _
        field_simp
      _ = _ := by
        rw [← Finset.sum_div, Finset.sum_neg_distrib]
        simp only [EuclideanSpace.real_norm_sq_eq, coordinateProjection_apply, neg_div]
  have hschur : D - C * B = Matrix.of (fun (_ _ : Fin 1) ↦ 1 / a) := by
    rw [hCB]
    ext i j
    change a - -(‖coordinateProjection p‖ ^ 2 / a) = 1 / a
    field_simp
    nlinarith [ha₂]
  have hsign : (SignType.sign r : ℝ) = |r| / r := by
    rcases lt_or_gt_of_ne hr with hneg | hpos
    · simp [hneg, abs_of_neg hneg, hr]
    · simp [hpos, abs_of_pos hpos, hr]
  let v : Fin n ⊕ Fin 1 → ℝ := Sum.elim (fun _ ↦ |r|) (fun _ ↦ 1)
  have hmatrix :
      (jacobianMatrix hemisphereRadialMap p).submatrix
          (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)) finSumFinEquiv =
        Matrix.of (fun i j ↦ v i * Matrix.fromBlocks 1 B C D i j) := by
    rw [jacobianMatrix_hemisphereRadialMap_blocks hp]
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · change (SignType.sign r : ℝ) * p i.castSucc = |r| * (p i.castSucc / r)
      rw [hsign]
      ring
    · change -(r / a) * p j.castSucc = 1 * (-(r / a) * p j.castSucc)
      exact (one_mul _).symm
    · change a = 1 * a
      exact (one_mul _).symm
  rw [← det_jacobianMatrix (differentiableAt_hemisphereRadialMap hp),
    ← Matrix.det_submatrix_equiv_self
      (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)), hmatrix,
    Matrix.det_mul_column, Matrix.det_fromBlocks_one₁₁, hschur, Matrix.det_fin_one]
  simp [v, Fintype.prod_sum_type, div_eq_mul_inv, r, a]

end PDE.Analysis
