/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean

/-!
# Coordinate formulas in `ℝ^n`

The Euclidean inner product is the coordinate sum `Σᵢ aᵢ bᵢ`, the norm is at most the sum of
the absolute values of the coordinates, and a linear map is determined by its values on the
standard basis, `L v = Σⱼ vⱼ L eⱼ`. The trace `Σₖ B(eₖ, eₖ)` of a bilinear form is unchanged when
the standard basis is replaced by its image under a linear isometry.
-/

@[expose] public section

open scoped RealInnerProductSpace

namespace EuclideanSpace

variable {n : ℕ}

/-- The Euclidean inner product as a coordinate sum. -/
theorem real_inner_eq_sum (a b : ℝ^n) : ⟪a, b⟫ = ∑ i, a i * b i := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [RCLike.inner_apply, conj_trivial, mul_comm]

/-- The Euclidean norm is at most the sum of the absolute values of the coordinates. -/
theorem norm_le_sum_abs (w : ℝ^n) : ‖w‖ ≤ ∑ i, |w i| := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hexp : w = ∑ i, ⟪b i, w⟫ • b i := (b.sum_repr' w).symm
  calc ‖w‖ = ‖∑ i, ⟪b i, w⟫ • b i‖ := by rw [← hexp]
    _ ≤ ∑ i, ‖⟪b i, w⟫ • b i‖ := norm_sum_le _ _
    _ = ∑ i, |w i| := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [norm_smul, b.orthonormal.1 i, mul_one, EuclideanSpace.basisFun_inner,
          Real.norm_eq_abs]

/-- Each coordinate is bounded by the norm: `|xᵢ| ≤ ‖x‖`. -/
theorem abs_apply_le_norm (x : ℝ^n) (i : Fin n) : |x i| ≤ ‖x‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i

/-- In the plane, `‖x‖² = x₀² + x₁²`. -/
theorem norm_sq_fin_two (x : ℝ^2) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

/-- In the plane, `‖x‖ ≤ |x₀| + |x₁|`. -/
theorem norm_le_abs_add_abs_fin_two (x : ℝ^2) : ‖x‖ ≤ |x 0| + |x 1| :=
  (norm_le_sum_abs x).trans_eq (Fin.sum_univ_two _)

/-- A linear map applied to `v` is `Σⱼ vⱼ L eⱼ`. -/
theorem map_eq_sum_smul_single {F G : Type*} [AddCommGroup G] [Module ℝ G] [FunLike F (ℝ^n) G]
    [LinearMapClass F ℝ (ℝ^n) G] (L : F) (v : ℝ^n) :
    L v = ∑ j, v j • L (EuclideanSpace.single j 1) := by
  have hv : v = ∑ j, v j • EuclideanSpace.single j (1 : ℝ) := by
    ext i
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul]

/-- The trace of a bilinear form is the same in the standard basis and in its image under a
linear isometry. -/
theorem sum_bilinear_isometry (B : ℝ^n →ₗ[ℝ] ℝ^n →ₗ[ℝ] ℝ) (g : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) :
    ∑ k, B (g (EuclideanSpace.single k 1)) (g (EuclideanSpace.single k 1)) =
      ∑ k, B (EuclideanSpace.single k 1) (EuclideanSpace.single k 1) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hb (k : Fin n) : b k = EuclideanSpace.single k 1 := EuclideanSpace.basisFun_apply _ _ _
  have hexp (v : ℝ^n) : v = ∑ i, ⟪b i, v⟫ • b i := (b.sum_repr' v).symm
  have hkey (k : Fin n) : B (g (b k)) (g (b k)) =
      ∑ i, ∑ j, ⟪b i, g (b k)⟫ * ⟪b j, g (b k)⟫ * B (b i) (b j) := by
    conv_lhs => rw [hexp (g (b k))]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have horth (i j : Fin n) : ∑ k, ⟪b i, g (b k)⟫ * ⟪b j, g (b k)⟫ = ⟪b i, b j⟫ := by
    have h := b.sum_inner_mul_inner (g.symm (b i)) (g.symm (b j))
    rw [g.symm.inner_map_map] at h
    rw [← h]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [g.symm.inner_map_eq_flip, LinearIsometryEquiv.symm_symm, ← g.inner_map_eq_flip,
      real_inner_comm (g (b k)) (b j)]
  have hdelta (i j : Fin n) : ⟪b i, b j⟫ = if i = j then 1 else 0 := by
    rw [hb, hb, EuclideanSpace.inner_single_left]
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  calc ∑ k, B (g (EuclideanSpace.single k 1)) (g (EuclideanSpace.single k 1))
      = ∑ k, ∑ i, ∑ j, ⟪b i, g (b k)⟫ * ⟪b j, g (b k)⟫ * B (b i) (b j) := by
        simp only [← hb]
        exact Finset.sum_congr rfl fun k _ ↦ hkey k
    _ = ∑ i, ∑ j, (∑ k, ⟪b i, g (b k)⟫ * ⟪b j, g (b k)⟫) * B (b i) (b j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
    _ = ∑ i, B (b i) (b i) := by
        simp only [horth, hdelta, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
          Finset.mem_univ, ite_true]
    _ = _ := by simp only [hb]

end EuclideanSpace
