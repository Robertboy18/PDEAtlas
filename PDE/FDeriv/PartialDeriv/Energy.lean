/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv

/-!
# Operator energy from coordinate derivatives

The norm of a linear map on Euclidean space is bounded by the sum of the norms
of its values on coordinate unit vectors. Finite-sum convexity then bounds its
`p`-energy by `n ^ (p - 1)` times the coordinate `p`-energy for `p ≥ 1`.
For squared norms, Cauchy–Schwarz removes the dimension factor entirely.

The target can be any real normed space, and `n = 0` is allowed. The corollary
for `fderiv` needs no differentiability hypothesis, since the comparison holds
for every continuous linear map.
-/

@[expose] public section

namespace ContinuousLinearMap

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The images of the Euclidean coordinate unit vectors control the operator norm. -/
theorem norm_le_sum_norm_apply_single (L : ℝ^n →L[ℝ] F) :
    ‖L‖ ≤ ∑ i, ‖L (EuclideanSpace.single i 1)‖ := by
  classical
  apply L.opNorm_le_bound (Finset.sum_nonneg fun i _ ↦ norm_nonneg _)
  intro x
  have hx : (∑ i : Fin n, x i • EuclideanSpace.single i (1 : ℝ)) = x := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x
  calc
    ‖L x‖ = ‖∑ i : Fin n, x i • L (EuclideanSpace.single i 1)‖ := by
      conv_lhs => rw [← hx, map_sum]
      simp only [map_smul]
    _ ≤ ∑ i : Fin n, ‖x i • L (EuclideanSpace.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin n, ‖L (EuclideanSpace.single i 1)‖ * ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x i) (norm_nonneg _)
    _ = (∑ i : Fin n, ‖L (EuclideanSpace.single i 1)‖) * ‖x‖ := by
      rw [Finset.sum_mul]

/-- The operator `p`-energy is bounded by the coordinate `p`-energy with the
explicit factor `n ^ (p - 1)`. This includes `p = 1` and `n = 0`. -/
theorem norm_rpow_le_sum_norm_apply_single_rpow (L : ℝ^n →L[ℝ] F)
    {p : ℝ} (hp : 1 ≤ p) :
    ‖L‖ ^ p ≤ (n : ℝ) ^ (p - 1) * ∑ i, ‖L (EuclideanSpace.single i 1)‖ ^ p := by
  calc
    ‖L‖ ^ p ≤ (∑ i, ‖L (EuclideanSpace.single i 1)‖) ^ p :=
      Real.rpow_le_rpow (norm_nonneg _) L.norm_le_sum_norm_apply_single (zero_le_one.trans hp)
    _ ≤ _ := by
      simpa using Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg Finset.univ hp
        (fun i _ ↦ norm_nonneg (L (EuclideanSpace.single i 1)))

/-- The sum of squared column norms bounds the squared operator norm on Euclidean
space. The target may be any real normed space, and the empty domain is included. -/
theorem norm_sq_le_sum_norm_apply_single_sq
    (L : ℝ^n →L[ℝ] F) :
    ‖L‖ ^ 2 ≤ ∑ i, ‖L (EuclideanSpace.single i 1)‖ ^ 2 := by
  classical
  have hsum : 0 ≤ ∑ i : Fin n, ‖L (EuclideanSpace.single i 1)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hnorm : ‖L‖ ≤ √(∑ i : Fin n, ‖L (EuclideanSpace.single i 1)‖ ^ 2) := by
    apply L.opNorm_le_bound (Real.sqrt_nonneg _)
    intro x
    have hx : (∑ i : Fin n, x i • EuclideanSpace.single i (1 : ℝ)) = x := by
      simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
        (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x
    calc
      ‖L x‖ = ‖∑ i : Fin n, x i • L (EuclideanSpace.single i 1)‖ := by
        conv_lhs => rw [← hx, map_sum]
        simp only [map_smul]
      _ ≤ ∑ i : Fin n, ‖x i • L (EuclideanSpace.single i 1)‖ := norm_sum_le _ _
      _ = ∑ i : Fin n, ‖L (EuclideanSpace.single i 1)‖ * ‖x i‖ := by
        simp only [norm_smul, mul_comm]
      _ ≤ √(∑ i : Fin n, ‖L (EuclideanSpace.single i 1)‖ ^ 2) *
          √(∑ i : Fin n, ‖x i‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
          (fun i ↦ ‖L (EuclideanSpace.single i 1)‖) (fun i ↦ ‖x i‖)
      _ = √(∑ i : Fin n, ‖L (EuclideanSpace.single i 1)‖ ^ 2) * ‖x‖ := by
        rw [← EuclideanSpace.norm_sq_eq, Real.sqrt_sq (norm_nonneg x)]
  exact ((sq_le_sq₀ (norm_nonneg L) (Real.sqrt_nonneg _)).mpr hnorm).trans_eq
    (Real.sq_sqrt hsum)


end ContinuousLinearMap

namespace PDE

/-- The operator norm of the Fréchet derivative is at most the sum of the norms of the
coordinate partial derivatives, `‖Df(x)‖ ≤ ∑ᵢ ‖∂ᵢf(x)‖`. -/
theorem norm_fderiv_le_sum_norm_partialDeriv
    {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ^n → F) (x : ℝ^n) :
    ‖fderiv ℝ f x‖ ≤ ∑ i, ‖(∂[i] f) x‖ :=
  (fderiv ℝ f x).norm_le_sum_norm_apply_single

/-- Coordinate partial derivatives control the Fréchet derivative's operator
`p`-energy, with dimension factor `n ^ (p - 1)` and arbitrary real normed target. -/
theorem norm_fderiv_rpow_le_sum_norm_partialDeriv_rpow
    {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ^n → F) (x : ℝ^n) {p : ℝ} (hp : 1 ≤ p) :
    ‖fderiv ℝ f x‖ ^ p ≤ (n : ℝ) ^ (p - 1) * ∑ i, ‖(∂[i] f) x‖ ^ p := by
  exact (fderiv ℝ f x).norm_rpow_le_sum_norm_apply_single_rpow hp


/-- The squared operator norm of the Fréchet derivative is bounded by the sum of
squared coordinate derivative norms, without a dimension factor. -/
theorem norm_fderiv_sq_le_sum_norm_partialDeriv_sq
    {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ^n → F) (x : ℝ^n) :
    ‖fderiv ℝ f x‖ ^ 2 ≤ ∑ i, ‖(∂[i] f) x‖ ^ 2 :=
  (fderiv ℝ f x).norm_sq_le_sum_norm_apply_single_sq

end PDE
