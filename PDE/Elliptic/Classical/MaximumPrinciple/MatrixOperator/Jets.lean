/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.MaximumPrinciple.MatrixOperator

/-!
# The matrix operator on given derivatives

First and second Fréchet derivatives identify the coordinate
operator without additional smoothness assumptions. Its perturbation estimate
uses the operator norms of these derivatives and the sum of absolute matrix
entries. No symmetry or ellipticity is needed for this estimate.
-/

@[expose] public noncomputable section

namespace EllipticMaximum

open Filter
open scoped Topology

variable {n : ℕ}

/-- Supplied first and second derivatives evaluate the matrix operator.
The first derivative is identified on a neighborhood so that its derivative
also identifies the iterated partial derivatives. -/
theorem matrixOperator_eq_of_hasFDerivAt
    (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n) (c : ℝ^n → ℝ)
    {u : ℝ^n → ℝ} {Du : ℝ^n → ℝ^n →L[ℝ] ℝ}
    {H : ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ} {x : ℝ^n}
    (hu : ∀ᶠ y in 𝓝 x, HasFDerivAt u (Du y) y) (hDu : HasFDerivAt Du H x) :
    matrixOperator a b c u x =
      -(∑ i : Fin n, ∑ j : Fin n,
        a x i j * H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) +
        Du x (b x) + c x * u x := by
  have heq : fderiv ℝ u =ᶠ[𝓝 x] Du := hu.mono fun _ hy ↦ hy.fderiv
  have hsecond := hDu.congr_of_eventuallyEq heq
  rw [matrixOperator_apply, hu.self_of_nhds.fderiv]
  simp only [PDE.secondPartialDeriv_eq_fderiv _ _ hsecond.differentiableAt, hsecond.fderiv]

/-- Differences of the value, gradient and Hessian control the difference
of matrix residuals. The statement also covers zero spatial dimension. -/
theorem abs_matrixOperator_sub_le_of_hasFDerivAt
    (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n) (c : ℝ^n → ℝ)
    {u v : ℝ^n → ℝ} {Du Dv : ℝ^n → ℝ^n →L[ℝ] ℝ}
    {Hu Hv : ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ} {x : ℝ^n}
    (hu : ∀ᶠ y in 𝓝 x, HasFDerivAt u (Du y) y) (hDu : HasFDerivAt Du Hu x)
    (hv : ∀ᶠ y in 𝓝 x, HasFDerivAt v (Dv y) y) (hDv : HasFDerivAt Dv Hv x) :
    |matrixOperator a b c u x - matrixOperator a b c v x| ≤
      (∑ i : Fin n, ∑ j : Fin n, |a x i j|) * ‖Hu - Hv‖ +
        ‖b x‖ * ‖Du x - Dv x‖ + |c x| * |u x - v x| := by
  have hentry (i j : Fin n) :
      |(Hu - Hv) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤
        ‖Hu - Hv‖ := by
    simpa only [PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs] using
      (Hu - Hv).le_opNorm₂ (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  have hsum :
      |∑ i : Fin n, ∑ j : Fin n, a x i j *
          (Hu - Hv) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤
        (∑ i : Fin n, ∑ j : Fin n, |a x i j|) * ‖Hu - Hv‖ := by
    calc
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, |a x i j *
          (Hu - Hv) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ ↦ Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, |a x i j| * ‖Hu - Hv‖ := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hentry i j) (abs_nonneg _)
      _ = _ := by simp only [Finset.sum_mul]
  have hdrift : |(Du x - Dv x) (b x)| ≤ ‖b x‖ * ‖Du x - Dv x‖ := by
    simpa only [Real.norm_eq_abs, mul_comm] using (Du x - Dv x).le_opNorm (b x)
  rw [matrixOperator_eq_of_hasFDerivAt a b c hu hDu,
    matrixOperator_eq_of_hasFDerivAt a b c hv hDv]
  have heq :
      -(∑ i : Fin n, ∑ j : Fin n,
          a x i j * Hu (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) +
        Du x (b x) + c x * u x -
        (-(∑ i : Fin n, ∑ j : Fin n,
          a x i j * Hv (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) +
        Dv x (b x) + c x * v x) =
      -(∑ i : Fin n, ∑ j : Fin n,
          a x i j * (Hu - Hv) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) +
        (Du x - Dv x) (b x) + c x * (u x - v x) := by
    simp only [sub_apply, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [heq]
  calc
    _ ≤ |∑ i : Fin n, ∑ j : Fin n,
          a x i j * (Hu - Hv) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| +
        |(Du x - Dv x) (b x)| + |c x * (u x - v x)| := by
      apply (abs_add_le _ _).trans
      apply add_le_add _ le_rfl
      simpa only [abs_neg] using
        (abs_add_le (-(∑ i : Fin n, ∑ j : Fin n, a x i j *
          (Hu - Hv) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)))
          ((Du x - Dv x) (b x)))
    _ ≤ _ := by
      rw [abs_mul]
      exact add_le_add (add_le_add hsum hdrift) le_rfl

end EllipticMaximum
