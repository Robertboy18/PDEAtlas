/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.MaximumPrinciple.Hopf
public import PDE.FDeriv.Calculus.SecondDirectionalDerivative

/-!
# Hopf's lemma for the Laplacian with constant potential

A positive supersolution of `−Δ + c`, with nonnegative constant potential, has negative outward
derivative at a zero on the sphere (`hopf_fderiv_neg_of_pos_of_neg_laplacian_add_mul_nonneg`). Only
the function's regularity inside the tangent ball and differentiability at the contact point are
required. Applied to `-u`, which has the boundary maximum `0`, this is part (ii) of Hopf's Lemma in
Evans's §6.4.2 for `L = -Δ + c`. It specializes the factored Hopf lemma of `MaximumPrinciple.Hopf`
to the standard orthonormal basis.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.4.2, Hopf's Lemma, pp. 347-349.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE (laplacian)

namespace EllipticMaximum

open Set Metric PDE.Analysis
open scoped RealInnerProductSpace

/-- A positive supersolution of `−Δ + c` has strictly negative derivative in the
outward normal direction of a tangent ball at a zero boundary value. -/
theorem hopf_fderiv_neg_of_pos_of_neg_laplacian_add_mul_nonneg
    {n : ℕ} {u : ℝ^n → ℝ} {z x : ℝ^n} {R c : ℝ}
    (hR : 0 < R) (hc : 0 ≤ c) (hx : ‖x - z‖ = R) (hzero : u x = 0)
    (hcont : ContinuousOn u (closedBall z R))
    (hreg : ∀ y ∈ ball z R, ContDiffAt ℝ 2 u y)
    (hpos : ∀ y ∈ ball z R, 0 < u y)
    (hsuper : ∀ y ∈ ball z R, 0 ≤ -laplacian u y + c * u y)
    (hdiff : DifferentiableAt ℝ u x) :
    fderiv ℝ u x (R⁻¹ • (x - z)) < 0 := by
  have hoperator (g : ℝ^n → ℝ) (y : ℝ^n) (hg : ContDiffAt ℝ 2 g y) :
      factoredOperator (fun (_ : ℝ^n) (i : Fin n) ↦ EuclideanSpace.single i (1 : ℝ))
        (fun _ ↦ 0) (fun _ ↦ c) g y = -laplacian g y + c * g y := by
    simp [factoredOperator, secondDirectionalDerivative_eq_sum hg, laplacian]
  have h := hopf_normal_fderiv_pos
    (fun (_ : ℝ^n) (i : Fin n) ↦ EuclideanSpace.single i (1 : ℝ))
    (fun _ ↦ 0) (fun _ ↦ c) z hR (κ := 1) zero_lt_one
    (A := n) (Nat.cast_nonneg n) (B := 0) le_rfl (C := c) hc
    (fun _ _ _ v ↦ by
      simp [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.inner_single_right])
    (fun _ _ _ ↦ by simp)
    (fun _ _ _ ↦ by simp)
    (fun _ _ _ ↦ ⟨hc, le_rfl⟩) hx (u := fun y ↦ -u y) (by simp [hzero])
    hcont.neg (fun y hy ↦ (hreg y hy).neg) (fun y hy ↦ by
      rw [hoperator _ y (hreg y hy).neg]
      change -laplacian (-u) y + c * (-u y) ≤ 0
      rw [PDE.laplacian_neg]
      linarith [hsuper y hy])
    (fun y hy ↦ by simpa [hzero] using hpos y hy) hdiff.neg
  simpa only [fderiv_fun_neg, neg_apply, neg_pos] using h

end EllipticMaximum
