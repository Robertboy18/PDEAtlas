/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.GaussianRegularization.Parameter
public import PDE.Analysis.Operator.ConstantCoefficient.FirstOrder.Evolution

/-!
# Gaussian regularization of a classical first-order evolution

For compactly supported classical solutions with zero initial value, the
regularized inverse Fourier integral is the spacetime action of the operator
kernel on the source. The coefficient pencil retains Mathlib's `2π` convention.
-/

@[expose] public noncomputable section

open MeasureTheory Set Complex
open scoped FourierTransform RealInnerProductSpace

namespace PDE.Analysis

open PDE.Analysis.Fourier

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

attribute [local instance] Evolution.normedAlgebraRatLinearEndomorphism

/-- Gaussian regularization of a zero-initial classical solution is given by
the operator kernel acting on its forcing. All integrability is derived
from continuity and a common compact spatial support. -/
theorem integral_gaussian_fourier_eq_firstOrder_source
    (A : Fin n → E →L[ℂ] E) {u F : ℝ × ℝ^n → E}
    {a c b : ℝ} {K : Set (ℝ^n)} (hac : a ≤ c) (hb : 0 < b) (hK : IsCompact K)
    (hu : ContDiffOn ℝ 1 u (Ioo a c ×ˢ univ))
    (huc : ContinuousOn u (Icc a c ×ˢ univ))
    (hFc : ContinuousOn F (Icc a c ×ˢ univ))
    (hsu : ∀ t ∈ Icc a c, ∀ x ∉ K, u (t, x) = 0)
    (hsF : ∀ t ∈ Icc a c, ∀ x ∉ K, F (t, x) = 0)
    (hi : ∀ x, u (a, x) = 0)
    (heq : ∀ t ∈ Ioo a c, ∀ x, fderiv ℝ u (t, x) (1, 0) +
      ∑ j, A j (fderiv ℝ u (t, x) (0, EuclideanSpace.single j 1)) = F (t, x))
    (x : ℝ^n) :
    (∫ ξ : ℝ^n, Complex.exp (-(b : ℂ) * ‖ξ‖ ^ 2 +
      2 * Real.pi * I * ⟪x, ξ⟫) • (𝓕 (fun y ↦ u (c, y))) ξ) =
      ∫ t in a..c, ∫ y : ℝ^n,
        gaussianExponentialKernel
          (fun j ↦ (((c - t : ℝ) : ℂ) * (-(2 * Real.pi * I))) • A j) b
          (fun j ↦ 2 * Real.pi * (x j - y j)) (F (t, y)) := by
  let S : ℝ → Fin n → E →L[ℂ] E :=
    fun t j ↦ (((c - t : ℝ) : ℂ) * (-(2 * Real.pi * I))) • A j
  have hgen (t : ℝ) (ξ : ℝ^n) :
      (c - t) • ((-(2 * Real.pi * I)) • ∑ j, ⟪EuclideanSpace.single j 1, ξ⟫ • A j) =
        ∑ j, (ξ j : ℂ) • S t j := by
    simp only [S, EuclideanSpace.inner_single_left, map_one, one_mul,
      RCLike.real_smul_eq_coe_smul (K := ℂ), Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    simpa only [mul_assoc] using!
      mul_comm (((c - t : ℝ) : ℂ) * (-(2 * Real.pi * I))) (ξ j : ℂ)
  have hsolution (ξ : ℝ^n) :
      𝓕 (fun y ↦ u (c, y)) ξ =
        ∫ t in a..c, NormedSpace.exp (∑ j, (ξ j : ℂ) • S t j)
          (𝓕 (fun y ↦ F (t, y)) ξ) := by
    have h := fourier_eq_exp_add_integral_of_firstOrder
      (fun j ↦ EuclideanSpace.single j 1) A hac hK hu huc hFc hsu hsF heq ξ
    have hz : 𝓕 (fun y ↦ u (a, y)) ξ = 0 := by
      simp only [hi, Real.fourier_eq, smul_zero, integral_zero]
    dsimp only at h
    simpa only [hz, map_zero, zero_add, hgen] using h
  have hS (j : Fin n) : ContinuousOn (fun t ↦ S t j) (Icc a c) := by
    dsimp [S]
    fun_prop
  calc
    _ = ∫ ξ : ℝ^n, ∫ t in a..c,
        gaussianExponentialIntegrand (S t) b (fun j ↦ 2 * Real.pi * x j)
          (WithLp.ofLp ξ) (𝓕 (fun y ↦ F (t, y)) ξ) := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [hsolution, ← intervalIntegral.integral_smul]
      apply intervalIntegral.integral_congr
      intro t _
      unfold gaussianExponentialIntegrand
      simp only [smul_apply]
      congr 2
      have hphase : (∑ j, 2 * Real.pi * x j * ξ j) = 2 * Real.pi * ⟪x, ξ⟫ := by
        simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Finset.mul_sum,
          mul_comm, mul_assoc]
      rw [← Complex.ofReal_pow, EuclideanSpace.real_norm_sq_eq, hphase]
      push_cast
      ring
    _ = ∫ t in a..c, ∫ y : ℝ^n,
        gaussianExponentialKernel (S t) b
          (fun j ↦ 2 * Real.pi * x j - 2 * Real.pi * y j) (F (t, y)) :=
      integral_intervalIntegral_gaussianExponential_fourier_eq S hac hb
        (fun j ↦ 2 * Real.pi * x j) hK hS hFc hsF
    _ = _ := by simp only [S, mul_sub]

end PDE.Analysis
