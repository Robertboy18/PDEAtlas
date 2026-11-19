/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# A signed nonquadratic uniformly convex density

The density `p²/2 + (1-cos p)/4 + 2p - 3` has Hessian between `3/4`
and `5/4`. Its value and first derivative at zero are both nonzero. These are the
convexity and Hessian bounds used by the interval energy examples.
-/

@[expose] public noncomputable section

namespace PDE.Examples.GradientEnergy

open scoped RealInnerProductSpace

/-- A smooth signed density with an oscillating positive Hessian and a
nonzero affine part. -/
def signedDensity (p : ℝ^1) : ℝ :=
  p 0 ^ 2 / 2 + (1 - Real.cos (p 0)) / 4 + 2 * p 0 - 3

/-- The concrete density is twice continuously differentiable. -/
theorem signedDensity_contDiff : ContDiff ℝ 2 signedDensity := by
  cas

/-- The flux `DF(p) = p + sin p / 4 + 2`. -/
theorem signedDensity_firstPartial (p : ℝ^1) :
    (∂[0] signedDensity) p = p 0 + Real.sin (p 0) / 4 + 2 := by
  cas

/-- The Hessian `1 + cos p / 4`. -/
theorem signedDensity_secondPartial (p : ℝ^1) :
    (∂[0] (∂[0] signedDensity)) p = 1 + Real.cos (p 0) / 4 := by
  rw [funext signedDensity_firstPartial]
  cas

/-- The flux at zero is `2`. -/
theorem signedDensity_firstPartial_zero : (∂[0] signedDensity) 0 = 2 := by
  cas

/-- The density takes a negative value at the zero gradient. -/
theorem signedDensity_zero : signedDensity 0 = -3 := by
  cas

/-- The second Fréchet derivative is `(1 + cos p₀ / 4) v₀ w₀`. -/
theorem signedDensity_hessian (p v w : ℝ^1) :
    fderiv ℝ (fderiv ℝ signedDensity) p v w =
      (1 + Real.cos (p 0) / 4) * v 0 * w 0 := by
  have he (z : ℝ^1) : z = z 0 • EuclideanSpace.single 0 1 := by
    ext i
    fin_cases i
    simp
  have hc := signedDensity_secondPartial p
  rw [secondPartialDeriv_eq_fderiv 0 0
    ((signedDensity_contDiff.fderiv_right (m := 1) (by norm_num)).differentiable_one p)] at hc
  calc
    _ = fderiv ℝ (fderiv ℝ signedDensity) p
        (v 0 • EuclideanSpace.single 0 1) (w 0 • EuclideanSpace.single 0 1) := by
      rw [← he v, ← he w]
    _ = _ := by
      simp only [map_smul, smul_apply, smul_eq_mul, hc]
      ring

/-- Uniform convexity holds in every direction with constant `3/4`. -/
theorem signedDensity_hessian_lower (p v : ℝ^1) :
    (3 / 4 : ℝ) * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ signedDensity) p v v := by
  rw [signedDensity_hessian, EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_one]
  nlinarith [Real.neg_one_le_cos (p 0), sq_nonneg (v 0)]

/-- The Hessian operator norm is bounded by `5/4` everywhere. -/
theorem signedDensity_hessian_upper (p : ℝ^1) :
    ‖fderiv ℝ (fderiv ℝ signedDensity) p‖ ≤ (5 / 4 : ℝ) := by
  have hc : |1 + Real.cos (p 0) / 4| ≤ (5 / 4 : ℝ) :=
    abs_le.mpr ⟨by linarith [Real.neg_one_le_cos (p 0)], by linarith [Real.cos_le_one (p 0)]⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) (norm_nonneg v))
  intro w
  rw [signedDensity_hessian, Real.norm_eq_abs, abs_mul, abs_mul]
  exact mul_le_mul
    (mul_le_mul hc (PiLp.norm_apply_le v 0) (abs_nonneg _) (by norm_num))
    (PiLp.norm_apply_le w 0) (abs_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg v))

end PDE.Examples.GradientEnergy
