/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import PDE.Common.Euclidean
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# The Infinite-Exponent Morrey Endpoint

The dimension-independent `p = ∞` estimate, obtained from the pointwise derivative bound
and the convex mean-value theorem.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.6.2, Theorem 4, (20), p. 280.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace


open MeasureTheory Set
open scoped ENNReal

/-- For a `C¹` function on Euclidean space, the norm of the derivative at every point is bounded
by its `L∞` essential supremum.  The representative upgrade is valid because the derivative norm
is continuous and Lebesgue measure is positive on every nonempty open set. -/
theorem enorm_fderiv_le_eLpNorm_top
    {n : ℕ} (u : ℝ^n → ℝ) (hu : ContDiff ℝ 1 u) (z : ℝ^n) :
    ‖fderiv ℝ u z‖ₑ ≤ eLpNorm (fderiv ℝ u) ∞ volume := by
  rw [eLpNorm_exponent_top (hu.continuous_fderiv one_ne_zero).aestronglyMeasurable]
  let good : Set (ℝ^n) :=
    {x | ‖fderiv ℝ u x‖ₑ ≤ eLpNormEssSup (fderiv ℝ u) volume}
  have hgoodAE : ∀ᵐ x ∂(volume : Measure (ℝ^n)), x ∈ good := by
    simpa [good] using
      (ae_le_eLpNormEssSup :
        ∀ᵐ x ∂(volume : Measure (ℝ^n)),
          ‖fderiv ℝ u x‖ₑ ≤ eLpNormEssSup (fderiv ℝ u) volume)
  have hgoodDense : Dense good :=
    (volume : Measure (ℝ^n)).dense_of_ae hgoodAE
  have hgoodClosed : IsClosed good := by
    exact isClosed_le
      ((hu.continuous_fderiv one_ne_zero).enorm)
      continuous_const
  have hzClosure : z ∈ closure good := by
    rw [hgoodDense.closure_eq]
    exact Set.mem_univ z
  exact hgoodClosed.closure_subset hzClosure

/-- The mean value inequality on `ℝ^n`: if `u` is differentiable and `‖Du(z)‖ ≤ C` for every `z`,
then `|u y - u x| ≤ C ‖y - x‖`. This is the pointwise form of the exponent-one endpoint
`1 - n/∞ = 1` of Morrey's estimate (Evans §5.6.2, estimate (20)), proved by Mathlib's convex
mean-value theorem `Convex.norm_image_sub_le_of_norm_fderiv_le`. -/
theorem norm_sub_le_of_fderiv_bound
    {n : ℕ} (u : ℝ^n → ℝ) (hu : Differentiable ℝ u) {C : ℝ}
    (hC : ∀ z, ‖fderiv ℝ u z‖ ≤ C) (x y : ℝ^n) :
    |u y - u x| ≤ C * ‖y - x‖ := by
  simpa [Real.norm_eq_abs, abs_sub_comm, norm_sub_rev] using
    (convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (s := (Set.univ : Set (ℝ^n))) (f := u)
      (fun z _ ↦ hu z) (fun z _ ↦ hC z) (Set.mem_univ y) (Set.mem_univ x))

/-- **Morrey's `p = ∞` estimate in arbitrary dimension**, the seminorm part of Evans §5.6.2,
Theorem 4, estimate (20), for `p = ∞`.

If `u` is `C¹` on `ℝ^n` and `‖Du‖_{L∞}` is finite, then `|u y - u x| ≤ ‖Du‖_{L∞} ‖y - x‖` for all
`x` and `y`. The bound on the uniform norm is added in
`SobolevSpace.exists_holder_one_of_contDiff`. -/
theorem norm_sub_le_eLpNorm_fderiv_top_toReal_mul_norm
    {n : ℕ} (u : ℝ^n → ℝ) (hu : ContDiff ℝ 1 u)
    (hfinite : eLpNorm (fderiv ℝ u) ∞ volume ≠ ∞) (x y : ℝ^n) :
    |u y - u x| ≤
      (eLpNorm (fderiv ℝ u) ∞ volume).toReal * ‖y - x‖ := by
  have hpoint : ∀ z, ‖fderiv ℝ u z‖ ≤
      (eLpNorm (fderiv ℝ u) ∞ volume).toReal := by
    intro z
    have hz := enorm_fderiv_le_eLpNorm_top u hu z
    have hzReal := ENNReal.toReal_mono hfinite hz
    simpa using hzReal
  exact norm_sub_le_of_fderiv_bound u
    (hu.differentiable one_ne_zero) hpoint x y

end SobolevSpace
