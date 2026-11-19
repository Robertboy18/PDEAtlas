/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.MeanValue.PDEToMeanValue
public import PDE.Elliptic.Classical.MeanValue.Estimates.Integral

/-!
# Derivative estimates and Liouville's theorem for harmonic functions

We develop the first-order part of Evans's interior derivative
estimates for harmonic functions.  The derivative formula for the Poisson
extension at the center of a ball first gives a quantitative bound in terms
of the boundary supremum.  Applying the ball mean-value formula on overlapping
half-radius balls yields Evans's `L¹` estimate with its explicit constant.
Increasing the radius in the boundary estimate proves that every bounded
entire harmonic function is constant.

Evans gets the boundary bound (his (20)) from the mean-value formula for `u_{x_i}` and the
divergence theorem. We differentiate Poisson's formula for the ball at its center instead
(`fderiv_poissonBallExtension_zero_apply`), which bounds the derivative in every direction at
once.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.3, Theorem 7 (Estimates on derivatives), its constants
  (19) and the bound (20) in its proof, p. 29; Theorem 8 (Liouville's Theorem) and its proof, p. 30;
  §2.2.4, Poisson's formula for the ball (45), p. 41.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace GreenFunction

open MeasureTheory PDE.Analysis Set

/-- Directional derivative of the Poisson extension at the center of a ball.

The coefficient is normalized using the surface area of the unit sphere. -/
theorem fderiv_poissonBallExtension_zero_apply
    {n : ℕ} [Fact (0 < n)] {r : ℝ} (hr : 0 < r)
    {g : ℝ^n → ℝ} (hg : Continuous g) (v : ℝ^n) :
    fderiv ℝ (poissonBallExtension (n := n) r g) 0 v =
      ((n : ℝ) / (unitSphereArea n * r)) *
        ∫ ω : Metric.sphere (0 : ℝ^n) 1,
          g (r • (ω : ℝ^n)) * inner ℝ v (ω : ℝ^n)
            ∂((volume : Measure (ℝ^n)).toSphere) := by
  classical
  have hzero : (0 : ℝ^n) ∈ Metric.ball (0 : ℝ^n) r := Metric.mem_ball_self hr
  have hkernel (ω : Metric.sphere (0 : ℝ^n) 1) :
      EuclideanDistance.invDistPowFDerivFormula n (0 : ℝ^n) (r • (ω : ℝ^n)) v =
        ((n : ℝ) / r ^ (n + 1)) * inner ℝ v (ω : ℝ^n) := by
    have hω : ‖(ω : ℝ^n)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
    rw [EuclideanDistance.invDistPowFDerivFormula_apply_eq_of_ne n fun h ↦ by
        simpa [norm_smul, hω, abs_of_pos hr, hr.ne] using congrArg norm h,
      show dist (0 : ℝ^n) (r • (ω : ℝ^n)) = r by simp [norm_smul, hω, abs_of_pos hr],
      show (innerSL ℝ v) ((0 : ℝ^n) - r • (ω : ℝ^n)) = -r * inner ℝ v (ω : ℝ^n) by
        simp [innerSL_apply_apply, inner_smul_right], pow_succ r (n + 1)]
    field_simp
  have hintegral :
      ((∫ ω : Metric.sphere (0 : ℝ^n) 1,
          (g (r • (ω : ℝ^n))) •
            EuclideanDistance.invDistPowFDerivFormula n (0 : ℝ^n) (r • (ω : ℝ^n))
          ∂((volume : Measure (ℝ^n)).toSphere)) : ℝ^n →L[ℝ] ℝ) v =
        ((n : ℝ) / r ^ (n + 1)) * ∫ ω : Metric.sphere (0 : ℝ^n) 1,
          g (r • (ω : ℝ^n)) * inner ℝ v (ω : ℝ^n) ∂((volume : Measure (ℝ^n)).toSphere) := by
    have hInt := integrable_smul_invDistPowFDeriv (n := n) (r := r) hr hg.continuousOn
      (x := (0 : ℝ^n)) (by simpa using hr) n
    rw [ContinuousLinearMap.integral_apply hInt v, ← integral_const_mul]
    exact integral_congr_ae (.of_forall fun ω ↦ by
      simp only [smul_apply, smul_eq_mul, hkernel]; ring)
  rw [(hasFDerivAt_poissonBallExtension (n := n) (r := r) hr hg.continuousOn hzero).fderiv]
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, sub_zero, one_div, abs_of_pos hr,
    add_apply, smul_apply, smul_eq_mul, innerSL_apply_apply, inner_zero_left,
    hintegral, mul_zero, add_zero]
  rw [unitSphereArea_eq]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : 0 < n).ne'
  have := (unitBallVolume_pos n).ne'
  field_simp
  rw [show n + 1 = n - 1 + 2 by have : 0 < n := Fact.out; omega]
  ring

/-- First derivative estimate for the Poisson extension at the center.

If the boundary datum is bounded in absolute value by `M` on the radius-`r`
sphere, then the operator norm of the derivative at the center is at most
`n M / r`. -/
theorem norm_fderiv_poissonBallExtension_zero_le
    {n : ℕ} [Fact (0 < n)] {r M : ℝ}
    (hr : 0 < r) {g : ℝ^n → ℝ} (hg : Continuous g)
    (hM0 : 0 ≤ M) (hM : ∀ y ∈ Metric.sphere (0 : ℝ^n) r, |g y| ≤ M) :
    ‖fderiv ℝ (poissonBallExtension (n := n) r g) 0‖ ≤
      (n : ℝ) * M / r := by
  classical
  have hc0 : 0 ≤ (n : ℝ) / (unitSphereArea n * r) := by
    have := unitSphereArea_pos (n := n)
    positivity
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  rw [fderiv_poissonBallExtension_zero_apply hr hg v, norm_mul, Real.norm_of_nonneg hc0]
  have hintegral : ‖∫ ω : Metric.sphere (0 : ℝ^n) 1, g (r • (ω : ℝ^n)) * inner ℝ v (ω : ℝ^n)
      ∂((volume : Measure (ℝ^n)).toSphere)‖ ≤ (M * ‖v‖) * unitSphereArea n := by
    refine (norm_integral_le_of_norm_le_const (C := M * ‖v‖) (.of_forall fun ω ↦ ?_)).trans_eq
      (by simp [unitSphereArea, MeasureTheory.measureReal_def])
    have hω : ‖(ω : ℝ^n)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul (hM _ (by simp [norm_smul, hω, abs_of_pos hr]))
      ((norm_inner_le_norm v _).trans_eq (by rw [hω, mul_one])) (norm_nonneg _) hM0
  calc _ ≤ (n : ℝ) / (unitSphereArea n * r) * ((M * ‖v‖) * unitSphereArea n) := by gcongr
    _ = (n : ℝ) * M / r * ‖v‖ := by
      have := (unitSphereArea_pos (n := n)).ne'
      field_simp

end GreenFunction

namespace LaplacianEquation

open MeasureTheory PDE.Analysis Set

/-- First-order interior derivative estimate for a harmonic function.

If `closedBall x r` lies in the harmonicity domain and `|u| ≤ M` on
its boundary sphere, then `‖Du(x)‖ ≤ n M / r`.  The Poisson integral takes a
function on the whole space, so the boundary data are extended; the estimate
depends only on their values on the sphere. -/
theorem IsHarmonicPDE.norm_fderiv_le
    {n : ℕ} [Fact (0 < n)] {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U) {x : ℝ^n} {r M : ℝ}
    (hr : 0 < r) (hball : Metric.closedBall x r ⊆ U)
    (hM0 : 0 ≤ M) (hM : ∀ y ∈ Metric.sphere x r, |u y| ≤ M) :
    ‖fderiv ℝ u x‖ ≤ (n : ℝ) * M / r := by
  obtain ⟨g, hg_boundary, hrepresentation⟩ := hu.exists_poisson_representation hr hball
  have hlocal : (fun z ↦ u (x + z)) =ᶠ[nhds (0 : ℝ^n)] GreenFunction.poissonBallExtension r g :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds 0 hr) fun z hz ↦ hrepresentation hz
  rw [← show fderiv ℝ (fun z ↦ u (x + z)) 0 = fderiv ℝ u x by
    simpa using fderiv_comp_add_left (𝕜 := ℝ) (f := u) (x := (0 : ℝ^n)) x, hlocal.fderiv_eq]
  refine GreenFunction.norm_fderiv_poissonBallExtension_zero_le hr g.continuous hM0 fun y hy ↦ ?_
  rw [hg_boundary hy]
  exact hM (x + y) (by simpa using hy)

/-- Operator-norm form of Evans's first-order interior derivative estimate.

If `u` is harmonic on a set containing `Metric.closedBall x r`, then
`‖Du(x)‖` is bounded by

`2^(n+1) n / (α(n) r^(n+1))` times the `L¹` norm of `u` on `Metric.ball x r`,

where `α(n) = unitBallVolume n`.  This implies the coordinate estimates in
Theorem 7 for `k = 1` in Evans, §2.2.3.  The closed-ball hypothesis matches the
library's mean-value theorems. -/
theorem IsHarmonicPDE.norm_fderiv_le_integral_abs
    {n : ℕ} [Fact (0 < n)] {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U) {x : ℝ^n} {r : ℝ}
    (hr : 0 < r) (hball : Metric.closedBall x r ⊆ U) :
    ‖fderiv ℝ u x‖ ≤
      ((2 : ℝ) ^ (n + 1) * (n : ℝ) /
          (unitBallVolume n * r ^ (n + 1))) *
        ∫ y in Metric.ball x r, |u y| := by
  classical
  set I : ℝ := ∫ y in Metric.ball x r, |u y|
  have hρ : 0 < r / 2 := by positivity
  have hα := unitBallVolume_pos n
  have hu_int : IntegrableOn u (Metric.ball x r) (volume : Measure (ℝ^n)) :=
    ((hu.contDiffOn.mono hball).continuousOn.integrableOn_compact
      (isCompact_closedBall x r)).mono_set Metric.ball_subset_closedBall
  have hI0 : 0 ≤ I := integral_nonneg fun y ↦ abs_nonneg (u y)
  refine (hu.norm_fderiv_le hρ ((Metric.closedBall_subset_closedBall (by linarith)).trans hball)
    (by positivity : 0 ≤ I / (unitBallVolume n * (r / 2) ^ n)) fun y hy ↦ ?_).trans_eq ?_
  · have := Metric.mem_sphere.1 hy
    exact hu.hasSphereMeanValueProperty.abs_le_integral_abs_of_subset hρ
      ((Metric.closedBall_subset_closedBall' (by linarith)).trans hball)
      (Metric.ball_subset_ball' (by linarith)) hu_int
  · rw [div_pow, pow_succ, pow_succ]
    field_simp

/-- Liouville's theorem for bounded entire harmonic functions.

An entire PDE-harmonic function with a global absolute bound is equal
everywhere to its value at the origin. -/
theorem IsHarmonicPDE.eq_const_of_bounded
    {n : ℕ} [Fact (0 < n)] {u : ℝ^n → ℝ}
    (hu : IsHarmonicPDE n u Set.univ)
    {M : ℝ} (hM : ∀ x, |u x| ≤ M) :
    ∀ x, u x = u 0 := by
  have hM0 : 0 ≤ M := (abs_nonneg (u 0)).trans (hM 0)
  have hfderiv_zero (x : ℝ^n) : fderiv ℝ u x = 0 := by
    refine norm_le_zero_iff.1 (le_of_not_gt fun hA ↦ ?_)
    have hr : 0 < (n : ℝ) * M / ‖fderiv ℝ u x‖ + 1 := by positivity
    refine (hu.norm_fderiv_le (x := x) hr (fun _ _ ↦ Set.mem_univ _) hM0 fun y _ ↦ hM y).not_gt ?_
    rw [div_lt_iff₀ hr]
    field_simp
    nlinarith
  exact fun x ↦ is_const_of_fderiv_eq_zero (fun x ↦ (hu.contDiffAt_of_isOpen isOpen_univ
    (Set.mem_univ x)).differentiableAt (by norm_num)) hfderiv_zero x 0

end LaplacianEquation
