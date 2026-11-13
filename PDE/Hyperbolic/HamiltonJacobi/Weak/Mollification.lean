/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import PDE.Analysis.Calculus.Semiconcavity
public import PDE.Analysis.Convolution.SecondDifference

/-!
# Spatial curvature after spacetime mollification

The proof of Theorem 7 in Evans, §3.3.3(b), uses the spatial Hessian bound (43) for
spacetime mollifications of weak solutions and leaves its verification as an exercise. We
derive it from the second-difference condition (c) of the definition of weak solution, and the
gradient bound (41) from the Lipschitz constant. The kernel is Mathlib's normalized smooth bump,
and the regularized function is its convolution with the input.

The input is a continuous function on all spacetime whose second differences are
controlled at positive times. Values at nonpositive times do not enter the estimates.
There is no boundedness or differentiability assumption on the input.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.3(b), proof of Theorem 7, step 3, equations (41)
  and (43).
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

noncomputable section

namespace HamiltonJacobi.Weak

open MeasureTheory Function Metric
open scoped Convolution

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure (E × ℝ)} [μ.IsAddHaarMeasure]

/-- The singular semiconcavity constant at a time sampled by a small spacetime
kernel is bounded by twice its value at the center time. -/
theorem semiconcavity_factor_le {C t ε s : ℝ} (hC : 0 ≤ C)
    (hε : 0 < ε) (ht : 2 * ε < t) (hs : |s| < ε) :
    C * (1 + (t - s)⁻¹) ≤ 2 * C * (1 + t⁻¹) := by
  have htpos : 0 < t := by linarith
  have hslt : s < ε := (le_abs_self s).trans_lt hs
  have hshift : 0 < t - s := by linarith
  have hinv : (t - s)⁻¹ ≤ 2 * t⁻¹ := by
    rw [inv_eq_one_div, ← div_eq_mul_inv, div_le_div_iff₀ hshift htpos]
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hinv hC]

open Filter Topology in
/-- Spacetime convolution preserves Evans's spatial second-difference bound
with constant `2 C` at times beyond twice the kernel radius. For `z ≠ 0` the bound forces
`0 ≤ C`: the second difference of `u` is continuous at time `0`, while `C (1 + t⁻¹) ‖z‖²` would
tend to `-∞`. -/
theorem second_difference_convolution_spatial_le (φ : ContDiffBump (0 : E × ℝ)) {u : E × ℝ → ℝ}
    (hu : Continuous u) {C : ℝ}
    (hsemi : ∀ x z t, 0 < t → u (x + z, t) - 2 * u (x, t) + u (x - z, t) ≤ C * (1 + t⁻¹) * ‖z‖ ^ 2)
    {t : ℝ} (ht : 2 * φ.rOut < t) (x z : E) :
    (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u) (x + z, t) -
        2 * (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u) (x, t) +
        (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u) (x - z, t) ≤
      2 * C * (1 + t⁻¹) * ‖z‖ ^ 2 := by
  rcases eq_or_ne z 0 with rfl | hz
  · have h0 : ‖(0 : E)‖ ^ 2 = 0 := by simp
    rw [add_zero, sub_zero, h0, mul_zero]
    linarith
  have hC : 0 ≤ C := by
    by_contra hC
    have hlim : Tendsto (fun s : ℝ ↦ C * (1 + s⁻¹) * ‖z‖ ^ 2) (𝓝[>] 0) atBot :=
      ((tendsto_atTop_add_const_left _ 1 tendsto_inv_nhdsGT_zero).const_mul_atTop_of_neg
        (mul_neg_of_neg_of_pos (not_le.mp hC) (pow_pos (norm_pos_iff.mpr hz) 2))).congr
        fun s ↦ by ring
    have hgc : Continuous (fun s : ℝ ↦ u (x + z, s) - 2 * u (x, s) + u (x - z, s)) := by
      fun_prop
    obtain ⟨s, hs1, hs2, hs3⟩ :=
      (((hgc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds).eventually
        (eventually_gt_nhds (sub_one_lt _)) |>.and
        ((hlim.eventually (eventually_lt_atBot
          (u (x + z, 0) - 2 * u (x, 0) + u (x - z, 0) - 1))).and self_mem_nhdsWithin)).exists
    linarith [hsemi x z s hs3]
  have hbound (y : E × ℝ) (hy : y ∈ support (φ.normed μ)) :
      |y.2| < φ.rOut := by
    rw [φ.support_normed_eq, mem_ball, dist_zero_right] at hy
    exact (show |y.2| ≤ ‖y‖ from norm_snd_le y).trans_lt hy
  have h := PDE.Analysis.second_difference_convolution_le (μ := μ)
    φ.hasCompactSupport_normed φ.nonneg_normed φ.integral_normed hu
    (x, t) (z, 0) (C := 2 * C * (1 + t⁻¹)) ?_
  · simpa using h
  intro y hy
  have hytime := hbound y hy
  have hpos : 0 < t - y.2 := by
    have := le_abs_self y.2
    have := φ.rOut_pos
    linarith
  have hsemi' := hsemi (x - y.1) z (t - y.2) hpos
  have hfactor := semiconcavity_factor_le hC φ.rOut_pos ht hytime
  change u (x - y.1 + z, t - y.2 + 0) - 2 * u (x - y.1, t - y.2) +
    u (x - y.1 - z, t - y.2 - 0) ≤ 2 * C * (1 + t⁻¹) * ‖(z, (0 : ℝ))‖ ^ 2
  simpa using hsemi'.trans (mul_le_mul_of_nonneg_right hfactor (sq_nonneg ‖z‖))

/-- The mollified spatial Hessian satisfies Evans's estimate (43).
Smoothness and the Hessian bound are consequences of convolution and semiconcavity. -/
theorem hessian_convolution_spatial_le (φ : ContDiffBump (0 : E × ℝ)) {u : E × ℝ → ℝ}
    (hu : Continuous u) {C : ℝ}
    (hsemi : ∀ x z t, 0 < t → u (x + z, t) - 2 * u (x, t) + u (x - z, t) ≤ C * (1 + t⁻¹) * ‖z‖ ^ 2)
    {t : ℝ} (ht : 2 * φ.rOut < t) (x v : E) :
    fderiv ℝ (fderiv ℝ (fun y : E ↦ (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u) (y, t))) x v
      v ≤ 2 * C * (1 + t⁻¹) * ‖v‖ ^ 2 := by
  have hsmooth : ContDiff ℝ 2 (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u) :=
    φ.hasCompactSupport_normed.contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) φ.contDiff_normed hu.locallyIntegrable
  apply PDE.Analysis.hessian_le_of_second_difference
    (hsmooth.comp (contDiff_id.prodMk contDiff_const))
  exact second_difference_convolution_spatial_le φ hu hsemi ht x

/-- The spatial Lipschitz constant of a spacetime mollification is bounded by
the original forward-spacetime Lipschitz constant. -/
theorem lipschitzWith_convolution_spatial (φ : ContDiffBump (0 : E × ℝ)) {u : E × ℝ → ℝ}
    (hu : Continuous u) {K : NNReal} (hLip : LipschitzOnWith K u {w | 0 ≤ w.2}) {t : ℝ}
    (ht : φ.rOut < t) :
    LipschitzWith K (fun x : E ↦ (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u) (x, t)) := by
  refine LipschitzWith.of_dist_le_mul fun x z ↦ ?_
  apply PDE.Analysis.dist_convolution_le_of_dist_le
    φ.hasCompactSupport_normed φ.nonneg_normed φ.integral_normed hu (x, t) (z, t)
  intro y hy
  rw [φ.support_normed_eq, mem_ball, dist_zero_right] at hy
  have hytime : |y.2| < φ.rOut := (show |y.2| ≤ ‖y‖ from norm_snd_le y).trans_lt hy
  have hpos : 0 ≤ t - y.2 := by
    have := le_abs_self y.2
    linarith
  simpa using hLip.dist_le_mul ((x, t) - y) (show (x, t) - y ∈ {w : E × ℝ | 0 ≤ w.2} from hpos)
    ((z, t) - y) (show (z, t) - y ∈ {w : E × ℝ | 0 ≤ w.2} from hpos)

end Normed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure (E × ℝ)} [μ.IsAddHaarMeasure]

/-- Evans's mollified gradient bound (41), derived from the original Lipschitz
constant using the isometric Riesz representation of the spatial derivative. -/
theorem norm_gradient_convolution_spatial_le (φ : ContDiffBump (0 : E × ℝ)) {u : E × ℝ → ℝ}
    (hu : Continuous u) {K : NNReal} (hLip : LipschitzOnWith K u {w | 0 ≤ w.2}) {t : ℝ}
    (ht : φ.rOut < t) (x : E) :
    ‖∇ (fun y : E ↦ (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u) (y, t)) x‖ ≤ K := by
  simpa only [gradient, LinearIsometryEquiv.norm_map] using (norm_fderiv_le_of_lipschitz ℝ (x₀ := x)
      (lipschitzWith_convolution_spatial φ hu hLip ht (μ := μ)))

end HamiltonJacobi.Weak
