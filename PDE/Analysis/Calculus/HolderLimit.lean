/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Limits of functions with uniformly Hölder derivatives

On a convex set `S`, let `gₙ` have derivatives `Gₙ` within `S` that are `α`-Hölder with a common
constant `M`, `0 < α`. If `gₙ → g` and `Gₙ → G` pointwise on `S`, then `G` is the derivative of
`g` within `S` and is `α`-Hölder with the same constant. The Taylor remainder of each `gₙ` is at
most `M ‖y - x‖^α ‖y - x‖` by the mean value inequality on the segment from `x` to `y`, and this
bound passes to the limit. No uniform convergence is needed.

## Main results

* `norm_sub_sub_le_of_holder`: the Taylor remainder bound for a single function.
* `hasFDerivWithinAt_of_tendsto_of_holder`: the limit has the limit derivative.
* `norm_sub_le_of_tendsto_of_holder`: the limit derivative keeps the Hölder bound.
* `continuousOn_of_norm_sub_le_rpow`: Hölder maps are continuous.
-/

@[expose] public section

noncomputable section

open Set Filter Asymptotics
open scoped Topology

namespace PDE.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {S : Set E} {M α : ℝ}

/-- **Taylor remainder from a Hölder derivative.** If `g` has derivative `G y` within the convex
set `S` at every `y ∈ S` and `‖G y - G z‖ ≤ M ‖y - z‖^α` on `S` with `M ≥ 0`, `α > 0`, then
`‖g y - g x - G x (y - x)‖ ≤ M ‖y - x‖^α ‖y - x‖` for `x, y ∈ S`. -/
theorem norm_sub_sub_le_of_holder (hS : Convex ℝ S) (hM : 0 ≤ M) (hα : 0 < α) {g : E → F}
    {G : E → E →L[ℝ] F} (hg : ∀ y ∈ S, HasFDerivWithinAt g (G y) S y)
    (hG : ∀ y ∈ S, ∀ z ∈ S, ‖G y - G z‖ ≤ M * ‖y - z‖ ^ α) {x y : E} (hx : x ∈ S)
    (hy : y ∈ S) : ‖g y - g x - G x (y - x)‖ ≤ M * ‖y - x‖ ^ α * ‖y - x‖ := by
  have hseg : segment ℝ x y ⊆ S := hS.segment_subset hx hy
  refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z hz ↦ (hg z (hseg hz)).mono hseg) (fun z hz ↦ ?_) (convex_segment x y)
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  have hzx : ‖z - x‖ ≤ ‖y - x‖ := by
    have h := segment_subset_closedBall_left x y hz
    rw [Metric.mem_closedBall, dist_eq_norm, dist_eq_norm, norm_sub_rev x y] at h
    exact h
  calc ‖G z - G x‖ ≤ M * ‖z - x‖ ^ α := hG z (hseg hz) x hx
    _ ≤ M * ‖y - x‖ ^ α := by gcongr

/-- **Limits with uniformly Hölder derivatives.** On a convex set `S`, if `gₙ` has derivatives
`Gₙ y` within `S` that are `α`-Hölder on `S` with a common constant `M ≥ 0`, `α > 0`, and
`gₙ → g`, `Gₙ → G` pointwise on `S`, then `g` has derivative `G x` within `S` at every
`x ∈ S`. -/
theorem hasFDerivWithinAt_of_tendsto_of_holder (hS : Convex ℝ S) (hM : 0 ≤ M) (hα : 0 < α)
    {g : ℕ → E → F} {G : ℕ → E → E →L[ℝ] F} {g' : E → F} {G' : E → E →L[ℝ] F}
    (hg : ∀ n, ∀ y ∈ S, HasFDerivWithinAt (g n) (G n y) S y)
    (hG : ∀ n, ∀ y ∈ S, ∀ z ∈ S, ‖G n y - G n z‖ ≤ M * ‖y - z‖ ^ α)
    (hgt : ∀ y ∈ S, Tendsto (fun n ↦ g n y) atTop (𝓝 (g' y)))
    (hGt : ∀ y ∈ S, Tendsto (fun n ↦ G n y) atTop (𝓝 (G' y))) {x : E} (hx : x ∈ S) :
    HasFDerivWithinAt g' (G' x) S x := by
  have hbound : ∀ y ∈ S, ‖g' y - g' x - G' x (y - x)‖ ≤ M * ‖y - x‖ ^ α * ‖y - x‖ := by
    intro y hy
    have ht : Tendsto (fun n ↦ ‖g n y - g n x - G n x (y - x)‖) atTop
        (𝓝 ‖g' y - g' x - G' x (y - x)‖) := by
      refine (((hgt y hy).sub (hgt x hx)).sub ?_).norm
      exact ((ContinuousLinearMap.apply ℝ F (y - x)).continuous.tendsto _).comp (hGt x hx)
    exact le_of_tendsto' ht fun n ↦ norm_sub_sub_le_of_holder hS hM hα (hg n) (hG n) hx hy
  refine HasFDerivWithinAt.of_isLittleO (Asymptotics.isLittleO_iff.mpr fun c hc ↦ ?_)
  have hcont : Continuous fun y : E ↦ M * ‖y - x‖ ^ α :=
    continuous_const.mul ((continuous_id.sub continuous_const).norm.rpow_const
      fun _ ↦ Or.inr hα.le)
  have hlim : Tendsto (fun y : E ↦ M * ‖y - x‖ ^ α) (𝓝 x) (𝓝 0) := by
    have h := hcont.tendsto x
    simpa [Real.zero_rpow hα.ne'] using h
  have hev : ∀ᶠ y in 𝓝 x, M * ‖y - x‖ ^ α < c := hlim (Iio_mem_nhds hc)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hev] with y hy hyc
  calc ‖g' y - g' x - G' x (y - x)‖ ≤ M * ‖y - x‖ ^ α * ‖y - x‖ := hbound y hy
    _ ≤ c * ‖y - x‖ := mul_le_mul_of_nonneg_right hyc.le (norm_nonneg _)

omit [NormedSpace ℝ F] in
/-- The pointwise limit of uniformly `α`-Hölder maps is `α`-Hölder with the same constant. -/
theorem norm_sub_le_of_tendsto_of_holder {X : Type*} [PseudoMetricSpace X] {T : Set X}
    {G : ℕ → X → F} {G' : X → F} (hG : ∀ n, ∀ y ∈ T, ∀ z ∈ T, ‖G n y - G n z‖ ≤ M * dist y z ^ α)
    (hGt : ∀ y ∈ T, Tendsto (fun n ↦ G n y) atTop (𝓝 (G' y))) {y z : X} (hy : y ∈ T)
    (hz : z ∈ T) : ‖G' y - G' z‖ ≤ M * dist y z ^ α :=
  le_of_tendsto' ((hGt y hy).sub (hGt z hz)).norm fun n ↦ hG n y hy z hz

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- A map with `‖f y - f z‖ ≤ M ‖y - z‖^α` on `S`, `0 < α`, is continuous on `S`. -/
theorem continuousOn_of_norm_sub_le_rpow (hα : 0 < α) {f : E → F}
    (h : ∀ y ∈ S, ∀ z ∈ S, ‖f y - f z‖ ≤ M * ‖y - z‖ ^ α) : ContinuousOn f S := by
  intro y hy
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hcont : Continuous fun z : E ↦ M * ‖z - y‖ ^ α :=
    continuous_const.mul ((continuous_id.sub continuous_const).norm.rpow_const
      fun _ ↦ Or.inr hα.le)
  have hlim : Tendsto (fun z : E ↦ M * ‖z - y‖ ^ α) (𝓝[S] y) (𝓝 0) := by
    have h1 := hcont.tendsto y
    simp only [sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero] at h1
    exact tendsto_nhdsWithin_of_tendsto_nhds h1
  exact squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
    (eventually_nhdsWithin_of_forall fun z hz ↦ h z hz y hy) hlim

end PDE.Analysis
