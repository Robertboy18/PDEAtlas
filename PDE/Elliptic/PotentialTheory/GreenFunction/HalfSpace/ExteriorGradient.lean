/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.FirstDerivative
import PDE.Analysis.Normed.PiLp.CompareExp

/-!
# Exterior gradient bounds for compact planar Green sources

Outside a source ball of radius `R`, every gradient-kernel denominator is at
least `|x| - R`. The `L¹` mass of the canonical odd source extension therefore
bounds each Cartesian derivative by `mass/(2π(|x|-R))` and the gradient norm by
`mass/(π(|x|-R))`. These bounds are uniform in direction, so the gradient
grows sublinearly at infinity.

## Main results

* `norm_partialDeriv_halfSpaceGreenPotential_le_exterior`: each Cartesian derivative is at most
  `mass/(2π(|x|-R))` outside the source ball.
* `norm_gradient_halfSpaceGreenPotential_le_exterior`: the gradient norm is at most
  `mass/(π(|x|-R))` outside the source ball.
* `eventually_norm_gradient_halfSpaceGreenPotential_div_radius_lt_of_hasCompactSupport`: for a
  compactly supported source the gradient is uniformly sublinear outside a large ball.
* `tendsto_norm_gradient_halfSpaceGreenPotential_div_radius`: `|∇φ(x)| / |x| → 0` as
  `|x| → ∞`.
-/

@[expose] public section

noncomputable section

namespace GreenFunction

open MeasureTheory Filter Topology Set SobolevSpace
open scoped Convolution Gradient

/-- The odd extension of a source vanishing outside the closed disc of radius `R` vanishes outside
the same disc. -/
private theorem oddHalfSpaceExtension_eq_zero_of_radial_support
    {f : ℝ^2 → ℝ} {R : ℝ} (hR : ∀ y, R < ‖y‖ → f y = 0)
    {y : ℝ^2} (hy : R < ‖y‖) : oddHalfSpaceExtension f y = 0 := by
  have hfy := hR y hy
  have hfr := hR (HalfSpace.reflect 2 y) (by simpa only [HalfSpace.norm_reflect] using hy)
  simp [oddHalfSpaceExtension, Set.indicator, hfy, hfr]

/-- The canonical odd source's `L¹` mass controls each Cartesian derivative
outside the original source ball. Reflection preserves that ball. -/
theorem norm_partialDeriv_halfSpaceGreenPotential_le_exterior
    {f : ℝ^2 → ℝ} (hf : Continuous f) {R : ℝ} (hR : ∀ y, R < ‖y‖ → f y = 0)
    (i : Fin 2) {x : ℝ^2} (hx : R < ‖x‖) :
    ‖(∂[i] (halfSpaceGreenPotential f)) x‖ ≤
      (∫ y, ‖oddHalfSpaceExtension f y‖) / (2 * Real.pi * (‖x‖ - R)) := by
  have hc := hasCompactSupport_of_eq_zero_of_lt_norm hR
  have hFc := hasCompactSupport_oddHalfSpaceExtension hc
  have hFi : Integrable (oddHalfSpaceExtension f) volume :=
    (integrableOn_iff_integrable_of_support_subset
      (subset_tsupport (oddHalfSpaceExtension f))).mp
        ((locallyIntegrable_oddHalfSpaceExtension hf).integrableOn_isCompact hFc)
  have hd : 0 < ‖x‖ - R := sub_pos.mpr hx
  let C : ℝ := 1 / (2 * Real.pi)
  have hC : 0 ≤ C := by positivity
  have hbound : ∀ y, ‖PotentialTheory.Planar.gradientKernel i (x - y) *
      oddHalfSpaceExtension f y‖ ≤ C / (‖x‖ - R) * ‖oddHalfSpaceExtension f y‖ := by
    intro y
    by_cases hy : R < ‖y‖
    · rw [oddHalfSpaceExtension_eq_zero_of_radial_support hR hy]
      simp
    · have hyR : ‖y‖ ≤ R := le_of_not_gt hy
      have hdist : ‖x‖ - R ≤ ‖x - y‖ := by
        have ht : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
          simpa only [sub_add_cancel] using norm_add_le (x - y) y
        linarith
      have hk : ‖PotentialTheory.Planar.gradientKernel i (x - y)‖ ≤
          C / (‖x‖ - R) := by
        calc
          _ ≤ C / ‖x - y‖ := by
            simpa only [C, Real.rpow_neg_one, div_eq_mul_inv] using
              PotentialTheory.Planar.norm_gradientKernel_le i (x - y)
          _ ≤ _ := div_le_div_of_nonneg_left hC hd hdist
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hk (norm_nonneg _)
  have hcoord : (∂[i] (halfSpaceGreenPotential f)) x =
      (PotentialTheory.Planar.gradientKernel i ⋆[ContinuousLinearMap.mul ℝ ℝ]
        oddHalfSpaceExtension f) x := by
    unfold PDE.partialDeriv
    rw [(hasFDerivAt_halfSpaceGreenPotential hf hc x).fderiv]
    simp [halfSpaceGreenPotentialGradient, innerSL_apply_apply,
      EuclideanSpace.inner_single_right]
  rw [hcoord, convolution_mul_swap]
  have hi := norm_integral_le_of_norm_le (hFi.norm.const_mul (C / (‖x‖ - R)))
    (Eventually.of_forall hbound)
  refine hi.trans_eq ?_
  rw [integral_const_mul]
  dsimp [C]
  field_simp

/-- The full gradient has inverse-distance decay outside a compact source ball.
The bound applies in every direction, including along the boundary. -/
theorem norm_gradient_halfSpaceGreenPotential_le_exterior
    {f : ℝ^2 → ℝ} (hf : Continuous f) {R : ℝ} (hR : ∀ y, R < ‖y‖ → f y = 0)
    {x : ℝ^2} (hx : R < ‖x‖) :
    ‖∇ (halfSpaceGreenPotential f) x‖ ≤
      (∫ y, ‖oddHalfSpaceExtension f y‖) / (Real.pi * (‖x‖ - R)) := by
  have hzero := norm_partialDeriv_halfSpaceGreenPotential_le_exterior hf hR (0 : Fin 2) hx
  have hone := norm_partialDeriv_halfSpaceGreenPotential_le_exterior hf hR (1 : Fin 2) hx
  let v := ∇ (halfSpaceGreenPotential f) x
  calc
    ‖∇ (halfSpaceGreenPotential f) x‖ = ‖v‖ := rfl
    _ ≤ ‖v 0‖ + ‖v 1‖ := by simpa only [Fin.sum_univ_two] using PiLp.norm_le_sum_norm v
    _ ≤ (∫ y, ‖oddHalfSpaceExtension f y‖) / (2 * Real.pi * (‖x‖ - R)) +
        (∫ y, ‖oddHalfSpaceExtension f y‖) / (2 * Real.pi * (‖x‖ - R)) := by
      simpa only [v, PDE.gradient_apply_eq_partialDeriv] using add_le_add hzero hone
    _ = _ := by field_simp; ring

/-- The Green potential of a compact source has uniformly sublinear gradient outside a
finite ball.
The radius can be chosen independently of the observation direction. -/
theorem eventually_norm_gradient_halfSpaceGreenPotential_div_radius_lt
    {f : ℝ^2 → ℝ} (hf : Continuous f) {R : ℝ} (hR : ∀ y, R < ‖y‖ → f y = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in atTop, ∀ x : ℝ^2, r ≤ ‖x‖ →
      ‖∇ (halfSpaceGreenPotential f) x‖ / ‖x‖ < ε := by
  let M : ℝ := ∫ y, ‖oddHalfSpaceExtension f y‖
  have hM : 0 ≤ M := integral_nonneg (fun y ↦ norm_nonneg _)
  have harg : Tendsto (fun r : ℝ ↦ r - R) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using
      tendsto_atTop_add_const_right atTop (-R) tendsto_id
  have hdecay : Tendsto (fun r : ℝ ↦ M / (Real.pi * (r - R))) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, Function.comp_def, mul_assoc, mul_comm, mul_left_comm] using
      (tendsto_inv_atTop_zero.comp harg).const_mul (M / Real.pi)
  filter_upwards [hdecay.eventually (gt_mem_nhds hε), eventually_gt_atTop R,
    eventually_ge_atTop (1 : ℝ)] with r hsmall hr hone
  intro x hx
  have hxr : R < ‖x‖ := hr.trans_le hx
  calc
    _ ≤ ‖∇ (halfSpaceGreenPotential f) x‖ := div_le_self (norm_nonneg _) (hone.trans hx)
    _ ≤ M / (Real.pi * (‖x‖ - R)) := norm_gradient_halfSpaceGreenPotential_le_exterior hf hR hxr
    _ ≤ M / (Real.pi * (r - R)) := div_le_div_of_nonneg_left hM
      (mul_pos Real.pi_pos (sub_pos.mpr hr))
      (mul_le_mul_of_nonneg_left (sub_le_sub_right hx R) Real.pi_pos.le)
    _ < ε := hsmall

/-- Compact support alone gives a direction-independent sublinear gradient bound
outside a sufficiently large ball. -/
theorem eventually_norm_gradient_halfSpaceGreenPotential_div_radius_lt_of_hasCompactSupport
    {f : ℝ^2 → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in atTop, ∀ x : ℝ^2, r ≤ ‖x‖ →
      ‖∇ (halfSpaceGreenPotential f) x‖ / ‖x‖ < ε := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.exists_norm_le
  apply eventually_norm_gradient_halfSpaceGreenPotential_div_radius_lt hf (R := R) _ hε
  intro y hy
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  exact (not_lt_of_ge (hR y hmem)) hy

/-- The gradient of a compact source's Green potential divided by radius tends to zero at
spatial
infinity. The cocompact limit allows arbitrary observation directions. -/
theorem tendsto_norm_gradient_halfSpaceGreenPotential_div_radius
    {f : ℝ^2 → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Tendsto (fun x : ℝ^2 ↦ ‖∇ (halfSpaceGreenPotential f) x‖ / ‖x‖)
      (cocompact (ℝ^2)) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨r, hr⟩ := eventually_atTop.1
    (eventually_norm_gradient_halfSpaceGreenPotential_div_radius_lt_of_hasCompactSupport hf hc hε)
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop r] with x hx
  simpa only [dist_zero_right, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg x))] using hr r le_rfl x hx

end GreenFunction
