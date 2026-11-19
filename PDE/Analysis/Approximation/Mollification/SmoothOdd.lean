/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Mollification.Weighted
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import CAS.ExactTactic

/-!
# Smooth initialization by endpoint flattening and relative mollification

An odd Lipschitz profile with zero endpoint value, interior `C¹` regularity, and a
smooth odd origin germ has compact smooth odd approximations in the singular
weighted `H¹` energy. The origin germ is retained exactly. No endpoint slope is
assumed to vanish, and no approximation or weighted error hypothesis is assumed.

The input weights must be measurable, nonnegative, continuous on the open interval,
and satisfy the endpoint upper comparisons used in the flattening estimate.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal ContDiff

namespace PDE.Analysis.Calculus

/-- The squared triangle estimate uses the derivative of the sum. Only the first
summand's density needs to be measurable. -/
theorem singularWeightedH1Error_add_le {q₁ q₂ w v : ℝ → ℝ} {L : ℝ}
    (hq₁ : Measurable q₁) (hw : Measurable w) (hv : Measurable v)
    (hw0 : ∀ x ∈ Ioo 0 L, 0 ≤ w x) (hv0 : ∀ x ∈ Ioo 0 L, 0 ≤ v x)
    (hd₁ : ∀ x ∈ Ioo 0 L, DifferentiableAt ℝ q₁ x)
    (hd₂ : ∀ x ∈ Ioo 0 L, DifferentiableAt ℝ q₂ x) :
    singularWeightedH1Error w v (fun x ↦ q₁ x + q₂ x) L ≤
      2 * singularWeightedH1Error w v q₁ L + 2 * singularWeightedH1Error w v q₂ L := by
  let D₁ := fun x ↦ ENNReal.ofReal (q₁ x ^ 2 * w x + deriv q₁ x ^ 2 * v x)
  let D₂ := fun x ↦ ENNReal.ofReal (q₂ x ^ 2 * w x + deriv q₂ x ^ 2 * v x)
  have hm : Measurable D₁ :=
    (((hq₁.pow_const 2).mul hw).add (((measurable_deriv q₁).pow_const 2).mul hv)).ennreal_ofReal
  have hbound : singularWeightedH1Error w v (fun x ↦ q₁ x + q₂ x) L ≤
      ∫⁻ x in Ioo 0 L, 2 * D₁ x + 2 * D₂ x := by
    apply setLIntegral_mono' measurableSet_Ioo
    intro x hx
    have hd : deriv (fun x ↦ q₁ x + q₂ x) x = deriv q₁ x + deriv q₂ x :=
      deriv_add (hd₁ x hx) (hd₂ x hx)
    rw [hd]
    have hsq := mul_le_mul_of_nonneg_right (add_sq_le (a := q₁ x) (b := q₂ x)) (hw0 x hx)
    have hdsq := mul_le_mul_of_nonneg_right
      (add_sq_le (a := deriv q₁ x) (b := deriv q₂ x)) (hv0 x hx)
    have hdensity :
        (q₁ x + q₂ x) ^ 2 * w x + (deriv q₁ x + deriv q₂ x) ^ 2 * v x ≤
          2 * (q₁ x ^ 2 * w x + deriv q₁ x ^ 2 * v x) +
          2 * (q₂ x ^ 2 * w x + deriv q₂ x ^ 2 * v x) := by cas
    refine (ENNReal.ofReal_le_ofReal hdensity).trans ?_
    calc
      _ ≤ ENNReal.ofReal (2 * (q₁ x ^ 2 * w x + deriv q₁ x ^ 2 * v x)) +
          ENNReal.ofReal (2 * (q₂ x ^ 2 * w x + deriv q₂ x ^ 2 * v x)) :=
        ENNReal.ofReal_add_le
      _ = 2 * D₁ x + 2 * D₂ x := by
        simp only [D₁, D₂, ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num),
          ENNReal.ofReal_ofNat]
  refine hbound.trans_eq ?_
  rw [lintegral_add_left (hm.const_mul 2), lintegral_const_mul' _ _ (by norm_num),
    lintegral_const_mul' _ _ (by norm_num)]
  rfl

/-- A continuous real weight has a nonnegative finite upper bound on every closed interval
strictly inside the singular endpoints. -/
theorem exists_weight_upper_bound_on_Icc {w : ℝ → ℝ} {a b L : ℝ}
    (hw : ContinuousOn w (Ioo 0 L)) (ha : 0 < a) (hb : b < L) :
    ∃ A ≥ 0, ∀ x ∈ Icc a b, w x ≤ A := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hw.mono (fun _ hx ↦ ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩))
  refine ⟨max C 0, le_max_right _ _, fun x hx ↦ ?_⟩
  have hnorm : |w x| ≤ C := by simpa only [Real.norm_eq_abs] using hC x hx
  exact (le_abs_self (w x)).trans (hnorm.trans (le_max_left _ _))

/-- Endpoint flattening followed by interior convolution constructs the smooth
initializer. The final squared error is arbitrarily small, and all origin identities,
including the first derivative, are preserved exactly. -/
theorem exists_smooth_odd_initialization {f p w v : ℝ → ℝ} {K : ℝ≥0}
    {L c A B ε : ℝ}
    (hf : LipschitzWith K f) (hfL : f L = 0) (hfodd : ∀ x, f (-x) = -f x)
    (hregular : ContDiffOn ℝ 1 f (Ioo (-L) L))
    (hp : ContDiff ℝ ∞ p) (hpodd : ∀ x, p (-x) = -p x)
    (hfp : f =ᶠ[𝓝 0] p)
    (hc : 0 < c) (hcL : c < L) (hε : 0 < ε) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hw : Measurable w) (hv : Measurable v)
    (hw0 : ∀ x ∈ Ioo 0 L, 0 ≤ w x) (hv0 : ∀ x ∈ Ioo 0 L, 0 ≤ v x)
    (hwc : ContinuousOn w (Ioo 0 L)) (hvc : ContinuousOn v (Ioo 0 L))
    (hwL : ∀ x ∈ Ioo (L - c) L, w x ≤ A / (L - x) ^ 2)
    (hvL : ∀ x ∈ Ioo (L - c) L, v x ≤ B) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      (∀ x, g (-x) = -g x) ∧ tsupport g ⊆ Ioo (-L) L ∧
      g =ᶠ[𝓝 0] p ∧ deriv g 0 = deriv f 0 ∧
      deriv (fun x ↦ g x - f x) 0 = 0 ∧
      singularWeightedH1Error w v (fun x ↦ g x - f x) L < ENNReal.ofReal ε := by
  have hL : 0 < L := hc.trans hcL
  have hfd : ∀ x ∈ Ioo 0 L, DifferentiableAt ℝ f x := by
    intro x hx
    exact (hregular.contDiffAt (Ioo_mem_nhds (by cas) hx.2)).differentiableAt one_ne_zero
  have heighth : 0 < ε / 8 := by positivity
  obtain ⟨δ, hδ, hδc, hF, hFc, hFodd, _, hFslope, hE⟩ :=
    exists_flattenedProfile_error_lt hf hfL hfodd hregular hfd hc hcL heighth hA hB hwL hvL
  let F := flattenedProfile f L δ
  have hFfp : F =ᶠ[𝓝 0] p :=
    (flattenedProfile_eventuallyEq_self hδ (hδc.trans hcL)).trans hfp
  obtain ⟨t, ht, htball⟩ := Metric.mem_nhds_iff.mp hFfp
  let r := min t ((L - δ) / 2)
  have hδL : 2 * δ < L := hδc.trans hcL
  have hr : 0 < r := lt_min ht (by cas)
  have hrR : r < L - δ := (min_le_right _ _).trans_lt (by cas)
  have hrgerm : ∀ x, |x| < r → F x = p x := by
    intro x hx
    apply htball
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using
      hx.trans_le (min_le_left _ _)
  have hFzero : ∀ x, L - δ ≤ |x| → F x = 0 :=
    fun _ hx ↦ flattenedProfile_eq_zero hδ hx
  have hs : 0 < δ / 2 := half_pos hδ
  have hsL : (L - δ) + δ / 2 < L := by cas
  obtain ⟨A', hA', hw'⟩ :=
    exists_weight_upper_bound_on_Icc hwc (show 0 < r / 4 by positivity) hsL
  obtain ⟨B', hB', hv'⟩ :=
    exists_weight_upper_bound_on_Icc hvc (show 0 < r / 4 by positivity) hsL
  obtain ⟨g, hg, hgc, hgodd, hgsupport, hgF, hgslope, _, hgE⟩ :=
    exists_smooth_odd_relative_weighted_approximation hF hFc hp hFodd hpodd
      hr hrR hs hsL heighth hA' hB' hrgerm hFzero hw' hv'
  have hgf : g =ᶠ[𝓝 0] f :=
    hgF.trans (flattenedProfile_eventuallyEq_self hδ hδL)
  have hqzero : (fun x ↦ g x - f x) =ᶠ[𝓝 0] (fun _ ↦ 0) := by
    filter_upwards [hgf] with x hx
    exact sub_eq_zero.mpr hx
  refine ⟨g, hg, hgc, hgodd, ?_, hgF.trans hFfp,
    hgslope.trans hFslope, ?_, ?_⟩
  · intro x hx
    have hxs := hgsupport hx
    constructor <;> cas
  · rw [hqzero.deriv_eq, deriv_const]
  · have hsum := singularWeightedH1Error_add_le
      (q₁ := fun x ↦ g x - F x) (q₂ := fun x ↦ F x - f x)
      (hg.continuous.sub hF.continuous).measurable hw hv hw0 hv0
      (fun x _ ↦ ((hg.differentiable (by simp)) x).sub (hF.differentiable one_ne_zero x))
      (fun x hx ↦ (hF.differentiable one_ne_zero x).sub (hfd x hx))
    have heq : (fun x ↦ (g x - F x) + (F x - f x)) = (fun x ↦ g x - f x) := by
      funext x
      cas
    rw [heq] at hsum
    have hsmall := ENNReal.add_lt_add
      (ENNReal.mul_lt_mul_right (a := 2) (by norm_num) (by norm_num) hgE)
      (ENNReal.mul_lt_mul_right (a := 2) (by norm_num) (by norm_num) hE)
    refine hsum.trans_lt (hsmall.trans_le ?_)
    calc
      2 * ENNReal.ofReal (ε / 8) + 2 * ENNReal.ofReal (ε / 8) =
          ENNReal.ofReal (ε / 2) := by
        rw [← ENNReal.ofReal_ofNat (n := 2), ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        cas
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (by cas)

end PDE.Analysis.Calculus
