/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.PrincipalValue
public import Mathlib.Topology.EMetricSpace.Lipschitz
import PDE.Analysis.Fourier.HilbertTransform.PrincipalValue.Continuity
import CAS.ExactTactic

/-!
# The Hilbert principal value of an integrable locally Lipschitz function

For every integrable locally Lipschitz `f : ℝ → ℝ` the Hilbert principal value
`(1 / π) p.v. ∫ f (y) / (x - y) dy` exists at every point `x` and is a continuous function of
`x`. No compact support is assumed, so the theorems apply to rational functions that decay at
infinity. The compactly supported Lipschitz and `C¹` cases are
`hasHilbertPV_of_lipschitzWith_compactSupport`,
`continuous_hilbertPV_of_lipschitzWith_compactSupport` and
`continuous_hilbertPV_of_contDiff_one_compactSupport` in
`PDE.Analysis.Fourier.HilbertTransform.PrincipalValue.Continuity`.

## Main results

* `PDE.Analysis.continuous_hilbertTruncation`: for every integrable `f` and every `ε > 0`, the
  truncation `(1 / π) ∫_{|t| > ε} f (x - t) / t dt` is continuous in the evaluation point `x`.
* `PDE.Analysis.continuous_hilbertPV`: the principal value of every integrable locally Lipschitz
  function is continuous.
* `PDE.Analysis.hasHilbertPV_of_locallyLipschitz`: every integrable locally Lipschitz function
  has a principal value at every point.

## How it works

Near a point `x₀`, where `f` is Lipschitz on a ball of radius `r`, the principal value at `x` is
the truncation `(1 / π) ∫_{|t| > r / 4} f (x - t) / t dt` plus the integral of
`(f (x - t) - f x) / t` over `|t| ≤ r / 4` (`hilbertTruncation_eq_regularized`). The second
integrand is bounded by the Lipschitz constant. The truncation is the integral of
`f (y) k (x - y)` in `y`, where `k (t) = 1 / t` for `|t| > r / 4` and `k (t) = 0` otherwise, so it
is bounded by `|f (y)| / (r / 4)` and continuous in `x` for every `y` except `x ± r / 4`.
Dominated convergence gives the continuity of both parts.

The statements are standard facts on the Hilbert transform, and the proofs follow no particular
source.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace PDE.Analysis

/-- For an integrable `f` and `ε > 0` the truncation `(1 / π) ∫_{|t| > ε} f (x - t) / t dt` of the
Hilbert principal value is a continuous function of `x`. -/
theorem continuous_hilbertTruncation {f : ℝ → ℝ} (hf : Integrable f) {ε : ℝ} (hε : 0 < ε) :
    Continuous fun x ↦ hilbertTruncation f x ε := by
  obtain ⟨k, hkm, hkc, hkb, hk⟩ : ∃ k : ℝ → ℝ, Measurable k ∧
      (∀ t, |t| ≠ ε → ContinuousAt k t) ∧ (∀ t, ‖k t‖ ≤ ε⁻¹) ∧
      ∀ x, hilbertTruncation f x ε = Real.pi⁻¹ * ∫ y, f y * k (x - y) := by
    refine ⟨{t : ℝ | ε < |t|}.indicator fun t ↦ t⁻¹,
      measurable_inv.indicator (measurableSet_hilbertCutoff ε), fun t ht ↦ ?_, fun t ↦ ?_,
      fun x ↦ ?_⟩
    · refine (continuousOn_inv₀.mono fun s hs ↦ ?_).continuousAt_indicator fun h ↦
        ht (frontier_lt_subset_eq continuous_const continuous_abs h).symm
      have hs' : s ∈ {t : ℝ | ε < |t|} := interior_subset hs
      exact abs_pos.mp (hε.trans hs')
    · by_cases ht : ε < |t|
      · rw [indicator_of_mem (s := {t : ℝ | ε < |t|}) ht, norm_inv, Real.norm_eq_abs]
        exact inv_anti₀ hε ht.le
      · rw [indicator_of_notMem (s := {t : ℝ | ε < |t|}) ht, norm_zero]
        exact inv_nonneg.mpr hε.le
    · have hs : MeasurableSet {y : ℝ | ε < |x - y|} :=
        measurableSet_lt measurable_const (by fun_prop)
      rw [hilbertTruncation_eq_integral, ← integral_indicator hs]
      congr 2 with y
      by_cases hy : ε < |x - y|
      · rw [indicator_of_mem (s := {y : ℝ | ε < |x - y|}) hy,
          indicator_of_mem (s := {t : ℝ | ε < |t|}) hy, div_eq_mul_inv]
      · rw [indicator_of_notMem (s := {y : ℝ | ε < |x - y|}) hy,
          indicator_of_notMem (s := {t : ℝ | ε < |t|}) hy, mul_zero]
  simp_rw [hk]
  refine continuous_const.mul (continuous_iff_continuousAt.mpr fun x₀ ↦ ?_)
  refine continuousAt_of_dominated (bound := fun y ↦ ε⁻¹ * ‖f y‖) (.of_forall fun x ↦ ?_)
    (.of_forall fun x ↦ .of_forall fun y ↦ ?_) (hf.norm.const_mul _) ?_
  · exact hf.aestronglyMeasurable.mul
      (hkm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  · rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hkb _) (norm_nonneg _)
  · filter_upwards [(volume : Measure ℝ).ae_ne (x₀ - ε), (volume : Measure ℝ).ae_ne (x₀ + ε)]
      with y h₁ h₂
    refine continuousAt_const.mul
      (ContinuousAt.comp (f := fun x ↦ x - y) (hkc _ fun h ↦ ?_) (by cas))
    rcases (abs_eq hε.le).mp h with h | h
    · exact h₁ (by cas using [h])
    · exact h₂ (by cas using [h])

/-- **Continuity of the principal value.** The Hilbert principal value of an integrable locally
Lipschitz function is continuous. No compact support is assumed. -/
theorem continuous_hilbertPV {f : ℝ → ℝ} (hf : Integrable f) (hlip : LocallyLipschitz f) :
    Continuous (hilbertPV f) := by
  refine continuous_iff_continuousAt.mpr fun x₀ ↦ ?_
  obtain ⟨K, U, hU, hK⟩ := hlip x₀
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hr2 : 0 < r / 2 := half_pos hr
  have hr4 : 0 < r / 4 := by cas using [hr]
  have hloc {x t : ℝ} (hx : x ∈ Metric.ball x₀ (r / 2)) (ht : |t| < r / 2) :
      |f (x - t) - f x| ≤ K * |t| := by
    rw [Metric.mem_ball, Real.dist_eq] at hx
    have hxt : x - t ∈ U := hball <| by
      rw [Metric.mem_ball, Real.dist_eq]
      cas using [hx, ht]
    have hxU : x ∈ U := hball <| by
      rw [Metric.mem_ball, Real.dist_eq]
      cas using [hx, hr]
    simpa only [Real.norm_eq_abs, sub_sub_cancel_left, abs_neg] using hK.norm_sub_le hxt hxU
  have hint {x : ℝ} (hx : x ∈ Metric.ball x₀ (r / 2)) :
      Integrable (hilbertRegularizedKernel f x (r / 2)) :=
    integrable_hilbertRegularizedKernel hf hr2 K.coe_nonneg fun _ ht ↦ hloc hx ht
  have heq : ∀ᶠ x in 𝓝 x₀, hilbertTruncation f x (r / 4) + Real.pi⁻¹ *
      ∫ t in {t : ℝ | r / 4 < |t|}ᶜ, hilbertRegularizedKernel f x (r / 2) t = hilbertPV f x := by
    filter_upwards [Metric.ball_mem_nhds x₀ hr2] with x hx
    rw [(hasHilbertPV_of_regularized (hint hx)).hilbertPV_eq,
      hilbertTruncation_eq_regularized (hint hx) hr4, ← mul_add,
      integral_add_compl (measurableSet_hilbertCutoff _) (hint hx)]
  refine ContinuousAt.congr ((continuous_hilbertTruncation hf hr4).continuousAt.add
    (continuousAt_const.mul ?_)) heq
  refine continuousAt_of_dominated (bound := {t : ℝ | |t| < r / 2}.indicator fun _ ↦ (K : ℝ))
    ?_ ?_ (integrable_hilbertLocalConstant (r / 2) K).integrableOn (.of_forall fun t ↦
      (continuous_hilbertRegularizedKernel_eval hlip.continuous _ t).continuousAt)
  · filter_upwards [Metric.ball_mem_nhds x₀ hr2] with x hx
      using (hint hx).aestronglyMeasurable.restrict
  · filter_upwards [Metric.ball_mem_nhds x₀ hr2] with x hx
    filter_upwards [ae_restrict_mem (measurableSet_hilbertCutoff (r / 4)).compl] with t ht
    have ht' : |t| < r / 2 := by cas using [hr, not_lt.mp (show ¬r / 4 < |t| from ht)]
    rw [hilbertRegularizedKernel, indicator_of_mem (s := {t : ℝ | |t| < r / 2}) ht',
      indicator_of_mem (s := {t : ℝ | |t| < r / 2}) ht', norm_div, Real.norm_eq_abs,
      Real.norm_eq_abs]
    exact div_le_of_le_mul₀ (abs_nonneg t) K.coe_nonneg (hloc hx ht')

/-- An integrable locally Lipschitz function has a Hilbert principal value at every point. -/
theorem hasHilbertPV_of_locallyLipschitz {f : ℝ → ℝ} (hf : Integrable f)
    (hlip : LocallyLipschitz f) (x : ℝ) : HasHilbertPV f x (hilbertPV f x) := by
  obtain ⟨K, U, hU, hK⟩ := hlip x
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hpv := hasHilbertPV_of_lipschitzOnWith hf hr (hK.mono hball)
  rwa [hpv.hilbertPV_eq]

end PDE.Analysis
