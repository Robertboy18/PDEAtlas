/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov.BoundaryInequality
import Mathlib.MeasureTheory.Covering.OneDim

/-!
# Localization at a positive time

A decreasing cutoff ending just before `T` tests the left time trace. On nonnegative
time, its negative derivative is a nonnegative approximate identity. Lebesgue
differentiation supplies the limit at almost every time without imposing a
representative on exceptional slices. The cutoff plays the role of the decreasing linear ramp
of `β` on `[t, t + δ]` in step 4 of the proof of Evans, §11.4.3, Theorem 3, where `δ → 0` gives
(50) for almost every time.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.4.3, proof of Theorem 3, step 4, equation (50).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Common PDE.Analysis
open scoped Distributions Topology

namespace PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov

/-- A compact time cutoff which ends just before `T`. For `T > 0` and sufficiently
small positive `ε`, it is one near time zero. -/
def finalTimeCutoff (T ε t : ℝ) : ℝ :=
  Real.smoothTransition (t + 2) * initialTimeCutoff ε (T - t)

/-- The terminal time cutoff is continuously differentiable. -/
theorem contDiff_finalTimeCutoff (T ε : ℝ) : ContDiff ℝ 1 (finalTimeCutoff T ε) :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).mul
    (((contDiff_initialTimeCutoff ε).of_le (by norm_num)).comp (contDiff_const.sub contDiff_id))

/-- The terminal time cutoff is nonnegative. -/
theorem finalTimeCutoff_nonneg (T ε t : ℝ) : 0 ≤ finalTimeCutoff T ε t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

/-- The terminal time cutoff has compact support. -/
theorem hasCompactSupport_finalTimeCutoff (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (finalTimeCutoff T ε) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -2) (b := T))
  intro t ht
  constructor
  · by_contra h
    exact ht (by
      unfold finalTimeCutoff
      rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul])
  · by_contra h
    exact ht (by
      unfold finalTimeCutoff
      rw [initialTimeCutoff_zero hε (by linarith : T - t ≤ ε), mul_zero])

/-- At nonnegative times the lower cutoff is identically one. -/
theorem finalTimeCutoff_eq {t : ℝ} (ht : 0 ≤ t) (T ε : ℝ) :
    finalTimeCutoff T ε t = initialTimeCutoff ε (T - t) := by
  unfold finalTimeCutoff
  rw [Real.smoothTransition.one_of_one_le (by linarith), one_mul]

/-- The derivative of the terminal cutoff is the negative reflected initial kernel. -/
theorem deriv_finalTimeCutoff {t : ℝ} (ht : 0 ≤ t) (T ε : ℝ) :
    deriv (finalTimeCutoff T ε) t = -deriv (initialTimeCutoff ε) (T - t) := by
  have heq : finalTimeCutoff T ε =ᶠ[𝓝 t] fun s ↦ initialTimeCutoff ε (T - s) := by
    filter_upwards [lt_mem_nhds (show -1 < t from by linarith)] with s hs
    unfold finalTimeCutoff
    rw [Real.smoothTransition.one_of_one_le (by linarith), one_mul]
  rw [heq.deriv_eq]
  simpa [Function.comp_def] using
    (((contDiff_initialTimeCutoff ε).differentiable (by norm_num) _).hasDerivAt.comp t
    ((hasDerivAt_id t).const_sub T)).deriv

/-- The reflected kernel has mass one on the time interval when its support lies inside. -/
theorem integral_terminal_kernel {T ε : ℝ} (hε : 0 < ε) (hT : 2 * ε ≤ T) :
    (∫ t : ℝ in Ioo 0 T, deriv (initialTimeCutoff ε) (T - t)) = 1 := by
  have hT0 : 0 ≤ T := (mul_pos (by norm_num) hε).le.trans hT
  have hd (t : ℝ) : HasDerivAt (fun s ↦ initialTimeCutoff ε (T - s))
      (-deriv (initialTimeCutoff ε) (T - t)) t := by
    simpa [Function.comp_def] using
      ((contDiff_initialTimeCutoff ε).differentiable (by norm_num) _).hasDerivAt.comp t
      ((hasDerivAt_id t).const_sub T)
  have hi : IntervalIntegrable (fun t ↦ -deriv (initialTimeCutoff ε) (T - t)) volume 0 T :=
    ((continuous_deriv_initialTimeCutoff ε).comp (continuous_const.sub continuous_id)).neg
      |>.intervalIntegrable 0 T
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t) hi
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_of_le hT0,
    initialTimeCutoff_zero hε (by simpa only [sub_self] using hε.le),
    show T - 0 = T from sub_zero T, initialTimeCutoff_one hε hT] at h
  rw [integral_Ioc_eq_integral_Ioo] at h
  linarith

/-- Terminal kernels recover any strong left trace of an integrable function. -/
theorem tendsto_integral_terminal_kernel {F : ℝ → ℝ} {T A : ℝ} (hT : 0 < T)
    (hF : IntegrableOn F (Ioo 0 T)) (hlim : Tendsto F (𝓝[<] T) (𝓝 A)) :
    Tendsto (fun ε : ℝ ↦ ∫ t : ℝ in Ioo 0 T,
      deriv (initialTimeCutoff ε) (T - t) * F t) (𝓝[>] 0) (𝓝 A) := by
  apply tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto
    measurableSet_Ioo measurableSet_Ioo (Subset.refl _) self_mem_nhdsWithin
    (by simp)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact fun t _ ↦ deriv_initialTimeCutoff_nonneg hε (T - t)
  · intro U hU hTU
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU T hTU
    refine Metric.tendstoUniformlyOn_iff.mpr fun δ hδ ↦ ?_
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (half_pos hr))] with ε hε hε'
    intro t ht
    have ht' : T - t ∉ Icc ε (2 * ε) := by
      intro hm
      apply ht.2
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (sub_neg.mpr ht.1.2)]
      linarith [hm.2, show ε < r / 2 from hε']
    simpa [deriv_initialTimeCutoff_eq_zero hε ht'] using hδ
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (half_pos hT))] with ε hε hε'
    exact (integral_terminal_kernel hε (by have h : ε < T / 2 := hε'; linarith : 2 * ε ≤ T)).symm
  · filter_upwards with ε
    exact ((continuous_deriv_initialTimeCutoff ε).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
  · exact hF
  · exact hlim.mono_left (nhdsWithin_mono _ Ioo_subset_Iio_self)

/-- The time kernels have a uniform inverse-width bound. -/
theorem exists_bound_deriv_initialTimeCutoff :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, 0 < ε → ∀ t : ℝ, ‖deriv (initialTimeCutoff ε) t‖ ≤ K / ε := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := deriv (initialTimeCutoff 1)) (continuous_deriv_initialTimeCutoff 1).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun ε hε t ↦ ?_⟩
  have hb (r : ℝ) : ‖deriv (initialTimeCutoff 1) r‖ ≤ max C 0 := by
    by_cases hr : r ∈ Icc 1 2
    · exact (hC r hr).trans (le_max_left _ _)
    · rw [deriv_initialTimeCutoff_eq_zero zero_lt_one (by simpa using hr), norm_zero]
      exact le_max_right _ _
  have hd : deriv (initialTimeCutoff ε) t =
      deriv (initialTimeCutoff 1) (t / ε) / ε := by
    have h := (((contDiff_initialTimeCutoff 1).differentiable (by norm_num) _).hasDerivAt.comp t
      ((hasDerivAt_id t).div_const ε)).deriv
    unfold initialTimeCutoff at h ⊢
    simpa [Function.comp_def, div_eq_mul_inv] using h
  rw [hd, norm_div, Real.norm_of_nonneg hε.le]
  exact div_le_div_of_nonneg_right (hb _) hε.le

/-- A terminal-kernel error is controlled by a local Lebesgue average. -/
theorem norm_terminal_kernel_error_le {F : ℝ → ℝ} (hF : LocallyIntegrable F volume) {K T ε : ℝ}
    (hε : 0 < ε) (hT : 2 * ε < T) (hK : ∀ t : ℝ, ‖deriv (initialTimeCutoff ε) t‖ ≤ K / ε) :
    ‖(∫ t : ℝ in Ioo 0 T, deriv (initialTimeCutoff ε) (T - t) * F t) - F T‖ ≤
      2 * K * ⨍ t : ℝ in Icc (T - 2 * ε) T, ‖F t - F T‖ := by
  let k := fun t : ℝ ↦ deriv (initialTimeCutoff ε) (T - t)
  have hk : Continuous k := (continuous_deriv_initialTimeCutoff ε).comp
    (continuous_const.sub continuous_id)
  have hki := hk.integrableOn_Icc (μ := volume) (a := 0) (b := T)
  have hFi := hF.integrableOn_isCompact (isCompact_Icc (a := 0) (b := T))
  have hprod := hFi.continuousOn_mul hk.continuousOn isCompact_Icc
  have heq : (∫ t : ℝ in Ioo 0 T, k t * (F t - F T)) =
      (∫ t : ℝ in Ioo 0 T, k t * F t) - F T := by
    simp_rw [mul_sub]
    rw [integral_sub (hprod.mono_set Ioo_subset_Icc_self)
      (IntegrableOn.mono_set (hki.mul_const (F T)) Ioo_subset_Icc_self), integral_mul_const,
      integral_terminal_kernel hε hT.le, one_mul]
  have hz (t : ℝ) (ht : t ∉ Ioo 0 T) : k t = 0 := by
    refine deriv_initialTimeCutoff_eq_zero hε fun hm ↦ ?_
    apply ht
    constructor <;> linarith [hm.1, hm.2]
  have hz' (t : ℝ) (ht : t ∉ Icc (T - 2 * ε) T) : k t = 0 := by
    refine deriv_initialTimeCutoff_eq_zero hε fun hm ↦ ?_
    apply ht
    constructor <;> linarith [hm.1, hm.2]
  change ‖(∫ t : ℝ in Ioo 0 T, k t * F t) - F T‖ ≤ _
  rw [← heq, setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht ↦ by
    rw [hz t ht, zero_mul])]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Icc (T - 2 * ε) T) (fun t ht ↦ by rw [hz' t ht, zero_mul])]
  have hdiff := ((hF.integrableOn_isCompact (isCompact_Icc (a := T - 2 * ε) (b := T))).sub
    (integrableOn_const isCompact_Icc.measure_ne_top (C := F T))).norm
  calc
    ‖∫ t : ℝ in Icc (T - 2 * ε) T, k t * (F t - F T)‖ ≤
        ∫ t : ℝ in Icc (T - 2 * ε) T, K / ε * ‖F t - F T‖ := by
      apply norm_integral_le_of_norm_le (hdiff.const_mul (K / ε))
      filter_upwards with t
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hK _) (norm_nonneg _)
    _ = 2 * K * ⨍ t : ℝ in Icc (T - 2 * ε) T, ‖F t - F T‖ := by
      rw [integral_const_mul, setAverage_eq, measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith : 0 ≤ T - (T - 2 * ε))]
      simp only [smul_eq_mul]
      field_simp [ne_of_gt hε]
      ring

/-- Terminal kernels recover the value at almost every positive time. -/
theorem ae_tendsto_integral_terminal_kernel {F : ℝ → ℝ} (hF : LocallyIntegrable F volume) :
    ∀ᵐ T : ℝ, 0 < T → Tendsto (fun ε : ℝ ↦ ∫ t : ℝ in Ioo 0 T,
      deriv (initialTimeCutoff ε) (T - t) * F t) (𝓝[>] 0) (𝓝 (F T)) := by
  have hLeb := (IsUnifLocDoublingMeasure.vitaliFamily volume 1).ae_tendsto_average_norm_sub hF
  obtain ⟨K, _, hK⟩ := exists_bound_deriv_initialTimeCutoff
  filter_upwards [hLeb] with T hT hpos
  have hleft : Tendsto (fun ε : ℝ ↦ T - 2 * ε) (𝓝[>] 0) (𝓝[<] T) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (tendsto_const_nhds.sub
        (((tendsto_id : Tendsto (fun x : ℝ ↦ x) (𝓝 0) (𝓝 0)).mono_left
          nhdsWithin_le_nhds).const_mul 2))
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      change T - 2 * ε < T
      linarith [show 0 < ε from hε]
  have havg := hT.comp (T.tendsto_Icc_vitaliFamily_left.comp hleft)
  apply tendsto_sub_nhds_zero_iff.mp
  apply squeeze_zero_norm' ?_ (by simpa using havg.const_mul (2 * K))
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (half_pos hpos))] with ε hε hε'
  exact norm_terminal_kernel_error_le hF (T := T) hε
    (by have h : ε < T / 2 := hε'; linarith) (hK ε hε)

end PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov
