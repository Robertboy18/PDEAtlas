/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.LogPotential
public import PDE.Analysis.Fourier.HilbertTransform.PrincipalValue.Continuity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.ParametricIntegral
import CAS.ExactTactic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Logarithmic Hilbert moments for compact Lipschitz input

Absolute continuity permits derivative jumps, including at the support endpoints.
The boundary at zero is canceled by the Lipschitz estimate, and derivatives of the
input are used only almost everywhere. No endpoint derivative is required to vanish.
Compactly supported `C¹` input is Lipschitz, so the `C¹` statements are special cases.
`mean_velocity_eq_log_moment` identifies `-u(L)/L` with the logarithmic moment `c_ω` of Chen,
Hou and Huang, whose kernel is `g_cω` in (4.24).

## References

* J. Chen, T. Y. Hou and D. Huang, "On the finite time blowup of the De Gregorio model for the 3D
  Euler equations", *Comm. Pure Appl. Math.* 74 (2021), 1282-1350, numbering of arXiv:1905.06387v3,
  Section 4.2.3, the formula for `c_ω` and (4.24). <https://arxiv.org/abs/1905.06387v3>
-/

@[expose] public section

namespace PDE.Analysis

open Filter MeasureTheory Set
open scoped NNReal Topology

noncomputable section

/-- Multiplying the logarithm by a bounded measurable compactly supported function
produces an absolutely integrable function, even when the multiplier has jumps. -/
theorem integrable_log_mul_of_bounded_compactSupport {g : ℝ → ℝ} {B : ℝ}
    (hg : StronglyMeasurable g) (hc : HasCompactSupport g) (hB : ∀ t, ‖g t‖ ≤ B) :
    Integrable (fun t ↦ Real.log t * g t) := by
  apply (integrableOn_iff_integrable_of_support_subset
    (s := tsupport g) (fun t ht ↦ subset_tsupport g (by
      exact fun hzero ↦ ht (by simp [hzero])))).mp
  exact (locallyIntegrable_real_log.integrableOn_isCompact hc).mul_bdd
    hg.aestronglyMeasurable (Eventually.of_forall hB)

/-- A Lipschitz zero cancels the logarithmic boundary term without a derivative at zero. -/
theorem tendsto_mul_log_zero_of_lipschitzWith {g : ℝ → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hzero : g 0 = 0) :
    Tendsto (fun t ↦ g t * Real.log t) (𝓝[>] 0) (𝓝 0) := by
  have hbound (t : ℝ) : ‖g t * Real.log t‖ ≤ (K : ℝ) * ‖t * Real.log t‖ := by
    have h := hg.norm_sub_le t 0
    simp only [hzero, sub_zero] at h
    simp only [norm_mul]
    calc
      _ ≤ ((K : ℝ) * ‖t‖) * ‖Real.log t‖ :=
        mul_le_mul_of_nonneg_right h (norm_nonneg _)
      _ = _ := mul_assoc _ _ _
  have hlim : Tendsto (fun t ↦ (K : ℝ) * ‖t * Real.log t‖) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((Real.continuous_mul_log.continuousAt (x := 0)).norm.const_mul
      (K : ℝ)).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  exact squeeze_zero_norm (fun t ↦ hbound t) hlim

/-- The derivative-log product is integrable for compact Lipschitz input; its derivative
may be discontinuous or fail to exist on a null set. -/
theorem integrable_deriv_mul_log_of_lipschitzWith {g : ℝ → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hc : HasCompactSupport g) :
    Integrable (fun t ↦ deriv g t * Real.log t) := by
  simpa only [mul_comm] using integrable_log_mul_of_bounded_compactSupport
    (stronglyMeasurable_deriv g) hc.deriv (fun _ ↦ norm_deriv_le_of_lipschitz hg)

/-- At any zero of compact Lipschitz input, its uncentered Hilbert kernel is integrable. -/
theorem integrable_hilbertKernel_of_lipschitzWith_zero {g : ℝ → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hc : HasCompactSupport g) {x : ℝ} (hx : g x = 0) :
    Integrable (fun y ↦ g y / (x - y)) := by
  apply integrable_hilbertKernel_of_local_lipschitz_zero
    (hg.continuous.integrable_of_hasCompactSupport hc) hx (R := 1) (by norm_num) K.coe_nonneg
  intro t _
  simpa only [Real.norm_eq_abs, sub_sub_cancel_left, abs_neg] using hg.norm_sub_le (x - t) x

/-- Logarithmic integration by parts on the positive half-line for compact Lipschitz
input vanishing at zero. Finite-interval absolute continuity handles derivative jumps. -/
theorem integral_Ioi_div_eq_neg_deriv_mul_log_of_lipschitzWith {g : ℝ → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hc : HasCompactSupport g) (hzero : g 0 = 0) :
    (∫ t in Ioi 0, g t / t) = -∫ t in Ioi 0, deriv g t * Real.log t := by
  have hdiv : Integrable (fun t ↦ g t / t) := by
    simpa only [zero_sub, div_neg, neg_neg] using
      (integrable_hilbertKernel_of_lipschitzWith_zero hg hc hzero).fun_neg
  have hlog := integrable_deriv_mul_log_of_lipschitzWith hg hc
  have hfinite {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
      (∫ t in a..b, g t / t) =
        g b * Real.log b - g a * Real.log a - ∫ t in a..b, deriv g t * Real.log t := by
    have hlogac : AbsolutelyContinuousOnInterval Real.log a b := by
      apply ContDiffOn.absolutelyContinuousOnInterval
      apply Real.contDiffOn_log.mono
      intro t ht
      have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht
      exact ne_of_gt (lt_of_lt_of_le ha ht'.1)
    convert hg.lipschitzOnWith.absolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul
      hlogac using 1
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le ha ht'.1)
    have hd : HasDerivAt Real.log (1 / t) t := by cas using ht0
    rw [hd.deriv]
    exact div_eq_mul_one_div (g t) t
  have hzeroFinite (b : ℝ) (hb : 0 < b) :
      (∫ t in 0..b, g t / t) =
        g b * Real.log b - ∫ t in 0..b, deriv g t * Real.log t := by
    have hleft : Tendsto (fun a ↦ ∫ t in a..b, g t / t) (𝓝[>] 0)
        (𝓝 (∫ t in 0..b, g t / t)) := by
      simpa only [Pi.neg_def, ← intervalIntegral.integral_symm b] using
        ((hdiv.continuous_primitive b).neg.continuousAt (x := 0)).tendsto.mono_left
          (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    have hright : Tendsto
        (fun a ↦ g b * Real.log b - g a * Real.log a -
          ∫ t in a..b, deriv g t * Real.log t) (𝓝[>] 0)
        (𝓝 (g b * Real.log b - ∫ t in 0..b, deriv g t * Real.log t)) := by
      have hi : Tendsto (fun a ↦ ∫ t in a..b, deriv g t * Real.log t) (𝓝[>] 0)
          (𝓝 (∫ t in 0..b, deriv g t * Real.log t)) := by
        simpa only [Pi.neg_def, ← intervalIntegral.integral_symm b] using
          ((hlog.continuous_primitive b).neg.continuousAt (x := 0)).tendsto.mono_left
            (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa only [sub_zero] using
        ((tendsto_mul_log_zero_of_lipschitzWith hg hzero).const_sub
          (g b * Real.log b)).sub hi
    apply tendsto_nhds_unique hleft
    apply hright.congr'
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with a ha hab
    exact (hfinite ha hab.le).symm
  have hleft := intervalIntegral_tendsto_integral_Ioi 0 hdiv.integrableOn
    (tendsto_id : Tendsto (fun b : ℝ ↦ b) atTop atTop)
  have hboundary : Tendsto (fun b ↦ g b * Real.log b) atTop (𝓝 0) :=
    (hc.mul_right (f' := Real.log)).is_zero_at_infty.mono_left atTop_le_cocompact
  have hright := hboundary.sub (intervalIntegral_tendsto_integral_Ioi 0 hlog.integrableOn
    (tendsto_id : Tendsto (fun b : ℝ ↦ b) atTop atTop))
  simp only [zero_sub] at hright
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
  exact (hzeroFinite b hb).symm

/-- The symmetric cancellation formula holds at every point of compact Lipschitz input,
including corners, by the integrable regularized kernel. -/
theorem hilbertPV_eq_integral_symmetric_difference_of_lipschitzWith {f : ℝ → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) (hc : HasCompactSupport f) (x : ℝ) :
    hilbertPV f x = Real.pi⁻¹ * ∫ t in Ioi 0, (f (x - t) - f (x + t)) / t := by
  have hint := integrable_hilbertRegularizedKernel_one_of_lipschitzWith hf hc x
  rw [(hasHilbertPV_of_regularized hint).hilbertPV_eq,
    integral_eq_integral_Ioi_add_reflection hint]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp only [hilbertRegularizedKernel, indicator, mem_ofPred_eq, abs_neg, sub_neg_eq_add,
    div_neg]
  split_ifs <;> ring

/-- Logarithmic integration by parts identifies the principal value using only the
almost-everywhere derivative of a compact Lipschitz function. -/
theorem hilbertPV_eq_integral_log_mul_deriv_of_lipschitzWith {f : ℝ → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) (hc : HasCompactSupport f) (x : ℝ) :
    hilbertPV f x = Real.pi⁻¹ * ∫ t, Real.log t * deriv f (x - t) := by
  let g : ℝ → ℝ := fun t ↦ f (x - t) - f (x + t)
  have hg : LipschitzWith (K + K) g := by
    simpa using (hf.comp ((LipschitzWith.const x).sub LipschitzWith.id)).sub
      (hf.comp (isometry_add_left x).lipschitzWith)
  have hgc : HasCompactSupport g :=
    (hc.comp_homeomorph (Homeomorph.subLeft x)).sub
      (hc.comp_homeomorph (Homeomorph.addLeft x))
  have hgzero : g 0 = 0 := by simp [g]
  have hminus := (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae
    hf.ae_differentiableAt_real
  have hplus := (measurePreserving_add_left volume x).quasiMeasurePreserving.ae
    hf.ae_differentiableAt_real
  have hgderiv : ∀ᵐ t, deriv g t = -deriv f (x - t) - deriv f (x + t) := by
    filter_upwards [hminus, hplus] with t hm hp
    have hdm := hm.hasDerivAt.comp t ((hasDerivAt_id t).const_sub x)
    have hdp := hp.hasDerivAt.comp t ((hasDerivAt_id t).const_add x)
    simpa only [g, mul_neg_one, mul_one, Function.comp_def, Pi.sub_def, id_eq] using
      (hdm.sub hdp).deriv
  have hlog : Integrable (fun t ↦ Real.log t * deriv f (x - t)) := by
    apply integrable_log_mul_of_bounded_compactSupport
      ((stronglyMeasurable_deriv f).comp_measurable (measurable_const.sub measurable_id))
      (hc.deriv.comp_homeomorph (Homeomorph.subLeft x))
    exact fun _ ↦ norm_deriv_le_of_lipschitz hf
  rw [hilbertPV_eq_integral_symmetric_difference_of_lipschitzWith hf hc x,
    integral_Ioi_div_eq_neg_deriv_mul_log_of_lipschitzWith hg hgc hgzero,
    integral_eq_integral_Ioi_add_reflection hlog, ← integral_neg]
  congr 1
  apply integral_congr_ae
  filter_upwards [hgderiv.filter_mono (ae_restrict_le (μ := volume))] with t ht
  rw [ht]
  simp only [Real.log_neg_eq_log, sub_neg_eq_add]
  ring

/-- Integration by parts identifies the logarithmic convolution derivative with
the principal value, without a separate operator-identification hypothesis. -/
theorem hilbertPV_eq_integral_log_mul_deriv {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hcompact : HasCompactSupport f) (x : ℝ) :
    hilbertPV f x = Real.pi⁻¹ * ∫ t, Real.log t * deriv f (x - t) := by
  obtain ⟨_, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcompact hf one_ne_zero
  exact hilbertPV_eq_integral_log_mul_deriv_of_lipschitzWith hK hcompact x

/-- A common compact logarithmic majorant controls translations of Lipschitz input
on a neighborhood of an evaluation point. This permits differentiation under the integral. -/
theorem exists_integrable_lipschitz_bound_log_translate {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) (x : ℝ) :
    ∃ bound : ℝ → ℝ, Integrable bound ∧ ∀ t,
      LipschitzOnWith (Real.nnabs (bound t)) (fun z ↦ Real.log t * f (z - t))
        (Metric.ball x 1) := by
  obtain ⟨S, hS, hs⟩ := hc.exists_pos_le_norm
  let R : ℝ := |x| + S + 2
  let bound : ℝ → ℝ := (Icc (-R) R).indicator (fun t ↦ (K : ℝ) * ‖Real.log t‖)
  have hb : Integrable bound := by
    apply IntegrableOn.integrable_indicator
    · exact (locallyIntegrable_real_log.integrableOn_isCompact isCompact_Icc).norm.const_mul
        (K : ℝ)
    · exact measurableSet_Icc
  refine ⟨bound, hb, fun t ↦ ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro z hz w hw
  by_cases ht : t ∈ Icc (-R) R
  · have hnonneg : 0 ≤ (K : ℝ) * ‖Real.log t‖ := mul_nonneg K.coe_nonneg (norm_nonneg _)
    simp only [bound, indicator_of_mem ht, Real.coe_nnabs, abs_of_nonneg hnonneg]
    rw [dist_eq_norm, ← mul_sub, norm_mul]
    calc
      _ ≤ ‖Real.log t‖ * ((K : ℝ) * ‖(z - t) - (w - t)‖) :=
        mul_le_mul_of_nonneg_left (hf.norm_sub_le _ _) (norm_nonneg _)
      _ = _ := by rw [sub_sub_sub_cancel_right, dist_eq_norm]; ring
  · have hzero (v : ℝ) (hv : v ∈ Metric.ball x 1) : f (v - t) = 0 := by
      have hv1 : |v - x| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hv
      have hvnorm : |v| ≤ |v - x| + |x| := by
        simpa only [sub_zero] using abs_sub_le v x 0
      have htnorm : |t| ≤ |v - t| + |v| := by
        simpa only [sub_zero, abs_sub_comm t v] using abs_sub_le t v 0
      have htR : R < |t| := lt_of_not_ge (fun h ↦ ht (abs_le.mp h))
      apply hs
      rw [Real.norm_eq_abs]
      dsimp only [R] at htR
      linarith
    simp only [hzero z hz, hzero w hw, mul_zero, dist_self]
    exact mul_nonneg (NNReal.coe_nonneg _) dist_nonneg

/-- The logarithmic potential has the Hilbert principal value as its classical
derivative at every point, although the compact input need only be Lipschitz. -/
theorem hasDerivAt_log_potential_of_lipschitzWith {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) (x : ℝ) :
    HasDerivAt (fun z ↦ Real.pi⁻¹ * ∫ y, Real.log (z - y) * f y) (hilbertPV f x) x := by
  obtain ⟨bound, hbound, hlip⟩ := exists_integrable_lipschitz_bound_log_translate hf hc x
  have hmeas (z : ℝ) : Integrable (fun t ↦ Real.log t * f (z - t)) :=
    (hc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
      locallyIntegrable_real_log hf.continuous z).integrable
  have hdiff : ∀ᵐ t, HasDerivAt (fun z ↦ Real.log t * f (z - t))
      (Real.log t * deriv f (x - t)) x := by
    filter_upwards [(Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae
      hf.ae_differentiableAt_real] with t ht
    simpa only [Function.comp_def, mul_one, id_eq] using
      (ht.hasDerivAt.comp x ((hasDerivAt_id x).sub_const t)).const_mul (Real.log t)
  have h := (hasDerivAt_integral_of_dominated_loc_of_lip (Metric.ball_mem_nhds x zero_lt_one)
    (Eventually.of_forall fun z ↦ (hmeas z).aestronglyMeasurable) (hmeas x)
    ((Real.measurable_log.mul ((measurable_deriv f).comp
      (measurable_const.sub measurable_id))).aestronglyMeasurable)
    (Eventually.of_forall hlip) hbound hdiff).2.const_mul Real.pi⁻¹
  simp only [Pi.mul_def, Function.comp_def, Pi.sub_def, id_eq] at h
  rw [hilbertPV_eq_integral_log_mul_deriv_of_lipschitzWith hf hc x]
  convert h using 1
  ext z
  congr 1
  simpa only [sub_sub_cancel] using
    (integral_sub_left_eq_self (fun y ↦ Real.log (z - y) * f y) volume z).symm

/-- The logarithmic convolution is a classical primitive of the Hilbert PV. -/
theorem hasDerivAt_log_potential {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hcompact : HasCompactSupport f) (x : ℝ) :
    HasDerivAt (fun z ↦ Real.pi⁻¹ * ∫ y, Real.log (z - y) * f y)
      (hilbertPV f x) x := by
  obtain ⟨_, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcompact hf one_ne_zero
  exact hasDerivAt_log_potential_of_lipschitzWith hK hcompact x

/-- For odd compact input the logarithmic potential vanishes at the origin. Hence
`u' = H f` and `u(0) = 0` determine the velocity by this integral, not by an assumed moment. -/
theorem velocity_eq_log_potential_of_lipschitzWith {f u : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hcompact : HasCompactSupport f)
    (hodd : Function.Odd f) (hu : ∀ x, HasDerivAt u (hilbertPV f x) x)
    (hu0 : u 0 = 0) (x : ℝ) :
    u x = Real.pi⁻¹ * ∫ y, Real.log (x - y) * f y := by
  exact velocity_eq_log_potential_of_hasDerivAt hodd hu
    (hasDerivAt_log_potential_of_lipschitzWith hf hcompact) hu0 x

/-- For odd compact `C¹` input the logarithmic potential vanishes at the origin. Hence
`u' = H f` and `u(0) = 0` determine the velocity by this integral, not by an assumed moment. -/
theorem velocity_eq_log_potential {f u : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hcompact : HasCompactSupport f)
    (hodd : Function.Odd f) (hu : ∀ x, HasDerivAt u (hilbertPV f x) x)
    (hu0 : u 0 = 0) (x : ℝ) :
    u x = Real.pi⁻¹ * ∫ y, Real.log (x - y) * f y := by
  obtain ⟨_, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcompact hf one_ne_zero
  exact velocity_eq_log_potential_of_lipschitzWith hK hcompact hodd hu hu0 x

/-- Odd reflection and compact support give the logarithmic mean-velocity coefficient
in Chen–Hou–Huang (4.24). All logarithms are evaluated in ordinary absolutely convergent
integrals; the interval endpoints are null sets. -/
theorem mean_velocity_eq_log_moment_of_lipschitzWith {f u : ℝ → ℝ} {L : ℝ} {K : ℝ≥0}
    (hL : 0 < L) (hf : LipschitzWith K f) (hcompact : HasCompactSupport f)
    (hodd : Function.Odd f) (hsupport : ∀ y, L ≤ y → f y = 0)
    (hu : ∀ x, HasDerivAt u (hilbertPV f x) x) (hu0 : u 0 = 0) :
    -u L / L =
      ∫ y in Ioo 0 L, (Real.log ((L + y) / (L - y)) / (L * Real.pi)) * f y := by
  rw [velocity_eq_log_potential_of_lipschitzWith hf hcompact hodd hu hu0 L]
  exact neg_log_potential_div_eq_log_moment hL hf.continuous hcompact hodd hsupport

/-- Odd reflection and compact support give the logarithmic mean-velocity coefficient
in Chen–Hou–Huang (4.24) for `C¹` input. -/
theorem mean_velocity_eq_log_moment {f u : ℝ → ℝ} {L : ℝ}
    (hL : 0 < L) (hf : ContDiff ℝ 1 f) (hcompact : HasCompactSupport f)
    (hodd : Function.Odd f) (hsupport : ∀ y, L ≤ y → f y = 0)
    (hu : ∀ x, HasDerivAt u (hilbertPV f x) x) (hu0 : u 0 = 0) :
    -u L / L =
      ∫ y in Ioo 0 L, (Real.log ((L + y) / (L - y)) / (L * Real.pi)) * f y := by
  obtain ⟨_, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcompact hf one_ne_zero
  exact mean_velocity_eq_log_moment_of_lipschitzWith hL hK hcompact hodd hsupport hu hu0

end

end PDE.Analysis
