/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.IntegralLifespan
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.SpatialSupport

/-!
# Finite propagation of bounded integral trajectories

Retarded splitting preserves the support of the past forcing. Short-cone
uniqueness advances the zero exterior through a positive time interval, and
continuous induction covers every finite interval. This applies to the C¹ integral trajectory.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData.Classical.LocalPower
open scoped Topology unitInterval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- A source supported in the expanding ball up to the anchor has no retarded
past contribution outside the same expanding ball at any later time. -/
theorem retardedHistory_eq_zero_of_forward_support {a R : ℝ} (ha : 0 ≤ a) {F : ℝ × ℝ^3 → ℝ}
    (hF : ∀ s ∈ Icc 0 a, ∀ x : ℝ^3, R + s < ‖x‖ → F (s, x) = 0) {p : ℝ × ℝ^3} (hp : 0 ≤ p.1)
    (hx : R + a + p.1 < ‖p.2‖) :
    retardedHistory a F p = 0 := by
  unfold retardedHistory
  apply intervalIntegral.integral_zero_ae
  filter_upwards with s hs
  have hs' : s ∈ Icc 0 a := by
    have hs'' : s ∈ Ioc 0 a := by simpa only [uIoc_of_le ha] using hs
    exact ⟨hs''.1.le, hs''.2⟩
  have hage : 0 ≤ a + p.1 - s := by linarith [hs'.2]
  have havg : unitSphereAverage 3 (fun y ↦ F (s, y)) p.2 (a + p.1 - s) = 0 := by
    unfold unitSphereAverage
    suffices h : (∫ θ : Direction, F (s, p.2 + (a + p.1 - s) • (θ : ℝ^3))
        ∂((volume : Measure (ℝ^3)).toSphere)) = 0 by rw [h, zero_div]
    apply integral_eq_zero_of_ae
    filter_upwards with θ
    apply hF s hs'
    have hn := norm_sub_le (p.2 + (a + p.1 - s) • (θ : ℝ^3)) ((a + p.1 - s) • (θ : ℝ^3))
    rw [add_sub_cancel_right, norm_smul, Real.norm_of_nonneg hage,
      norm_eq_of_mem_sphere θ, mul_one] at hn
    linarith
  change (a + p.1 - s) * unitSphereAverage 3 (fun y ↦ F (s, y)) p.2 (a + p.1 - s) = 0
  rw [havg, mul_zero]

/-- Vanishing outside the expanding ball on the whole past advances across
any future cone on which the amplitude absorption estimate holds. -/
theorem eq_zero_on_short_future_of_supported_past {r b L a D M R : ℝ} (hr : 1 ≤ r) (hb : 0 < b)
    (hM : 0 ≤ M) (ha : 0 ≤ a) (haL : a < L) (hDL : D ≤ L - a) (hDb : D ≤ a + b) {u H : ℝ × ℝ^3 → ℝ}
    (hu : ContDiffOn ℝ 1 u {p | -b < p.1 ∧ p.1 < L}) (hH : ContDiff ℝ 1 H)
    (hHs : ∀ p : ℝ × ℝ^3, 0 ≤ p.1 → R + p.1 < ‖p.2‖ → H p = 0)
    (huB : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → |u p| ≤ M)
    (hue : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → u p = H p + oddDuhamelSolution 0
      (fun z : ℝ^4 ↦ -Real.signedPower r (u (timeSpaceContinuousLinearEquiv 3 z)))
      (timeSpaceCons p.1 p.2))
    (hpast : ∀ s ∈ Icc 0 a, ∀ x : ℝ^3, R + s < ‖x‖ → u (s, x) = 0) {p : ℝ × ℝ^3}
    (hp : p.1 ∈ Ico 0 D) (hsmall : p.1 ^ 2 * ‖duhamelOperator‖ * ((2 * r) * (2 * M) ^ (r - 1)) < 1)
    (hx : R + a + p.1 < ‖p.2‖) :
    u (a + p.1, p.2) = 0 := by
  obtain ⟨U, hU, hUeq⟩ := exists_contDiff_representative_on_initial_band hb hu haL
  let F : ℝ × ℝ^3 → ℝ := fun q ↦ -Real.signedPower r (U q)
  have hF : ContDiff ℝ 1 F := ((Real.contDiff_one_signedPower hr).comp hU).neg
  have hFpast (s : ℝ) (hs : s ∈ Icc 0 a) (x : ℝ^3) :
      F (s, x) = -Real.signedPower r (u (s, x)) := by
    change -Real.signedPower r (U (s, x)) = _
    rw [hUeq (s, x) hs]
  let G : ℝ × ℝ^3 → ℝ := fun q ↦ H (a + q.1, q.2) + retardedHistory a F q
  have hG : ContDiff ℝ 1 G := (hH.comp ((contDiff_const.add contDiff_fst).prodMk contDiff_snd)).add
      (contDiff_one_retardedHistory hF a)
  have hGs (q : ℝ × ℝ^3) (hq : 0 ≤ q.1) (hqx : R + a + q.1 < ‖q.2‖) :
      G q = 0 := by
    have hHz := hHs (a + q.1, q.2) (add_nonneg ha hq) (by
      change R + (a + q.1) < ‖q.2‖; linarith)
    have hFz := retardedHistory_eq_zero_of_forward_support ha
      (F := F) (R := R) (fun s hs x hxs ↦ by
        rw [hFpast s hs x, hpast s hs x hxs]
        simp [Real.signedPower]) hq hqx
    change H (a + q.1, q.2) + retardedHistory a F q = 0
    rw [hHz, hFz, add_zero]
  have hshift : ContinuousOn (fun q : ℝ × ℝ^3 ↦ u (a + q.1, q.2))
      {q | |q.1| < D} := by
    apply hu.continuousOn.comp
      ((continuous_const.add continuous_fst).prodMk continuous_snd).continuousOn
    intro q hq
    have habs := abs_lt.mp (show |q.1| < D from hq)
    change -b < a + q.1 ∧ a + q.1 < L
    exact ⟨by linarith [habs.1], by linarith [habs.2]⟩
  apply eq_zero_of_supported_free_integral_eq hr hM hshift ⟨G, hG.continuous⟩ hGs
    (fun q hq ↦ huB (a + q.1, q.2)
      ⟨add_nonneg ha hq.1, by linarith [hq.2]⟩) ?_ hp hsmall hx
  intro q hq
  have he := shift_eq_retarded_of_integral_eq hr hb hu hue ha (p := q) ⟨hq.1, hq.2.trans_le hDL⟩
  rw [← retardedHistory_congr ha hFpast q, oddDuhamelSolution_zero_eq_normalized _ _ hq.1] at he
  exact he

/-- A bounded C¹ integral trajectory inherits speed-one propagation from its
free field on the whole finite forward interval. No short-time restriction
remains after continuous induction. -/
theorem IsBoundedIntegralTrajectoryBefore.eq_zero_of_supported_free {r b L R : ℝ} (hr : 1 ≤ r)
    (hb : 0 < b) {H u : ℝ × ℝ^3 → ℝ} (hH : ContDiff ℝ 1 H)
    (hHs : ∀ p : ℝ × ℝ^3, 0 ≤ p.1 → R + p.1 < ‖p.2‖ → H p = 0)
    (hu : IsBoundedIntegralTrajectoryBefore r b H L u) {p : ℝ × ℝ^3} (hp : p.1 ∈ Ico 0 L)
    (hx : R + p.1 < ‖p.2‖) :
    u p = 0 := by
  obtain ⟨M, hM, huM⟩ := hu.bounded
  obtain ⟨S, hpS, hSL⟩ := exists_between hp.2
  have hS : 0 < S := hp.1.trans_lt hpS
  obtain ⟨U, hU, hUeq⟩ := exists_contDiff_representative_on_initial_band hb hu.regular hSL
  let E : Set ℝ := {t | ∀ x : ℝ^3, R + t < ‖x‖ → U (t, x) = 0}
  have hE : IsClosed E := by
    change IsClosed {t | ∀ x : ℝ^3, R + t < ‖x‖ → U (t, x) = 0}
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro x
    have he : {t : ℝ | R + t < ‖x‖ → U (t, x) = 0} =
        {t : ℝ | ‖x‖ ≤ R + t} ∪ {t : ℝ | U (t, x) = 0} := by
      ext t
      simp only [mem_ofPred_eq, mem_union, imp_iff_not_or, not_lt]
    rw [he]
    exact (isClosed_le continuous_const (continuous_const.add continuous_id)).union
      (isClosed_eq (hU.continuous.comp (continuous_id.prodMk continuous_const)) continuous_const)
  have hzero : (0 : ℝ) ∈ E := by
    intro x hx
    rw [hUeq (0, x) ⟨le_rfl, hS.le⟩, hu.equation (0, x) ⟨le_rfl, hu.time_pos⟩]
    rw [hHs (0, x) le_rfl hx]
    simp only [oddDuhamelSolution_zero_eq_normalized _ _ le_rfl,
      zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero]
  have hcover : Icc 0 S ⊆ E := by
    apply (hE.inter isClosed_Icc).Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hzero
    intro a ha hpast
    let D := min (L - a) (a + b)
    have hD : 0 < D := lt_min (sub_pos.mpr (ha.2.trans hSL)) (by linarith [ha.1])
    have hc : Continuous (fun t : ℝ ↦
        t ^ 2 * ‖duhamelOperator‖ * ((2 * r) * (2 * M) ^ (r - 1))) := by fun_prop
    have hnear : ∀ᶠ t : ℝ in 𝓝 0, t ^ 2 * ‖duhamelOperator‖ * ((2 * r) * (2 * M) ^ (r - 1)) < 1 :=
      hc.continuousAt.eventually (gt_mem_nhds (by simp))
    obtain ⟨ε, hε, hsmall⟩ := Metric.mem_nhds_iff.mp hnear
    let δ := min D (min ε (S - a))
    have hδ : 0 < δ := lt_min hD (lt_min hε (sub_pos.mpr ha.2))
    have hδD : δ ≤ D := min_le_left _ _
    have hδε : δ ≤ ε := (min_le_right _ _).trans (min_le_left _ _)
    have hδS : δ ≤ S - a := (min_le_right _ _).trans (min_le_right _ _)
    apply mem_of_superset (Ioo_mem_nhdsGT (show a < a + δ by linarith))
    intro t ht x hxt
    have hta : 0 ≤ t - a := sub_nonneg.mpr ht.1.le
    have htD : t - a < D := by linarith [ht.2]
    have htS : t ∈ Icc 0 S := ⟨ha.1.trans ht.1.le, by linarith [ht.2]⟩
    rw [hUeq (t, x) htS]
    have he := eq_zero_on_short_future_of_supported_past hr hb hM ha.1
      (ha.2.trans hSL) (min_le_left _ _) (min_le_right _ _) hu.regular hH hHs huM
      hu.equation (fun s hs y hys ↦ by
        have hsS : s ∈ Icc 0 S := ⟨hs.1, hs.2.trans ha.2.le⟩
        have hz := hpast hs y hys
        rwa [hUeq (s, y) hsS] at hz)
      (p := (t - a, x)) ⟨hta, htD⟩ (by
        apply hsmall
        change dist (t - a) 0 < ε
        rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hta]
        linarith [ht.2]) (by change R + a + (t - a) < ‖x‖; linarith)
    simpa only [add_sub_cancel] using he
  have he := hcover ⟨hp.1, hpS.le⟩ p.2 hx
  rwa [hUeq p ⟨hp.1, hpS.le⟩] at he

/-- Bounds on proper prefixes suffice for finite propagation up to an open
endpoint, even when the total amplitude is unbounded near that endpoint. -/
theorem IsIntegralTrajectoryBefore.eq_zero_of_supported_free {r b L R : ℝ} (hr : 1 ≤ r) (hb : 0 < b)
    {H u : ℝ × ℝ^3 → ℝ} (hH : ContDiff ℝ 1 H)
    (hHs : ∀ p : ℝ × ℝ^3, 0 ≤ p.1 → R + p.1 < ‖p.2‖ → H p = 0)
    (hu : IsIntegralTrajectoryBefore r b H L u) {p : ℝ × ℝ^3} (hp : p.1 ∈ Ico 0 L)
    (hx : R + p.1 < ‖p.2‖) :
    u p = 0 := by
  obtain ⟨S, hpS, hSL⟩ := exists_between hp.2
  exact (hu.before (hp.1.trans_lt hpS) hSL).eq_zero_of_supported_free hr hb hH hHs ⟨hp.1, hpS⟩ hx

/-- A global integral trajectory retains speed-one propagation on every
finite interval. -/
theorem IsGlobalIntegralTrajectory.eq_zero_of_supported_free {r b R : ℝ} (hr : 1 ≤ r) (hb : 0 < b)
    {H u : ℝ × ℝ^3 → ℝ} (hH : ContDiff ℝ 1 H)
    (hHs : ∀ p : ℝ × ℝ^3, 0 ≤ p.1 → R + p.1 < ‖p.2‖ → H p = 0)
    (hu : IsGlobalIntegralTrajectory r b H u) {p : ℝ × ℝ^3} (hp : 0 ≤ p.1) (hx : R + p.1 < ‖p.2‖) :
    u p = 0 := by
  exact (hu.before (show 0 < p.1 + 1 by linarith)).eq_zero_of_supported_free hr hb hH hHs
    ⟨hp, by linarith⟩ hx

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
