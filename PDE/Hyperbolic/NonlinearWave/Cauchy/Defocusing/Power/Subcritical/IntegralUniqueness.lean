/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RetardedOverlap
import PDE.Analysis.Calculus.SignedPower.Deriv

/-!
# Uniqueness on finite intervals for bounded signed-power integral waves

Retarded splitting isolates the common past. Short-time cone uniqueness then
propagates equality to a right neighborhood of each matching past interval.
Continuous induction removes the short-time restriction.
-/

@[expose] public noncomputable section

open Set Filter PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData.Classical.LocalPower
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- A common past supplies the same retarded free input for two bounded
integral trajectories. Equality extends through every sufficiently short future cone. -/
theorem eq_on_short_future_of_eq_past {r b L a D M : ℝ} (hr : 1 ≤ r) (hb : 0 < b) (hM : 0 ≤ M)
    (ha : 0 ≤ a) (haL : a < L) (hDL : D ≤ L - a) (hDb : D ≤ a + b) {u v H : ℝ × ℝ^3 → ℝ}
    (hu : ContDiffOn ℝ 1 u {p | -b < p.1 ∧ p.1 < L})
    (hv : ContDiffOn ℝ 1 v {p | -b < p.1 ∧ p.1 < L}) (hH : ContDiff ℝ 1 H)
    (huB : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → |u p| ≤ M)
    (hvB : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → |v p| ≤ M)
    (hue : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → u p = H p + oddDuhamelSolution 0
      (fun z : ℝ^4 ↦ -Real.signedPower r (u (timeSpaceContinuousLinearEquiv 3 z)))
      (timeSpaceCons p.1 p.2))
    (hve : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → v p = H p + oddDuhamelSolution 0
      (fun z : ℝ^4 ↦ -Real.signedPower r (v (timeSpaceContinuousLinearEquiv 3 z)))
      (timeSpaceCons p.1 p.2))
    (hpast : ∀ s ∈ Icc 0 a, ∀ x : ℝ^3, u (s, x) = v (s, x)) {p : ℝ × ℝ^3} (hp : p.1 ∈ Ico 0 D)
    (hsmall : p.1 ^ 2 * ‖duhamelOperator‖ * ((2 * r) * (2 * M) ^ (r - 1)) < 1) :
    u (a + p.1, p.2) = v (a + p.1, p.2) := by
  obtain ⟨U, hU, hUeq⟩ := exists_contDiff_representative_on_initial_band hb hu haL
  let F : ℝ × ℝ^3 → ℝ := fun q ↦ -Real.signedPower r (U q)
  have hF : ContDiff ℝ 1 F := ((Real.contDiff_one_signedPower hr).comp hU).neg
  have hFpast (s : ℝ) (hs : s ∈ Icc 0 a) (x : ℝ^3) :
      F (s, x) = -Real.signedPower r (u (s, x)) := by
    change -Real.signedPower r (U (s, x)) = _
    rw [hUeq (s, x) hs]
  have hvshift : ContDiffOn ℝ 1 (fun q : ℝ × ℝ^3 ↦ v (a + q.1, q.2))
      {q | |q.1| < D} := by
    apply hv.comp ((contDiff_const.add contDiff_fst).prodMk contDiff_snd).contDiffOn
    intro q hq
    have habs := abs_lt.mp (show |q.1| < D from hq)
    change -b < a + q.1 ∧ a + q.1 < L
    exact ⟨by linarith [habs.1], by linarith [habs.2]⟩
  apply eq_on_restart_overlap hr hb hM ha hDL le_rfl hDb hu hvshift hH hF hFpast
    huB (fun q hq ↦ hvB (a + q.1, q.2)
      ⟨add_nonneg ha hq.1, by linarith [hq.2]⟩) hue ?_ hp hsmall
  intro q hq
  have he := shift_eq_retarded_of_integral_eq hr hb hv hve ha (p := q) ⟨hq.1, hq.2.trans_le hDL⟩
  have hhist : retardedHistory a F q =
      retardedHistory a (fun z ↦ -Real.signedPower r (v z)) q := by
    apply retardedHistory_congr ha
    intro s hs x
    rw [hFpast s hs x, hpast s hs x]
  rw [← hhist] at he
  exact he

/-- Bounded C¹ integral trajectories with a common free field coincide on
an arbitrary finite forward interval. Only the amplitude is bounded; there
is no smallness restriction on the interval and no derivative bound. -/
theorem eq_on_forward_interval_of_bounded_signedPower_integral_eq {r b L M : ℝ} (hr : 1 ≤ r)
    (hb : 0 < b) (hM : 0 ≤ M) {u v H : ℝ × ℝ^3 → ℝ} (hu : ContDiffOn ℝ 1 u {p | -b < p.1 ∧ p.1 < L})
    (hv : ContDiffOn ℝ 1 v {p | -b < p.1 ∧ p.1 < L}) (hH : ContDiff ℝ 1 H)
    (huB : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → |u p| ≤ M)
    (hvB : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → |v p| ≤ M)
    (hue : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → u p = H p + oddDuhamelSolution 0
      (fun z : ℝ^4 ↦ -Real.signedPower r (u (timeSpaceContinuousLinearEquiv 3 z)))
      (timeSpaceCons p.1 p.2))
    (hve : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → v p = H p + oddDuhamelSolution 0
      (fun z : ℝ^4 ↦ -Real.signedPower r (v (timeSpaceContinuousLinearEquiv 3 z)))
      (timeSpaceCons p.1 p.2)) :
    ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → u p = v p := by
  intro p hp
  obtain ⟨S, hpS, hSL⟩ := exists_between hp.2
  have hS : 0 < S := hp.1.trans_lt hpS
  obtain ⟨U, hU, hUeq⟩ := exists_contDiff_representative_on_initial_band hb hu hSL
  obtain ⟨V, hV, hVeq⟩ := exists_contDiff_representative_on_initial_band hb hv hSL
  let E : Set ℝ := {t | ∀ x : ℝ^3, U (t, x) = V (t, x)}
  have hE : IsClosed E := by
    change IsClosed {t | ∀ x : ℝ^3, U (t, x) = V (t, x)}
    simp only [ofPred_forall]
    exact isClosed_iInter fun x ↦ isClosed_eq
      (hU.continuous.comp (continuous_id.prodMk continuous_const))
      (hV.continuous.comp (continuous_id.prodMk continuous_const))
  have hzero : (0 : ℝ) ∈ E := by
    intro x
    rw [hUeq (0, x) ⟨le_rfl, hS.le⟩, hVeq (0, x) ⟨le_rfl, hS.le⟩,
      hue (0, x) ⟨le_rfl, hS.trans hSL⟩, hve (0, x) ⟨le_rfl, hS.trans hSL⟩]
    simp only [oddDuhamelSolution_zero_eq_normalized _ _ le_rfl, zero_pow (by decide : 2 ≠ 0),
      zero_mul, add_zero]
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
    intro t ht
    have hta : 0 ≤ t - a := sub_nonneg.mpr ht.1.le
    have htD : t - a < D := by linarith [ht.2]
    have htS : t ∈ Icc 0 S := ⟨ha.1.trans ht.1.le, by linarith [ht.2]⟩
    intro x
    rw [hUeq (t, x) htS, hVeq (t, x) htS]
    have he := eq_on_short_future_of_eq_past hr hb hM ha.1 (ha.2.trans hSL)
      (min_le_left _ _) (min_le_right _ _) hu hv hH huB hvB hue hve
      (fun s hs y ↦ by
        have hsS : s ∈ Icc 0 S := ⟨hs.1, hs.2.trans ha.2.le⟩
        have hxy := hpast hs y
        rwa [hUeq (s, y) hsS, hVeq (s, y) hsS] at hxy)
      (p := (t - a, x)) ⟨hta, htD⟩ (by
        apply hsmall
        change dist (t - a) 0 < ε
        rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hta]
        linarith [ht.2])
    simpa only [add_sub_cancel] using he
  have he := hcover ⟨hp.1, hpS.le⟩ p.2
  rwa [hUeq p ⟨hp.1, hpS.le⟩, hVeq p ⟨hp.1, hpS.le⟩] at he

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
