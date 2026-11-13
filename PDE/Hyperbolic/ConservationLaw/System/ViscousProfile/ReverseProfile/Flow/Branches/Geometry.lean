/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flow.Events.Speed

import CAS.ExactTactic

/-!
# Uniform branch geometry for a supplied prescribed speed family

Strict reference brackets persist on one smaller open parameter neighborhood.
The completed-switch bracket extends past the reference zero. Evenness of the
middle clock controls the lower field slightly below state zero, so the
supplied ODE makes every nearby trajectory strictly decreasing on that bracket.
Its zero then gives the nonnegative band up to its own return time.

The family and both event maps are supplied. Reference bands and endpoint slack at parameter zero
remain hypotheses.
-/

@[expose] public noncomputable section

open Set
open scoped Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

open MiddleClock

/-- The full lower denominator stays positive slightly below the zero state. -/
private theorem eight_fifths_lt_speed_lower_denominator {μ y : ℝ}
    (hμ : |μ| < 1 / 410) (hy : y ∈ Icc (-1 : ℝ) 210) :
    (8 / 5 : ℝ) < 4 - g y + 4 * cutoff y + μ * y := by
  have hyabs : |y| ≤ 210 := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩
  have hgabs : g |y| = g y := by
    rcases le_total 0 y with hy0 | hy0
    · rw [abs_of_nonneg hy0]
    · rw [abs_of_nonpos hy0, g_neg]
  have hg : g y < 7 / 5 := by
    rw [← hgabs]
    exact (monotoneOn_g_nonneg (abs_nonneg y) (by cas : (0 : ℝ) ≤ 210) hyabs).trans_lt g_210_lt
  have hproduct : |μ * y| < 1 := by
    rw [abs_mul]; linarith [mul_le_mul_of_nonneg_left hyabs (abs_nonneg μ)]
  linarith [cutoff_nonneg y, (abs_lt.mp hproduct).1]

/-- Reference branch margins persist for the same supplied family and event maps.
The fixed lower bracket extends beyond the reference zero; its strict decrease
recovers the closed nonnegative state band only up to each zero `L p`. -/
theorem exists_prescribed_speed_branch_neighborhood {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {N : Set (ℝ × ℝ)}
    {L Bhit : ℝ × ℝ → ℝ} {A B τ0 sUp eUp sDown : ℝ} (hAB : A ^ 2 < B ^ 2) (hFcont : Continuous F)
    (hN : IsOpen N) (hbase : (0, 0) ∈ N) (hμ : ∀ p ∈ N, |p.1| < 1 / 410)
    (hODE : ∀ p ∈ N, ∀ t ∈ Icc (-1 : ℝ) (τ0 + 1),
      HasDerivAt (fun u ↦ F (u, p)) (prescribedSpeedField A B (p.1, F (t, p))) t)
    (hL : ContinuousOn L N) (hBhit : ContinuousOn Bhit N) (hLbase : L (0, 0) = τ0)
    (hBbase : Bhit (0, 0) ∈ Ioo sUp eUp) (hzero : ∀ p ∈ N, (F (L p, p)).1 = 0)
    (hdownTime : -1 ≤ sDown ∧ sDown < τ0)
    (hrefUp : ∀ t ∈ Icc sUp eUp, (F (t, (0, 0))).1 ∈ Ioo (0 : ℝ) 210 ∧ 2 < (F (t, (0, 0))).2 ∧
      (F (t, (0, 0))).2 ^ 2 < A ^ 2)
    (hrefDown : ∀ t ∈ Icc sDown τ0, (F (t, (0, 0))).1 ∈ Ico (0 : ℝ) 210 ∧ B ^ 2 <
      (F (t, (0, 0))).2 ^ 2)
    (hrefStartUp : (F (sUp, (0, 0))).1 < 205) (hrefEndUp : (2051 / 10 : ℝ) < (F (eUp, (0, 0))).1)
    (hrefStartDown : (2051 / 10 : ℝ) < (F (sDown, (0, 0))).1) :
    ∃ (eDown : ℝ) (N' : Set (ℝ × ℝ)),
      eDown ∈ Ioo τ0 (τ0 + 1) ∧ IsOpen N' ∧ (0, 0) ∈ N' ∧ N' ⊆ N ∧
      ∀ p ∈ N',
        Bhit p ∈ Ioo sUp eUp ∧ L p ∈ Ioo sDown eDown ∧
        (∀ t ∈ Icc sUp eUp, (F (t, p)).1 ∈ Ioo (0 : ℝ) 210 ∧
          2 < (F (t, p)).2 ∧ (F (t, p)).2 ^ 2 < A ^ 2) ∧
        (F (sUp, p)).1 < 205 ∧ (2051 / 10 : ℝ) < (F (eUp, p)).1 ∧
        (∀ t ∈ Icc sDown eDown, (F (t, p)).1 ∈ Ioo (-1 : ℝ) 210 ∧
          B ^ 2 < (F (t, p)).2 ^ 2) ∧
        (2051 / 10 : ℝ) < (F (sDown, p)).1 ∧
        StrictAntiOn (fun t ↦ (F (t, p)).1) (Icc sDown eDown) ∧
        (∀ t ∈ Icc sDown (L p), (F (t, p)).1 ∈ Icc (0 : ℝ) 210) := by
  let x : (ℝ × ℝ) × ℝ → ℝ := fun q ↦ (F (q.2, q.1)).1
  let z : (ℝ × ℝ) × ℝ → ℝ := fun q ↦ (F (q.2, q.1)).2
  have hx : Continuous x := (hFcont.comp (continuous_snd.prodMk continuous_fst)).fst
  have hz : Continuous z := (hFcont.comp (continuous_snd.prodMk continuous_fst)).snd
  let ΩUp : Set ((ℝ × ℝ) × ℝ) := {q | x q ∈ Ioo (0 : ℝ) 210 ∧ 2 < z q ∧ z q ^ 2 < A ^ 2}
  let ΩDown : Set ((ℝ × ℝ) × ℝ) := {q | x q ∈ Ioo (-1 : ℝ) 210 ∧ B ^ 2 < z q ^ 2}
  have hΩUp : IsOpen ΩUp := (isOpen_Ioo.preimage hx).inter
    ((isOpen_lt continuous_const hz).inter (isOpen_lt (hz.pow 2) continuous_const))
  have hΩDown : IsOpen ΩDown := (isOpen_Ioo.preimage hx).inter
    (isOpen_lt continuous_const (hz.pow 2))
  -- Extend the reference bracket before taking a compact tube in parameter and time.
  let V0 : Set ℝ := {t | ((0, 0), t) ∈ ΩDown} ∩ Iio (τ0 + 1)
  have hV0 : IsOpen V0 := (hΩDown.preimage (continuous_const.prodMk continuous_id)).inter isOpen_Iio
  have hτV0 : τ0 ∈ V0 := ⟨⟨show (F (τ0, (0, 0))).1 ∈ Ioo (-1 : ℝ) 210 by
    rw [← hLbase, hzero (0, 0) hbase]; norm_num, (hrefDown τ0 ⟨hdownTime.2.le, le_rfl⟩).2⟩,
    lt_add_one τ0⟩
  obtain ⟨l, r, hτlr, hlr⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hV0.mem_nhds hτV0)
  let eDown : ℝ := (τ0 + r) / 2
  have hτe : τ0 < eDown := show τ0 < (τ0 + r) / 2 by linarith [hτlr.2]
  have her : eDown < r := show (τ0 + r) / 2 < r by linarith [hτlr.2]
  have heV0 : eDown ∈ V0 := hlr ⟨hτlr.1.trans hτe, her⟩
  have heDown : eDown ∈ Ioo τ0 (τ0 + 1) := ⟨hτe, heV0.2⟩
  have hrefDownExtended (t : ℝ) (ht : t ∈ Icc sDown eDown) :
      ((0, 0), t) ∈ ΩDown := by
    rcases le_or_gt t τ0 with htτ | hτt
    · have hr := hrefDown t ⟨ht.1, htτ⟩
      exact ⟨⟨(by norm_num : (-1 : ℝ) < 0).trans_le hr.1.1, hr.1.2⟩, hr.2⟩
    · exact (hlr ⟨hτlr.1.trans hτt, ht.2.trans_lt her⟩).1
  have hrefΩUp : {((0, 0) : ℝ × ℝ)} ×ˢ Icc sUp eUp ⊆ ΩUp := by
    rintro ⟨p, t⟩ ⟨rfl, ht⟩
    exact hrefUp t ht
  have hrefΩDown : {((0, 0) : ℝ × ℝ)} ×ˢ Icc sDown eDown ⊆ ΩDown := by
    rintro ⟨p, t⟩ ⟨rfl, ht⟩
    exact hrefDownExtended t ht
  obtain ⟨Nup, Vup, hNup, _hVup, hbaseNup, hupTimes, hupTube⟩ :=
    generalized_tube_lemma (s := {((0, 0) : ℝ × ℝ)}) (t := Icc sUp eUp)
      isCompact_singleton isCompact_Icc hΩUp hrefΩUp
  obtain ⟨Ndown, Vdown, hNdown, _hVdown, hbaseNdown, hdownTimes, hdownTube⟩ :=
    generalized_tube_lemma (s := {((0, 0) : ℝ × ℝ)}) (t := Icc sDown eDown)
      isCompact_singleton isCompact_Icc hΩDown hrefΩDown
  have hfixed (t : ℝ) : Continuous (fun p : ℝ × ℝ ↦ (F (t, p)).1) :=
    (hFcont.comp (continuous_const.prodMk continuous_id)).fst
  let E : Set (ℝ × ℝ) := {p | (F (sUp, p)).1 < 205 ∧
    (2051 / 10 : ℝ) < (F (eUp, p)).1 ∧ (2051 / 10 : ℝ) < (F (sDown, p)).1}
  have hE : IsOpen E := (isOpen_lt (hfixed sUp) continuous_const).inter
    ((isOpen_lt continuous_const (hfixed eUp)).inter (isOpen_lt continuous_const (hfixed sDown)))
  let NL : Set (ℝ × ℝ) := N ∩ L ⁻¹' Ioo sDown eDown
  let NB : Set (ℝ × ℝ) := N ∩ Bhit ⁻¹' Ioo sUp eUp
  have hNL : IsOpen NL := hL.isOpen_inter_preimage hN isOpen_Ioo
  have hNB : IsOpen NB := hBhit.isOpen_inter_preimage hN isOpen_Ioo
  let N' : Set (ℝ × ℝ) := NL ∩ (NB ∩ (Nup ∩ (Ndown ∩ E)))
  have hbaseN' : (0, 0) ∈ N' :=
    ⟨⟨hbase, (hLbase ▸ ⟨hdownTime.2, hτe⟩ : L (0, 0) ∈ Ioo sDown eDown)⟩, ⟨hbase, hBbase⟩,
      hbaseNup (mem_singleton _), hbaseNdown (mem_singleton _),
      hrefStartUp, hrefEndUp, hrefStartDown⟩
  have hsub : N' ⊆ N := fun _ hp ↦ hp.1.1
  refine ⟨eDown, N', heDown, hNL.inter (hNB.inter (hNup.inter (hNdown.inter hE))), hbaseN', hsub,
    fun p hp ↦ ?_⟩
  have hpN : p ∈ N := hsub hp
  have hl : L p ∈ Ioo sDown eDown := hp.1.2
  have hb : Bhit p ∈ Ioo sUp eUp := hp.2.1.2
  have hup (t : ℝ) (ht : t ∈ Icc sUp eUp) : (F (t, p)).1 ∈ Ioo (0 : ℝ) 210 ∧
        2 < (F (t, p)).2 ∧ (F (t, p)).2 ^ 2 < A ^ 2 :=
    hupTube (show (p, t) ∈ Nup ×ˢ Vup from ⟨hp.2.2.1, hupTimes ht⟩)
  have hdown (t : ℝ) (ht : t ∈ Icc sDown eDown) :
      (F (t, p)).1 ∈ Ioo (-1 : ℝ) 210 ∧ B ^ 2 < (F (t, p)).2 ^ 2 :=
    hdownTube (show (p, t) ∈ Ndown ×ˢ Vdown from ⟨hp.2.2.2.1, hdownTimes ht⟩)
  have hderiv (t : ℝ) (ht : t ∈ Icc sDown eDown) : HasDerivAt (fun u ↦ (F (u, p)).1)
        (lowerClockField (F (t, p)).1 - p.1 * (F (t, p)).1) t := by
    have hfirst : HasDerivAt (fun u ↦ (F (u, p)).1)
        (prescribedClockField A B (F (t, p)).2 (F (t, p)).1 - p.1 * (F (t, p)).1) t :=
      (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t
        (hODE p hpN t ⟨hdownTime.1.trans ht.1, ht.2.trans heDown.2.le⟩)
    rwa [prescribedClockField_eq_lower hAB (hdown t ht).2.le] at hfirst
  have hanti : StrictAntiOn (fun t ↦ (F (t, p)).1) (Icc sDown eDown) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc sDown eDown)
      (hFcont.comp (continuous_id.prodMk continuous_const)).fst.continuousOn
    intro t ht
    have htK : t ∈ Icc sDown eDown := interior_subset ht
    change deriv (fun u ↦ (F (u, p)).1) t < 0
    rw [(hderiv t htK).deriv]
    change g (F (t, p)).1 - 4 - 4 * cutoff (F (t, p)).1 - p.1 * (F (t, p)).1 < 0
    linarith [eight_fifths_lt_speed_lower_denominator (hμ p hpN)
      ⟨(hdown t htK).1.1.le, (hdown t htK).1.2.le⟩]
  refine ⟨hb, hl, hup, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hdown, hp.2.2.2.2.2.2, hanti, fun t ht ↦ ?_⟩
  have htK : t ∈ Icc sDown eDown := ⟨ht.1, ht.2.trans hl.2.le⟩
  exact ⟨by simpa only [hzero p hpN] using hanti.antitoneOn htK ⟨hl.1.le, hl.2.le⟩ ht.2,
    (hdown t htK).1.2.le⟩

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
