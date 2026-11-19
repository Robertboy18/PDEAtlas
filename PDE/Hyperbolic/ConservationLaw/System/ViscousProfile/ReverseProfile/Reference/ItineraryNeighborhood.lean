/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Reference.Itinerary

import CAS.ExactTactic

/-!
# A common parameter neighborhood for the prescribed clock itinerary

The input is the conclusion of `prescribed_clock_reference_itinerary` for
the retained reference clock and passage data. Joint continuity of the supplied
family gives five compact tubes on one open parameter neighborhood. They retain
the four original conclusions and exclude the full gate on the two complementary
fixed intervals. The stronger between-branches tube also gives the weaker bound.
The late tube extends beyond the reference zero; reference agreement is used only
on `[0, τ0]`.
-/

@[expose] public noncomputable section

open Set
open scoped Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

open Gate.Weights

/-- A reference state condition given by an open set on a time interval inside `[0, τ0]`
persists on a product of open parameter and time neighborhoods (tube lemma). -/
private theorem exists_reference_tube {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {X Z : ℝ → ℝ} {τ0 a b : ℝ}
    {O : Set (ℝ × ℝ)} (hFcont : Continuous F) (hO : IsOpen O)
    (href : EqOn (fun t ↦ F (t, (0, 0))) (fun t ↦ (X t, Z t)) (Icc 0 τ0))
    (ha : 0 ≤ a) (hb : b ≤ τ0) (h : ∀ t ∈ Icc a b, (X t, Z t) ∈ O) :
    ∃ (N : Set (ℝ × ℝ)) (V : Set ℝ), IsOpen N ∧ IsOpen V ∧ (0, 0) ∈ N ∧ Icc a b ⊆ V ∧
      ∀ p ∈ N, ∀ t ∈ V, F (t, p) ∈ O := by
  obtain ⟨N, V, hN, hV, h0, hab, htube⟩ := generalized_tube_lemma isCompact_singleton
    isCompact_Icc (hO.preimage (hFcont.comp (continuous_snd.prodMk continuous_fst)))
    (show {((0, 0) : ℝ × ℝ)} ×ˢ Icc a b ⊆ (fun q ↦ F (q.2, q.1)) ⁻¹' O by
      rintro ⟨p, t⟩ ⟨rfl, ht⟩
      rw [mem_preimage, show F (t, (0, 0)) = (X t, Z t) from href ⟨ha.trans ht.1, ht.2.trans hb⟩]
      exact h t ht)
  exact ⟨N, V, hN, hV, h0 rfl, hab, fun p hp t ht ↦ htube (mk_mem_prod hp ht)⟩

/-- The reference itinerary persists for the same continuous family on one open
parameter neighborhood. The cuts remain the fixed base passage times. Only the last
interval is extended, with its new endpoint below any supplied `Hmax > τ0`.
The reference hypothesis is the conclusion of `prescribed_clock_reference_itinerary`. The two
full-gate exclusions persist on the same neighborhood as the original four conclusions. -/
theorem exists_prescribed_clock_itinerary_neighborhood {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {N : Set (ℝ × ℝ)}
    {X Z : ℝ → ℝ} {D : PassageData} {T τ0 upBaseTime A B Hmax : ℝ} (hFcont : Continuous F)
    (hN : IsOpen N) (hbase : (0, 0) ∈ N)
    (href : EqOn (fun t ↦ F (t, (0, 0))) (fun t ↦ (X t, Z t)) (Icc 0 τ0)) (hHmax : τ0 < Hmax) :
    let sUp := (1 + upBaseTime) / 2
    let eUp := (D.tPlus (2051 / 10) + T) / 2
    let sDown := (T + 1 / 2 + D.tMinus (2051 / 10)) / 2
    let rUp := D.tPlus (41001 / 200)
    let rDown := D.tMinus (41001 / 200)
    ((0 < sUp ∧ sUp < rUp ∧ rUp < eUp ∧ eUp < sDown ∧
      sDown < rDown ∧ rDown < τ0) ∧
      (∀ t ∈ Icc 0 rUp, X t ∈ Ioo (-1 : ℝ) (20501 / 100) ∧ Z t ^ 2 < A ^ 2) ∧
      (∀ t ∈ Icc rUp rDown, 205 < X t) ∧
      (∀ t ∈ Icc eUp sDown, (20509 / 100 : ℝ) < X t) ∧
      (∀ t ∈ Icc rDown τ0, X t ∈ Ioo (-1 : ℝ) (20501 / 100) ∧ B ^ 2 < Z t ^ 2) ∧
      (∀ t ∈ Icc 0 sUp, X t < 205) ∧
      (∀ t ∈ Icc eUp sDown, (2051 / 10 : ℝ) < X t)) →
    ∃ (H : ℝ) (N' : Set (ℝ × ℝ)),
      H ∈ Ioo τ0 Hmax ∧ IsOpen N' ∧ (0, 0) ∈ N' ∧ N' ⊆ N ∧
        ∀ p ∈ N',
          (∀ t ∈ Icc 0 rUp,
            (F (t, p)).1 ∈ Ioo (-1 : ℝ) (20501 / 100) ∧ (F (t, p)).2 ^ 2 < A ^ 2) ∧
          (∀ t ∈ Icc rUp rDown, 205 < (F (t, p)).1) ∧
          (∀ t ∈ Icc eUp sDown, (20509 / 100 : ℝ) < (F (t, p)).1) ∧
          (∀ t ∈ Icc rDown H,
            (F (t, p)).1 ∈ Ioo (-1 : ℝ) (20501 / 100) ∧ B ^ 2 < (F (t, p)).2 ^ 2) ∧
          (∀ t ∈ Icc 0 sUp, (F (t, p)).1 < 205) ∧
          (∀ t ∈ Icc eUp sDown, (2051 / 10 : ℝ) < (F (t, p)).1) := by
  intro sUp eUp sDown rUp rDown
  rintro ⟨⟨h0s, hsr, hre, hed, hdr, hrt⟩,
    hearly, hmiddle, _hbetween, hlate, hbeforeAll, hbetweenAll⟩
  have hr0 : 0 ≤ rUp := (h0s.trans hsr).le
  have he0 : 0 ≤ eUp := hr0.trans hre.le
  have hrτ : rUp ≤ τ0 := hre.le.trans (hed.le.trans (hdr.le.trans hrt.le))
  obtain ⟨Nearly, Vearly, hNearly, -, hbaseEarly, htimesEarly, htubeEarly⟩ :=
    exists_reference_tube (O := Ioo (-1 : ℝ) (20501 / 100) ×ˢ {z | z ^ 2 < A ^ 2}) hFcont
      (isOpen_Ioo.prod (isOpen_lt (continuous_pow 2) continuous_const)) href le_rfl hrτ hearly
  obtain ⟨Nmiddle, Vmiddle, hNmiddle, -, hbaseMiddle, htimesMiddle, htubeMiddle⟩ :=
    exists_reference_tube (O := {s | 205 < s.1}) hFcont
      (isOpen_lt continuous_const continuous_fst) href hr0 hrt.le hmiddle
  obtain ⟨Nbetween, Vbetween, hNbetween, -, hbaseBetween, htimesBetween, htubeBetween⟩ :=
    exists_reference_tube (O := {s | (2051 / 10 : ℝ) < s.1}) hFcont
      (isOpen_lt continuous_const continuous_fst) href he0 (hdr.le.trans hrt.le) hbetweenAll
  obtain ⟨Nbefore, Vbefore, hNbefore, -, hbaseBefore, htimesBefore, htubeBefore⟩ :=
    exists_reference_tube (O := {s | s.1 < 205}) hFcont
      (isOpen_lt continuous_fst continuous_const) href le_rfl (hsr.le.trans hrτ) hbeforeAll
  obtain ⟨Nlate, Vlate, hNlate, hVlate, hbaseLate, htimesLate, htubeLate⟩ :=
    exists_reference_tube (O := Ioo (-1 : ℝ) (20501 / 100) ×ˢ {z | B ^ 2 < z ^ 2}) hFcont
      (isOpen_Ioo.prod (isOpen_lt continuous_const (continuous_pow 2))) href
      (hr0.trans (hre.le.trans (hed.le.trans hdr.le))) le_rfl hlate
  -- The open time factor extends the entire last tube with its parameter factor fixed.
  obtain ⟨H, hτH, hinterval⟩ := mem_nhdsGE_iff_exists_Icc_subset.mp (nhdsWithin_le_nhds
    ((hVlate.inter isOpen_Iio).mem_nhds ⟨htimesLate ⟨hrt.le, le_rfl⟩, hHmax⟩))
  have htimesExtended : Icc rDown H ⊆ Vlate := fun t ht ↦ by
    rcases le_total t τ0 with htτ | hτt
    · exact htimesLate ⟨ht.1, htτ⟩
    · exact (hinterval ⟨hτt, ht.2⟩).1
  refine ⟨H, N ∩ (Nearly ∩ (Nmiddle ∩ (Nbetween ∩ (Nlate ∩ Nbefore)))),
    ⟨hτH, (hinterval ⟨hτH.le, le_rfl⟩).2⟩,
    hN.inter (hNearly.inter (hNmiddle.inter (hNbetween.inter (hNlate.inter hNbefore)))),
    ⟨hbase, hbaseEarly, hbaseMiddle, hbaseBetween, hbaseLate, hbaseBefore⟩, fun _ hp ↦ hp.1,
    fun p hp ↦ ⟨fun t ht ↦ htubeEarly p hp.2.1 t (htimesEarly ht),
      fun t ht ↦ htubeMiddle p hp.2.2.1 t (htimesMiddle ht),
      fun t ht ↦ (by norm_num : (20509 / 100 : ℝ) < 2051 / 10).trans
        (htubeBetween p hp.2.2.2.1 t (htimesBetween ht)),
      fun t ht ↦ htubeLate p hp.2.2.2.2.1 t (htimesExtended ht),
      fun t ht ↦ htubeBefore p hp.2.2.2.2.2 t (htimesBefore ht),
      fun t ht ↦ htubeBetween p hp.2.2.2.1 t (htimesBetween ht)⟩⟩

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
