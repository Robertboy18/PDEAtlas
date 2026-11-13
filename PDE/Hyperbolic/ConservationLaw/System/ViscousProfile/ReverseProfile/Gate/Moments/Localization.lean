/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flow.Branches.Substitution
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Moments.Variation

import CAS.ExactTactic

/-!
# Localization of the supplied prescribed clock integral

Closed-gate passage uniqueness and continuity localize each branch to its
passage endpoints. Uniform itinerary exclusions are supplied on the same parameter
neighborhood as the passages. Weight regularity and denominator nonvanishing give
one smaller open neighborhood where substitution yields the signed moment.
The family and event maps are retained throughout. The lower primitive keeps its
full cutoff.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff Interval Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

open Gate.Weights

variable {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {L Bhit : ℝ × ℝ → ℝ}
  {b : ℝ → ℝ} {sUp eUp sDown : ℝ}

/-- Closed-gate hits and uniqueness localize the full prescribed forcing integral
once the two complementary time intervals avoid the gate. These are state inequalities. The
descending time endpoints are reversed. -/
theorem prescribed_speed_integral_eq_gate_branches {p : ℝ × ℝ} (hF : Continuous F)
    (hb : Continuous b) (hbsupp : tsupport b ⊆ Ioo (205 : ℝ) (2051 / 10)) (h0s : 0 ≤ sUp)
    (hed : eUp ≤ sDown) (hbefore : ∀ t ∈ Icc 0 sUp, (F (t, p)).1 < 205)
    (hbetween : ∀ t ∈ Icc eUp sDown, (2051 / 10 : ℝ) < (F (t, p)).1)
    (hpassages : ∀ y ∈ Icc (205 : ℝ) (2051 / 10), let D := parameterizedClockPassageData L Bhit p;
      (D.tPlus y ∈ Icc sUp eUp ∧ (F (D.tPlus y, p)).1 = y ∧ ∀ t ∈ Icc sUp eUp, (F (t, p)).1 = y ↔
      t = D.tPlus y) ∧ (D.tMinus y ∈ Icc sDown (L p) ∧ (F (D.tMinus y, p)).1 = y ∧ ∀ t ∈
      Icc sDown (L p), (F (t, p)).1 = y ↔ t = D.tMinus y)) :
    let D := parameterizedClockPassageData L Bhit p
    (∫ t in (0 : ℝ)..L p, b ((F (t, p)).1) * Real.exp (-4 * (L p - t))) =
      (∫ t in D.tPlus 205..D.tPlus (2051 / 10),
        b ((F (t, p)).1) * Real.exp (-4 * (L p - t))) +
      (∫ t in D.tMinus (2051 / 10)..D.tMinus 205,
        b ((F (t, p)).1) * Real.exp (-4 * (L p - t))) := by
  let D := parameterizedClockPassageData L Bhit p
  let X : ℝ → ℝ := fun t ↦ (F (t, p)).1
  let H : ℝ → ℝ := fun t ↦ b (X t) * Real.exp (-4 * (L p - t))
  have hX : Continuous X := (hF.comp (continuous_id.prodMk continuous_const)).fst
  have hH : Continuous H := (hb.comp hX).mul
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id)))
  have hgate : (205 : ℝ) ≤ 2051 / 10 := by norm_num
  obtain ⟨hu₀, hu₁⟩ := hpassages 205 ⟨le_rfl, hgate⟩
  obtain ⟨hv₀, hv₁⟩ := hpassages (2051 / 10) ⟨hgate, le_rfl⟩
  have hupLo : X (D.tPlus 205) = 205 := hu₀.2.1
  have hupHi : X (D.tPlus (2051 / 10)) = 2051 / 10 := hv₀.2.1
  have hdownLo : X (D.tMinus 205) = 205 := hu₁.2.1
  have hdownHi : X (D.tMinus (2051 / 10)) = 2051 / 10 := hv₁.2.1
  have hse : sUp ≤ eUp := hu₀.1.1.trans hu₀.1.2
  have hdl : sDown ≤ L p := hu₁.1.1.trans hu₁.1.2
  -- The first upper hit cannot follow the higher hit, by the intermediate value theorem.
  have hupOrder : D.tPlus 205 ≤ D.tPlus (2051 / 10) := by
    have hlevel : (205 : ℝ) ∈ Icc (X sUp) (X (D.tPlus (2051 / 10))) :=
      ⟨(hbefore sUp ⟨h0s, le_rfl⟩).le, by simpa only [hupHi] using hgate⟩
    obtain ⟨t, ht, hXt⟩ := intermediate_value_Icc hv₀.1.1 hX.continuousOn hlevel
    have heq := (hu₀.2.2 t ⟨ht.1, ht.2.trans hv₀.1.2⟩).mp hXt
    simpa only [heq] using ht.2
  have hdownOrder : D.tMinus (2051 / 10) ≤ D.tMinus 205 := by
    have hlevel : (2051 / 10 : ℝ) ∈ Icc (X (D.tMinus 205)) (X sDown) :=
      ⟨by simpa only [hdownLo] using hgate, (hbetween sDown ⟨hed, le_rfl⟩).le⟩
    obtain ⟨t, ht, hXt⟩ := intermediate_value_Icc' hu₁.1.1 hX.continuousOn hlevel
    have heq := (hv₁.2.2 t ⟨ht.1, ht.2.trans hu₁.1.2⟩).mp hXt
    simpa only [heq] using ht.2
  -- Any nonzero gate value has its unique branch witness between the endpoint hits.
  have hupSupport (t : ℝ) (ht : t ∈ Icc sUp eUp) (hbt : b (X t) ≠ 0) :
      t ∈ Ioc (D.tPlus 205) (D.tPlus (2051 / 10)) := by
    have hy := hbsupp (subset_tsupport b hbt)
    have hlevel : X t ∈ Icc (X (D.tPlus 205)) (X (D.tPlus (2051 / 10))) := by
      simpa only [hupLo, hupHi] using Ioo_subset_Icc_self hy
    obtain ⟨v, hv, hXv⟩ := intermediate_value_Icc hupOrder hX.continuousOn hlevel
    have huniq := (hpassages (X t) (Ioo_subset_Icc_self hy)).1.2.2
    have hvt : v = t := ((huniq v ⟨hu₀.1.1.trans hv.1, hv.2.trans hv₀.1.2⟩).mp hXv).trans
        ((huniq t ht).mp rfl).symm
    have htt : t ∈ Icc (D.tPlus 205) (D.tPlus (2051 / 10)) := hvt ▸ hv
    exact ⟨lt_of_le_of_ne htt.1 fun heq ↦ hy.1.ne' (heq ▸ hupLo), htt.2⟩
  have hdownSupport (t : ℝ) (ht : t ∈ Icc sDown (L p)) (hbt : b (X t) ≠ 0) :
      t ∈ Ioc (D.tMinus (2051 / 10)) (D.tMinus 205) := by
    have hy := hbsupp (subset_tsupport b hbt)
    have hlevel : X t ∈ Icc (X (D.tMinus 205)) (X (D.tMinus (2051 / 10))) := by
      simpa only [hdownLo, hdownHi] using Ioo_subset_Icc_self hy
    obtain ⟨v, hv, hXv⟩ := intermediate_value_Icc' hdownOrder hX.continuousOn hlevel
    have huniq := (hpassages (X t) (Ioo_subset_Icc_self hy)).2.2.2
    have hvt : v = t := ((huniq v ⟨hv₁.1.1.trans hv.1, hv.2.trans hu₁.1.2⟩).mp hXv).trans
        ((huniq t ht).mp rfl).symm
    have htt : t ∈ Icc (D.tMinus (2051 / 10)) (D.tMinus 205) := hvt ▸ hv
    exact ⟨lt_of_le_of_ne htt.1 fun heq ↦ hy.2.ne (heq ▸ hdownHi), htt.2⟩
  have hupIntegral : (∫ t in sUp..eUp, H t) =
      ∫ t in D.tPlus 205..D.tPlus (2051 / 10), H t := by
    rw [intervalIntegral.integral_of_le hse, intervalIntegral.integral_of_le hupOrder]
    exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
      (Ioc_subset_Ioc hu₀.1.1 hv₀.1.2) fun t ht ↦ by
        simp only [H, not_not.mp fun hn ↦ ht.2 (hupSupport t (Ioc_subset_Icc_self ht.1) hn),
          zero_mul]
  have hdownIntegral : (∫ t in sDown..L p, H t) =
      ∫ t in D.tMinus (2051 / 10)..D.tMinus 205, H t := by
    rw [intervalIntegral.integral_of_le hdl, intervalIntegral.integral_of_le hdownOrder]
    exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
      (Ioc_subset_Ioc hv₁.1.1 hu₁.1.2) fun t ht ↦ by
        simp only [H, not_not.mp fun hn ↦ ht.2 (hdownSupport t (Ioc_subset_Icc_self ht.1) hn),
          zero_mul]
  have hbeforeIntegral : (∫ t in (0 : ℝ)..sUp, H t) = 0 :=
    (intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ by
      rw [uIcc_of_le h0s] at ht
      simp only [H, show b (X t) = 0 from image_eq_zero_of_notMem_tsupport fun h ↦
        lt_asymm (hbefore t ht) (hbsupp h).1, zero_mul]).trans intervalIntegral.integral_zero
  have hbetweenIntegral : (∫ t in eUp..sDown, H t) = 0 :=
    (intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ by
      rw [uIcc_of_le hed] at ht
      simp only [H, show b (X t) = 0 from image_eq_zero_of_notMem_tsupport fun h ↦
        lt_asymm (hbetween t ht) (hbsupp h).2, zero_mul]).trans intervalIntegral.integral_zero
  change (∫ t in (0 : ℝ)..L p, H t) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hH.intervalIntegrable 0 eUp)
      (hH.intervalIntegrable eUp (L p)),
    ← intervalIntegral.integral_add_adjacent_intervals (hH.intervalIntegrable 0 sUp)
      (hH.intervalIntegrable sUp eUp),
    ← intervalIntegral.integral_add_adjacent_intervals (hH.intervalIntegrable eUp sDown)
      (hH.intervalIntegrable sDown (L p)),
    hbeforeIntegral, hbetweenIntegral, zero_add, zero_add, hupIntegral, hdownIntegral]

/-- Uniform itinerary exclusions and closed-gate passages identify the prescribed
forcing integral with the whole-line signed weight moment. Both geometric
inputs hold on the same supplied neighborhood for the same `F`, `L`, and `Bhit`.
The neighborhood shrinks only for weight regularity and denominator nonvanishing,
so one neighborhood works for every continuous gate with the stated support. -/
theorem exists_prescribed_speed_integral_eq_weight_moment {N : Set (ℝ × ℝ)} (hF : Continuous F)
    (hN : IsOpen N) (h0 : (0, 0) ∈ N) (hL : ContDiffOn ℝ ∞ L N) (hBhit : ContDiffOn ℝ ∞ Bhit N)
    (h0s : 0 ≤ sUp) (hed : eUp ≤ sDown) (hbefore : ∀ p ∈ N, ∀ t ∈ Icc 0 sUp, (F (t, p)).1 < 205)
    (hbetween : ∀ p ∈ N, ∀ t ∈ Icc eUp sDown, (2051 / 10 : ℝ) < (F (t, p)).1)
    (hpassages : ∀ p ∈ N, ∀ y ∈ Icc (205 : ℝ) (2051 / 10),
      let D := parameterizedClockPassageData L Bhit p; (D.tPlus y ∈ Icc sUp eUp ∧
      (F (D.tPlus y, p)).1 = y ∧ ∀ t ∈ Icc sUp eUp, (F (t, p)).1 = y ↔ t = D.tPlus y) ∧
      (D.tMinus y ∈ Icc sDown (L p) ∧ (F (D.tMinus y, p)).1 = y ∧ ∀ t ∈ Icc sDown (L p),
      (F (t, p)).1 = y ↔ t = D.tMinus y)) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (0, 0) ∈ U ∧ U ⊆ N ∧
      ∀ b : ℝ → ℝ, Continuous b → tsupport b ⊆ Ioo (205 : ℝ) (2051 / 10) →
        ∀ p ∈ U,
        (∫ t in (0 : ℝ)..L p, b ((F (t, p)).1) * Real.exp (-4 * (L p - t))) =
          prescribedClockWeightMoment b L Bhit p := by
  obtain ⟨W, hW, h0W, hWN, _ht, hw⟩ :=
    exists_contDiffOn_parameterizedClockPassageData L Bhit hN h0 hL hBhit
  obtain ⟨ε, hε, η, hη, hsep, _hclosed, _hat⟩ :=
    exists_parameterizedClockPassageData_integral_tube L Bhit
  let U : Set (ℝ × ℝ) := W ∩ Prod.fst ⁻¹' Ioo (-ε) ε
  have hU : IsOpen U := hW.inter (isOpen_Ioo.preimage continuous_fst)
  have h0U : (0, 0) ∈ U := ⟨h0W, neg_lt_zero.mpr hε, hε⟩
  refine ⟨U, hU, h0U, (fun _ hp ↦ hWN hp.1), fun b hb hbsupp p hp ↦ ?_⟩
  let D := parameterizedClockPassageData L Bhit p
  have hpN : p ∈ N := hWN hp.1
  have hden : ∀ v ∈ Icc (0 : ℝ) 210, D.downSpeed v ≠ 0 ∧ D.g v + 1 ≠ 0 := by
    intro v hv
    have hs := hsep p.1 (Ioo_subset_Icc_self hp.2) v hv
    have hm := abs_pos.mp (hη.trans_le hs.1)
    have hu := abs_pos.mp (hη.trans_le hs.2)
    have heqm : (parameterizedClockPassageData L Bhit (0, 0)).downSpeed v + p.1 * v =
        D.downSpeed v := by
      simp only [D, parameterizedClockPassageData, clockPassageData, PassageData.downSpeed,
        zero_mul, sub_zero]
      ring
    have hequ : (parameterizedClockPassageData L Bhit (0, 0)).g v + 1 - p.1 * v =
        D.g v + 1 := by
      simp only [D, parameterizedClockPassageData, clockPassageData, zero_mul, sub_zero]
      ring
    exact ⟨heqm ▸ hm, hequ ▸ hu⟩
  have hX : Continuous (fun t ↦ (F (t, p)).1) :=
    (hF.comp (continuous_id.prodMk continuous_const)).fst
  have hup := prescribed_speed_up_branch_integral_eq
    (F := F) (L := L) (Bhit := Bhit) (p := p) (b := b) (s := sUp) (e := eUp)
    hX.continuousOn hb (fun y hy ↦ (hpassages p hpN y hy).1.1)
    (fun y hy ↦ (hpassages p hpN y hy).1.2.1) (fun v hv ↦ (hden v hv).2)
  have hdown := prescribed_speed_down_branch_integral_eq
    (F := F) (L := L) (Bhit := Bhit) (p := p) (b := b) (s := sDown)
    hX.continuousOn hb (fun y hy ↦ (hpassages p hpN y hy).2.1)
    (fun y hy ↦ (hpassages p hpN y hy).2.2.1) (fun v hv ↦ (hden v hv).1)
  have hwSlice : ContinuousOn (fun y ↦ (D.wMinus y, D.wPlus y))
      (Icc (205 : ℝ) (2051 / 10)) := by
    simpa only [Function.comp_def, id_eq] using hw.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (show MapsTo (fun y ↦ (p, y)) (Icc (205 : ℝ) (2051 / 10))
        (W ×ˢ Icc (205 : ℝ) (2051 / 10)) from fun _ hy ↦ ⟨hp.1, hy⟩)
  have hm : IntervalIntegrable (fun y ↦ b y * D.wMinus y) volume 205 (2051 / 10) :=
    (hb.continuousOn.mul hwSlice.fst).intervalIntegrable_of_Icc (by norm_num)
  have hu : IntervalIntegrable (fun y ↦ b y * D.wPlus y) volume 205 (2051 / 10) :=
    (hb.continuousOn.mul hwSlice.snd).intervalIntegrable_of_Icc (by norm_num)
  calc
    _ = (∫ t in D.tPlus 205..D.tPlus (2051 / 10), b ((F (t, p)).1) * Real.exp (-4 * (L p - t))) +
        (∫ t in D.tMinus (2051 / 10)..D.tMinus 205, b ((F (t, p)).1) * Real.exp (-4 * (L p - t))) :=
      prescribed_speed_integral_eq_gate_branches hF hb hbsupp h0s hed
        (hbefore p hpN) (hbetween p hpN) (hpassages p hpN)
    _ = (∫ y in (205 : ℝ)..(2051 / 10), b y * D.wPlus y) +
        ∫ y in (205 : ℝ)..(2051 / 10), b y * D.wMinus y := by rw [hup, hdown]
    _ = ∫ y in (205 : ℝ)..(2051 / 10), b y * (D.wMinus y + D.wPlus y) := by
      rw [add_comm, ← intervalIntegral.integral_add hm hu]
      exact intervalIntegral.integral_congr (fun y _ ↦ (mul_add _ _ _).symm)
    _ = prescribedClockWeightMoment b L Bhit p :=
      intervalIntegral.integral_eq_integral_of_support_subset
        ((Function.support_mul_subset_left b _).trans ((subset_tsupport b).trans
            (fun y hy ↦ ⟨(hbsupp hy).1, (hbsupp hy).2.le⟩)))

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
