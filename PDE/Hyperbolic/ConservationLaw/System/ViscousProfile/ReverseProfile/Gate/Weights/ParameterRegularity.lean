/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Weights.ParameterVariation

import CAS.ExactTactic

/-!
# Joint regularity of the same parameterized clock weights

The compact denominator bounds on `[0,210]` give a common speed window for
both oriented passage integrals. Slack around `[205,205.1]` gives ordinary
joint smoothness, including its two endpoints. Intersecting that window with
the supplied event neighborhood gives joint smoothness for the
remaining lower travel duration, upper passage time, and weights. The entire
lower cutoff remains in its integral.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff Interval Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

open Gate.Weights MiddleClock

/-- One speed window and denominator margin work for both primitives.
Relative smoothness holds on the larger closed interval `[0,210]`; ordinary
smoothness holds at every point of the closed gate. The event maps are arbitrary
here, since the two primitive integrands do not depend on their values. -/
theorem exists_parameterizedClockPassageData_integral_tube (L Bhit : ℝ × ℝ → ℝ) :
    let D := parameterizedClockPassageData L Bhit (0, 0)
    ∃ ε > 0, ∃ η > 0,
      (∀ μ ∈ Icc (-ε) ε, ∀ v ∈ Icc (0 : ℝ) 210,
        η ≤ |D.downSpeed v + μ * v| ∧ η ≤ |D.g v + 1 - μ * v|) ∧
      ContDiffOn ℝ ∞
        (fun q : ℝ × ℝ ↦ (D.downRemaining q.1 q.2, D.upPassageIntegral q.1 q.2))
        (Ioo (-ε) ε ×ˢ Icc (0 : ℝ) 210) ∧
      ∀ μ ∈ Ioo (-ε) ε, ∀ y ∈ Icc (205 : ℝ) (2051 / 10),
        ContDiffAt ℝ ∞
          (fun q : ℝ × ℝ ↦ (D.downRemaining q.1 q.2, D.upPassageIntegral q.1 q.2))
          (μ, y) := by
  intro D
  have hDg : D.g = g := by
    simp [D, clockPassageData]
  have hDd : D.downSpeed = fun v ↦ 4 - g v + 4 * cutoff v := by
    funext v
    simp [D, PassageData.downSpeed, clockPassageData]
  have hDb : D.base = 205 := rfl
  have hd : ContDiff ℝ ∞ D.downSpeed :=
    hDd ▸ (contDiff_const.sub contDiff_g).add (contDiff_const.mul contDiff_cutoff)
  have hu : ContDiff ℝ ∞ (fun v ↦ D.g v + 1) := hDg ▸ contDiff_g.add contDiff_const
  have hdne : ∀ v ∈ Icc (0 : ℝ) 210, D.downSpeed v ≠ 0 := fun v hv ↦
    hDd ▸ (lower_denominator_pos hv.1 hv.2).ne'
  have hune : ∀ v ∈ Icc (0 : ℝ) 210, D.g v + 1 ≠ 0 := fun v _ ↦
    hDg ▸ (add_pos_of_nonneg_of_pos (g_nonneg v) zero_lt_one).ne'
  obtain ⟨εm, hεm, ηm, hηm, hsepm, hclosedm, hatm⟩ :=
    PDE.Analysis.exists_contDiffAt_intervalIntegral_reciprocal_affine_of_slack
      (n := ⊤) (d := D.downSpeed) (c := fun v : ℝ ↦ v)
      (a := 0) (b := 210) (base := 0) (y₀ := 205) (y₁ := 2051 / 10)
      hd.contDiffOn contDiff_id.contDiffOn
      (by constructor <;> norm_num) (by constructor <;> norm_num) (by constructor <;> norm_num) hdne
  obtain ⟨εp, hεp, ηp, hηp, hsepp, hclosedp, hatp⟩ :=
    PDE.Analysis.exists_contDiffAt_intervalIntegral_reciprocal_affine_of_slack
      (n := ⊤) (d := fun v ↦ D.g v + 1) (c := fun v : ℝ ↦ -v)
      (a := 0) (b := 210) (base := 205) (y₀ := 205) (y₁ := 2051 / 10)
      hu.contDiffOn contDiff_id.neg.contDiffOn
      (by constructor <;> norm_num) (by constructor <;> norm_num) (by constructor <;> norm_num) hune
  let ε := min εm εp
  have hmclosed : Icc (-ε) ε ⊆ Icc (-εm) εm :=
    Icc_subset_Icc (neg_le_neg (min_le_left εm εp)) (min_le_left εm εp)
  have hpclosed : Icc (-ε) ε ⊆ Icc (-εp) εp :=
    Icc_subset_Icc (neg_le_neg (min_le_right εm εp)) (min_le_right εm εp)
  have hmopen : Ioo (-ε) ε ⊆ Ioo (-εm) εm :=
    Ioo_subset_Ioo (neg_le_neg (min_le_left εm εp)) (min_le_left εm εp)
  have hpopen : Ioo (-ε) ε ⊆ Ioo (-εp) εp :=
    Ioo_subset_Ioo (neg_le_neg (min_le_right εm εp)) (min_le_right εm εp)
  refine ⟨ε, lt_min hεm hεp, min ηm ηp, lt_min hηm hηp, fun μ hμ v hv ↦
    ⟨(min_le_left ηm ηp).trans (hsepm μ (hmclosed hμ) v hv), by
      simpa only [mul_neg, sub_eq_add_neg] using
        (min_le_right ηm ηp).trans (hsepp μ (hpclosed hμ) v hv)⟩, ?_, fun μ hμ y hy ↦ ?_⟩
  · have hm : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ ↦ D.downRemaining q.1 q.2)
        (Ioo (-ε) ε ×ˢ Icc (0 : ℝ) 210) := by
      simpa only [PassageData.downRemaining] using hclosedm.mono (prod_mono hmopen subset_rfl)
    have hp : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ ↦ D.upPassageIntegral q.1 q.2)
        (Ioo (-ε) ε ×ˢ Icc (0 : ℝ) 210) := by
      simpa only [PassageData.upPassageIntegral, hDb, mul_neg, sub_eq_add_neg] using
        hclosedp.mono (prod_mono hpopen subset_rfl)
    exact hm.prodMk hp
  · have hy' : y ∈ uIcc (205 : ℝ) (2051 / 10) := mem_uIcc_of_le hy.1 hy.2
    have hm : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ ↦ D.downRemaining q.1 q.2) (μ, y) := by
      simpa only [PassageData.downRemaining] using hatm μ (hmopen hμ) y hy'
    have hp : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ ↦ D.upPassageIntegral q.1 q.2) (μ, y) := by
      simpa only [PassageData.upPassageIntegral, hDb, mul_neg, sub_eq_add_neg] using
        hatp μ (hpopen hμ) y hy'
    exact hm.prodMk hp

/-- The same supplied smooth event maps give one open parameter neighborhood
for joint smoothness of the lower travel duration, upper passage time, and integral weights.
The quantified gate is closed, so this includes ordinary regularity at 205 and 205.1.
No regularity of the target integrals or weights is an assumption. -/
theorem exists_contDiffAt_parameterizedClockPassageData (L Bhit : ℝ × ℝ → ℝ) {N : Set (ℝ × ℝ)}
    (hN : IsOpen N) (h0 : (0, 0) ∈ N) (hL : ContDiffOn ℝ ∞ L N) (hBhit : ContDiffOn ℝ ∞ Bhit N) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (0, 0) ∈ U ∧ U ⊆ N ∧
      ∀ p ∈ U, ∀ y ∈ Icc (205 : ℝ) (2051 / 10),
        ContDiffAt ℝ ∞
          (fun q : (ℝ × ℝ) × ℝ ↦
            ((parameterizedClockPassageData L Bhit q.1).downTime q.2,
             (parameterizedClockPassageData L Bhit q.1).tPlus q.2)) (p, y) ∧
        ContDiffAt ℝ ∞
          (fun q : (ℝ × ℝ) × ℝ ↦
            ((parameterizedClockPassageData L Bhit q.1).wMinus q.2,
             (parameterizedClockPassageData L Bhit q.1).wPlus q.2)) (p, y) := by
  obtain ⟨ε, hε, η, hη, hsep, _hclosed, hat⟩ :=
    exists_parameterizedClockPassageData_integral_tube L Bhit
  let U : Set (ℝ × ℝ) := N ∩ Prod.fst ⁻¹' Ioo (-ε) ε
  have hU : IsOpen U := hN.inter (isOpen_Ioo.preimage continuous_fst)
  have h0U : (0, 0) ∈ U := ⟨h0, neg_lt_zero.mpr hε, hε⟩
  refine ⟨U, hU, h0U, inter_subset_left, fun p hp y hy ↦ ?_⟩
  have hi : ContDiffAt ℝ ∞ (fun q : (ℝ × ℝ) × ℝ ↦
        ((parameterizedClockPassageData L Bhit (0, 0)).downRemaining q.1.1 q.2,
         (parameterizedClockPassageData L Bhit (0, 0)).upPassageIntegral q.1.1 q.2))
      (p, y) := by
    simpa only [Function.comp_def] using (hat p.1 hp.2 y hy).comp (p, y)
        (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  have hBp : ContDiffAt ℝ ∞ (fun q : (ℝ × ℝ) × ℝ ↦ Bhit q.1) (p, y) :=
    (hBhit.contDiffAt (hN.mem_nhds hp.1)).fst'
  have hmEq : (fun q : (ℝ × ℝ) × ℝ ↦ (parameterizedClockPassageData L Bhit q.1).downTime q.2) =
      (fun q : (ℝ × ℝ) × ℝ ↦
        (parameterizedClockPassageData L Bhit (0, 0)).downRemaining q.1.1 q.2) := by
    funext q
    rcases q with ⟨⟨μ, a⟩, v⟩
    exact parameterizedClockPassageData_downTime L Bhit μ a v
  have hpEq : (fun q : (ℝ × ℝ) × ℝ ↦ (parameterizedClockPassageData L Bhit q.1).tPlus q.2) =
      (fun q : (ℝ × ℝ) × ℝ ↦ Bhit q.1 +
        (parameterizedClockPassageData L Bhit (0, 0)).upPassageIntegral q.1.1 q.2) := by
    funext q
    rcases q with ⟨⟨μ, a⟩, v⟩
    exact parameterizedClockPassageData_tPlus L Bhit μ a v
  have hm : ContDiffAt ℝ ∞
      (fun q : (ℝ × ℝ) × ℝ ↦ (parameterizedClockPassageData L Bhit q.1).downTime q.2)
      (p, y) := hmEq ▸ hi.fst
  have ht : ContDiffAt ℝ ∞
      (fun q : (ℝ × ℝ) × ℝ ↦ (parameterizedClockPassageData L Bhit q.1).tPlus q.2)
      (p, y) := hpEq ▸ hBp.add hi.snd
  have hg : ContDiffAt ℝ ∞ (fun q : (ℝ × ℝ) × ℝ ↦ (parameterizedClockPassageData L Bhit q.1).g q.2)
      (p, y) := by
    change ContDiffAt ℝ ∞ (fun q : (ℝ × ℝ) × ℝ ↦ g q.2 - q.1.1 * q.2) (p, y)
    exact (contDiff_g.contDiffAt.comp (p, y) contDiffAt_snd).sub
      (contDiffAt_fst.fst.mul contDiffAt_snd)
  have hb := hsep p.1 (Ioo_subset_Icc_self hp.2) y ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hdenm : 4 - (parameterizedClockPassageData L Bhit p).g y ≠ 0 := by
    have hn := abs_pos.mp (hη.trans_le hb.1)
    have heq : (parameterizedClockPassageData L Bhit (0, 0)).downSpeed y + p.1 * y =
        4 - (parameterizedClockPassageData L Bhit p).g y := by
      simp only [PassageData.downSpeed,
        clockPassageData, parameterizedClockPassageData, cutoff_of_ge hy.1, mul_zero, add_zero]
      ring
    exact heq ▸ hn
  have hdenp : (parameterizedClockPassageData L Bhit p).g y + 1 ≠ 0 := by
    have hn := abs_pos.mp (hη.trans_le hb.2)
    have heq : (parameterizedClockPassageData L Bhit (0, 0)).g y + 1 - p.1 * y =
        (parameterizedClockPassageData L Bhit p).g y + 1 := by
      simp only [clockPassageData, parameterizedClockPassageData]
      ring
    exact heq ▸ hn
  have hwm : ContDiffAt ℝ ∞
      (fun q : (ℝ × ℝ) × ℝ ↦ (parameterizedClockPassageData L Bhit q.1).wMinus q.2)
      (p, y) := by
    simp only [PassageData.wMinus_eq_downTime]
    exact (contDiffAt_const.mul hm).exp.div (contDiffAt_const.sub hg) hdenm
  have hwp : ContDiffAt ℝ ∞
      (fun q : (ℝ × ℝ) × ℝ ↦ (parameterizedClockPassageData L Bhit q.1).wPlus q.2)
      (p, y) := by
    unfold PassageData.wPlus
    exact (contDiffAt_const.mul (((hL.contDiffAt (hN.mem_nhds hp.1)).fst').sub ht)).exp.div
      (hg.add contDiffAt_const) hdenp
  exact ⟨hm.prodMk ht, hwm.prodMk hwp⟩

/-- A closed-product formulation for subsequent fixed-interval integration.
Both maps use the same open parameter neighborhood and the same supplied events.
The stronger ordinary endpoint regularity is provided by the preceding theorem. -/
theorem exists_contDiffOn_parameterizedClockPassageData (L Bhit : ℝ × ℝ → ℝ) {N : Set (ℝ × ℝ)}
    (hN : IsOpen N) (h0 : (0, 0) ∈ N) (hL : ContDiffOn ℝ ∞ L N) (hBhit : ContDiffOn ℝ ∞ Bhit N) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (0, 0) ∈ U ∧ U ⊆ N ∧
      ContDiffOn ℝ ∞
        (fun q : (ℝ × ℝ) × ℝ ↦
          ((parameterizedClockPassageData L Bhit q.1).downTime q.2,
           (parameterizedClockPassageData L Bhit q.1).tPlus q.2))
        (U ×ˢ Icc (205 : ℝ) (2051 / 10)) ∧
      ContDiffOn ℝ ∞
        (fun q : (ℝ × ℝ) × ℝ ↦
          ((parameterizedClockPassageData L Bhit q.1).wMinus q.2,
           (parameterizedClockPassageData L Bhit q.1).wPlus q.2))
        (U ×ˢ Icc (205 : ℝ) (2051 / 10)) := by
  obtain ⟨U, hU, h0U, hUN, hsmooth⟩ :=
    exists_contDiffAt_parameterizedClockPassageData L Bhit hN h0 hL hBhit
  refine ⟨U, hU, h0U, hUN, ?_, ?_⟩
  · exact fun q hq ↦ (hsmooth q.1 hq.1 q.2 hq.2).1.contDiffWithinAt
  · exact fun q hq ↦ (hsmooth q.1 hq.1 q.2 hq.2).2.contDiffWithinAt

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
