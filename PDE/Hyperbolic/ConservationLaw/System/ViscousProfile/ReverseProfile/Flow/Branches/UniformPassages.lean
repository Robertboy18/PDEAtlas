/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flow.Branches.Coverage
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flow.Branches.Geometry
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Weights.ParameterVariation

import CAS.ExactTactic

/-!
# Uniform passages for the prescribed clock datum

One common parameter neighborhood identifies both integral passage times with
levels of the supplied flow on the whole closed gate. The upward branch uses the
supplied `Bhit` anchor; the lower branch ends at the supplied zero `L p`.
The datum is the `parameterizedClockPassageData L Bhit p` throughout.

Reference brackets remain explicit inputs. The proof combines the compact branch
geometry with the oriented primitive identities.
Uniqueness is within each stated branch.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

open Gate.Weights MiddleClock

/-- On one smaller open neighborhood, every closed gate level is attained at the
datum's two explicit passage times, uniquely within the respective
branches of the same supplied flow. The lower branch ends at its `L p`.
The reference-only hypotheses are those of the branch geometry theorem. -/
theorem exists_prescribed_speed_uniform_passages {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {N : Set (ℝ × ℝ)}
    {L Bhit : ℝ × ℝ → ℝ} {A B τ0 sUp eUp sDown : ℝ} (hAB : A ^ 2 < B ^ 2) (hFcont : Continuous F)
    (hN : IsOpen N) (hbase : (0, 0) ∈ N) (hμ : ∀ p ∈ N, |p.1| < 1 / 410)
    (hODE : ∀ p ∈ N, ∀ t ∈ Icc (-1 : ℝ) (τ0 + 1),
      HasDerivAt (fun u ↦ F (u, p)) (prescribedSpeedField A B (p.1, F (t, p))) t)
    (hL : ContinuousOn L N) (hBhit : ContinuousOn Bhit N) (hLbase : L (0, 0) = τ0)
    (hBbase : Bhit (0, 0) ∈ Ioo sUp eUp) (hzero : ∀ p ∈ N, (F (L p, p)).1 = 0)
    (hhit : ∀ p ∈ N, (F (Bhit p, p)).1 = 205) (hupTime : -1 ≤ sUp ∧ eUp ≤ τ0 + 1)
    (hdownTime : -1 ≤ sDown ∧ sDown < τ0)
    (hrefUp : ∀ t ∈ Icc sUp eUp, (F (t, (0, 0))).1 ∈ Ioo (0 : ℝ) 210 ∧ 2 < (F (t, (0, 0))).2 ∧
      (F (t, (0, 0))).2 ^ 2 < A ^ 2)
    (hrefDown : ∀ t ∈ Icc sDown τ0, (F (t, (0, 0))).1 ∈ Ico (0 : ℝ) 210 ∧ B ^ 2 <
      (F (t, (0, 0))).2 ^ 2)
    (hrefStartUp : (F (sUp, (0, 0))).1 < 205) (hrefEndUp : (2051 / 10 : ℝ) < (F (eUp, (0, 0))).1)
    (hrefStartDown : (2051 / 10 : ℝ) < (F (sDown, (0, 0))).1) :
    ∃ N' : Set (ℝ × ℝ), IsOpen N' ∧ (0, 0) ∈ N' ∧ N' ⊆ N ∧
      ∀ p ∈ N', ∀ y ∈ Icc (205 : ℝ) (2051 / 10),
        let Dp := parameterizedClockPassageData L Bhit p
        (Dp.tPlus y ∈ Icc sUp eUp ∧ (F (Dp.tPlus y, p)).1 = y ∧
          ∀ t ∈ Icc sUp eUp, (F (t, p)).1 = y ↔ t = Dp.tPlus y) ∧
        (Dp.tMinus y ∈ Icc sDown (L p) ∧ (F (Dp.tMinus y, p)).1 = y ∧
          ∀ t ∈ Icc sDown (L p), (F (t, p)).1 = y ↔ t = Dp.tMinus y) := by
  obtain ⟨eDown, N', heDown, hN', hbase', hsub, hgeometry⟩ :=
    exists_prescribed_speed_branch_neighborhood hAB hFcont hN hbase hμ hODE hL hBhit
      hLbase hBbase hzero hdownTime hrefUp hrefDown hrefStartUp hrefEndUp hrefStartDown
  have hupSlab : Icc sUp eUp ⊆ Icc (-1 : ℝ) (τ0 + 1) := Icc_subset_Icc hupTime.1 hupTime.2
  refine ⟨N', hN', hbase', hsub, fun p hp y hy ↦ ?_⟩
  have hpN : p ∈ N := hsub hp
  obtain ⟨hb, hl, hup, hstartUp, hendUp, hdown, hstartDown, _hanti, hband⟩ := hgeometry p hp
  -- The completed-switch tube extends farther than the nonnegative lower branch.
  have hdownTube : Icc sDown (L p) ⊆ Icc sDown eDown := Icc_subset_Icc le_rfl hl.2.le
  have hdownSlab : Icc sDown (L p) ⊆ Icc (-1 : ℝ) (τ0 + 1) :=
    Icc_subset_Icc hdownTime.1 (hl.2.trans heDown.2).le
  have hendDown : (F (L p, p)).1 ≤ (205 : ℝ) := by
    rw [hzero p hpN]
    cas
  have hupPassage := prescribed_speed_up_gate_coverage
    (F := F) (A := A) (B := B) (p := p) (s := sUp) (e := eUp) (b₀ := Bhit p)
    hAB (hμ p hpN) (fun t ht ↦ hODE p hpN t (hupSlab ht))
    (fun t ht ↦ (hup t ht).2.1) (fun t ht ↦ (hup t ht).2.2)
    (fun t ht ↦ Ioo_subset_Icc_self (hup t ht).1)
    (Ioo_subset_Icc_self hb) (hhit p hpN) hstartUp.le hendUp.le y hy
  have hdownPassage := prescribed_speed_down_gate_coverage
    (F := F) (A := A) (B := B) (p := p) (s := sDown) (e := L p) (τ := L p)
    hAB (hμ p hpN) (fun t ht ↦ hODE p hpN t (hdownSlab ht))
    (fun t ht ↦ (hdown t (hdownTube ht)).2) hband
    ⟨hl.1.le, le_rfl⟩ (hzero p hpN) hstartDown.le hendDown y hy
  -- Datum identities normalize the oriented integrals in the coverage results.
  have htPlus : (parameterizedClockPassageData L Bhit p).tPlus y =
      Bhit p + (∫ v in (205 : ℝ)..y, 1 / (g v + 1 - p.1 * v)) := by
    rcases p with ⟨μ, a⟩
    rw [parameterizedClockPassageData_tPlus]
    simp only [PassageData.upPassageIntegral, parameterizedClockPassageData,
      clockPassageData, zero_mul, sub_zero]
  have htMinus : (parameterizedClockPassageData L Bhit p).tMinus y =
      L p - (∫ v in (0 : ℝ)..y, 1 / (4 - g v + 4 * cutoff v + p.1 * v)) := by
    rcases p with ⟨μ, a⟩
    unfold PassageData.tMinus
    rw [parameterizedClockPassageData_downTime]
    simp only [PassageData.downRemaining, PassageData.downSpeed,
      parameterizedClockPassageData, clockPassageData, zero_mul, sub_zero]
  refine ⟨?_, ?_⟩
  · simpa only [htPlus] using hupPassage
  · simpa only [htMinus] using hdownPassage

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
