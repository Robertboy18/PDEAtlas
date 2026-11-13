/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.IntegralUniqueness
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Continuation

/-!
# C² persistence along the bounded integral trajectory

A local C² germ propagates through every finite interval where the
C¹ signed-power integral trajectory stays bounded. At the supremum of the
regularity interval, retarded continuation constructs a C² extension;
bounded C¹ uniqueness identifies it with the original trajectory. The
argument uses no terminal derivative trace or bound on higher derivatives.
-/

@[expose] public noncomputable section

open Set Filter PDE.Analysis PDE.Common WaveEquation
open PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

/-- An initial C² band persists for the bounded C¹ integral trajectory
throughout any finite lifespan, for every real exponent above two. -/
theorem contDiffOn_two_of_initial_signedPower_integral_eq {r b L B M S : ℝ} (hr : 2 < r)
    (hb : 0 < b) (hS : 0 < S) {u H : ℝ × ℝ^3 → ℝ}
    (hu : ContDiffOn ℝ 1 u {p | -b < p.1 ∧ p.1 < L})
    (hu₂ : ContDiffOn ℝ 2 u {p | -b < p.1 ∧ p.1 < S}) (hH : ContDiff ℝ 2 H)
    (hHB : ∀ p : ℝ × ℝ^3, p.1 ∈ Icc 0 (L + 1) → |H p| ≤ B)
    (huB : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → |u p| ≤ M)
    (hue : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → u p = H p + oddDuhamelSolution 0 (fun z : ℝ^4 ↦
      -Real.signedPower r (u (timeSpaceContinuousLinearEquiv 3 z))) (timeSpaceCons p.1 p.2)) :
    ContDiffOn ℝ 2 u {p | -b < p.1 ∧ p.1 < L} := by
  rcases le_or_gt L 0 with hL | hL
  · exact hu₂.mono fun p hp ↦ ⟨hp.1, hp.2.trans_le (hL.trans hS.le)⟩
  have hB : 0 ≤ B := (abs_nonneg _).trans (hHB ((0 : ℝ), (0 : ℝ^3)) ⟨le_rfl, by linarith⟩)
  have hM : 0 ≤ M := (abs_nonneg _).trans (huB ((0 : ℝ), (0 : ℝ^3)) ⟨le_rfl, hL⟩)
  let A : Set ℝ := {t | 0 < t ∧ t ≤ L ∧ ContDiffOn ℝ 2 u {p | -b < p.1 ∧ p.1 < t}}
  have hstart : min S L ∈ A := ⟨lt_min hS hL, min_le_right _ _,
    hu₂.mono (fun p hp ↦ ⟨hp.1, hp.2.trans_le (min_le_left _ _)⟩)⟩
  have hA : A.Nonempty := ⟨_, hstart⟩
  have hAb : BddAbove A := ⟨L, fun _ ht ↦ ht.2.1⟩
  let T := sSup A
  have hT : 0 < T := hstart.1.trans_le (le_csSup hAb hstart)
  have hTL : T ≤ L := csSup_le hA (fun _ ht ↦ ht.2.1)
  have huT : ContDiffOn ℝ 2 u {p | -b < p.1 ∧ p.1 < T} := by
    intro p hp
    obtain ⟨a, ha, hpa⟩ := (lt_csSup_iff hAb hA).mp hp.2
    exact ((ha.2.2).contDiffAt (((isOpen_lt continuous_const continuous_fst).inter
        (isOpen_lt continuous_fst continuous_const)).mem_nhds ⟨hp.1, hpa⟩)).contDiffWithinAt
  suffices hLT : L ≤ T from huT.mono (fun p hp ↦ ⟨hp.1, hp.2.trans_le hLT⟩)
  by_contra hnot
  have hlt : T < L := lt_of_not_ge hnot
  obtain ⟨T', M', hTT', hM', w, hw, hwold, hwB, hwe⟩ :=
    exists_c2_signedPower_integral_extension_of_bounded hr hb hT hB hM huT hH
      (fun p hp ↦ hHB p ⟨hp.1, hp.2.trans (by linarith)⟩)
      (fun p hp ↦ huB p ⟨hp.1, hp.2.trans_le hTL⟩) (fun p hp ↦ hue p ⟨hp.1, hp.2.trans_le hTL⟩)
  let D := min L T'
  have hTD : T < D := lt_min hlt hTT'
  have hDL : D ≤ L := min_le_left _ _
  have hDT : D ≤ T' := min_le_right _ _
  have hwD : ContDiffOn ℝ 2 w {p | -b < p.1 ∧ p.1 < D} :=
    hw.mono (fun p hp ↦ ⟨hp.1, hp.2.trans_le hDT⟩)
  have heq (p : ℝ × ℝ^3) (hp : p.1 ∈ Ico 0 D) : u p = w p := by
    apply eq_on_forward_interval_of_bounded_signedPower_integral_eq
      (by linarith : 1 ≤ r) hb (show 0 ≤ max M M' from hM.trans (le_max_left _ _))
      (hu.mono (fun p hp ↦ ⟨hp.1, hp.2.trans_le hDL⟩))
      (hwD.of_le (by norm_num)) (hH.of_le (by norm_num))
      (fun p hp ↦ (huB p ⟨hp.1, hp.2.trans_le hDL⟩).trans (le_max_left _ _))
      (fun p hp ↦ (hwB p ⟨hp.1, hp.2.trans_le hDT⟩).trans (le_max_right _ _))
      (fun p hp ↦ hue p ⟨hp.1, hp.2.trans_le hDL⟩) (fun p hp ↦ hwe p ⟨hp.1, hp.2.trans_le hDT⟩) p hp
  have huD : ContDiffOn ℝ 2 u {p | -b < p.1 ∧ p.1 < D} := by
    refine hwD.congr fun p hp ↦ ?_
    by_cases hp0 : 0 ≤ p.1
    · exact heq p ⟨hp0, hp.2⟩
    · exact (hwold ⟨hp.1, (lt_of_not_ge hp0).trans hT⟩).symm
  have hDmem : D ∈ A := ⟨hT.trans hTD, hDL, huD⟩
  exact (not_lt_of_ge (le_csSup hAb hDmem)) hTD

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower
