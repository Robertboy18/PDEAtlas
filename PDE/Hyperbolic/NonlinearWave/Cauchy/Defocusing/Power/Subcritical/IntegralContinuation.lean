/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RetardedOverlap
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RetardedRestart
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Constructed continuation of bounded C¹ signed-power integral trajectories

A bounded trajectory before a finite terminal time extends past that time.
The proof constructs a uniformly long future cone solution at a nearby anchor,
identifies both branches by bounded cone uniqueness, and glues inside the
open overlap.

This is a continuation theorem for C¹ integral trajectories.
-/

@[expose] public noncomputable section

open Set Filter PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData.Classical.LocalPower
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- A bounded C¹ signed-power integral trajectory before a finite time has a
bounded C¹ integral extension beyond it, preserving the entire old trajectory.
The new amplitude bound is supplied by the constructed future branch. The
construction uses no bound on derivatives and no terminal trace. -/
theorem exists_signedPower_integral_extension_of_bounded {r b L B M : ℝ}
    (hr : 1 ≤ r) (hb : 0 < b) (hL : 0 < L) (hB : 0 ≤ B) (hM : 0 ≤ M)
    {u H : ℝ × ℝ^3 → ℝ}
    (hu : ContDiffOn ℝ 1 u {p | -b < p.1 ∧ p.1 < L}) (hH : ContDiff ℝ 1 H)
    (hHB : ∀ p : ℝ × ℝ^3, p.1 ∈ Icc 0 (L + 1) → |H p| ≤ B)
    (huB : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → |u p| ≤ M)
    (hue : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L →
      u p = H p + oddDuhamelSolution 0
        (fun z : ℝ^4 ↦ -Real.signedPower r (u (timeSpaceContinuousLinearEquiv 3 z)))
        (timeSpaceCons p.1 p.2)) :
    ∃ L' M' : ℝ, L < L' ∧ 0 ≤ M' ∧ ∃ w : ℝ × ℝ^3 → ℝ,
      ContDiffOn ℝ 1 w {p | -b < p.1 ∧ p.1 < L'} ∧
      EqOn w u {p | -b < p.1 ∧ p.1 < L} ∧
      (∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L' → |w p| ≤ M') ∧
      ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L' →
        w p = H p + oddDuhamelSolution 0
          (fun z : ℝ^4 ↦ -Real.signedPower r (w (timeSpaceContinuousLinearEquiv 3 z)))
          (timeSpaceCons p.1 p.2) := by
  let A := B + L * (L + 1) * M ^ r
  let C := max M (A + 1)
  have hC : 0 ≤ C := hM.trans (le_max_left _ _)
  obtain ⟨T, hT, _, hconstruct⟩ := exists_signedPower_future_of_bounded_history hr
    hB (Real.rpow_nonneg hM r) hL.le
  have hc : Continuous (fun t : ℝ ↦
      t ^ 2 * ‖duhamelOperator‖ * ((2 * r) * (2 * C) ^ (r - 1))) := by fun_prop
  have hnear : ∀ᶠ t : ℝ in 𝓝 0,
      t ^ 2 * ‖duhamelOperator‖ * ((2 * r) * (2 * C) ^ (r - 1)) < 1 :=
    hc.continuousAt.eventually (gt_mem_nhds (by simp))
  obtain ⟨ε, hε, hsmall⟩ := Metric.mem_nhds_iff.mp hnear
  let δ := min T (min ε (L / 2))
  have hδ : 0 < δ := lt_min hT (lt_min hε (by positivity))
  have hδT : δ ≤ T := min_le_left _ _
  have hδε : δ ≤ ε := (min_le_right _ _).trans (min_le_left _ _)
  have hδL : δ ≤ L / 2 := (min_le_right _ _).trans (min_le_right _ _)
  let a := L - δ / 2
  have ha : 0 ≤ a := by dsimp only [a]; linarith
  have haL : a < L := by dsimp only [a]; linarith
  have haS : δ / 2 ≤ a + b := by dsimp only [a]; linarith
  obtain ⟨U, hU, hUeq⟩ := exists_contDiff_representative_on_initial_band hb hu haL
  let F : ℝ × ℝ^3 → ℝ := fun p ↦ -Real.signedPower r (U p)
  have hF : ContDiff ℝ 1 F := ((Real.contDiff_one_signedPower hr).comp hU).neg
  have hFpast (s : ℝ) (hs : s ∈ Icc 0 a) (x : ℝ^3) :
      F (s, x) = -Real.signedPower r (u (s, x)) := by
    rw [← hUeq (s, x) hs]
  have hFB (s : ℝ) (hs : s ∈ Icc 0 a) (x : ℝ^3) : |F (s, x)| ≤ M ^ r := by
    rw [hFpast s hs x, abs_neg, ← Real.norm_eq_abs, Real.norm_signedPower (zero_lt_one.trans_le hr)]
    exact Real.rpow_le_rpow (norm_nonneg _) (huB (s, x) ⟨hs.1, hs.2.trans_lt haL⟩)
      (zero_le_one.trans hr)
  obtain ⟨v, hv, _, _, hvB, hve⟩ := hconstruct a ⟨ha, haL.le⟩ H hH hHB F hF hFB
  have hmatch (p : ℝ × ℝ^3) (hp : p.1 ∈ Ico 0 (δ / 2)) :
      u (a + p.1, p.2) = v p := by
    apply eq_on_restart_overlap hr hb hC ha (by dsimp only [a]; linarith)
      (by linarith) haS hu hv hH hF hFpast
      (fun q hq ↦ (huB q hq).trans (le_max_left _ _))
      (fun q hq ↦ (hvB q hq).le.trans (le_max_right _ _)) hue hve hp
    apply hsmall
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hp.1]
    linarith [hp.2]
  let c := a + δ / 4
  have hac : a < c := by dsimp only [c]; linarith
  have hcL : c < L := by dsimp only [c, a]; linarith
  have hLT : L < a + T := by dsimp only [a]; linarith
  let w : ℝ × ℝ^3 → ℝ := fun p ↦ if p.1 < c then u p else v (p.1 - a, p.2)
  have hwold (p : ℝ × ℝ^3) (hp : p.1 < L) : w p = u p := by
    dsimp only [w]
    split_ifs with hpc
    · rfl
    simpa only [add_sub_cancel] using (hmatch (p.1 - a, p.2)
      ⟨by linarith, by dsimp only [a]; linarith⟩).symm
  have hwfuture (p : ℝ × ℝ^3) (hp : a ≤ p.1) : w p = v (p.1 - a, p.2) := by
    dsimp only [w]
    split_ifs with hpc
    · simpa only [add_sub_cancel] using
        hmatch (p.1 - a, p.2) ⟨sub_nonneg.mpr hp, by dsimp only [c] at hpc; linarith⟩
    · rfl
  have hw : ContDiffOn ℝ 1 w {p | -b < p.1 ∧ p.1 < a + T} := by
    intro p hp
    apply ContDiffAt.contDiffWithinAt
    by_cases hpl : p.1 < L
    · apply (hu.contDiffAt (((isOpen_lt continuous_const continuous_fst).inter
          (isOpen_lt continuous_fst continuous_const)).mem_nhds ⟨hp.1, hpl⟩)).congr_of_eventuallyEq
      filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hpl] with q hq
      exact hwold q hq
    · have hpa : a < p.1 := haL.trans_le (le_of_not_gt hpl)
      have hpt : |p.1 - a| < T := by rw [abs_of_pos (sub_pos.mpr hpa)]; linarith [hp.2]
      have hvp : ContDiffAt ℝ 1 v (p.1 - a, p.2) := hv.contDiffAt
        ((isOpen_lt continuous_fst.abs continuous_const).mem_nhds hpt)
      apply (hvp.comp p ((contDiffAt_fst.sub contDiffAt_const).prodMk
        contDiffAt_snd)).congr_of_eventuallyEq
      filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hpa] with q hq
      exact hwfuture q hq.le
  refine ⟨a + T, C, hLT, hC, w, hw, fun p hp ↦ hwold p hp.2, ?_, ?_⟩
  · intro p hp
    by_cases hpl : p.1 < L
    · rw [hwold p hpl]
      exact (huB p ⟨hp.1, hpl⟩).trans (le_max_left _ _)
    · have hpa : a ≤ p.1 := haL.le.trans (le_of_not_gt hpl)
      rw [hwfuture p hpa]
      exact (hvB (p.1 - a, p.2)
        ⟨sub_nonneg.mpr hpa, by linarith [hp.2]⟩).le.trans (le_max_right _ _)
  intro p hp
  by_cases hpl : p.1 < L
  · rw [hwold p hpl, hue p ⟨hp.1, hpl⟩]
    congr 1
    refine oddDuhamelSolution_congr_forward (F := fun q ↦ -Real.signedPower r (u q))
      (G := fun q ↦ -Real.signedPower r (w q)) p hp.1 fun s hs x ↦ ?_
    rw [hwold (s, x) (hs.2.trans_lt hpl)]
  · have hpa : 0 ≤ p.1 - a := by linarith [le_of_not_gt hpl]
    have hpt : p.1 - a < T := by linarith [hp.2]
    have he := hve (p.1 - a, p.2) ⟨hpa, hpt⟩
    rw [add_sub_cancel] at he
    rw [hwfuture p (by linarith)]
    have hW : ContDiffOn ℝ 1 (fun q ↦ -Real.signedPower r (w q))
        {q | -b < q.1 ∧ q.1 < a + T} :=
      ((Real.contDiff_one_signedPower hr).comp_contDiffOn hw).neg
    have hsplit := retarded_eq_history_add_shift_of_contDiffOn hb hW ha hpa
      (by simpa only [add_sub_cancel] using hp.2) p.2
    rw [add_sub_cancel] at hsplit
    have hhist : retardedHistory a F (p.1 - a, p.2) =
        retardedHistory a (fun q ↦ -Real.signedPower r (w q)) (p.1 - a, p.2) :=
      retardedHistory_congr ha (fun s hs x ↦ by
        rw [hFpast s hs x, hwold (s, x) (hs.2.trans_lt haL)]) _
    have hfuture : oddDuhamelSolution 0
        (fun z : ℝ^4 ↦ -Real.signedPower r (v (timeSpaceContinuousLinearEquiv 3 z)))
        (timeSpaceCons (p.1 - a) p.2) = oddDuhamelSolution 0
        (fun z : ℝ^4 ↦ -Real.signedPower r (w (a + z 0, spatialPartCLM 3 z)))
        (timeSpaceCons (p.1 - a) p.2) := by
      refine oddDuhamelSolution_congr_forward (F := fun q ↦ -Real.signedPower r (v q))
        (G := fun q ↦ -Real.signedPower r (w (a + q.1, q.2))) (p.1 - a, p.2) hpa fun s hs x ↦ ?_
      rw [hwfuture (a + s, x) (by linarith [hs.1]), add_sub_cancel_left]
    rw [he, hhist, hfuture, add_assoc, ← hsplit]

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
