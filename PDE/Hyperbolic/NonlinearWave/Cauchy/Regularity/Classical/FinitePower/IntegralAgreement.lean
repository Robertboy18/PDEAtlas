/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.ConeTrajectory
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.LocalUniqueness
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.TimeExtension
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.Formula

/-!
# Finite regularity of the bounded integral trajectory near time zero

Short-cone uniqueness identifies a continuous bounded trajectory
with the C² cone construction for exponents above two. Only the forward
trace is identified: an arbitrary negative-time extension is not upgraded.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData.Classical.LocalPower
open PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
open scoped Topology unitInterval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

/-- The bounded continuous integral trajectory for an exponent above
two agrees near time zero with a jointly C² representative. In particular,
the original trajectory is C² on a positive open strip. -/
theorem exists_c2_representative_of_bounded_integral_eq {r b L B M : ℝ} (hr : 2 < r) (hb : 0 < b)
    (hL : 0 < L) (hB : 0 ≤ B) (hM : 0 ≤ M) {H v : ℝ × ℝ^3 → ℝ} (hH : ContDiff ℝ 2 H)
    (hHB : ∀ p : ℝ × ℝ^3, p.1 ∈ Icc 0 1 → |H p| ≤ B) (hv : ContinuousOn v {p | -b < p.1 ∧ p.1 < L})
    (hvM : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → |v p| ≤ M)
    (hveq : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → v p = H p + oddDuhamelSolution 0 (fun z : ℝ^4 ↦
      -Real.signedPower r (v (timeSpaceContinuousLinearEquiv 3 z))) (timeSpaceCons p.1 p.2)) :
    ∃ S : ℝ, 0 < S ∧ S ≤ L ∧ ∃ V : ℝ × ℝ^3 → ℝ, ContDiff ℝ 2 V ∧
      (∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 S → V p = v p) ∧ ContDiffOn ℝ 2 v {p | 0 < p.1 ∧ p.1 < S} := by
  obtain ⟨T, hT, _, hconstruct⟩ := exists_c2_signedPower_cone_trajectory hr hB
  obtain ⟨w, a, hw, _, hweq, hwB, hrem⟩ := hconstruct H hH hHB
  obtain ⟨A, hA, hAT, V, hV, hVeq⟩ := exists_time_extension hT hw
  let N := max M (B + 1)
  have hN : 0 ≤ N := hM.trans (le_max_left _ _)
  have hc : Continuous
      (fun t : ℝ ↦ t ^ 2 * ‖duhamelOperator‖ * ((2 * r) * (2 * N) ^ (r - 1))) := by
    fun_prop
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, t ^ 2 * ‖duhamelOperator‖ * ((2 * r) * (2 * N) ^ (r - 1)) < 1 :=
    hc.continuousAt.eventually (gt_mem_nhds (by simp))
  obtain ⟨δ, hδ, hsmall⟩ := Metric.mem_nhds_iff.mp hnear
  let S := min b (min L (min A δ))
  have hS : 0 < S := lt_min hb (lt_min hL (lt_min hA hδ))
  have hSb : S ≤ b := min_le_left _ _
  have hSL : S ≤ L := (min_le_right _ _).trans (min_le_left _ _)
  have hSA : S ≤ A := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSδ : S ≤ δ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hST : S ≤ T := hSA.trans hAT.le
  have hvS : ContinuousOn v {p : ℝ × ℝ^3 | |p.1| < S} := by
    refine hv.mono fun p hp ↦ ?_
    have ht := abs_lt.mp (show |p.1| < S from hp)
    exact ⟨by linarith [ht.1], ht.2.trans_le hSL⟩
  have hwS : ContinuousOn w {p : ℝ × ℝ^3 | |p.1| < S} :=
    hw.continuousOn.mono (fun _ hp ↦ hp.trans_le hST)
  have hagree (p : ℝ × ℝ^3) (hp : p.1 ∈ Ico 0 S) : v p = w p := by
    apply eq_of_bounded_signedPower_integral_eq (by linarith : 1 ≤ r) hN hvS hwS ⟨H, hH.continuous⟩
      (fun q hq ↦ (hvM q ⟨hq.1, hq.2.trans_le hSL⟩).trans (le_max_left _ _))
      (fun q hq ↦ (hwB q ⟨hq.1, hq.2.trans_le hST⟩).le.trans (le_max_right _ _)) hp
      (hsmall (by
        simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs,
          abs_of_nonneg hp.1] using hp.2.trans_le hSδ))
    · intro q hq
      have he := hveq q ⟨hq.1, hq.2.trans_le hSL⟩
      rw [oddDuhamelSolution_zero_eq_normalized _ q.2 hq.1] at he
      simpa only [timeSpaceContinuousLinearEquiv_apply, PDE.time, timeSpaceCons_zero,
        spatialPart_timeSpaceCons, ContinuousMap.coe_mk] using he
    · intro q hq
      rw [hweq q (by simpa only [abs_of_nonneg hq.1] using hq.2.trans_le hST),
        hrem q ⟨hq.1, hq.2.trans_le hST⟩]
      rfl
  have hmatch (p : ℝ × ℝ^3) (hp : p.1 ∈ Ico 0 S) : V p = v p :=
    (hVeq p (by simpa only [abs_of_nonneg hp.1] using hp.2.trans_le hSA)).trans (hagree p hp).symm
  refine ⟨S, hS, hSL, V, hV, hmatch, ?_⟩
  exact hV.contDiffOn.congr fun p hp ↦ (hmatch p ⟨hp.1.le, hp.2⟩).symm

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower
