/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SignedPower.Deriv
public import
  PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.WeakCoupling.Trajectory
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.Truncation
import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.CompactData
import PDE.Hyperbolic.NonlinearWave.SmallData.Strauss.FreeWave
import CAS.ExactTactic

/-!
# C¹ signed-power trajectories from arbitrary compact Cauchy data

The full Kirchhoff field is the free input of a uniform cone contraction.
A compact C¹ cutoff first gives a trajectory and a regular retarded remainder.
A short-time bound keeps the trajectory inside the cutoff radius, so the
signed-power integral equation holds. Both initial traces are constructed.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory BoundedContinuousFunction PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData.Classical.LocalPower
open scoped Topology unitInterval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- A globally Lipschitz C¹ reaction and an arbitrary C¹ free field construct
one physical cone trajectory, with a C¹ remainder and a uniform remainder bound. -/
theorem exists_cone_trajectory_of_lipschitz {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {C : NNReal}
    (hLip : LipschitzWith C f) :
    ∃ T : ℝ, 0 < T ∧
      ∀ H : ℝ × ℝ^3 → ℝ, ContDiff ℝ 1 H → ∃ v a : ℝ × ℝ^3 → ℝ, ContDiffOn ℝ 1 v {p | |p.1| < T} ∧
      ContDiffOn ℝ 1 a {p | |p.1| < T} ∧ (∀ p : ℝ × ℝ^3, |p.1| < T → v p = H p + p.1 ^ 2 * a p) ∧
      (∀ p : ℝ × ℝ^3, |p.1| < T → a p = ∫ s : I, (1 - (s : ℝ)) * ((∫ ω : Direction,
        f (v (p.1 * (s : ℝ), p.2 + p.1 • ((1 - (s : ℝ)) • (ω : ℝ^3))))
        ∂((volume : Measure (ℝ^3)).toSphere)) / unitSphereArea 3)) ∧
      ∀ B : ℝ, 0 ≤ B → (∀ z, |f z| ≤ B) → ∀ p : ℝ × ℝ^3, |p.1| < T → |a p| ≤ ‖duhamelOperator‖ *
        B := by
  obtain ⟨T, hT, htrajectory⟩ := exists_weakCoupling_cone_trajectory_of_lipschitz hf hLip
  refine ⟨T, hT, ?_⟩
  intro H hH
  obtain ⟨v, a, hv, ha, heq, hrem, hbound, _, _⟩ :=
    htrajectory (fun z ↦ H z.2) (hH.comp contDiff_snd)
  have hslice : ContDiff ℝ 1 (fun p : ℝ × ℝ^3 ↦ ((1 : ℝ), p)) := contDiff_const.prodMk contDiff_id
  refine ⟨v 1, a 1, ?_, ?_, ?_, ?_, ?_⟩
  · exact hv.comp hslice.contDiffOn (fun _ hp ↦ by simpa only [mem_ofPred_eq, one_mul] using hp)
  · exact ha.comp hslice.contDiffOn (fun _ hp ↦ by simpa only [mem_ofPred_eq, one_mul] using hp)
  · intro p hp
    simpa only [one_mul] using heq 1 p (by simpa only [one_mul] using hp)
  · intro p hp
    exact hrem 1 p (by simpa only [one_mul] using hp)
  · intro B hB hfB p hp
    exact hbound B hB hfB 1 p (by simpa only [one_mul] using hp)

/-- Every signed real power of exponent at least one admits a C¹ integral
trajectory from a bounded C¹ free field. The cutoff is absent from the conclusion. -/
theorem exists_signedPower_cone_trajectory {r : ℝ} (hr : 1 ≤ r) {B : ℝ} (hB : 0 ≤ B) :
    ∃ T : ℝ, 0 < T ∧ T ≤ 1 ∧
      ∀ H : ℝ × ℝ^3 → ℝ, ContDiff ℝ 1 H → (∀ p : ℝ × ℝ^3, p.1 ∈ Icc 0 1 → |H p| ≤ B) →
        ∃ v a : ℝ × ℝ^3 → ℝ, ContDiffOn ℝ 1 v {p | |p.1| < T} ∧
      ContDiffOn ℝ 1 a {p | |p.1| < T} ∧ (∀ p : ℝ × ℝ^3, |p.1| < T → v p = H p + p.1 ^ 2 * a p) ∧
      (∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 T → |v p| < B + 1) ∧
      ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 T → a p = ∫ s : I, (1 - (s : ℝ)) * ((∫ ω : Direction,
        -Real.signedPower r (v (p.1 * (s : ℝ), p.2 + p.1 • ((1 - (s : ℝ)) • (ω : ℝ^3))))
        ∂((volume : Measure (ℝ^3)).toSphere)) / unitSphereArea 3) := by
  have hs (z : ℝ) : 0 ≤ z * Real.signedPower r z := by
    rw [Real.mul_signedPower_eq_abs_rpow hr]
    positivity
  obtain ⟨f, C, hf, hfc, hLip, hmatch, _⟩ := SignCondition.exists_sign_preserving_lipschitz_reaction
      (m := 1) (Real.contDiff_one_signedPower hr) one_ne_zero hs
      (show 0 < B + 2 by linarith)
  obtain ⟨M, hM⟩ := hf.continuous.bounded_above_of_compact_support hfc
  have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0)
  obtain ⟨T₀, hT₀, htrajectory⟩ := exists_cone_trajectory_of_lipschitz hf.neg hLip.neg
  have hc : Continuous (fun t : ℝ ↦ t ^ 2 * (‖duhamelOperator‖ * M)) := by fun_prop
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, t ^ 2 * (‖duhamelOperator‖ * M) < 1 :=
    hc.continuousAt.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhds_iff.mp hnear
  let T := min T₀ (min δ 1)
  have hT : 0 < T := lt_min hT₀ (lt_min hδ zero_lt_one)
  have hTT : T ≤ T₀ := min_le_left _ _
  have hTδ : T ≤ δ := (min_le_right _ _).trans (min_le_left _ _)
  have hT1 : T ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨T, hT, hT1, ?_⟩
  intro H hH hbound
  obtain ⟨v, a, hv, ha, heq, hrem, habound⟩ := htrajectory H hH
  have hva (p : ℝ × ℝ^3) (hp : p.1 ∈ Ico 0 T) : |v p| < B + 1 := by
    have hpt : |p.1| < T := by
      simpa only [abs_of_nonneg hp.1] using hp.2
    have hn : |a p| ≤ ‖duhamelOperator‖ * M := habound M hM0
      (fun z ↦ by simpa only [abs_neg, Real.norm_eq_abs] using hM z) p (hpt.trans_le hTT)
    have hsmall : p.1 ^ 2 * (‖duhamelOperator‖ * M) < 1 := hd (by
      simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hpt.trans_le hTδ)
    rw [heq p (hpt.trans_le hTT)]
    calc
      |H p + p.1 ^ 2 * a p| ≤ |H p| + p.1 ^ 2 * |a p| :=
        (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_of_nonneg (sq_nonneg p.1)])
      _ < B + 1 := by
        nlinarith [hbound p ⟨hp.1, hp.2.le.trans hT1⟩, mul_le_mul_of_nonneg_left hn (sq_nonneg p.1)]
  refine ⟨v, a, hv.mono (fun _ hp ↦ hp.trans_le hTT), ha.mono (fun _ hp ↦ hp.trans_le hTT),
    fun p hp ↦ heq p (hp.trans_le hTT), hva, ?_⟩
  intro p hp
  rw [hrem p (by simpa only [abs_of_nonneg hp.1] using hp.2.trans_le hTT)]
  refine integral_congr_ae (.of_forall fun s ↦ ?_)
  dsimp only
  congr 2
  refine integral_congr_ae (.of_forall fun ω ↦ ?_)
  have hbq := hva (physicalPoint p (rim s ω)) ⟨mul_nonneg hp.1 s.2.1,
    (mul_le_mul_of_nonneg_left s.2.2 hp.1).trans_lt (by simpa using hp.2)⟩
  exact congrArg Neg.neg (hmatch (show v (physicalPoint p (rim s ω)) ∈ Metric.closedBall 0 (B + 2)
    by rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]; linarith))

/-- Arbitrary compact C² displacement and C¹ velocity produce a C¹
signed-power integral trajectory and both ordinary Cauchy traces. -/
theorem exists_signedPower_trajectory_of_compact_data {r : ℝ} (hr : 1 ≤ r) {g h : ℝ^3 → ℝ}
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) (hgs : HasCompactSupport g)
    (hhs : HasCompactSupport h) :
    ∃ T : ℝ, 0 < T ∧ ∃ v a : ℝ × ℝ^3 → ℝ,
      ContDiffOn ℝ 1 v {p | |p.1| < T} ∧
      ContDiffOn ℝ 1 a {p | |p.1| < T} ∧
      (∀ x : ℝ^3, v (0, x) = g x) ∧
      (∀ x : ℝ^3, HasDerivAt (fun t ↦ v (t, x)) (h x) 0) ∧
      (∀ p : ℝ × ℝ^3, |p.1| < T →
        v p = cauchyFreeField g h p + p.1 ^ 2 * a p) ∧
      ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 T →
        a p = ∫ s : I, (1 - (s : ℝ)) *
          ((∫ ω : Direction,
            -Real.signedPower r
              (v (p.1 * (s : ℝ), p.2 + p.1 • ((1 - (s : ℝ)) • (ω : ℝ^3))))
              ∂((volume : Measure (ℝ^3)).toSphere)) / unitSphereArea 3) := by
  have hH := contDiff_one_cauchyFreeField hg hh
  obtain ⟨Rg, _, hgR⟩ := hgs.exists_pos_le_norm
  obtain ⟨Rh, _, hhR⟩ := hhs.exists_pos_le_norm
  let R := max Rg Rh
  have hsupport (t : ℝ) (ht : t ∈ Icc 0 1) (x : ℝ^3) (hx : x ∉ Metric.closedBall 0 (R + 1)) :
      spaceTimeUncurry (kirchhoffFormula g h) (timeSpaceCons t x) = 0 := by
    apply WaveEquation.SmallData.kirchhoffFormula_hasForwardSupport
      (hg.of_le (by norm_num)) hh.continuous (fun y hy ↦ hgR y ((le_max_left _ _).trans hy.le))
      (fun y hy ↦ hhR y ((le_max_right _ _).trans hy.le)) t ht.1 x
    have hx' : R + 1 < ‖x‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
    linarith [ht.2]
  have hHc : Continuous (spaceTimeUncurry (kirchhoffFormula g h)) := by
    have heq : spaceTimeUncurry (kirchhoffFormula g h) =
        cauchyFreeField g h ∘ timeSpaceContinuousLinearEquiv 3 := by
      funext z
      simp [cauchyFreeField, timeSpaceContinuousLinearEquiv_apply]
    rw [heq]
    exact hH.continuous.comp (timeSpaceContinuousLinearEquiv 3).continuous
  obtain ⟨B, hB, hbound⟩ := exists_bound_of_compact_slab hHc
    (isCompact_closedBall (0 : ℝ^3) (R + 1)) hsupport
  obtain ⟨T, hT, _, htrajectory⟩ := exists_signedPower_cone_trajectory hr hB
  obtain ⟨v, a, hv, ha, heq, _, hrem⟩ :=
    htrajectory (cauchyFreeField g h) hH (fun p hp ↦ hbound p.1 hp p.2)
  refine ⟨T, hT, v, a, hv, ha, ?_, ?_, heq, hrem⟩
  · intro x
    simpa only [zero_pow (by norm_num : 2 ≠ 0), zero_mul, add_zero,
      cauchyFreeField_initial_position] using heq (0, x) (by simpa using hT)
  · intro x
    have hnear : {p : ℝ × ℝ^3 | |p.1| < T} ∈ 𝓝 (0, x) :=
      (isOpen_lt continuous_fst.abs continuous_const).mem_nhds (by simpa using hT)
    have hac : ContDiffAt ℝ 1 (fun t : ℝ ↦ a (t, x)) 0 :=
      (ha.contDiffAt hnear).comp 0 (contDiffAt_id.prodMk contDiffAt_const)
    have hd := (hasDerivAt_cauchyFreeField_initial_velocity hg hh x).fun_add
      (((hasDerivAt_id (0 : ℝ)).fun_pow 2).fun_mul (hac.differentiableAt one_ne_zero).hasDerivAt)
    have htrace : HasDerivAt
        (fun t : ℝ ↦ cauchyFreeField g h (t, x) + t ^ 2 * a (t, x)) (h x) 0 := by
      simpa using hd
    apply htrace.congr_of_eventuallyEq
    filter_upwards [(continuous_id.prodMk continuous_const).continuousAt.eventually hnear] with t ht
    exact heq (t, x) ht

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
