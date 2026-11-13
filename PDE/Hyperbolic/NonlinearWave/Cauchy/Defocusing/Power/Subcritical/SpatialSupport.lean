/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.TrajectoryWeakEquation
import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.CompactData
import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RetardedRestart
import PDE.Hyperbolic.NonlinearWave.SmallData.Strauss.FreeWave
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Spatial support of signed-power integral trajectories

A backward cone outside the initial support sees zero free input. Cone
uniqueness against the zero solution then proves finite propagation directly
from the integral equation, without pointwise second derivatives or a classical
energy identity. The local construction can be shortened to satisfy the same
uniform cone absorption bound at every spatial center.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory BoundedContinuousFunction PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData.Classical.LocalPower
open WaveEquation.SmallData.Classical.LocalPower.LowerPower
open scoped Topology unitInterval Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- Every point of a backward cone beyond an outgoing support cone remains
beyond that support cone. -/
theorem add_time_lt_norm_physicalPoint {R : ℝ} {p : ℝ × ℝ^3} (hp : 0 ≤ p.1) (hx : R + p.1 < ‖p.2‖)
    (q : Cone) :
    R + (physicalPoint p q).1 < ‖(physicalPoint p q).2‖ := by
  have hdisp : ‖p.1 • coneSpace q‖ ≤ p.1 * (1 - coneTime q) := by
    rw [norm_smul, Real.norm_of_nonneg hp]
    exact mul_le_mul_of_nonneg_left (norm_coneSpace_le q) hp
  have hn := norm_sub_le (p.2 + p.1 • coneSpace q) (p.1 • coneSpace q)
  rw [add_sub_cancel_right] at hn
  change R + p.1 * coneTime q < ‖p.2 + p.1 • coneSpace q‖
  nlinarith

/-- A bounded integral trajectory vanishes outside the forward support of
its free field on every cone satisfying the amplitude absorption bound. -/
theorem eq_zero_of_supported_free_integral_eq {r T M R : ℝ} (hr : 1 ≤ r) (hM : 0 ≤ M)
    {u : ℝ × ℝ^3 → ℝ} (hu : ContinuousOn u {q | |q.1| < T}) (H : C(ℝ × ℝ^3, ℝ))
    (hsupport : ∀ q : ℝ × ℝ^3, 0 ≤ q.1 → R + q.1 < ‖q.2‖ → H q = 0)
    (hbound : ∀ q : ℝ × ℝ^3, q.1 ∈ Ico 0 T → |u q| ≤ M)
    (heq : ∀ q : ℝ × ℝ^3, q.1 ∈ Ico 0 T → u q = H q + q.1 ^ 2 * ∫ s : I,
      (1 - (s : ℝ)) * ((∫ ω : Direction, -Real.signedPower r
      (u (q.1 * (s : ℝ), q.2 + q.1 • ((1 - (s : ℝ)) • (ω : ℝ^3))))
      ∂((volume : Measure (ℝ^3)).toSphere)) / unitSphereArea 3))
    {p : ℝ × ℝ^3} (hp : p.1 ∈ Ico 0 T)
    (hsmall : p.1 ^ 2 * ‖duhamelOperator‖ * ((2 * r) * (2 * M) ^ (r - 1)) < 1)
    (hx : R + p.1 < ‖p.2‖) :
    u p = 0 := by
  let q : {q : ℝ × ℝ^3 | |q.1| < T} :=
    ⟨p, by change |p.1| < T; simpa only [abs_of_nonneg hp.1] using hp.2⟩
  let f : C(ℝ, ℝ) := ⟨fun z ↦ -Real.signedPower r z,
    (Real.continuous_signedPower (zero_lt_one.trans_le hr)).neg⟩
  have hcone : coneField H p = 0 := by
    ext z
    change coneField H p z = 0
    rw [coneField_apply]
    exact hsupport _ (mul_nonneg hp.1 (coneTime_mem z).1) (add_time_lt_norm_physicalPoint hp.1 hx z)
  have hnorm : ‖physicalCone hu q‖ ≤ M := by
    apply (BoundedContinuousFunction.norm_le hM).mpr
    intro z
    apply hbound
    exact ⟨mul_nonneg hp.1 (coneTime_mem z).1,
      (mul_le_mul_of_nonneg_left (coneTime_mem z).2 hp.1).trans_lt (by simpa using hp.2)⟩
  have hzero : composeCompact (α := Cone) f 0 = 0 := by
    ext z
    simp [f, composeCompact_apply, Real.signedPower]
  have hzeroeq : (0 : Cone →ᵇ ℝ) = coneField H p + p.1 ^ 2 •
      duhamelOperator (composeCompact f 0) := by
    rw [hcone, hzero, map_zero, smul_zero, add_zero]
  have he := eq_of_signedPower_cone_equations hr (coneField H p)
    (physicalCone hu q) 0 hnorm (by simpa using hM) hsmall
    (physicalCone_eq_of_free_integral_eq hu H f heq q hp.1) hzeroeq
  have hvtx := congrArg (fun w : Cone →ᵇ ℝ ↦ w vertex) he
  simpa only [physicalCone_apply, physicalPoint, vertex, coneTime, coneSpace,
    mul_one, smul_zero, add_zero, BoundedContinuousFunction.coe_zero, Pi.zero_apply] using hvtx

/-- Arbitrary compact C³ displacement and C² velocity construct a bounded C¹
signed-power trajectory with both Cauchy traces, finite propagation, and the
spatially tested PDE. The theorem does not assert the equation pointwise. -/
theorem exists_supported_signedPower_weak_trajectory_of_compact_data {r : ℝ} (hr : 1 ≤ r)
    {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) (hgs : HasCompactSupport g)
    (hhs : HasCompactSupport h) :
    ∃ T M R : ℝ, 0 < T ∧ 0 ≤ M ∧ ∃ u : ℝ × ℝ^3 → ℝ,
      ContDiffOn ℝ 1 u {p | |p.1| < T} ∧
      (∀ x : ℝ^3, u (0, x) = g x) ∧
      (∀ x : ℝ^3, HasDerivAt (fun t ↦ u (t, x)) (h x) 0) ∧
      (∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 T → |u p| ≤ M) ∧
      (∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 T → R + p.1 < ‖p.2‖ → u p = 0) ∧
      (∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 T →
        u p = cauchyFreeField g h p + oddDuhamelSolution 0
          (fun z : ℝ^4 ↦ -Real.signedPower r (u (timeSpaceContinuousLinearEquiv 3 z)))
          (timeSpaceCons p.1 p.2)) ∧
      ∀ φ : ℝ^3 → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
        ∀ t ∈ Ioo 0 T,
          HasDerivAt (deriv (fun s ↦ ∫ x : ℝ^3, u (s, x) * φ x))
            ((∫ x : ℝ^3, u (t, x) * laplacian φ x) -
              ∫ x : ℝ^3, Real.signedPower r (u (t, x)) * φ x) t := by
  have hg2 : ContDiff ℝ 2 g := hg.of_le (by norm_num)
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by norm_num)
  have hH := contDiff_one_cauchyFreeField hg2 hh1
  obtain ⟨Rg, _, hgR⟩ := hgs.exists_pos_le_norm
  obtain ⟨Rh, _, hhR⟩ := hhs.exists_pos_le_norm
  let R := max Rg Rh
  have hsupport (p : ℝ × ℝ^3) (hp : 0 ≤ p.1) (hx : R + p.1 < ‖p.2‖) :
      cauchyFreeField g h p = 0 := by
    exact WaveEquation.SmallData.kirchhoffFormula_hasForwardSupport
      (hg.of_le (by norm_num)) hh.continuous (fun y hy ↦ hgR y ((le_max_left _ _).trans hy.le))
      (fun y hy ↦ hhR y ((le_max_right _ _).trans hy.le)) p.1 hp p.2 hx
  have hHc : Continuous (spaceTimeUncurry (kirchhoffFormula g h)) := by
    have he : spaceTimeUncurry (kirchhoffFormula g h) =
        cauchyFreeField g h ∘ timeSpaceContinuousLinearEquiv 3 := by
      funext z
      simp [cauchyFreeField, timeSpaceContinuousLinearEquiv_apply]
    rw [he]
    exact hH.continuous.comp (timeSpaceContinuousLinearEquiv 3).continuous
  obtain ⟨B, hB, hbound⟩ := exists_bound_of_compact_slab hHc
    (isCompact_closedBall (0 : ℝ^3) (R + 1)) (S := 1) (by
      intro t ht x hx
      apply hsupport (t, x) ht.1
      have hx' : R + 1 < ‖x‖ := by
        simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
      linarith [ht.2])
  obtain ⟨T₀, hT₀, _, htrajectory⟩ := exists_signedPower_cone_trajectory hr hB
  obtain ⟨u, a, hu, ha, heq, hbounded, hrem⟩ :=
    htrajectory (cauchyFreeField g h) hH (fun p hp ↦ hbound p.1 hp p.2)
  let M := B + 1
  have hM : 0 ≤ M := by dsimp [M]; linarith
  let C := ‖duhamelOperator‖ * ((2 * r) * (2 * M) ^ (r - 1))
  have hc : Continuous (fun t : ℝ ↦ t ^ 2 * C) := by fun_prop
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, t ^ 2 * C < 1 :=
    hc.continuousAt.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhds_iff.mp hnear
  let T := min T₀ δ
  have hT : 0 < T := lt_min hT₀ hδ
  have hTT : T ≤ T₀ := min_le_left _ _
  have hut : ContDiffOn ℝ 1 u {p | |p.1| < T} := hu.mono (fun _ hp ↦ hp.trans_le hTT)
  have hnormalized (p : ℝ × ℝ^3) (hp : p.1 ∈ Ico 0 T) :
      u p = cauchyFreeField g h p + p.1 ^ 2 * ∫ s : I, (1 - (s : ℝ)) * ((∫ ω : Direction,
          -Real.signedPower r (u (p.1 * (s : ℝ), p.2 + p.1 • ((1 - (s : ℝ)) • (ω : ℝ^3))))
            ∂((volume : Measure (ℝ^3)).toSphere)) / unitSphereArea 3) := by
    rw [heq p (by simpa only [abs_of_nonneg hp.1] using hp.2.trans_le hTT),
      hrem p ⟨hp.1, hp.2.trans_le hTT⟩]
  have hphysical (p : ℝ × ℝ^3) (hp : p.1 ∈ Ico 0 T) :
      u p = cauchyFreeField g h p + oddDuhamelSolution 0
        (fun z : ℝ^4 ↦ -Real.signedPower r (u (timeSpaceContinuousLinearEquiv 3 z)))
        (timeSpaceCons p.1 p.2) := by
    rw [hnormalized p hp, oddDuhamelSolution_zero_eq_normalized _ _ hp.1]
    simp only [timeSpaceContinuousLinearEquiv_apply, PDE.time, timeSpaceCons_zero,
      spatialPart_timeSpaceCons]
  have huB (p : ℝ × ℝ^3) (hp : p.1 ∈ Ico 0 T) : |u p| ≤ M :=
    (hbounded p ⟨hp.1, hp.2.trans_le hTT⟩).le
  obtain ⟨hpos, hvel⟩ := cauchy_traces_of_quadratic_remainder hH hT₀ ha heq
  refine ⟨T, M, R, hT, hM, u, hut, ?_, ?_, huB, ?_, hphysical, ?_⟩
  · intro x
    simpa only [cauchyFreeField_initial_position] using hpos x
  · intro x
    simpa only [(hasDerivAt_cauchyFreeField_initial_velocity hg2 hh1 x).deriv] using hvel x
  · intro p hp hx
    apply eq_zero_of_supported_free_integral_eq hr hM hut.continuousOn
      ⟨cauchyFreeField g h, hH.continuous⟩ hsupport huB hnormalized hp _ hx
    have hsmall : p.1 ^ 2 * C < 1 := hd (by
      simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hp.1]
        using hp.2.trans_le (min_le_right T₀ δ))
    simpa only [C, mul_assoc] using hsmall
  · intro φ hφ hφs t ht
    exact hasDerivAt_deriv_integral_of_signedPower_integral_eq hr hT hg hh
      (hut.mono (fun _ hp ↦ abs_lt.mpr hp)) hphysical hφ hφs ht

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
