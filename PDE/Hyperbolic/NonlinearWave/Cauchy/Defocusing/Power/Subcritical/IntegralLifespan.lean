/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.IntegralUniqueness
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.IntegralContinuation

/-!
# The amplitude alternative for C¹ signed-power integral trajectories

Finite-interval uniqueness glues all bounded integral trajectories with one
free field. If their lifetimes are unbounded, the union is global. Otherwise
it solves the integral equation up to their positive finite supremum. The
constructed bounded extension forces amplitude to be unbounded arbitrarily
near that endpoint. The initial field is retained on a neighborhood of the initial slice.
-/

@[expose] public noncomputable section

open Set Filter PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData.Classical.LocalPower
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- A finite C¹ integral trajectory with one uniform forward amplitude bound.
The negative-time band supplies a two-sided initial germ; the integral
equation is required only at nonnegative times. -/
structure IsBoundedIntegralTrajectoryBefore (r b : ℝ) (H : ℝ × ℝ^3 → ℝ)
    (T : ℝ) (u : ℝ × ℝ^3 → ℝ) : Prop where
  time_pos : 0 < T
  regular : ContDiffOn ℝ 1 u {p | -b < p.1 ∧ p.1 < T}
  bounded : ∃ M : ℝ, 0 ≤ M ∧ ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 T → |u p| ≤ M
  equation : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 T →
    u p = H p + oddDuhamelSolution 0
      (fun z : ℝ^4 ↦ -Real.signedPower r (u (timeSpaceContinuousLinearEquiv 3 z)))
      (timeSpaceCons p.1 p.2)

/-- Every positive shorter interval is again a bounded integral trajectory. -/
theorem IsBoundedIntegralTrajectoryBefore.mono {r b S T : ℝ} {H u : ℝ × ℝ^3 → ℝ}
    (hu : IsBoundedIntegralTrajectoryBefore r b H T u) (hS : 0 < S) (hST : S ≤ T) :
    IsBoundedIntegralTrajectoryBefore r b H S u := by
  obtain ⟨M, hM, huM⟩ := hu.bounded
  exact ⟨hS, hu.regular.mono (fun _ hp ↦ ⟨hp.1, hp.2.trans_le hST⟩),
    ⟨M, hM, fun p hp ↦ huM p ⟨hp.1, hp.2.trans_le hST⟩⟩,
    fun p hp ↦ hu.equation p ⟨hp.1, hp.2.trans_le hST⟩⟩

/-- Integral trajectories with the same free field agree on their
whole forward overlap, regardless of its length. -/
theorem IsBoundedIntegralTrajectoryBefore.eq_on_overlap {r b S T : ℝ} (hr : 1 ≤ r) (hb : 0 < b)
    {H u v : ℝ × ℝ^3 → ℝ} (hH : ContDiff ℝ 1 H) (hu : IsBoundedIntegralTrajectoryBefore r b H S u)
    (hv : IsBoundedIntegralTrajectoryBefore r b H T v) {p : ℝ × ℝ^3} (hp : p.1 ∈ Ico 0 (min S T)) :
    u p = v p := by
  obtain ⟨M, hM, huM⟩ := hu.bounded
  obtain ⟨N, _, hvN⟩ := hv.bounded
  apply eq_on_forward_interval_of_bounded_signedPower_integral_eq hr hb (hM.trans (le_max_left M N))
    (hu.regular.mono (fun _ hq ↦ ⟨hq.1, hq.2.trans_le (min_le_left _ _)⟩))
    (hv.regular.mono (fun _ hq ↦ ⟨hq.1, hq.2.trans_le (min_le_right _ _)⟩)) hH
    (fun q hq ↦ (huM q ⟨hq.1, hq.2.trans_le (min_le_left _ _)⟩).trans (le_max_left _ _))
    (fun q hq ↦ (hvN q ⟨hq.1, hq.2.trans_le (min_le_right _ _)⟩).trans (le_max_right _ _))
    (fun q hq ↦ hu.equation q ⟨hq.1, hq.2.trans_le (min_le_left _ _)⟩)
    (fun q hq ↦ hv.equation q ⟨hq.1, hq.2.trans_le (min_le_right _ _)⟩) p hp

/-- The positive endpoints for which a bounded integral trajectory exists. -/
def boundedIntegralExistenceTimes (r b : ℝ) (H : ℝ × ℝ^3 → ℝ) : Set ℝ :=
  {T | ∃ u : ℝ × ℝ^3 → ℝ, IsBoundedIntegralTrajectoryBefore r b H T u}

/-- Union of all bounded forward integral trajectories. A fixed initial field
is retained below half its horizon, including the full negative-time band. -/
def integralTrajectoryUnion (r b : ℝ) (H : ℝ × ℝ^3 → ℝ)
    (a : ℝ) (u₀ : ℝ × ℝ^3 → ℝ) (p : ℝ × ℝ^3) : ℝ := by
  classical
  exact if p.1 < a / 2 then u₀ p else
    if hp : ∃ T : ℝ, p.1 < T ∧ ∃ u : ℝ × ℝ^3 → ℝ,
        IsBoundedIntegralTrajectoryBefore r b H T u then
      hp.choose_spec.2.choose p
    else 0

/-- The union agrees with every bounded integral trajectory at forward times. -/
theorem integralTrajectoryUnion_eq {r b a T : ℝ} (hr : 1 ≤ r) (hb : 0 < b) {H u₀ u : ℝ × ℝ^3 → ℝ}
    (hH : ContDiff ℝ 1 H) (h₀ : IsBoundedIntegralTrajectoryBefore r b H a u₀)
    (hu : IsBoundedIntegralTrajectoryBefore r b H T u) {p : ℝ × ℝ^3} (hp : p.1 ∈ Ico 0 T) :
    integralTrajectoryUnion r b H a u₀ p = u p := by
  classical
  unfold integralTrajectoryUnion
  split_ifs with ha ht
  · exact h₀.eq_on_overlap hr hb hH hu ⟨hp.1, lt_min (ha.trans (half_lt_self h₀.time_pos)) hp.2⟩
  · exact ht.choose_spec.2.choose_spec.eq_on_overlap hr hb hH hu
      ⟨hp.1, lt_min ht.choose_spec.1 hp.2⟩
  · exact (ht ⟨T, hp.2, u, hu⟩).elim

/-- The union retains the initial field on an open neighborhood of every
point below half the initial positive horizon. -/
theorem integralTrajectoryUnion_eventuallyEq_initial {r b a : ℝ} {H u₀ : ℝ × ℝ^3 → ℝ} {p : ℝ × ℝ^3}
    (hp : p.1 < a / 2) :
    integralTrajectoryUnion r b H a u₀ =ᶠ[𝓝 p] u₀ := by
  filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hp] with q hq
  simp [integralTrajectoryUnion, show q.1 < a / 2 from hq]

/-- At a positive time, the union agrees locally with any admissible trajectory
whose interval contains that time. -/
theorem integralTrajectoryUnion_eventuallyEq {r b a T : ℝ} (hr : 1 ≤ r) (hb : 0 < b)
    {H u₀ u : ℝ × ℝ^3 → ℝ} (hH : ContDiff ℝ 1 H) (h₀ : IsBoundedIntegralTrajectoryBefore r b H a u₀)
    (hu : IsBoundedIntegralTrajectoryBefore r b H T u) {p : ℝ × ℝ^3} (hp : p.1 ∈ Ioo 0 T) :
    integralTrajectoryUnion r b H a u₀ =ᶠ[𝓝 p] u := by
  filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hp.1,
    (isOpen_lt continuous_fst continuous_const).mem_nhds hp.2] with q hq₀ hqT
  exact integralTrajectoryUnion_eq hr hb hH h₀ hu ⟨hq₀.le, hqT⟩

/-- The union itself is a bounded C¹ integral trajectory on each admissible
interval. In the Duhamel term, overlap uniqueness identifies every past value. -/
theorem isBoundedIntegralTrajectoryBefore_integralTrajectoryUnion {r b a T : ℝ} (hr : 1 ≤ r)
    (hb : 0 < b) {H u₀ u : ℝ × ℝ^3 → ℝ} (hH : ContDiff ℝ 1 H)
    (h₀ : IsBoundedIntegralTrajectoryBefore r b H a u₀)
    (hu : IsBoundedIntegralTrajectoryBefore r b H T u) :
    IsBoundedIntegralTrajectoryBefore r b H T (integralTrajectoryUnion r b H a u₀) := by
  refine ⟨hu.time_pos, ?_, ?_, ?_⟩
  · intro p hp
    by_cases hp₀ : 0 < p.1
    · have hrp := hu.regular.contDiffAt (((isOpen_lt continuous_const continuous_fst).inter
          (isOpen_lt continuous_fst continuous_const)).mem_nhds hp)
      exact (hrp.congr_of_eventuallyEq
        (integralTrajectoryUnion_eventuallyEq hr hb hH h₀ hu ⟨hp₀, hp.2⟩)).contDiffWithinAt
    · have hpa : p.1 < a / 2 := (le_of_not_gt hp₀).trans_lt (half_pos h₀.time_pos)
      have hrp := h₀.regular.contDiffAt (((isOpen_lt continuous_const continuous_fst).inter
          (isOpen_lt continuous_fst continuous_const)).mem_nhds
            ⟨hp.1, hpa.trans (half_lt_self h₀.time_pos)⟩)
      exact (hrp.congr_of_eventuallyEq
        (integralTrajectoryUnion_eventuallyEq_initial hpa)).contDiffWithinAt
  · obtain ⟨M, hM, huM⟩ := hu.bounded
    exact ⟨M, hM, fun p hp ↦ by
      rw [integralTrajectoryUnion_eq hr hb hH h₀ hu hp]
      exact huM p hp⟩
  · intro p hp
    rw [integralTrajectoryUnion_eq hr hb hH h₀ hu hp, hu.equation p hp]
    congr 1
    apply oddDuhamelSolution_congr_forward (F := fun q ↦ -Real.signedPower r (u q))
      (G := fun q ↦ -Real.signedPower r (integralTrajectoryUnion r b H a u₀ q)) p hp.1
    intro s hs x
    rw [integralTrajectoryUnion_eq hr hb hH h₀ hu ⟨hs.1, hs.2.trans_lt hp.2⟩]

/-- The union preserves the whole initial band, not merely the initial value. -/
theorem integralTrajectoryUnion_eq_initial {r b a : ℝ} (hr : 1 ≤ r) (hb : 0 < b)
    {H u₀ : ℝ × ℝ^3 → ℝ} (hH : ContDiff ℝ 1 H) (h₀ : IsBoundedIntegralTrajectoryBefore r b H a u₀) :
    EqOn (integralTrajectoryUnion r b H a u₀) u₀ {p | -b < p.1 ∧ p.1 < a} := by
  intro p hp
  by_cases hpa : p.1 < a / 2
  · exact (integralTrajectoryUnion_eventuallyEq_initial hpa).eq_of_nhds
  · exact integralTrajectoryUnion_eq hr hb hH h₀ h₀
      ⟨(half_pos h₀.time_pos).le.trans (le_of_not_gt hpa), hp.2⟩

/-- A C¹ integral trajectory before a positive endpoint, with an amplitude
bound on every shorter forward interval. The endpoint itself need not have
one uniform amplitude bound. -/
structure IsIntegralTrajectoryBefore (r b : ℝ) (H : ℝ × ℝ^3 → ℝ)
    (T : ℝ) (u : ℝ × ℝ^3 → ℝ) : Prop where
  time_pos : 0 < T
  regular : ContDiffOn ℝ 1 u {p | -b < p.1 ∧ p.1 < T}
  bounded_before : ∀ S : ℝ, 0 < S → S < T →
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 S → |u p| ≤ M
  equation : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 T →
    u p = H p + oddDuhamelSolution 0
      (fun z : ℝ^4 ↦ -Real.signedPower r (u (timeSpaceContinuousLinearEquiv 3 z)))
      (timeSpaceCons p.1 p.2)

/-- Every shorter positive interval of a locally bounded trajectory is a
bounded integral trajectory. -/
theorem IsIntegralTrajectoryBefore.before {r b S T : ℝ} {H u : ℝ × ℝ^3 → ℝ}
    (hu : IsIntegralTrajectoryBefore r b H T u) (hS : 0 < S) (hST : S < T) :
    IsBoundedIntegralTrajectoryBefore r b H S u :=
  ⟨hS, hu.regular.mono (fun _ hp ↦ ⟨hp.1, hp.2.trans hST⟩),
    hu.bounded_before S hS hST, fun p hp ↦ hu.equation p ⟨hp.1, hp.2.trans hST⟩⟩

private theorem isIntegralTrajectoryBefore_of_cofinal {r b T : ℝ} {H u : ℝ × ℝ^3 → ℝ} (hT : 0 < T)
    (hcover : ∀ S < T, ∃ A : ℝ, S < A ∧ IsBoundedIntegralTrajectoryBefore r b H A u) :
    IsIntegralTrajectoryBefore r b H T u := by
  refine ⟨hT, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨A, hpA, hA⟩ := hcover p.1 hp.2
    exact (hA.regular.contDiffAt (((isOpen_lt continuous_const continuous_fst).inter
        (isOpen_lt continuous_fst continuous_const)).mem_nhds ⟨hp.1, hpA⟩)).contDiffWithinAt
  · intro S hS hST
    obtain ⟨A, hSA, hA⟩ := hcover S hST
    exact (hA.mono hS hSA.le).bounded
  · intro p hp
    obtain ⟨A, hpA, hA⟩ := hcover p.1 hp.2
    exact hA.equation p ⟨hp.1, hpA⟩

/-- A global forward C¹ integral trajectory. Amplitude is bounded on each finite interval. -/
structure IsGlobalIntegralTrajectory (r b : ℝ) (H : ℝ × ℝ^3 → ℝ)
    (u : ℝ × ℝ^3 → ℝ) : Prop where
  regular : ContDiffOn ℝ 1 u {p | -b < p.1}
  bounded_before : ∀ S : ℝ, ∃ M : ℝ, 0 ≤ M ∧
    ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 S → |u p| ≤ M
  equation : ∀ p : ℝ × ℝ^3, 0 ≤ p.1 →
    u p = H p + oddDuhamelSolution 0
      (fun z : ℝ^4 ↦ -Real.signedPower r (u (timeSpaceContinuousLinearEquiv 3 z)))
      (timeSpaceCons p.1 p.2)

/-- A global integral trajectory supplies every positive bounded interval. -/
theorem IsGlobalIntegralTrajectory.before {r b T : ℝ} {H u : ℝ × ℝ^3 → ℝ}
    (hu : IsGlobalIntegralTrajectory r b H u) (hT : 0 < T) :
    IsBoundedIntegralTrajectoryBefore r b H T u :=
  ⟨hT, hu.regular.mono (fun _ hp ↦ hp.1), hu.bounded_before T, fun p hp ↦ hu.equation p hp.1⟩

private theorem isGlobalIntegralTrajectory_of_unbounded {r b : ℝ} {H u : ℝ × ℝ^3 → ℝ}
    (hcover : ∀ S : ℝ, ∃ A : ℝ, S < A ∧ IsBoundedIntegralTrajectoryBefore r b H A u) :
    IsGlobalIntegralTrajectory r b H u := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨A, hpA, hA⟩ := hcover p.1
    exact (hA.regular.contDiffAt (((isOpen_lt continuous_const continuous_fst).inter
        (isOpen_lt continuous_fst continuous_const)).mem_nhds ⟨hp, hpA⟩)).contDiffWithinAt
  · intro S
    obtain ⟨A, hSA, hA⟩ := hcover S
    obtain ⟨M, hM, huM⟩ := hA.bounded
    exact ⟨M, hM, fun p hp ↦ huM p ⟨hp.1, hp.2.trans hSA⟩⟩
  · intro p hp
    obtain ⟨A, hpA, hA⟩ := hcover p.1
    exact hA.equation p ⟨hp, hpA⟩

/-- Arbitrarily long bounded integral trajectories give one global
C¹ trajectory. The initial two-sided germ is preserved by the construction. -/
theorem exists_globalIntegralTrajectory_of_unbounded {r b a : ℝ} (hr : 1 ≤ r) (hb : 0 < b)
    {H u₀ : ℝ × ℝ^3 → ℝ} (hH : ContDiff ℝ 1 H) (h₀ : IsBoundedIntegralTrajectoryBefore r b H a u₀)
    (hunbounded : ¬ BddAbove (boundedIntegralExistenceTimes r b H)) :
    ∃ u : ℝ × ℝ^3 → ℝ, IsGlobalIntegralTrajectory r b H u ∧ EqOn u u₀ {p | -b < p.1 ∧ p.1 < a} := by
  refine ⟨integralTrajectoryUnion r b H a u₀,
    isGlobalIntegralTrajectory_of_unbounded ?_, integralTrajectoryUnion_eq_initial hr hb hH h₀⟩
  intro S
  obtain ⟨A, ⟨u, hu⟩, hSA⟩ := not_bddAbove_iff.mp hunbounded S
  exact ⟨A, hSA, isBoundedIntegralTrajectoryBefore_integralTrajectoryUnion hr hb hH h₀ hu⟩

/-- If the nonempty set of bounded integral lifetimes has a finite supremum,
the union is C¹ and solves the integral equation up to that supremum.
Its amplitude is bounded on every shorter interval. -/
theorem exists_integralTrajectory_at_supremum {r b a : ℝ} (hr : 1 ≤ r) (hb : 0 < b)
    {H u₀ : ℝ × ℝ^3 → ℝ} (hH : ContDiff ℝ 1 H) (h₀ : IsBoundedIntegralTrajectoryBefore r b H a u₀)
    (hbounded : BddAbove (boundedIntegralExistenceTimes r b H)) :
    ∃ u : ℝ × ℝ^3 → ℝ, IsIntegralTrajectoryBefore r b H (sSup (boundedIntegralExistenceTimes r b H))
      u ∧ EqOn u u₀ {p | -b < p.1 ∧ p.1 < a} := by
  let E := boundedIntegralExistenceTimes r b H
  have hE : E.Nonempty := ⟨a, u₀, h₀⟩
  have hT : 0 < sSup E := h₀.time_pos.trans_le (le_csSup hbounded ⟨u₀, h₀⟩)
  refine ⟨integralTrajectoryUnion r b H a u₀,
    isIntegralTrajectoryBefore_of_cofinal hT ?_, integralTrajectoryUnion_eq_initial hr hb hH h₀⟩
  intro S hS
  obtain ⟨A, ⟨u, hu⟩, hSA⟩ := (lt_csSup_iff hbounded hE).mp hS
  exact ⟨A, hSA, isBoundedIntegralTrajectoryBefore_integralTrajectoryUnion hr hb hH h₀ hu⟩

/-- The trajectory at a finite supremum cannot have a uniform
amplitude bound: the bounded continuation construction would produce an
admissible interval beyond that supremum. -/
theorem IsIntegralTrajectoryBefore.amplitude_unbounded_at_supremum {r b : ℝ} (hr : 1 ≤ r)
    (hb : 0 < b) {H u : ℝ × ℝ^3 → ℝ} (hH : ContDiff ℝ 1 H)
    (hHB : ∀ S : ℝ, 0 < S → ∃ B : ℝ, 0 ≤ B ∧ ∀ p : ℝ × ℝ^3, p.1 ∈ Icc 0 S → |H p| ≤ B)
    (hbounded : BddAbove (boundedIntegralExistenceTimes r b H))
    (hu : IsIntegralTrajectoryBefore r b H (sSup (boundedIntegralExistenceTimes r b H)) u) :
    ∀ M : ℝ, ∃ p : ℝ × ℝ^3, p.1 ∈ Ico 0 (sSup (boundedIntegralExistenceTimes r b H)) ∧
      M < |u p| := by
  intro M
  by_contra! hM
  let L := sSup (boundedIntegralExistenceTimes r b H)
  obtain ⟨B, hB, hHB'⟩ := hHB (L + 1) (by linarith [hu.time_pos])
  obtain ⟨L', M', hLL', hM', w, hw, _, hwB, hwe⟩ :=
    exists_signedPower_integral_extension_of_bounded hr hb hu.time_pos hB
      (le_max_left 0 M) hu.regular hH hHB'
      (fun p hp ↦ (hM p hp).trans (le_max_right _ _)) hu.equation
  have hmem : L' ∈ boundedIntegralExistenceTimes r b H :=
    ⟨w, hu.time_pos.trans hLL', hw, ⟨M', hM', hwB⟩, hwe⟩
  exact (not_lt_of_ge (le_csSup hbounded hmem)) hLL'

/-- For a trajectory bounded on proper prefixes, unbounded amplitude must
occur arbitrarily near the terminal time. This rules out an artificial blowup
caused solely by taking a supremum over an early interval. -/
theorem IsIntegralTrajectoryBefore.amplitude_unbounded_near_endpoint {r b L : ℝ} {H u : ℝ × ℝ^3 → ℝ}
    (hu : IsIntegralTrajectoryBefore r b H L u)
    (hunbounded : ∀ M : ℝ, ∃ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L ∧ M < |u p|) :
    ∀ a < L, ∀ M : ℝ, ∃ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L ∧ a ≤ p.1 ∧ M < |u p| := by
  intro a ha M
  let S := max a (L / 2)
  have hS : 0 < S := (half_pos hu.time_pos).trans_le (le_max_right _ _)
  have hSL : S < L := max_lt ha (half_lt_self hu.time_pos)
  obtain ⟨K, _, huK⟩ := hu.bounded_before S hS hSL
  obtain ⟨p, hp, hMp⟩ := hunbounded (max M K)
  have hSp : S ≤ p.1 := by
    by_contra! hpS
    exact (not_lt_of_ge ((huK p ⟨hp.1, hpS⟩).trans (le_max_right _ _))) hMp
  exact ⟨p, hp, (le_max_left _ _).trans hSp, (le_max_left _ _).trans_lt hMp⟩

/-- Starting from one local bounded trajectory, the signed-power
integral equation has either a global C¹ trajectory or a trajectory with a
positive finite lifetime and unbounded amplitude near that endpoint. The
continuation and overlap hypotheses are proved by the imported constructions;
only finite-interval boundedness of the prescribed free field is required. -/
theorem exists_integral_lifespan_alternative {r b a : ℝ} (hr : 1 ≤ r) (hb : 0 < b)
    {H u₀ : ℝ × ℝ^3 → ℝ} (hH : ContDiff ℝ 1 H)
    (hHB : ∀ S : ℝ, 0 < S → ∃ B : ℝ, 0 ≤ B ∧ ∀ p : ℝ × ℝ^3, p.1 ∈ Icc 0 S → |H p| ≤ B)
    (h₀ : IsBoundedIntegralTrajectoryBefore r b H a u₀) :
    (∃ u : ℝ × ℝ^3 → ℝ, IsGlobalIntegralTrajectory r b H u ∧
      EqOn u u₀ {p | -b < p.1 ∧ p.1 < a}) ∨
    ∃ L : ℝ, ∃ u : ℝ × ℝ^3 → ℝ, IsIntegralTrajectoryBefore r b H L u ∧
      EqOn u u₀ {p | -b < p.1 ∧ p.1 < a} ∧
      ∀ A < L, ∀ M : ℝ, ∃ p : ℝ × ℝ^3,
        p.1 ∈ Ico 0 L ∧ A ≤ p.1 ∧ M < |u p| := by
  by_cases hbounded : BddAbove (boundedIntegralExistenceTimes r b H)
  · obtain ⟨u, hu, heq⟩ := exists_integralTrajectory_at_supremum hr hb hH h₀ hbounded
    exact Or.inr ⟨_, u, hu, heq, hu.amplitude_unbounded_near_endpoint
      (hu.amplitude_unbounded_at_supremum hr hb hH hHB hbounded)⟩
  · exact Or.inl (exists_globalIntegralTrajectory_of_unbounded hr hb hH h₀ hbounded)

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
