/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Mass
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# Initial mass velocity and forward growth

The nonnegative source makes the integrated time derivative nondecreasing.
Continuity of the spatial integrals on bounded forward intervals connects this fact to the
initial slice. The resulting affine lower bound uses the initial mass velocity, with
no assumed differential or growth inequality.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Common
open scoped Topology

namespace WaveEquation.SmallData

variable {n : ℕ}

/-- The mass is continuous on every bounded forward interval, including its initial endpoint. -/
theorem continuousOn_spatialMass_Icc {u : ℝ^(n + 1) → ℝ} {R T : ℝ} (hu : Continuous u)
    (hs : HasForwardSupport u R) :
    ContinuousOn (spatialMass u) (Icc 0 T) := by
  apply continuousOn_integral_of_compact_support
    (f := fun t x ↦ u (timeSpaceCons t x)) (s := Icc 0 T)
    (k := Metric.closedBall 0 (R + T)) (isCompact_closedBall _ _)
    (hu.comp (contDiff_timeSpaceCons_uncurry n (m := 1)).continuous).continuousOn
  intro t x ht hx
  have hnorm : R + T < ‖x‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
  exact hs t ht.1 x (by linarith [ht.2])

/-- The right derivative of the mass at the initial time is the initial velocity integral.

Forward propagation suffices; the field has no support restriction at negative times.
-/
theorem hasDerivWithinAt_spatialMass_zero {u : ℝ^(n + 1) → ℝ} {R : ℝ} (hu : ContDiff ℝ 1 u)
    (hs : HasForwardSupport u R) :
    HasDerivWithinAt (spatialMass u) (spatialMass (∂[0] u) 0) (Ici 0) 0 := by
  have hc : ContinuousWithinAt (spatialMass u) (Ici 0) 0 :=
    (continuousWithinAt_Icc_iff_Ici zero_lt_one).mp
      (continuousOn_spatialMass_Icc hu.continuous hs 0 ⟨le_rfl, zero_le_one⟩)
  have hdc : ContinuousWithinAt (spatialMass (∂[0] u)) (Ici 0) 0 :=
    (continuousWithinAt_Icc_iff_Ici zero_lt_one).mp (continuousOn_spatialMass_Icc
        (PDE.contDiff_partialDeriv_of_succ (m := 0) hu).continuous
        hs.partialDeriv_time 0 ⟨le_rfl, zero_le_one⟩)
  apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi 0)
    (fun t ht ↦ (hasDerivAt_spatialMass hu hs ht).differentiableAt.differentiableWithinAt)
    (hc.mono Ioi_subset_Ici_self) self_mem_nhdsWithin
  apply (hdc.mono Ioi_subset_Ici_self).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht using (hasDerivAt_spatialMass hu hs ht).deriv.symm

/-- The spatial integral of the time derivative is nondecreasing in forward time. -/
theorem monotoneOn_spatialMass_time {u : ℝ^(n + 1) → ℝ} {R p : ℝ} (hu : ContDiff ℝ 2 u)
    (hs : HasForwardSupport u R)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^n, waveOperator u (timeSpaceCons t x) =
      |u (timeSpaceCons t x)| ^ p) :
    MonotoneOn (spatialMass (∂[0] u)) (Ici 0) := by
  intro a ha b hb hab
  have hmono : MonotoneOn (spatialMass (∂[0] u)) (Icc 0 b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (continuousOn_spatialMass_Icc
        (PDE.contDiff_partialDeriv_of_succ (m := 1) hu).continuous
        hs.partialDeriv_time)
    · intro t ht
      have ht0 : 0 < t := (show t ∈ Ioo 0 b by simpa only [interior_Icc] using ht).1
      have hd := hasDerivAt_spatialMass_time_eq_source hu hs ht0 (hwave t ht0)
      exact hd.differentiableAt.differentiableWithinAt
    · intro t ht
      have ht0 : 0 < t := (show t ∈ Ioo 0 b by simpa only [interior_Icc] using ht).1
      rw [(hasDerivAt_spatialMass_time_eq_source hu hs ht0 (hwave t ht0)).deriv]
      exact integral_nonneg (fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
  exact hmono ⟨ha, hab⟩ ⟨hb, le_rfl⟩ hab

/-- The mass lies above the affine function determined by its two initial integrals. -/
theorem initial_affine_le_spatialMass {u : ℝ^(n + 1) → ℝ} {R p t : ℝ} (hu : ContDiff ℝ 2 u)
    (hs : HasForwardSupport u R)
    (hwave : ∀ s, 0 < s → ∀ x : ℝ^n, waveOperator u (timeSpaceCons s x) =
      |u (timeSpaceCons s x)| ^ p)
    (ht : 0 ≤ t) :
    spatialMass u 0 + spatialMass (∂[0] u) 0 * t ≤ spatialMass u t := by
  have hmono := monotoneOn_spatialMass_time hu hs hwave
  have hd : DifferentiableOn ℝ (spatialMass u) (interior (Icc 0 t)) := by
    intro s hsI
    have hs0 : 0 < s := (show s ∈ Ioo 0 t by simpa only [interior_Icc] using hsI).1
    have hd := hasDerivAt_spatialMass (hu.of_le (by norm_num)) hs hs0
    exact hd.differentiableAt.differentiableWithinAt
  have hbound : ∀ s ∈ interior (Icc 0 t),
      spatialMass (∂[0] u) 0 ≤ deriv (spatialMass u) s := by
    intro s hsI
    have hs0 : 0 < s := (show s ∈ Ioo 0 t by simpa only [interior_Icc] using hsI).1
    rw [(hasDerivAt_spatialMass (hu.of_le (by norm_num)) hs hs0).deriv]
    exact hmono (mem_Ici.mpr le_rfl) hs0.le hs0.le
  have h := (convex_Icc 0 t).mul_sub_le_image_sub_of_le_deriv
    (continuousOn_spatialMass_Icc hu.continuous hs) hd hbound 0 ⟨le_rfl, ht⟩ t ⟨ht, le_rfl⟩ ht
  linarith

/-- Positive integral of the initial velocity forces a positive mass derivative. -/
theorem deriv_spatialMass_pos {u : ℝ^(n + 1) → ℝ} {R p t : ℝ} (hu : ContDiff ℝ 2 u)
    (hs : HasForwardSupport u R)
    (hwave : ∀ s, 0 < s → ∀ x : ℝ^n, waveOperator u (timeSpaceCons s x) =
      |u (timeSpaceCons s x)| ^ p)
    (hpositive : 0 < spatialMass (∂[0] u) 0) (ht : 0 < t) :
    0 < deriv (spatialMass u) t := by
  rw [(hasDerivAt_spatialMass (hu.of_le (by norm_num)) hs ht).deriv]
  exact hpositive.trans_le
    (monotoneOn_spatialMass_time hu hs hwave (mem_Ici.mpr le_rfl) ht.le ht.le)

end WaveEquation.SmallData
