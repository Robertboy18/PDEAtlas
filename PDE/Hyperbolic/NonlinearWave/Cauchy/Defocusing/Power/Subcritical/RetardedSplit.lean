/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RetardedHistory
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.Formula
import CAS.ExactTactic

/-!
# Splitting the physical retarded field at a restart time

The three-dimensional Duhamel field splits into the waves emitted
before an anchor and a translated future retarded field. Continuity suffices
for integrability. Causality of each term uses only values on its time interval.
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData.Classical.LocalPower

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- The physical spherical kernel is continuous for a continuous source. -/
theorem continuous_retardedSourceKernel {F : ℝ × ℝ^3 → ℝ}
    (hF : Continuous F) : Continuous (retardedSourceKernel F) := by
  have hp : Continuous (fun z : ((ℝ × ℝ^3) × ℝ) × Direction ↦
      (z.1.2, z.1.1.2 + (z.1.1.1 - z.1.2) • (z.2 : ℝ^3))) := by fun_prop
  exact (continuous_fst.fst.sub continuous_snd).mul ((continuous_integral_of_compact
      (g := fun (q : (ℝ × ℝ^3) × ℝ) (θ : Direction) ↦ F (q.2, q.1.2 + (q.1.1 - q.2) • (θ : ℝ^3)))
      (μ := (volume : Measure (ℝ^3)).toSphere) (hF.comp hp)).div_const _)

/-- The physical Duhamel field is the unnormalized retarded-time
integral, with the same spherical area and sign conventions. -/
theorem oddDuhamelSolution_eq_retardedSourceKernel (F : ℝ × ℝ^3 → ℝ) (p : ℝ × ℝ^3) (hp : 0 ≤ p.1) :
    oddDuhamelSolution 0 (fun z : ℝ^4 ↦ F (timeSpaceContinuousLinearEquiv 3 z))
      (timeSpaceCons p.1 p.2) = ∫ s in (0 : ℝ)..p.1, retardedSourceKernel F (p, s) := by
  rw [oddDuhamelSolution_eq_integral 0 _ _ hp]
  simp only [Nat.mul_zero, Nat.doubleFactorial, Nat.cast_one, inv_one,
    one_mul, oddWavePotential_timeSpaceCons, oddSphericalProfile_zero,
    timeSpaceContinuousLinearEquiv_apply]
  rfl

/-- Splitting emission time at `a` leaves the past history and the Duhamel
field of the translated source. This is an equality of wave integrals. -/
theorem oddDuhamelSolution_eq_history_add_shift {F : ℝ × ℝ^3 → ℝ}
    (hF : Continuous F) {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (x : ℝ^3) :
    oddDuhamelSolution 0 (fun z : ℝ^4 ↦ F (timeSpaceContinuousLinearEquiv 3 z))
      (timeSpaceCons (a + t) x) = retardedHistory a F (t, x) + oddDuhamelSolution 0
      (fun z : ℝ^4 ↦ F (a + z 0, spatialPartCLM 3 z)) (timeSpaceCons t x) := by
  have hshift : (fun z : ℝ^4 ↦ F (a + z 0, spatialPartCLM 3 z)) =
      fun z ↦ (fun q : ℝ × ℝ^3 ↦ F (a + q.1, q.2))
        (timeSpaceContinuousLinearEquiv 3 z) := by
    funext z
    rw [timeSpaceContinuousLinearEquiv_apply]
    rfl
  rw [hshift, oddDuhamelSolution_eq_retardedSourceKernel _ (a + t, x) (add_nonneg ha ht),
    oddDuhamelSolution_eq_retardedSourceKernel (fun q : ℝ × ℝ^3 ↦ F (a + q.1, q.2)) (t, x) ht]
  have hc : Continuous (fun s : ℝ ↦ retardedSourceKernel F ((a + t, x), s)) :=
    (continuous_retardedSourceKernel hF).comp (continuous_const.prodMk continuous_id)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 a) (hc.intervalIntegrable a (a + t))]
  congr 1
  have he := intervalIntegral.integral_comp_add_left
    (fun s : ℝ ↦ retardedSourceKernel F ((a + t, x), s)) (a := 0) (b := t) a
  rw [add_zero] at he
  rw [← he]
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  have hage : a + t - (a + s) = t - s := by cas
  simp only [retardedSourceKernel, hage]

/-- The spherical kernel at an emission time depends only on that source slice. -/
theorem retardedSourceKernel_congr {F G : ℝ × ℝ^3 → ℝ}
    {p : ℝ × ℝ^3} {s : ℝ} (h : ∀ x : ℝ^3, F (s, x) = G (s, x)) :
    retardedSourceKernel F (p, s) = retardedSourceKernel G (p, s) := by
  unfold retardedSourceKernel
  rw [show (fun y : ℝ^3 ↦ F (s, y)) = (fun y ↦ G (s, y)) from funext h]

/-- Prescribed histories that agree on the past give the same free field. -/
theorem retardedHistory_congr {F G : ℝ × ℝ^3 → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ s ∈ Icc 0 a, ∀ x : ℝ^3, F (s, x) = G (s, x)) (p : ℝ × ℝ^3) :
    retardedHistory a F p = retardedHistory a G p := by
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  apply retardedSourceKernel_congr
  exact h s (by simpa only [uIcc_of_le ha] using hs)

/-- The physical retarded field uses only source values from the closed past
interval. No regularity is required for this integral congruence. -/
theorem oddDuhamelSolution_congr_forward {F G : ℝ × ℝ^3 → ℝ} (p : ℝ × ℝ^3) (hp : 0 ≤ p.1)
    (h : ∀ s ∈ Icc 0 p.1, ∀ x : ℝ^3, F (s, x) = G (s, x)) :
    oddDuhamelSolution 0 (fun z : ℝ^4 ↦ F (timeSpaceContinuousLinearEquiv 3 z))
      (timeSpaceCons p.1 p.2) = oddDuhamelSolution 0
      (fun z : ℝ^4 ↦ G (timeSpaceContinuousLinearEquiv 3 z)) (timeSpaceCons p.1 p.2) := by
  rw [oddDuhamelSolution_eq_retardedSourceKernel _ p hp,
    oddDuhamelSolution_eq_retardedSourceKernel _ p hp]
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  exact retardedSourceKernel_congr (h s (by simpa only [uIcc_of_le hp] using hs))

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
