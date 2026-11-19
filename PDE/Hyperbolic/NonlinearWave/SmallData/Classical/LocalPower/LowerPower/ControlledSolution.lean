/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.LowerPower.ConeBound
public import
  PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.LowerPower.InitialAcceleration
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-!
# Uniform control of the constructed lower-power integral solution

Arbitrary compactly supported C¹ velocity constructs a C¹ integral
solution with its ordinary initial displacement, velocity, and
acceleration. Shrinking the time strip gives a uniform amplitude bound
and a small coefficient for the linearized cone equation. Both bounds
are consequences of the integral equation and its zero initial trace.
-/

@[expose] public noncomputable section

open Set MeasureTheory BoundedContinuousFunction PDE.Analysis
open scoped unitInterval

namespace WaveEquation.SmallData.Classical.LocalPower.LowerPower

/-- Compact C¹ velocity gives a constructed integral solution with
ordinary Cauchy traces and uniform short-time control of its amplitude
and linearized cone coefficient. -/
theorem exists_controlled_mild_abs_rpow_three {p : ℝ} (hp : 1 < p)
    {h : ℝ^3 → ℝ} (hh : ContDiff ℝ 1 h) (hhc : HasCompactSupport h) :
    ∃ T : ℝ, 0 < T ∧ ∃ v : ℝ × ℝ^3 → ℝ,
      ContDiffOn ℝ 1 v {q | |q.1| < T} ∧
      (∀ q : ℝ × ℝ^3, |q.1| < T →
        v q = q.1 * unitSphereAverage 3 h q.2 q.1 +
          q.1 ^ 2 * ∫ s : I, (1 - (s : ℝ)) *
            ((∫ ω : Direction,
              |v (q.1 * (s : ℝ), q.2 + q.1 • ((1 - (s : ℝ)) • (ω : ℝ^3)))| ^ p
                ∂((volume : Measure (ℝ^3)).toSphere)) / unitSphereArea 3)) ∧
      (∀ x, v (0, x) = 0) ∧
      (∀ x, HasDerivAt (fun t ↦ v (t, x)) (h x) 0) ∧
      (∀ x, HasDerivAt (deriv (fun t ↦ v (t, x))) 0 0) ∧
      (∀ q : ℝ × ℝ^3, |q.1| < T → |v q| < 1) ∧
      ∀ t : ℝ, |t| < T → t ^ 2 * ‖duhamelOperator‖ * p ≤ 1 / 2 := by
  obtain ⟨T₀, hT₀, v, hv, heq, hzero, htrace, hacc⟩ :=
    exists_mild_abs_rpow_three_with_initial_acceleration hp hh hhc
  let g := ofCompactSupport h hh.continuous hhc
  let f : C(ℝ, ℝ) := ⟨fun x ↦ |x| ^ p, by
    simpa only [Real.norm_eq_abs] using
      (contDiff_norm_rpow hp : ContDiff ℝ 1 (fun x : ℝ ↦ ‖x‖ ^ p)).continuous⟩
  have hcone (q : {q : ℝ × ℝ^3 | |q.1| < T₀}) :
      physicalCone hv.continuousOn q = freeField g.toContinuousMap q.1 +
        q.1.1 ^ 2 • duhamelOperator (composeCompact f (physicalCone hv.continuousOn q)) :=
    physicalCone_eq_of_integral_eq hv.continuousOn f g.toContinuousMap heq q
  obtain ⟨T, hT, hTT, hcontrol⟩ :=
    exists_time_uniform_cone_control hp hT₀ hv.continuousOn hzero g hcone
  refine ⟨T, hT, v, hv.mono (fun _ hq ↦ hq.trans_le hTT),
    (fun q hq ↦ heq q (hq.trans_le hTT)), hzero, htrace, hacc, ?_, ?_⟩
  · intro q hq
    have hb :=
      ((physicalCone hv.continuousOn ⟨q, hq.trans_le hTT⟩).norm_coe_le_norm vertex).trans_lt
        (hcontrol ⟨q, hq.trans_le hTT⟩ hq).1
    simpa only [physicalCone_apply, physicalPoint, vertex, coneTime, coneSpace,
      mul_one, smul_zero, add_zero, Prod.eta, Real.norm_eq_abs] using hb
  · exact fun t ht ↦ (hcontrol ⟨(t, 0), ht.trans_le hTT⟩ ht).2

end WaveEquation.SmallData.Classical.LocalPower.LowerPower
