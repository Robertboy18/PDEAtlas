/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.LowerPower.InitialTrace
public import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-!
# A constructed C¹ power-wave integral solution

For every real exponent greater than one, compactly supported C¹ velocity
gives a jointly C¹ solution of the three-dimensional Kirchhoff
integral equation on a uniform open time strip. The displacement is zero
and the ordinary initial velocity is the prescribed datum.

This is an integral-equation existence theorem. A C² upgrade and the
pointwise wave equation require further regularity arguments when the
power is less than two.
-/

@[expose] public noncomputable section

open Set MeasureTheory BoundedContinuousFunction PDE.Analysis
open scoped unitInterval

namespace WaveEquation.SmallData.Classical.LocalPower.LowerPower

/-- A C¹ reaction and bounded C¹ velocity construct an integral solution
with ordinary Cauchy traces on a uniform time strip. -/
theorem exists_mild_solution {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (h : ℝ^3 →ᵇ ℝ) (hh : ContDiff ℝ 1 h) :
    ∃ T : ℝ, 0 < T ∧ ∃ v : ℝ × ℝ^3 → ℝ,
      ContDiffOn ℝ 1 v {p | |p.1| < T} ∧
      (∀ p : ℝ × ℝ^3, |p.1| < T →
        v p = p.1 * unitSphereAverage 3 h p.2 p.1 +
          p.1 ^ 2 * ∫ s : I, (1 - (s : ℝ)) *
            ((∫ ω : Direction,
              f (v (p.1 * (s : ℝ), p.2 + p.1 • ((1 - (s : ℝ)) • (ω : ℝ^3))))
                ∂((volume : Measure (ℝ^3)).toSphere)) / unitSphereArea 3)) ∧
      (∀ x, v (0, x) = 0) ∧
      ∀ x, HasDerivAt (fun t ↦ v (t, x)) (h x) 0 := by
  obtain ⟨T, hT, v, a, hv, ha, heq, hint⟩ := exists_cone_solution_with_remainder (k := 0) hf h hh
  obtain ⟨hzero, htrace⟩ := cauchy_traces_of_remainder hh hT ha heq
  refine ⟨T, hT, v, hv, ?_, hzero, htrace⟩
  intro p hp
  rw [heq p hp, hint p hp]

/-- For every `p > 1`, compactly supported C¹ velocity gives a constructed
C¹ solution of the absolute-power integral equation, with both initial traces. -/
theorem exists_mild_abs_rpow_three {p : ℝ} (hp : 1 < p)
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
      ∀ x, HasDerivAt (fun t ↦ v (t, x)) (h x) 0 := by
  have hf : ContDiff ℝ 1 (fun x : ℝ ↦ |x| ^ p) := by
    simpa only [Real.norm_eq_abs] using (contDiff_norm_rpow hp : ContDiff ℝ 1 (fun x : ℝ ↦ ‖x‖ ^ p))
  exact exists_mild_solution hf (ofCompactSupport h hh.continuous hhc) hh

end WaveEquation.SmallData.Classical.LocalPower.LowerPower
