/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.Models.Wave.Duhamel.EvenDimensions.Construction

/-!
# Initial traces of the even-dimensional forced wave

The collapsed integral and zero initial displacement of the kernel
give the full zero initial derivative. Joint `C²` regularity then supplies
the displacement and velocity limits in space and time.
-/

@[expose] public noncomputable section

open PDE (partialDeriv)

namespace WaveEquation

open PDE.Analysis PDE.Common

/-- The entire first derivative of the constructed even-dimensional field vanishes initially. -/
theorem fderiv_evenDuhamelSolution_initial (k : ℕ) {f : ℝ^(2 * k + 2 + 1) → ℝ}
    (hf : ContDiffOn ℝ (k + 2) f {p | 0 ≤ p 0}) (x : ℝ^(2 * k + 2)) :
    fderiv ℝ (evenDuhamelSolution k f) (timeSpaceCons 0 x) = 0 :=
  fderiv_retardedWave_initial (contDiff_two_evenWaveSolution_forward k hf)
    (fun _ hj ↦ continuous_iteratedFDeriv_evenWaveSolution_forward k hf hj)
    x (evenWaveSolution_initial_position k contDiff_const x)

/-- The initial time derivative is zero. -/
theorem partialDeriv_evenDuhamelSolution_initial (k : ℕ) {f : ℝ^(2 * k + 2 + 1) → ℝ}
    (hf : ContDiffOn ℝ (k + 2) f {p | 0 ≤ p 0}) (x : ℝ^(2 * k + 2)) :
    (∂[0] (evenDuhamelSolution k f)) (timeSpaceCons 0 x) = 0 := by
  simp [partialDeriv, fderiv_evenDuhamelSolution_initial k hf x]

/-- The displacement tends to zero jointly in space and time. -/
theorem tendsto_evenDuhamelSolution_initial (k : ℕ) {f : ℝ^(2 * k + 2 + 1) → ℝ}
    (hf : ContDiffOn ℝ (k + 2) f {p | 0 ≤ p 0}) (x : ℝ^(2 * k + 2)) :
    Filter.Tendsto (evenDuhamelSolution k f) (nhds (timeSpaceCons 0 x)) (nhds 0) := by
  simpa only [ContinuousAt, evenDuhamelSolution_initial] using
    (contDiff_two_evenDuhamelSolution k hf).continuous.continuousAt (x := timeSpaceCons 0 x)

/-- The time derivative tends to zero jointly in space and time. -/
theorem tendsto_partialDeriv_evenDuhamelSolution_initial (k : ℕ) {f : ℝ^(2 * k + 2 + 1) → ℝ}
    (hf : ContDiffOn ℝ (k + 2) f {p | 0 ≤ p 0}) (x : ℝ^(2 * k + 2)) :
    Filter.Tendsto (∂[0] (evenDuhamelSolution k f)) (nhds (timeSpaceCons 0 x)) (nhds 0) := by
  have hreg := PDE.contDiff_partialDeriv_of_succ (m := 1) (i := 0)
    (contDiff_two_evenDuhamelSolution k hf)
  simpa only [ContinuousAt, partialDeriv_evenDuhamelSolution_initial k hf] using
    hreg.continuous.continuousAt (x := timeSpaceCons 0 x)

end WaveEquation
