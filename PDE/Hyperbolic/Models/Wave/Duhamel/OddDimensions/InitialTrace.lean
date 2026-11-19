/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.Models.Wave.Duhamel.OddDimensions.Construction

/-!
# Initial traces of the odd-dimensional forced wave

The collapsed retarded integral and the zero-displacement velocity kernel
give zero initial displacement and velocity. Continuity of the field
and its time derivative gives joint traces in space and time.
-/

@[expose] public noncomputable section

open PDE (partialDeriv)

namespace WaveEquation

open PDE.Analysis PDE.Common

/-- The entire first derivative of the forced field vanishes initially. -/
theorem fderiv_oddDuhamelSolution_initial (k : ℕ) {f : ℝ^(2 * k + 3 + 1) → ℝ}
    (hf : ContDiffOn ℝ (k + 2) f {p | 0 ≤ p 0}) (x : ℝ^(2 * k + 3)) :
    fderiv ℝ (oddDuhamelSolution k f) (timeSpaceCons 0 x) = 0 := by
  let F (s : ℝ) := oddWavePotential k (fun y ↦ f (timeSpaceCons (max 0 s) y))
  have hreg : ContDiff ℝ 2 (retardedWave F) := contDiff_two_retardedWave
      (contDiff_two_oddWavePotential_forward k hf)
      (fun _ hj ↦ continuous_iteratedFDeriv_oddWavePotential_forward k hf hj)
      (fun _ y ↦ oddWavePotential_initial k _ y)
  have hd : fderiv ℝ (retardedWave F) (timeSpaceCons 0 x) = 0 := fderiv_retardedWave_initial
      (contDiff_two_oddWavePotential_forward k hf)
      (fun _ hj ↦ continuous_iteratedFDeriv_oddWavePotential_forward k hf hj)
      x (oddWavePotential_initial k _ x)
  change fderiv ℝ (fun p ↦ (Nat.doubleFactorial (2 * k + 1) : ℝ)⁻¹ *
    retardedWave F p) (timeSpaceCons 0 x) = 0
  rw [fderiv_const_mul (hreg.differentiable (by norm_num) _), hd, smul_zero]

/-- The time derivative has zero initial value. -/
theorem partialDeriv_oddDuhamelSolution_initial (k : ℕ) {f : ℝ^(2 * k + 3 + 1) → ℝ}
    (hf : ContDiffOn ℝ (k + 2) f {p | 0 ≤ p 0}) (x : ℝ^(2 * k + 3)) :
    (∂[0] (oddDuhamelSolution k f)) (timeSpaceCons 0 x) = 0 := by
  simp [partialDeriv, fderiv_oddDuhamelSolution_initial k hf x]

/-- The displacement tends to zero jointly in space and time. -/
theorem tendsto_oddDuhamelSolution_initial (k : ℕ) {f : ℝ^(2 * k + 3 + 1) → ℝ}
    (hf : ContDiffOn ℝ (k + 2) f {p | 0 ≤ p 0}) (x : ℝ^(2 * k + 3)) :
    Filter.Tendsto (oddDuhamelSolution k f) (nhds (timeSpaceCons 0 x)) (nhds 0) := by
  simpa only [ContinuousAt, oddDuhamelSolution_initial] using
    (contDiff_two_oddDuhamelSolution k hf).continuous.continuousAt (x := timeSpaceCons 0 x)

/-- The time derivative tends to zero jointly in space and time. -/
theorem tendsto_partialDeriv_oddDuhamelSolution_initial (k : ℕ) {f : ℝ^(2 * k + 3 + 1) → ℝ}
    (hf : ContDiffOn ℝ (k + 2) f {p | 0 ≤ p 0}) (x : ℝ^(2 * k + 3)) :
    Filter.Tendsto (∂[0] (oddDuhamelSolution k f)) (nhds (timeSpaceCons 0 x)) (nhds 0) := by
  have hreg := PDE.contDiff_partialDeriv_of_succ (m := 1) (i := 0)
    (contDiff_two_oddDuhamelSolution k hf)
  simpa only [ContinuousAt, partialDeriv_oddDuhamelSolution_initial k hf] using
    hreg.continuous.continuousAt (x := timeSpaceCons 0 x)

end WaveEquation
