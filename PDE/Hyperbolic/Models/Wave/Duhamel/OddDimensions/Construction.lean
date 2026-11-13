/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.Models.Wave.Duhamel.OddDimensions.SourceFamily
public import PDE.Hyperbolic.Models.Wave.Duhamel.SpaceTime

/-!
# Odd-dimensional Duhamel construction

The zero-displacement wave potential is integrated over forcing time.
Clipping only that index supplies a signed-time construction from the
forward source. Its `C²` regularity uses exactly `k+2` source derivatives in
dimension `2k+3`, with no support or growth restriction.
-/

@[expose] public noncomputable section

open PDE (time)

namespace WaveEquation

open PDE.Analysis PDE.Common

/-- The normalized retarded integral of the odd-dimensional velocity potential. -/
def oddDuhamelSolution (k : ℕ) (f : ℝ^(2 * k + 3 + 1) → ℝ) :
    ℝ^(2 * k + 3 + 1) → ℝ :=
  fun p ↦ (Nat.doubleFactorial (2 * k + 1) : ℝ)⁻¹ *
    retardedIntegral (fun s q ↦
      oddWavePotential k (fun x ↦ f (timeSpaceCons (max 0 s) x))
        (joinSpaceTime q)) (splitSpaceTime p)

/-- The constructed field is jointly `C²`, without extending the source smoothly
across time zero. The clipped index is only required to be continuous. -/
theorem contDiff_two_oddDuhamelSolution (k : ℕ) {f : ℝ^(2 * k + 3 + 1) → ℝ}
    (hf : ContDiffOn ℝ (k + 2) f {p | 0 ≤ p 0}) :
    ContDiff ℝ 2 (oddDuhamelSolution k f) :=
  contDiff_const.mul (contDiff_two_retardedWave (contDiff_two_oddWavePotential_forward k hf)
    (fun _ hj ↦ continuous_iteratedFDeriv_oddWavePotential_forward k hf hj)
    (fun _ x ↦ oddWavePotential_initial k _ x))

/-- The formula has zero initial displacement. -/
theorem oddDuhamelSolution_initial (k : ℕ) (f : ℝ^(2 * k + 3 + 1) → ℝ) (x : ℝ^(2 * k + 3)) :
    oddDuhamelSolution k f (timeSpaceCons 0 x) = 0 := by
  simp [oddDuhamelSolution, retardedIntegral, splitSpaceTime, time]

end WaveEquation
