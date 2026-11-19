/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.Models.Wave.Duhamel.OddDimensions.Construction

/-!
# The forced equation for the odd-dimensional Duhamel formula

The homogeneous velocity potential has age-zero velocity `(2k+1)‼ f`.
The same factor normalizes the retarded integral. Its interior wave residual
vanishes at positive ages, so the second Leibniz endpoint is exactly the source.
-/

@[expose] public noncomputable section

namespace WaveEquation

open PDE.Analysis PDE.Common

/-- The raw-source Duhamel formula has the prescribed wave residual,
including on the initial hyperplane. -/
theorem waveOperator_oddDuhamelSolution (k : ℕ) {f : ℝ^(2 * k + 3 + 1) → ℝ}
    (hf : ContDiffOn ℝ (k + 2) f {p | 0 ≤ p 0}) {p : ℝ^(2 * k + 3 + 1)} (hp : 0 ≤ p 0) :
    waveOperator (oddDuhamelSolution k f) p = f p := by
  let F (s : ℝ) := oddWavePotential k (fun y ↦ f (timeSpaceCons (max 0 s) y))
  have hF (s : ℝ) : ContDiff ℝ 2 (F s) := contDiff_two_oddWavePotential_forward k hf s
  have hjet (j : ℕ) (hj : j ≤ 2) : Continuous
      (fun q : ℝ × ℝ^(2 * k + 3 + 1) ↦ iteratedFDeriv ℝ j (F q.1) q.2) :=
    continuous_iteratedFDeriv_oddWavePotential_forward k hf hj
  have hzero (s : ℝ) (x : ℝ^(2 * k + 3)) : F s (timeSpaceCons 0 x) = 0 :=
    oddWavePotential_initial k _ x
  let x := spatialPartCLM (2 * k + 3) p
  let t := p 0
  have hpoint : timeSpaceCons t x = p := timeSpaceCons_spatialPartCLM p
  have hslice (s : ℝ) : ContDiff ℝ (k + 2) (fun y ↦ f (timeSpaceCons (max 0 s) y)) :=
    hf.contDiff_forward_spatialSlice (le_max_left 0 s)
  have he := waveOperator_retardedWave hF hjet hzero x t
  have hi : (∫ s in (0 : ℝ)..t, waveOperator (F s) (timeSpaceCons (t - s) x)) = 0 := by
    calc
      _ = ∫ _s in (0 : ℝ)..t, (0 : ℝ) := by
        refine intervalIntegral.integral_congr_Ioo_of_le hp fun s hs ↦ ?_
        exact waveOperator_oddWavePotential k (hslice s) (by simpa using sub_pos.mpr hs.2)
      _ = 0 := by simp
  have hb : (∂[0] (F t)) (timeSpaceCons 0 x) =
      (Nat.doubleFactorial (2 * k + 1) : ℝ) * f p := by
    rw [partialDeriv_oddWavePotential_initial k ((hslice t).of_le (by norm_cast; omega))]
    rw [max_eq_right (show 0 ≤ t from hp), hpoint]
  rw [hi, add_zero, hb] at he
  have hγ : (Nat.doubleFactorial (2 * k + 1) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.doubleFactorial_pos _).ne'
  change waveOperator (fun q ↦ (Nat.doubleFactorial (2 * k + 1) : ℝ)⁻¹ * retardedWave F q) p = _
  rw [waveOperator_const_mul, ← hpoint, he]
  simp only [← mul_assoc, inv_mul_cancel₀ hγ, one_mul, hpoint]

end WaveEquation
