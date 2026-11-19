/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.Models.Wave.Duhamel.EvenDimensions.Construction

/-!
# The forced equation for the even-dimensional Duhamel formula

The homogeneous wave has initial velocity equal to the forcing slice.
Its positive-age residual vanishes. The second Leibniz formula therefore gives
the original forcing, including at time zero, with the normalization already
contained in the homogeneous constructor.
-/

@[expose] public noncomputable section

namespace WaveEquation

open PDE.Analysis PDE.Common

/-- The even-dimensional retarded field has exactly the prescribed residual. -/
theorem waveOperator_evenDuhamelSolution (k : ℕ) {f : ℝ^(2 * k + 2 + 1) → ℝ}
    (hf : ContDiffOn ℝ (k + 2) f {p | 0 ≤ p 0}) {p : ℝ^(2 * k + 2 + 1)} (hp : 0 ≤ p 0) :
    waveOperator (evenDuhamelSolution k f) p = f p := by
  let F (s : ℝ) := evenWaveSolution k (fun _ ↦ 0) (fun y ↦ f (timeSpaceCons (max 0 s) y))
  have hF (s : ℝ) : ContDiff ℝ 2 (F s) := contDiff_two_evenWaveSolution_forward k hf s
  have hjet (j : ℕ) (hj : j ≤ 2) : Continuous
      (fun q : ℝ × ℝ^(2 * k + 2 + 1) ↦ iteratedFDeriv ℝ j (F q.1) q.2) :=
    continuous_iteratedFDeriv_evenWaveSolution_forward k hf hj
  have hzero (s : ℝ) (x : ℝ^(2 * k + 2)) : F s (timeSpaceCons 0 x) = 0 :=
    evenWaveSolution_initial_position k contDiff_const x
  let x := spatialPartCLM (2 * k + 2) p
  let t := p 0
  have hpoint : timeSpaceCons t x = p := timeSpaceCons_spatialPartCLM p
  have hslice (s : ℝ) : ContDiff ℝ (k + 2) (fun y ↦ f (timeSpaceCons (max 0 s) y)) :=
    hf.contDiff_forward_spatialSlice (le_max_left 0 s)
  have he := waveOperator_retardedWave hF hjet hzero x t
  have hi : (∫ s in (0 : ℝ)..t, waveOperator (F s) (timeSpaceCons (t - s) x)) = 0 := by
    calc
      _ = ∫ _s in (0 : ℝ)..t, (0 : ℝ) := by
        refine intervalIntegral.integral_congr_Ioo_of_le hp fun s hs ↦ ?_
        exact waveOperator_evenWaveSolution k contDiff_const (hslice s)
          (by simpa using sub_pos.mpr hs.2)
      _ = 0 := by simp
  have hb : (∂[0] (F t)) (timeSpaceCons 0 x) =
      f p := by
    rw [partialDeriv_evenWaveSolution_initial_velocity k contDiff_const (hslice t)]
    rw [max_eq_right (show 0 ≤ t from hp), hpoint]
  rw [hi, add_zero, hb] at he
  change waveOperator (retardedWave F) p = _
  rwa [hpoint] at he

end WaveEquation
