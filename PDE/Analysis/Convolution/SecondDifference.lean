/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Convolution

/-!
# Second differences of convolutions

Convolution with a nonnegative kernel of mass one preserves an upper bound on
second differences. Only points sampled by the kernel need satisfy the bound.
Continuous input suffices: compact support of the kernel supplies integrability
even for unbounded input.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open MeasureTheory Function
open scoped Convolution

variable {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

/-- A bound on increments passes through a nonnegative convolution kernel of mass one.
Only increments sampled by the kernel need satisfy the bound. The kernel is integrable because
its integral is `1`; no continuity of the kernel or local finiteness of `μ` is needed. -/
theorem dist_convolution_le_of_dist_le
    {ρ f : E → ℝ} (hcompact : HasCompactSupport ρ)
    (hnonneg : ∀ y, 0 ≤ ρ y) (hmass : ∫ y, ρ y ∂μ = 1) (hf : Continuous f)
    (x z : E) {a : ℝ}
    (hbound : ∀ y ∈ support ρ, dist (f (x - y)) (f (z - y)) ≤ a) :
    dist ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) x)
      ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) z) ≤ a := by
  have hρi : Integrable ρ μ := Integrable.of_integral_ne_zero (by rw [hmass]; exact one_ne_zero)
  have hint (b : E) : Integrable (fun y ↦ ρ y * f (b - y)) μ :=
    hcompact.convolutionExists_left_of_continuous_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hρi.locallyIntegrable hf b
  have hright : Integrable (fun y ↦ ρ y * a) μ := hρi.mul_const _
  simp only [dist_eq_norm, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [← integral_sub (hint x) (hint z)]
  calc
    _ ≤ ∫ y, ‖ρ y * f (x - y) - ρ y * f (z - y)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, ρ y * a ∂μ := by
      apply integral_mono ((hint x).sub (hint z)).norm hright
      intro y
      by_cases hy : ρ y = 0
      · simp [hy]
      change ‖ρ y * f (x - y) - ρ y * f (z - y)‖ ≤ ρ y * a
      simpa only [← mul_sub, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hnonneg y),
        Real.dist_eq] using mul_le_mul_of_nonneg_left (hbound y hy) (hnonneg y)
    _ = a := by rw [integral_mul_const, hmass, one_mul]

/-- A local second-difference bound passes through a positive convolution kernel.
The hypothesis is imposed precisely on the translates sampled by its support. -/
theorem second_difference_convolution_le
    {ρ f : E → ℝ} (hcompact : HasCompactSupport ρ)
    (hnonneg : ∀ y, 0 ≤ ρ y) (hmass : ∫ y, ρ y ∂μ = 1) (hf : Continuous f)
    (x z : E) {C : ℝ}
    (hsemi : ∀ y ∈ support ρ,
      f (x - y + z) - 2 * f (x - y) + f (x - y - z) ≤ C * ‖z‖ ^ 2) :
    (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) (x + z) -
        2 * (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) x +
        (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) (x - z) ≤ C * ‖z‖ ^ 2 := by
  have hρi : Integrable ρ μ := Integrable.of_integral_ne_zero (by rw [hmass]; exact one_ne_zero)
  have hint (a : E) : Integrable (fun y ↦ ρ y * f (a - y)) μ :=
    hcompact.convolutionExists_left_of_continuous_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hρi.locallyIntegrable hf a
  have hright : Integrable (fun y ↦ ρ y * (C * ‖z‖ ^ 2)) μ := hρi.mul_const _
  have hdiff : Integrable (fun y ↦ ρ y * f (x + z - y) - 2 * (ρ y * f (x - y))) μ :=
    (hint (x + z)).sub ((hint x).const_mul 2)
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [← integral_const_mul, ← integral_sub (hint (x + z)) ((hint x).const_mul 2),
    ← integral_add hdiff (hint (x - z))]
  calc
    _ ≤ ∫ y, ρ y * (C * ‖z‖ ^ 2) ∂μ := by
      apply integral_mono (hdiff.add (hint (x - z))) hright
      intro y
      by_cases hy : ρ y = 0
      · simp [hy]
      have h := mul_le_mul_of_nonneg_left (hsemi y hy) (hnonneg y)
      dsimp only [Pi.add_apply]
      rw [show x + z - y = x - y + z by abel,
        show x - z - y = x - y - z by abel]
      nlinarith
    _ = C * ‖z‖ ^ 2 := by rw [integral_mul_const, hmass, one_mul]

end PDE.Analysis
