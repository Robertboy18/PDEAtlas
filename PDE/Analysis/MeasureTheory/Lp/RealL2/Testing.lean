/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.Holder

/-!
# Scalar tests of real L² classes and their integrals

The L² pairing commutes with Bochner integration. On a finite-dimensional
real domain, smooth compactly supported scalar tests distinguish L² classes by
Mathlib's fundamental lemma.
-/

@[expose] public noncomputable section

namespace MeasureTheory.Lp

open scoped ContDiff

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}

/-- Pairing the Bochner integral of an L² curve with a fixed L² function
equals the integral of the scalar pairings. -/
theorem integral_mul_integral {u : α → Lp ℝ 2 ν} (hu : Integrable u μ)
    {φ : β → ℝ} (hφ : MemLp φ 2 ν) :
    (∫ x, (∫ t, u t ∂μ) x * φ x ∂ν) =
      ∫ t, (∫ x, (u t) x * φ x ∂ν) ∂μ := by
  let v : Lp ℝ 2 ν := hφ.toLp φ
  let B : Lp ℝ 2 ν →L[ℝ] ℝ :=
    (ContinuousLinearMap.lpPairing ν 2 2 (ContinuousLinearMap.mul ℝ ℝ)).flip v
  have hB (w : Lp ℝ 2 ν) : B w = ∫ x, w x * φ x ∂ν := by
    change ContinuousLinearMap.lpPairing ν 2 2
      (ContinuousLinearMap.mul ℝ ℝ) w v = _
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hφ.coeFn_toLp] with x hx
    change w x * v x = _
    rw [show v x = φ x from hx]
  simpa only [hB] using (B.integral_comp_comm hu).symm

/-- Smooth compactly supported scalar tests determine a real L² class. -/
theorem eq_of_integral_contDiff_mul_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ν : Measure E} [IsLocallyFiniteMeasure ν]
    {u v : Lp ℝ 2 ν}
    (h : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, u x * φ x ∂ν) = ∫ x, v x * φ x ∂ν) :
    u = v := by
  apply Lp.ext
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp u).locallyIntegrable (by norm_num))
    ((Lp.memLp v).locallyIntegrable (by norm_num))
  intro φ hφ hc
  simpa only [smul_eq_mul, mul_comm] using h φ hφ hc

end MeasureTheory.Lp
