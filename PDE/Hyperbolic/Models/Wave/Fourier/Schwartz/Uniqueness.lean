/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module
public import PDE.Hyperbolic.Models.Wave.Fourier.Schwartz.Cauchy
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FiniteForwardUniqueness

/-!
# Identification of the classical Fourier wave

The Fourier construction is the unique classical homogeneous wave on a finite
forward band. The competing wave needs interior C2 regularity and forward C1
traces. Finite-band nonlinear uniqueness applies, specialized to zero nonlinearity. Initial velocity
is the right derivative at time zero.
-/

@[expose] public section

open PDE.Common MeasureTheory Set
open scoped ENNReal SchwartzMap

namespace WaveEquation.Fourier

/-- The constructed Fourier wave is the classical solution on a finite
forward band. The competing field needs no spatial integrability or support assumption. -/
theorem eq_realSolution_on_finite_forward_strip {n : ℕ} [Fact (0 < n)] {u : ℝ^(n + 1) → ℝ} {T : ℝ}
    (g h : 𝓢(ℝ^n, ℝ)) (hu : ContDiffOn ℝ 2 u {p | p 0 ∈ Ioo 0 T})
    (hu₀ : ContDiffOn ℝ 1 u {p | p 0 ∈ Ico 0 T})
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x, waveOperator u (timeSpaceCons t x) = 0)
    (hpos : ∀ x, u (timeSpaceCons 0 x) = g x)
    (hvel : ∀ x, derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = h x) :
    ∀ t ∈ Ico 0 T, ∀ x, u (timeSpaceCons t x) = realSolution g h (timeSpaceCons t x) := by
  have hv := contDiff_two_realSolution g h
  apply PDE.Hyperbolic.NonlinearWave.Cauchy.eq_on_finite_forward_strip
    (f := fun _ ↦ 0) (LocallyLipschitz.const 0) hu hv.contDiffOn hu₀
      (hv.of_le (by norm_num)).contDiffOn
  · intro t ht x
    simpa only [add_zero] using hwave t ht x
  · intro t _ x
    simpa only [add_zero] using waveOperator_realSolution g h (timeSpaceCons t x)
  · exact fun x ↦ (hpos x).trans (realSolution_initial_position g h x).symm
  · intro x
    have hd := PDE.hasDerivAt_timeSpaceCons (realSolution g h) 0 x
      (hv.differentiable (by norm_num)).differentiableAt
    exact (hvel x).trans ((hd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici 0)).trans
      (partialDeriv_realSolution_initial_velocity g h x)).symm

end WaveEquation.Fourier
