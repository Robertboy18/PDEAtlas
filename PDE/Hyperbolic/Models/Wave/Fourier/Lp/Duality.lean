/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module
public import PDE.Hyperbolic.Models.Wave.Fourier.Lp.Duhamel

/-!
# Physical sine self-adjointness and forcing tests

Plancherel transports the real sine multiplier's self-adjointness to physical
L2 evolution. Bochner integration then moves the propagator onto a fixed dual
test in the causal Duhamel integral. The backward pairing's time
integrability is derived from the L1L2 forcing assumption.
-/

@[expose] public section

open MeasureTheory FourierTransform Filter Set
open scoped ENNReal

namespace WaveEquation.Fourier

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Physical sine evolution is self-adjoint, by Plancherel and the real sine
multiplier, for arbitrary L2 inputs. -/
theorem inner_sineEvolution_left (t : ℝ) (u v : Lp F 2 (volume : Measure V)) :
    inner ℂ (sineEvolution t u) v = inner ℂ u (sineEvolution t v) := by
  have hu := Lp.inner_fourier_eq (sineEvolution t u) v
  have hv := Lp.inner_fourier_eq u (sineEvolution t v)
  change inner ℂ (𝓕 (𝓕⁻ (sinePropagator (ω := fun ξ : V ↦ 2 * Real.pi * ‖ξ‖)
    (continuous_const.mul continuous_norm).measurable t (𝓕 u)))) (𝓕 v) = _ at hu
  change inner ℂ (𝓕 u) (𝓕 (𝓕⁻ (sinePropagator (ω := fun ξ : V ↦ 2 * Real.pi * ‖ξ‖)
    (continuous_const.mul continuous_norm).measurable t (𝓕 v)))) = _ at hv
  rw [fourier_fourierInv_eq] at hu hv
  exact hu.symm.trans ((inner_sinePropagator_left _ t (𝓕 u) (𝓕 v)).trans hv)

/-- Testing an L2 Duhamel integral moves the sine evolution onto the
fixed test. The time integrability follows from the L1L2 forcing assumption. -/
theorem re_inner_duhamelL2_eq_integral (a b t : ℝ)
    (f : Lp (Lp F 2 (volume : Measure V)) 1 (volume.restrict (Icc a b)))
    (φ : Lp F 2 (volume : Measure V)) :
    (inner ℂ φ (duhamelL2 a b t f)).re =
      ∫ s in Icc a b, (inner ℂ (sineEvolution (max (t - s) 0) φ) (f s)).re := by
  have hi := integrable_causalSineEvolution (L1.integrable_coeFn f) t
  rw [duhamelL2_apply, ← integral_inner hi]
  change RCLike.re (∫ s in Icc a b, inner ℂ φ (sineEvolution (max (t - s) 0) (f s))) = _
  rw [← integral_re (hi.const_inner (𝕜 := ℂ) φ)]
  apply integral_congr_ae
  exact .of_forall fun s ↦ congrArg Complex.re (inner_sineEvolution_left _ φ (f s)).symm

/-- The backward-wave pairing with arbitrary L1L2 forcing is integrable, as the Green identity
requires. -/
theorem integrable_re_inner_backwardSine (a b t : ℝ)
    (f : Lp (Lp F 2 (volume : Measure V)) 1 (volume.restrict (Icc a b)))
    (φ : Lp F 2 (volume : Measure V)) :
    Integrable (fun s ↦ (inner ℂ (sineEvolution (max (t - s) 0) φ) (f s)).re)
      (volume.restrict (Icc a b)) := by
  have hi := ((integrable_causalSineEvolution (L1.integrable_coeFn f) t).const_inner (𝕜 := ℂ) φ).re
  exact hi.congr (.of_forall fun s ↦ congrArg Complex.re (inner_sineEvolution_left _ φ (f s)).symm)

end WaveEquation.Fourier
