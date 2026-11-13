/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.Radon.Schwartz
public import PDE.Hyperbolic.Models.Wave.Fourier.Filtered
public import PDE.Hyperbolic.Models.Wave.Radon.Representation

/-!
# Radon wave formulas in odd dimension

In dimension `2k+1`, the radial filter is the even power `σ^(2k)`. Moving it
onto the Radon data turns the filtered wave into ordinary displacement
derivatives in the d'Alembert formula. In three dimensions the velocity integral
is an integral of a second derivative, so the fundamental theorem of calculus
reduces it to two first derivatives.

The formulas apply at every real time and use full Euclidean surface measure.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped RealInnerProductSpace SchwartzMap

namespace WaveEquation.Fourier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- In odd dimension, the wave is reconstructed from ordinary even derivatives
of the Radon data and their one-dimensional characteristic integrals. -/
theorem cauchySolution_eq_integral_iteratedDeriv_radonTransform (g h : 𝓢(E, ℂ)) (k : ℕ)
    (hdim : Module.finrank ℝ E = 2 * k + 1) (t : ℝ) (x : E) :
    cauchySolution g h (t, x) =
      ((-1 : ℝ) ^ k / (4 * (2 * Real.pi) ^ (2 * k))) •
        ∫ θ : Metric.sphere (0 : E) 1,
          iteratedDeriv (2 * k) (PDE.Analysis.Fourier.radonTransform g (θ : E))
              (⟪(θ : E), x⟫ + t) +
            iteratedDeriv (2 * k) (PDE.Analysis.Fourier.radonTransform g (θ : E))
              (⟪(θ : E), x⟫ - t) +
            (∫ y in ⟪(θ : E), x⟫ - t..⟪(θ : E), x⟫ + t,
              iteratedDeriv (2 * k) (PDE.Analysis.Fourier.radonTransform h (θ : E)) y)
          ∂(volume : Measure E).toSphere := by
  rw [cauchySolution_eq_integral_filtered_radonTransform, hdim, Nat.add_sub_cancel]
  have he (θ : Metric.sphere (0 : E) 1) : 𝓕⁻ (fun σ : ℝ ↦ |σ| ^ (2 * k) •
        waveValue (2 * Real.pi * |σ|) (𝓕 (PDE.Analysis.Fourier.radonTransform g (θ : E)) σ)
          (𝓕 (PDE.Analysis.Fourier.radonTransform h (θ : E)) σ) t) ⟪(θ : E), x⟫ =
      ((-1 : ℝ) ^ k / (2 * (2 * Real.pi) ^ (2 * k))) •
        (iteratedDeriv (2 * k) (PDE.Analysis.Fourier.radonTransform g (θ : E)) (⟪(θ : E), x⟫ + t) +
          iteratedDeriv (2 * k) (PDE.Analysis.Fourier.radonTransform g (θ : E)) (⟪(θ : E), x⟫ - t) +
          ∫ y in ⟪(θ : E), x⟫ - t..⟪(θ : E), x⟫ + t,
            iteratedDeriv (2 * k) (PDE.Analysis.Fourier.radonTransform h (θ : E)) y) := by
    simp_rw [(even_two_mul k).pow_abs, waveValue_real_frequency]
    rw [← SchwartzMap.radonTransformCLM_apply (θ := (θ : E)) (by simp) g,
      ← SchwartzMap.radonTransformCLM_apply (θ := (θ : E)) (by simp) h]
    rw [filtered_fourierSolution_eq_characteristicIntegral]
    simp only [Complex.real_smul]
    push_cast
    ring
  simp_rw [he]
  rw [integral_smul, smul_smul]
  congr 1
  ring

omit [Nontrivial E] in
private theorem integral_secondDeriv_radonTransform (h : 𝓢(E, ℂ)) {θ : E} (hθ : ‖θ‖ = 1) (a b : ℝ) :
    (∫ y in a..b, deriv (deriv (PDE.Analysis.Fourier.radonTransform h θ)) y) =
      deriv (PDE.Analysis.Fourier.radonTransform h θ) b -
        deriv (PDE.Analysis.Fourier.radonTransform h θ) a := by
  rw [← SchwartzMap.radonTransformCLM_apply hθ h]
  let H := SchwartzMap.radonTransformCLM hθ h
  have hdiff : Differentiable ℝ (deriv (H : ℝ → ℂ)) := (SchwartzMap.derivCLM ℂ ℂ H).differentiable
  have hi : IntervalIntegrable (deriv (deriv (H : ℝ → ℂ))) volume a b :=
    (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ H)).integrable.intervalIntegrable
  exact intervalIntegral.integral_deriv_eq_sub (fun y _ ↦ hdiff y) hi

/-- In three dimensions, the wave formula uses second derivatives of the
displacement data and first derivatives of the velocity data. -/
theorem cauchySolution_eq_integral_secondDeriv_radonTransform
    (g h : 𝓢(E, ℂ)) (hdim : Module.finrank ℝ E = 3) (t : ℝ) (x : E) :
    cauchySolution g h (t, x) = (-1 / (16 * Real.pi ^ 2) : ℝ) •
      ∫ θ : Metric.sphere (0 : E) 1,
        deriv (deriv (PDE.Analysis.Fourier.radonTransform g (θ : E)))
            (⟪(θ : E), x⟫ + t) +
          deriv (deriv (PDE.Analysis.Fourier.radonTransform g (θ : E)))
            (⟪(θ : E), x⟫ - t) +
          (deriv (PDE.Analysis.Fourier.radonTransform h (θ : E))
              (⟪(θ : E), x⟫ + t) -
            deriv (PDE.Analysis.Fourier.radonTransform h (θ : E))
              (⟪(θ : E), x⟫ - t))
        ∂(volume : Measure E).toSphere := by
  have hw := cauchySolution_eq_integral_iteratedDeriv_radonTransform g h 1 hdim t x
  norm_num only [Nat.mul_one, pow_one, iteratedDeriv_succ, iteratedDeriv_zero] at hw
  have hi (θ : Metric.sphere (0 : E) 1) (a b : ℝ) :=
    integral_secondDeriv_radonTransform h (θ := (θ : E)) (by simp) a b
  simp_rw [hi] at hw
  convert hw using 1
  congr 1
  ring

end WaveEquation.Fourier
