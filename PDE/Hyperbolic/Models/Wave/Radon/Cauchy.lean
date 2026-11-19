/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Fourier.Schwartz.Cauchy
public import PDE.Hyperbolic.Models.Wave.Radon.EvenDimension

/-!
# The even-dimensional Radon formula and the wave Cauchy problem

The Hilbert-filtered Radon formula represents the real classical Fourier
solution in the library's time-first Euclidean coordinates. Consequently,
the formula has the regularity, wave equation and assigned initial data
proved for that solution.
-/

@[expose] public noncomputable section

open MeasureTheory
open PDE.Common PDE.Analysis.Fourier
open scoped RealInnerProductSpace SchwartzMap

namespace WaveEquation.Fourier

/-- The classical wave with real Schwartz data has the Hilbert-filtered Radon
formula in every positive even dimension, at every spacetime point. -/
theorem realSolution_eq_integral_hilbertPV_iteratedDeriv_radonTransform
    {n : ℕ} (g h : 𝓢(ℝ^n, ℝ)) (k : ℕ) (hdim : n = 2 * k + 2) (p : ℝ^(n + 1)) :
    realSolution g h p =
      ((-1 : ℝ) ^ k / (4 * (2 * Real.pi) ^ (2 * k + 1))) *
        ∫ θ : Metric.sphere (0 : ℝ^n) 1,
          PDE.Analysis.hilbertPV
              (iteratedDeriv (2 * k + 1) (radonTransform g (θ : ℝ^n)))
              (⟪(θ : ℝ^n), spatialPartCLM n p⟫ + PDE.time p) +
            PDE.Analysis.hilbertPV
              (iteratedDeriv (2 * k + 1) (radonTransform g (θ : ℝ^n)))
              (⟪(θ : ℝ^n), spatialPartCLM n p⟫ - PDE.time p) +
            (∫ y in ⟪(θ : ℝ^n), spatialPartCLM n p⟫ - PDE.time p..
                ⟪(θ : ℝ^n), spatialPartCLM n p⟫ + PDE.time p,
              PDE.Analysis.hilbertPV
                (iteratedDeriv (2 * k + 1) (radonTransform h (θ : ℝ^n))) y)
          ∂(volume : Measure (ℝ^n)).toSphere := by
  subst n
  have hw := congrArg Complex.re
    (cauchySolution_eq_integral_hilbertPV_iteratedDeriv_radonTransform g h k (by simp)
      (PDE.time p) (spatialPartCLM (2 * k + 2) p))
  simpa only [realSolution, Function.comp_apply, timeSpaceContinuousLinearEquiv_apply,
    spatialPartCLM_eq_spatialPart, Complex.reCLM_apply, Complex.ofReal_re] using hw

end WaveEquation.Fourier
