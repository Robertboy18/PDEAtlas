/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Deriv.LinearMap
public import PDE.Analysis.Fourier.Radon.OddDimension

/-!
# Real-valued Radon inversion

The Fourier proof uses complex scalars, but the hyperplane transform of a real
function is real. Embedding into the complex numbers commutes with integration
and differentiation. Taking the real part therefore gives smoothness and
odd-dimensional inversion for the original real data, with the same constants.

The formulas below use ordinary derivatives of the hyperplane integral.
Integration over the unit sphere uses Euclidean surface measure.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped SchwartzMap RealInnerProductSpace

namespace PDE.Analysis.Fourier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Embedding real values into the complex numbers commutes with each
hyperplane integral. This also holds under the integral's zero convention. -/
theorem radonTransform_ofReal (f : E → ℝ) (θ : E) (s : ℝ) :
    radonTransform (fun x ↦ (f x : ℂ)) θ s =
      Complex.ofReal (radonTransform f θ s) := by
  exact integral_complex_ofReal

end PDE.Analysis.Fourier

namespace SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open PDE.Analysis.Fourier

/-- The hyperplane integral of real Schwartz data is smooth in its displacement. -/
theorem contDiff_radonTransform_real (f : 𝓢(E, ℝ)) {θ : E}
    (hθ : ‖θ‖ = 1) (n : ℕ∞) : ContDiff ℝ n (radonTransform f θ) := by
  let g : 𝓢(E, ℂ) := f.postcompCLM Complex.ofRealCLM
  have he : radonTransform f θ = Complex.reCLM ∘ radonTransform g θ := by
    funext s
    change radonTransform f θ s = (radonTransform (fun x ↦ (f x : ℂ)) θ s).re
    rw [radonTransform_ofReal]
    rfl
  rw [he]
  exact Complex.reCLM.contDiff.comp (g.contDiff_radonTransform hθ n)

variable [Nontrivial E]

/-- Real Schwartz data in odd dimension are reconstructed from the even
displacement derivative of their Radon transform. -/
theorem eq_integral_iteratedDeriv_radonTransform_real (f : 𝓢(E, ℝ)) (k : ℕ)
    (hdim : Module.finrank ℝ E = 2 * k + 1) (x : E) :
    f x = ((-1 : ℝ) ^ k / (2 * (2 * Real.pi) ^ (2 * k))) *
      ∫ θ : Metric.sphere (0 : E) 1,
        iteratedDeriv (2 * k) (radonTransform f (θ : E)) ⟪(θ : E), x⟫
          ∂(volume : Measure E).toSphere := by
  let g : 𝓢(E, ℂ) := f.postcompCLM Complex.ofRealCLM
  have he (θ : E) : radonTransform g θ =
      fun s ↦ Complex.ofReal (radonTransform f θ s) := by
    funext s
    exact radonTransform_ofReal f θ s
  have h := g.eq_integral_iteratedDeriv_radonTransform k hdim x
  simp_rw [he] at h
  have hd (θ : Metric.sphere (0 : E) 1) :
      iteratedDeriv (2 * k) (fun s ↦ Complex.ofReal (radonTransform f (θ : E) s))
        ⟪(θ : E), x⟫ =
      Complex.ofReal (iteratedDeriv (2 * k) (radonTransform f (θ : E)) ⟪(θ : E), x⟫) :=
    Complex.ofRealCLM.iteratedDeriv_comp_left
      (f.contDiff_radonTransform_real (by simp) _).contDiffAt
  simp_rw [hd] at h
  rw [integral_complex_ofReal] at h
  apply Complex.ofReal_injective
  simpa only [g, postcompCLM_apply, Complex.ofRealCLM_apply, Complex.ofReal_mul,
    Complex.real_smul] using h

/-- Three-dimensional real inversion, with its `-1/(8π²)` coefficient. -/
theorem eq_integral_secondDeriv_radonTransform_real (f : 𝓢(E, ℝ))
    (hdim : Module.finrank ℝ E = 3) (x : E) :
    f x = (-1 / (8 * Real.pi ^ 2) : ℝ) *
      ∫ θ : Metric.sphere (0 : E) 1,
        deriv (deriv (radonTransform f (θ : E))) ⟪(θ : E), x⟫
          ∂(volume : Measure E).toSphere := by
  have h := f.eq_integral_iteratedDeriv_radonTransform_real 1 hdim x
  norm_num [iteratedDeriv_succ, iteratedDeriv_zero] at h
  convert h using 1
  congr 2
  ring

end SchwartzMap
