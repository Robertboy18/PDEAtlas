/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.Radon.RealSchwartz
public import PDE.Analysis.Fourier.Schwartz.HilbertDerivatives

/-!
# Radon inversion by a Hilbert filter in even dimensions

In dimension `2k + 2`, the backprojection weight is `|σ|^(2k+1)`.
Taking an odd derivative alone leaves a sign change between positive and
negative frequencies. The Hilbert transform supplies the missing sign.

We use the convergent Hilbert principal value of the displacement
derivative. Its Fourier representation turns the filtered inversion formula
`eq_integral_filtered_radonTransform` into a physical-space formula with coefficient
`(-1)^k / (2 (2π)^(2k+1))`.

In the plane, this is `1/(4π)` times the backprojection of the Hilbert
transform of the first derivative. The angular measure is Euclidean surface
measure on the full unit circle, and the Hilbert transform itself includes
its usual `1/π` normalization.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap RealInnerProductSpace

namespace SchwartzMap

open PDE.Analysis.Fourier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Every displacement derivative of real Schwartz Radon data has a convergent
Hilbert principal value at every point. -/
theorem hasHilbertPV_iteratedDeriv_radonTransform_real (f : 𝓢(E, ℝ))
    {θ : E} (hθ : ‖θ‖ = 1) (n : ℕ) (s : ℝ) :
    PDE.Analysis.HasHilbertPV (iteratedDeriv n (radonTransform f θ)) s
      (PDE.Analysis.hilbertPV (iteratedDeriv n (radonTransform f θ)) s) := by
  rw [← radonTransformRealCLM_apply hθ f]
  exact (radonTransformRealCLM hθ f).hasHilbertPV_iteratedDeriv n s

variable [Nontrivial E]

/-- In even dimension, an odd displacement derivative followed by its Hilbert
principal value gives the backprojection filter. -/
theorem eq_integral_hilbertPV_iteratedDeriv_radonTransform_real (f : 𝓢(E, ℝ))
    (k : ℕ) (hdim : Module.finrank ℝ E = 2 * k + 2) (x : E) :
    f x = ((-1 : ℝ) ^ k / (2 * (2 * Real.pi) ^ (2 * k + 1))) *
      ∫ θ : Metric.sphere (0 : E) 1,
        PDE.Analysis.hilbertPV (iteratedDeriv (2 * k + 1) (radonTransform f (θ : E)))
          ⟪(θ : E), x⟫ ∂(volume : Measure E).toSphere := by
  let g : 𝓢(E, ℂ) := f.postcompCLM Complex.ofRealCLM
  have he (θ : Metric.sphere (0 : E) 1) :
      𝓕⁻ (fun σ : ℝ ↦ |σ| ^ (2 * k + 1) • 𝓕 (radonTransform g (θ : E)) σ)
        ⟪(θ : E), x⟫ =
      (((-1 : ℝ) ^ k / (2 * Real.pi) ^ (2 * k + 1)) *
        PDE.Analysis.hilbertPV (iteratedDeriv (2 * k + 1) (radonTransform f (θ : E)))
          ⟪(θ : E), x⟫ : ℝ) := by
    let r := radonTransformRealCLM (θ := (θ : E)) (by simp) f
    have hr : (r : ℝ → ℝ) = radonTransform f (θ : E) :=
      radonTransformRealCLM_apply (by simp) f
    have hg : radonTransform g (θ : E) = fun y ↦ (r y : ℂ) := by
      funext y
      rw [hr]
      exact radonTransform_ofReal f (θ : E) y
    rw [hg, ← hr]
    exact fourierInv_odd_abs_pow_smul_fourier_real r k ⟪(θ : E), x⟫
  have h := g.eq_integral_filtered_radonTransform x
  rw [hdim, show 2 * k + 2 - 1 = 2 * k + 1 by omega] at h
  simp_rw [he] at h
  rw [integral_complex_ofReal, integral_const_mul] at h
  have hr := congrArg Complex.re h
  simp only [Complex.real_smul, ← Complex.ofReal_mul, Complex.ofReal_re] at hr
  change f x = (1 / 2 : ℝ) * (((-1 : ℝ) ^ k / (2 * Real.pi) ^ (2 * k + 1)) *
    ∫ θ : Metric.sphere (0 : E) 1,
      PDE.Analysis.hilbertPV (iteratedDeriv (2 * k + 1) (radonTransform f (θ : E)))
        ⟪(θ : E), x⟫ ∂(volume : Measure E).toSphere) at hr
  convert hr using 1
  ring

/-- In the plane, inversion uses the Hilbert transform of the first
displacement derivative, with coefficient `1/(4π)` for the full unit circle. -/
theorem eq_integral_hilbertPV_deriv_radonTransform_real (f : 𝓢(E, ℝ))
    (hdim : Module.finrank ℝ E = 2) (x : E) :
    f x = (1 / (4 * Real.pi)) *
      ∫ θ : Metric.sphere (0 : E) 1,
        PDE.Analysis.hilbertPV (deriv (radonTransform f (θ : E)))
          ⟪(θ : E), x⟫ ∂(volume : Measure E).toSphere := by
  have h := f.eq_integral_hilbertPV_iteratedDeriv_radonTransform_real 0 hdim x
  norm_num [iteratedDeriv_succ, iteratedDeriv_zero] at h
  convert h using 1
  ring

end SchwartzMap
