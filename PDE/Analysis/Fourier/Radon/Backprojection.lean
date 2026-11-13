/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.Radon.Inversion
public import PDE.Analysis.Integration.Polar.SignedRadius

/-!
# Filtered Radon backprojection

Each unit normal supplies a one-dimensional Fourier transform. Multiplying
it by `|σ|^(dim E - 1)` restores the radial volume weight. Inverting this
filtered transform and averaging its values at the displacement `⟪θ, x⟫`
recovers the original function at `x`.

The factor `1/2` comes from integrating over both orientations of each radial
line. The sphere measure is the one induced by Euclidean volume, and the
Fourier convention is Mathlib's `exp(-2πi⟪ξ,x⟫)`.

`eq_integral_filtered_radonTransform` is formula (32) of Evans, §4.3.2, Theorem 5(i), with the
weight `|σ|^(n-1)` in place of `r^(n-1)`, in Mathlib's convention; the change of variables
`r = 2πσ` turns his factor `1 / (2 (2π)^n)` into `1 / 2`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.3.2, Theorem 5(i), (32), p. 199.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped RealInnerProductSpace SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace PDE.Analysis.Fourier

/-- Filter the one-dimensional Radon data by the radial Fourier weight,
then average the inverse transforms over all normals to reconstruct the
function at each continuity point. -/
theorem eq_integral_filtered_radonTransform {f : E → F}
    (hf : Integrable f) (hFf : Integrable (𝓕 f)) {x : E}
    (hx : ContinuousAt f x) :
    f x = (1 / 2 : ℝ) • ∫ θ : Metric.sphere (0 : E) 1,
      𝓕⁻ (fun σ : ℝ ↦ |σ| ^ (Module.finrank ℝ E - 1) •
        𝓕 (radonTransform f (θ : E)) σ) ⟪(θ : E), x⟫
      ∂(volume : Measure E).toSphere := by
  have hphase : Integrable (fun ξ : E ↦ 𝐞 ⟪ξ, x⟫ • 𝓕 f ξ) := by
    simpa only [inner_neg_right, neg_neg] using
      (Real.fourierIntegral_convergent_iff (-x)).mpr hFf
  have hpolar := integral_polar_addHaar_signedRadius volume hphase
  have hrec : (∫ ξ : E, 𝐞 ⟪ξ, x⟫ • 𝓕 f ξ) = f x := by
    rw [← Real.fourierInv_eq]
    exact hf.fourierInv_fourier_eq hFf hx
  rw [hrec] at hpolar
  calc
    f x = (1 / 2 : ℝ) • ((2 : ℝ) • f x) := by
      rw [smul_smul]
      norm_num
    _ = _ := by
      rw [← hpolar]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with θ
      rw [Real.fourierInv_eq]
      apply integral_congr_ae
      filter_upwards [] with σ
      rw [fourier_radonTransform hf (θ := (θ : E)) (by simp),
        real_inner_smul_left, Real.inner_apply]
      exact smul_comm _ _ _

end PDE.Analysis.Fourier

namespace SchwartzMap

open PDE.Analysis.Fourier

/-- Filtered backprojection recovers every Schwartz function pointwise,
with integrability and continuity supplied by its rapid decay. -/
theorem eq_integral_filtered_radonTransform (f : 𝓢(E, F)) (x : E) :
    f x = (1 / 2 : ℝ) • ∫ θ : Metric.sphere (0 : E) 1,
      𝓕⁻ (fun σ : ℝ ↦ |σ| ^ (Module.finrank ℝ E - 1) •
        𝓕 (radonTransform f (θ : E)) σ) ⟪(θ : E), x⟫
      ∂(volume : Measure E).toSphere :=
  PDE.Analysis.Fourier.eq_integral_filtered_radonTransform
    f.integrable (𝓕 f).integrable f.continuous.continuousAt

end SchwartzMap
