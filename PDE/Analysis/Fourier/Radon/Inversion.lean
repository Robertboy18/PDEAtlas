/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.Radon.Basic
public import PDE.Analysis.Integration.Polar
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Reconstructing a function from its Radon transform

The Fourier slice theorem supplies the Fourier transform on each ray from
the origin. Polar integration then assembles these rays into the ordinary
Fourier inversion integral. The radial factor is `r^(dim E - 1)` and the
angular measure is the sphere measure induced by Euclidean volume.

The first theorem applies whenever both the function and its Fourier
transform are integrable, at each point of continuity. For a Schwartz
function these hypotheses follow from Mathlib, giving pointwise
reconstruction everywhere. In particular, two Schwartz functions agree if
their Radon data agree for almost every normal and almost every displacement.

The ambient space must have positive dimension: in dimension zero the
unit sphere is empty and there are no hyperplane data to reconstruct from.

`eq_integral_fourier_radonTransform` is the form with `r > 0` in step 1 of Evans's proof of
Theorem 5 of §4.3.2: Fourier inversion in polar coordinates together with the slice theorem,
his Theorem 4, in Mathlib's convention and with the sphere integral outside.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.3.2, Theorem 4, p. 198, and step 1 of the proof of
  Theorem 5, p. 199. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped RealInnerProductSpace SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace PDE.Analysis.Fourier

/-- Reconstruct an integrable function with integrable Fourier transform from
its Radon data at each continuity point. Polar volume supplies the radial
weight and the angular normalization. -/
theorem eq_integral_fourier_radonTransform {f : E → F}
    (hf : Integrable f) (hFf : Integrable (𝓕 f)) {x : E}
    (hx : ContinuousAt f x) :
    f x = ∫ θ : Metric.sphere (0 : E) 1,
      (∫ r in Set.Ioi (0 : ℝ),
        r ^ (Module.finrank ℝ E - 1) •
          (𝐞 (r * ⟪(θ : E), x⟫) • 𝓕 (radonTransform f (θ : E)) r))
      ∂(volume : Measure E).toSphere := by
  rw [← hf.fourierInv_fourier_eq hFf hx, Real.fourierInv_eq]
  have hphase : Integrable (fun ξ : E ↦ 𝐞 ⟪ξ, x⟫ • 𝓕 f ξ) := by
    simpa only [inner_neg_right, neg_neg] using
      (Real.fourierIntegral_convergent_iff (-x)).mpr hFf
  rw [integral_polar_addHaar_iterated_sphereFirst volume _ hphase]
  apply integral_congr_ae
  filter_upwards with θ
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  dsimp only
  rw [fourier_radonTransform hf (θ := (θ : E)) (by simp), real_inner_smul_left]

end PDE.Analysis.Fourier

namespace SchwartzMap

open PDE.Analysis.Fourier

/-- The Fourier synthesis of all hyperplane integrals recovers a Schwartz
function at every point. No additional decay or Fourier-integrability
hypotheses are needed. -/
theorem eq_integral_fourier_radonTransform (f : 𝓢(E, F)) (x : E) :
    f x = ∫ θ : Metric.sphere (0 : E) 1,
      (∫ r in Set.Ioi (0 : ℝ),
        r ^ (Module.finrank ℝ E - 1) •
          (𝐞 (r * ⟪(θ : E), x⟫) • 𝓕 (radonTransform f (θ : E)) r))
      ∂(volume : Measure E).toSphere :=
  PDE.Analysis.Fourier.eq_integral_fourier_radonTransform
    f.integrable (𝓕 f).integrable f.continuous.continuousAt

/-- Radon data determine a Schwartz function uniquely, even if the data
are specified only almost everywhere in the normal and displacement. -/
theorem eq_of_radonTransform_ae_eq (f g : 𝓢(E, F))
    (h : ∀ᵐ θ : Metric.sphere (0 : E) 1 ∂(volume : Measure E).toSphere,
      radonTransform f (θ : E) =ᵐ[volume] radonTransform g (θ : E)) : f = g := by
  ext x
  rw [eq_integral_fourier_radonTransform f x, eq_integral_fourier_radonTransform g x]
  apply integral_congr_ae
  filter_upwards [h] with θ hθ
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  dsimp only
  rw [Real.fourier_congr_ae hθ]

end SchwartzMap
