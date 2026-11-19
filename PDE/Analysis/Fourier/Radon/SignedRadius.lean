/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.Radon.Backprojection
public import PDE.Analysis.Fourier.Radon.Schwartz
import CAS.ExactTactic

/-!
# Signed radial weights in Radon inversion

Evans, §4.3.2, Theorem 5(i), writes the Radon inversion formula (32) with radii over all of
`ℝ` and the radial weight `r^(n-1)`; `angularFourierRadonTransform` is his `ū` of (31). The
Jacobian for this range is `|r|^(n-1)`, as in `eq_integral_filtered_radonTransform`. For
even data at the origin in even dimension, the signed weight `r^(n-1)` gives an odd
integrand (`integral_signed_pow_angularFourierRadonTransform_eq_zero`). In step 1 of his
proof Evans substitutes `r ↦ -r` and `ω ↦ -ω` on `(-∞, 0)`, which produces the factor
`(-1)^(n-1)`, so (32) as printed holds in odd dimension only;
`exists_signed_radius_backprojection_ne` gives a counterexample in every positive even
dimension.

The angular-frequency transform below uses exactly the kernel `exp(-i r s)`.
Its conversion to Mathlib's convention evaluates the Fourier transform at
`r / (2π)`; no unitary normalization factor belongs to this one-dimensional
transform of the Radon data.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.3.2, Theorem 4, (31), p. 198, and Theorem 5(i), (32),
  and step 1 of its proof, p. 199. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped RealInnerProductSpace SchwartzMap

namespace PDE.Analysis.Fourier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The unnormalized angular-frequency Fourier transform of the Radon data. -/
def angularFourierRadonTransform (f : E → ℂ) (θ : E) (r : ℝ) : ℂ :=
  ∫ s : ℝ, Complex.exp (-(r * s : ℝ) * Complex.I) * radonTransform f θ s

/-- Angular frequencies differ from Mathlib's frequencies by exactly `2π`. -/
theorem angularFourierRadonTransform_eq (f : E → ℂ) (θ : E) (r : ℝ) :
    angularFourierRadonTransform f θ r =
      𝓕 (radonTransform f θ) (r / (2 * Real.pi)) := by
  rw [angularFourierRadonTransform, Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [] with s
  simp only [Real.inner_apply, smul_eq_mul]
  congr 2
  push_cast
  cas using Real.pi_ne_zero

/-- The Fourier transform preserves reflection symmetry. -/
theorem fourier_neg_eq_of_even {f : E → ℂ} (hf : Function.Even f) (ξ : E) :
    𝓕 f (-ξ) = 𝓕 f ξ := by
  have h := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ) f ξ
  have heq : f ∘ LinearIsometryEquiv.neg ℝ = f := funext hf
  rw [heq] at h
  exact h.symm

/-- At the origin, even data have even angular-frequency Radon data. -/
theorem angularFourierRadonTransform_even {f : E → ℂ} (hf : Integrable f)
    (heven : Function.Even f) {θ : E} (hθ : ‖θ‖ = 1) :
    Function.Even (angularFourierRadonTransform f θ) := by
  intro r
  simp only [angularFourierRadonTransform_eq, fourier_radonTransform hf hθ,
    neg_div, neg_smul]
  exact fourier_neg_eq_of_even heven _

/-- An odd signed radial power annihilates even angular-frequency Radon data.
Integrability is established separately for Schwartz data below. -/
theorem integral_signed_pow_angularFourierRadonTransform_eq_zero
    {f : E → ℂ} (hf : Integrable f) (heven : Function.Even f)
    {θ : E} (hθ : ‖θ‖ = 1) {k : ℕ} (hk : Odd k) :
    (∫ r : ℝ, r ^ k • angularFourierRadonTransform f θ r) = 0 := by
  have he := angularFourierRadonTransform_even hf heven hθ
  unfold Function.Even at he
  have h := integral_neg_eq_self (fun r : ℝ ↦
    r ^ k • angularFourierRadonTransform f θ r) volume
  simp only [hk.neg_pow, he, neg_smul, integral_neg] at h
  exact CharZero.neg_eq_self_iff.mp h

end PDE.Analysis.Fourier

namespace SchwartzMap

open PDE.Analysis.Fourier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Every polynomially weighted angular-frequency Radon slice is integrable. -/
theorem integrable_signed_pow_angularFourierRadonTransform (f : 𝓢(E, ℂ))
    {θ : E} (hθ : ‖θ‖ = 1) (k : ℕ) :
    Integrable (fun r : ℝ ↦ r ^ k • angularFourierRadonTransform f θ r) := by
  let a : ℝˣ := Units.mk0 ((2 * Real.pi)⁻¹) (by positivity)
  let g : 𝓢(ℝ, ℂ) := compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft a) (𝓕 (radonTransformCLM hθ f))
  have hg (r : ℝ) : g r = angularFourierRadonTransform f θ r := by
    change 𝓕 (radonTransformCLM hθ f : ℝ → ℂ) ((2 * Real.pi)⁻¹ * r) = _
    rw [radonTransformCLM_apply, angularFourierRadonTransform_eq]
    rw [div_eq_inv_mul]
  have hint := g.integrable_pow_mul volume k
  apply hint.mono
  · have hcont : Continuous (fun r : ℝ ↦ r ^ k • g r) := by fun_prop
    simpa only [hg] using hcont.aestronglyMeasurable
  · filter_upwards [] with r
    simp [hg, Real.norm_eq_abs]

end SchwartzMap
