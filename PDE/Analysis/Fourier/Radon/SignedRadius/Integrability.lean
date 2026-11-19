/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.Radon.SignedRadius

/-!
# Absolute integrability of signed radial Radon data

For even Schwartz data, the angular-frequency Radon transform is even in the radius.
Polar integration of its norm proves joint integrability over directions and signed radii.
Fubini then transfers the odd-power cancellation to the order of integration of formula (32)
in Evans, §4.3.2, Theorem 5(i), with the integral over the sphere inside.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.3.2, Theorem 5(i), (32), p. 199.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped RealInnerProductSpace SchwartzMap

namespace SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open PDE.Analysis.Fourier

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem integral_norm_signed_radius_eq (g : E → ℂ)
    (heven : Function.Even g) (θ : Metric.sphere (0 : E) 1) (k : ℕ) :
    (∫ r : ℝ, ‖r ^ k • g (r • (θ : E))‖) =
      2 * ∫ r in Set.Ioi (0 : ℝ), r ^ k * ‖g (r • (θ : E))‖ := by
  rw [← integral_comp_abs]
  apply integral_congr_ae
  filter_upwards [] with r
  rw [norm_smul, Real.norm_eq_abs, abs_pow]
  congr 1
  by_cases hr : 0 ≤ r
  · rw [abs_of_nonneg hr]
  · rw [abs_of_neg (lt_of_not_ge hr), neg_smul, heven]

/-- The signed radial Fourier integrand of even Schwartz data is jointly integrable. -/
theorem integrable_signed_radius_angularFourierRadonTransform_of_even (f : 𝓢(E, ℂ))
    (heven : Function.Even (f : E → ℂ)) :
    Integrable (fun p : Metric.sphere (0 : E) 1 × ℝ ↦
      p.2 ^ (Module.finrank ℝ E - 1) •
        angularFourierRadonTransform f (p.1 : E) p.2)
      ((volume : Measure E).toSphere.prod volume) := by
  -- Rescale the ambient Fourier transform to angular frequencies.
  let a : ℝˣ := Units.mk0 ((2 * Real.pi)⁻¹) (by positivity)
  let g : 𝓢(E, ℂ) := compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft a) (𝓕 f)
  have hg (θ : Metric.sphere (0 : E) 1) (r : ℝ) :
      g (r • (θ : E)) = angularFourierRadonTransform f (θ : E) r := by
    change 𝓕 f ((2 * Real.pi)⁻¹ • (r • (θ : E))) = _
    rw [angularFourierRadonTransform_eq,
      fourier_radonTransform f.integrable (by simp), smul_smul, div_eq_inv_mul]
    rfl
  have hge (ξ : E) : g (-ξ) = g ξ := by
    change 𝓕 f ((2 * Real.pi)⁻¹ • -ξ) = 𝓕 f ((2 * Real.pi)⁻¹ • ξ)
    rw [smul_neg]
    exact fourier_neg_eq_of_even heven _
  have hcont : Continuous (fun p : Metric.sphere (0 : E) 1 × ℝ ↦
      p.2 ^ (Module.finrank ℝ E - 1) • g (p.2 • (p.1 : E))) := by
    fun_prop
  have hm : AEStronglyMeasurable (fun p : Metric.sphere (0 : E) 1 × ℝ ↦
      p.2 ^ (Module.finrank ℝ E - 1) •
        angularFourierRadonTransform f (p.1 : E) p.2)
      ((volume : Measure E).toSphere.prod volume) := by
    simpa only [hg] using hcont.aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  refine ⟨?_, ?_⟩
  · filter_upwards [] with θ
    exact f.integrable_signed_pow_angularFourierRadonTransform
      (θ := (θ : E)) (by simp) (Module.finrank ℝ E - 1)
  -- Reflection symmetry turns the absolute radial integral into twice its positive half.
  have hnorm := (PDE.Analysis.integrable_polar_radialIntegral
    (volume : Measure E) g.integrable.norm).const_mul (2 : ℝ)
  apply hnorm.congr
  filter_upwards [] with θ
  simp only [← hg, smul_eq_mul]
  exact (integral_norm_signed_radius_eq g hge θ _).symm

/-- The signed radial weight annihilates even data in even dimensions,
including when the radius is integrated after the direction. -/
theorem integral_signed_radius_angularFourierRadonTransform_eq_zero (f : 𝓢(E, ℂ))
    (heven : Function.Even (f : E → ℂ)) (hodd : Odd (Module.finrank ℝ E - 1)) :
    (∫ r : ℝ, ∫ θ : Metric.sphere (0 : E) 1,
      r ^ (Module.finrank ℝ E - 1) • angularFourierRadonTransform f (θ : E) r
      ∂(volume : Measure E).toSphere) = 0 := by
  rw [← integral_integral_swap
    (f.integrable_signed_radius_angularFourierRadonTransform_of_even heven)]
  have hθ (θ : Metric.sphere (0 : E) 1) :
      (∫ r : ℝ, r ^ (Module.finrank ℝ E - 1) •
        angularFourierRadonTransform f (θ : E) r) = 0 :=
    integral_signed_pow_angularFourierRadonTransform_eq_zero
      f.integrable heven (by simp) hodd
  simp only [hθ, integral_zero]

end SchwartzMap
