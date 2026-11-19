/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# Reconstruction from an integrable Fourier representative

An integrable Fourier datum has a bounded continuous inverse transform. The
Schwartz-test identity below identifies this function with the inverse tempered
distribution. It requires integrability only of the Fourier datum, not of its
inverse transform.

Integrable frequency moments give spatial derivatives by Mathlib's Fourier
differentiation theorem. This supplies both a classical representative and its
distributional identification, without choosing point values for an `Lp` class.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap ContDiff BoundedContinuousFunction

open Real

namespace PDE.Analysis.Fourier

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Pairing the inverse Fourier integral of an `L¹` datum with a Schwartz test
equals evaluation of its inverse tempered distribution. The proof is Fubini's
theorem with the negative inner-product pairing. -/
theorem integral_smul_fourierInv_eq (g : MeasureTheory.Lp F 1 (volume : Measure E))
    (φ : 𝓢(E, ℂ)) :
    (∫ x, φ x • 𝓕⁻ (g : E → F) x) =
      (𝓕⁻ (g : 𝓢'(E, F))) φ := by
  have hflip : (-innerₗ E).flip = -innerₗ E := by
    ext x y
    simp only [LinearMap.flip_apply, LinearMap.neg_apply]
    exact congrArg Neg.neg (real_inner_comm x y)
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (μ := (volume : Measure E)) (ν := (volume : Measure E))
    (L := -innerₗ E) Real.continuous_fourierChar continuous_inner.neg
    φ.integrable (L1.integrable_coeFn g)
  rw [hflip] at h
  rw [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply,
    SchwartzMap.fourierInv_coe]
  exact h.symm

/-- Frequency moments through order `r` give `C^r` regularity of the bounded
continuous inverse transform, with equality to the original distribution on
every Schwartz test. -/
theorem exists_contDiff_representative_of_fourier_eq
    {r : ℕ} {f : 𝓢'(E, F)} (g : MeasureTheory.Lp F 1 (volume : Measure E))
    (hg : 𝓕 f = (g : 𝓢'(E, F)))
    (hmom : ∀ k ≤ r, Integrable (fun ξ : E ↦ ‖ξ‖ ^ k * ‖g ξ‖)) :
    ∃ u : E →ᵇ F, ContDiff ℝ r (u : E → F) ∧
      ∀ φ : 𝓢(E, ℂ), (∫ x, φ x • u x) = f φ := by
  refine ⟨Lp.fourierTransformInv g, ?_, ?_⟩
  · rw [Lp.coe_fourierTransformInv]
    have hfourier : ContDiff ℝ (r : ℕ∞) (𝓕 (g : E → F)) :=
      Real.contDiff_fourier fun k hk ↦ hmom k (by exact_mod_cast hk)
    simpa only [Function.comp_def, id_eq, WithTop.coe_natCast,
      ← Real.fourierInv_eq_fourier_neg] using
      hfourier.comp contDiff_id.neg
  · intro φ
    rw [Lp.coe_fourierTransformInv, integral_smul_fourierInv_eq, ← hg,
      fourierInv_fourier_eq]

omit [CompleteSpace F] in
/-- A continuous operator multiplier of polynomial growth consumes precisely
that many integrable frequency moments. The vector-valued datum need only be
almost everywhere strongly measurable. -/
theorem integrable_norm_pow_clm_apply_of_polynomial_bound
    {g : E → F} (hg : AEStronglyMeasurable g volume)
    {M : E → F →L[ℂ] F} (hM : Continuous M)
    {d k : ℕ} {C : ℝ}
    (hbound : ∀ ξ, ‖M ξ‖ ≤ C * (1 + ‖ξ‖ ^ d))
    (hk : Integrable (fun ξ : E ↦ ‖ξ‖ ^ k * ‖g ξ‖))
    (hkd : Integrable (fun ξ : E ↦ ‖ξ‖ ^ (k + d) * ‖g ξ‖)) :
    Integrable (fun ξ : E ↦ ‖ξ‖ ^ k * ‖M ξ (g ξ)‖) := by
  have hMg : AEStronglyMeasurable (fun ξ ↦ M ξ (g ξ)) volume :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hM.aestronglyMeasurable.prodMk hg)
  refine ((hk.add hkd).const_mul C).mono'
    ((continuous_norm.pow k).aestronglyMeasurable.mul hMg.norm) ?_
  filter_upwards with ξ
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    ‖ξ‖ ^ k * ‖M ξ (g ξ)‖ ≤
        ‖ξ‖ ^ k * (‖M ξ‖ * ‖g ξ‖) :=
      mul_le_mul_of_nonneg_left ((M ξ).le_opNorm (g ξ)) (by positivity)
    _ ≤ ‖ξ‖ ^ k * ((C * (1 + ‖ξ‖ ^ d)) * ‖g ξ‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hbound ξ) (norm_nonneg _)) (by positivity)
    _ = C * (‖ξ‖ ^ k * ‖g ξ‖ + ‖ξ‖ ^ (k + d) * ‖g ξ‖) := by
      rw [pow_add]
      ring

end PDE.Analysis.Fourier
