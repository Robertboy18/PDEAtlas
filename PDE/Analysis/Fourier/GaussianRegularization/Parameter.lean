/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.CompactSupport.Parameter
public import PDE.Analysis.Fourier.GaussianRegularization.Convolution
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Integration of families of Gaussian-regularized multipliers

A continuous operator family on a compact parameter interval admits one
integrable Gaussian majorant. For continuous sources with common compact spatial
support, this justifies the parameter-frequency interchange from the raw data.
-/

@[expose] public noncomputable section

open MeasureTheory Set Complex
open scoped FourierTransform RealInnerProductSpace

namespace PDE.Analysis.Fourier

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The regularized Fourier source is integrable jointly in a compact
parameter interval and frequency. No Fourier integrability premise is needed. -/
theorem integrable_gaussianExponential_fourier_parameter
    (S : ℝ → Fin n → E →L[ℂ] E) {a c b : ℝ} (hb : 0 < b) (k : Fin n → ℝ)
    {F : ℝ × ℝ^n → E} {K : Set (ℝ^n)} (hK : IsCompact K)
    (hS : ∀ j, ContinuousOn (fun t ↦ S t j) (Icc a c))
    (hF : ContinuousOn F (Icc a c ×ˢ univ))
    (hs : ∀ t ∈ Icc a c, ∀ x ∉ K, F (t, x) = 0) :
    Integrable (fun p : ℝ × ℝ^n ↦
      gaussianExponentialIntegrand (S p.1) b k (WithLp.ofLp p.2)
        (𝓕 (fun x ↦ F (p.1, x)) p.2))
      ((volume.restrict (Icc a c)).prod volume) := by
  classical
  choose C hC using fun j ↦ isCompact_Icc.exists_bound_of_continuousOn (hS j)
  let q : ℝ^n → ℝ := fun ξ ↦
    ∏ j, Real.exp (C j ^ 2 / (2 * b)) * Real.exp (-(b / 2) * ξ j ^ 2)
  have hq : Integrable q :=
    (PiLp.volume_preserving_ofLp (Fin n)).integrable_comp_of_integrable
      (Integrable.fintype_prod fun j ↦
        (integrable_exp_neg_mul_sq (half_pos hb)).const_mul _)
  have hFn : ContinuousOn (fun t ↦ ∫ x, ‖F (t, x)‖) (Icc a c) := by
    apply continuousOn_integral_of_compact_support hK hF.norm
    intro t x ht hx
    simp only [hs t ht x hx, norm_zero]
  have hmajorant : Integrable
      (fun p : ℝ × ℝ^n ↦ (∫ x, ‖F (p.1, x)‖) * q p.2)
      ((volume.restrict (Icc a c)).prod volume) :=
    (hFn.integrableOn_Icc (μ := volume)).mul_prod hq
  have hG : ContinuousOn
      (fun p : ℝ × ℝ^n ↦ gaussianExponentialIntegrand (S p.1) b k (WithLp.ofLp p.2))
      (Icc a c ×ˢ univ) := by
    have hexp : Continuous (NormedSpace.exp : (E →L[ℂ] E) → E →L[ℂ] E) :=
      continuous_iff_continuousAt.mpr
        (fun R ↦ (NormedSpace.exp_analytic (𝕂 := ℂ) R).continuousAt)
    have hsum : ContinuousOn
        (fun p : ℝ × ℝ^n ↦ ∑ j, (p.2 j : ℂ) • S p.1 j) (Icc a c ×ˢ univ) := by
      apply continuousOn_finsetSum
      intro j _
      exact (by fun_prop : Continuous (fun p : ℝ × ℝ^n ↦ (p.2 j : ℂ))).continuousOn.smul
        ((hS j).comp continuous_fst.continuousOn (fun _ hp ↦ hp.1))
    unfold gaussianExponentialIntegrand
    exact (by fun_prop : Continuous (fun p : ℝ × ℝ^n ↦
      Complex.exp ((-(b * ∑ j, p.2 j ^ 2) : ℝ) + (∑ j, k j * p.2 j : ℝ) * I)))
      |>.continuousOn.smul (hexp.comp_continuousOn hsum)
  apply hmajorant.mono'
  · rw [Measure.restrict_prod_eq_prod_univ]
    exact (hG.clm_apply
      (continuousOn_fourier_of_uniform_compact_support hK hF hs)).aestronglyMeasurable
        (measurableSet_Icc.prod MeasurableSet.univ)
  · have ht : ∀ᵐ p : ℝ × ℝ^n ∂(volume.restrict (Icc a c)).prod volume,
        p.1 ∈ Icc a c := by
      rw [Measure.restrict_prod_eq_prod_univ]
      filter_upwards [self_mem_ae_restrict
        (μ := (volume : Measure ℝ).prod volume)
        (measurableSet_Icc.prod (MeasurableSet.univ : MeasurableSet (univ : Set (ℝ^n))))]
        with p hp
      exact hp.1
    filter_upwards [ht] with p hp
    have hbound : ‖gaussianExponentialIntegrand (S p.1) b k (WithLp.ofLp p.2)‖ ≤ q p.2 := by
      apply (norm_gaussianExponentialIntegrand_le
        (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := E)) (S p.1) hb k _).trans
      apply Finset.prod_le_prod₀
      · intro j _
        positivity
      · intro j _
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        apply Real.exp_le_exp.mpr
        exact div_le_div_of_nonneg_right
          (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans (hC j p.1 hp)) |>.2
            (hC j p.1 hp)) (by positivity)
    have hfourier : ‖𝓕 (fun x ↦ F (p.1, x)) p.2‖ ≤ ∫ x, ‖F (p.1, x)‖ := by
      simpa only [Real.fourier_eq, VectorFourier.fourierIntegral, innerₗ_apply_apply] using
        VectorFourier.norm_fourierIntegral_le_integral_norm
          Real.fourierChar volume (innerₗ (ℝ^n)) (fun x ↦ F (p.1, x)) p.2
    calc
      _ ≤ ‖gaussianExponentialIntegrand (S p.1) b k (WithLp.ofLp p.2)‖ *
          ‖𝓕 (fun x ↦ F (p.1, x)) p.2‖ :=
        (gaussianExponentialIntegrand (S p.1) b k (WithLp.ofLp p.2)).le_opNorm _
      _ ≤ q p.2 * (∫ x, ‖F (p.1, x)‖) :=
        mul_le_mul hbound hfourier (norm_nonneg _) (by positivity)
      _ = _ := mul_comm _ _

/-- A time integral of Gaussian-regularized Fourier multipliers equals
the time integral of their spatial kernels. Both interchanges are justified by
integrability derived from compact support and continuity. -/
theorem integral_intervalIntegral_gaussianExponential_fourier_eq
    (S : ℝ → Fin n → E →L[ℂ] E) {a c b : ℝ} (hac : a ≤ c)
    (hb : 0 < b) (k : Fin n → ℝ)
    {F : ℝ × ℝ^n → E} {K : Set (ℝ^n)} (hK : IsCompact K)
    (hS : ∀ j, ContinuousOn (fun t ↦ S t j) (Icc a c))
    (hF : ContinuousOn F (Icc a c ×ˢ univ))
    (hs : ∀ t ∈ Icc a c, ∀ x ∉ K, F (t, x) = 0) :
    (∫ ξ : ℝ^n, ∫ t in a..c,
      gaussianExponentialIntegrand (S t) b k (WithLp.ofLp ξ)
        (𝓕 (fun x ↦ F (t, x)) ξ)) =
      ∫ t in a..c, ∫ y : ℝ^n,
        gaussianExponentialKernel (S t) b (fun j ↦ k j - 2 * Real.pi * y j)
          (F (t, y)) := by
  have hi := integrable_gaussianExponential_fourier_parameter S hb k hK hS hF hs
  have hio : Integrable (fun p : ℝ × ℝ^n ↦
      gaussianExponentialIntegrand (S p.1) b k (WithLp.ofLp p.2)
        (𝓕 (fun x ↦ F (p.1, x)) p.2))
      ((volume.restrict (uIoc a c)).prod volume) := by
    rw [uIoc_of_le hac, Measure.restrict_prod_eq_prod_univ]
    rw [Measure.restrict_prod_eq_prod_univ] at hi
    exact hi.mono_measure (Measure.restrict_mono
      (Set.prod_mono Ioc_subset_Icc_self Subset.rfl) le_rfl)
  rw [← intervalIntegral_integral_swap hio]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hac] at ht
  have hc : Continuous (fun x ↦ F (t, x)) :=
    hF.comp_continuous (continuous_const.prodMk continuous_id)
      (fun x ↦ ⟨ht, mem_univ x⟩)
  exact integral_gaussianExponential_fourier_eq (S t) hb k
    (hc.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact hK
        (Function.support_subset_iff'.mpr (hs t ht))))

end PDE.Analysis.Fourier
