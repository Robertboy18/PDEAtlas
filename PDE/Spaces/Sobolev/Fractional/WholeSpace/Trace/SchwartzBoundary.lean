/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Geometry.TangentialEmbedding
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.FourierSlice
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.KernelWeight
import CAS.ExactTactic

/-!
# The Fourier transform of a Schwartz boundary value

Restriction to the last-coordinate hyperplane preserves Schwartz regularity.
Normal integration of a Schwartz function is continuous by an integrable
Cauchy bound. Fourier inversion then identifies the normal Fourier integral
with the Fourier transform of the boundary value.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform ProbabilityTheory
open scoped SchwartzMap

namespace SobolevSpace.Fractional.Trace

open SobolevSpace.Trace.HalfSpace

/-- Boundary restriction as a continuous linear map of Schwartz spaces. -/
def schwartzBoundaryCLM (n : ℕ) : 𝓢(ℝ^(n + 1), ℂ) →L[ℂ] 𝓢(ℝ^n, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ
    (tangentialEmbedding (n := n)).toContinuousLinearMap.hasTemperateGrowth
    (tangentialEmbedding (n := n)).isometry.antilipschitzWith

/-- The Schwartz restriction has the classical point values. -/
theorem schwartzBoundaryCLM_apply (n : ℕ) (f : 𝓢(ℝ^(n + 1), ℂ)) (y : ℝ^n) :
    schwartzBoundaryCLM n f y = f (joinTangentialNormal (y, 0)) := by
  exact congrFun (SchwartzMap.compCLMOfAntilipschitz_apply ℂ
    (tangentialEmbedding (n := n)).toContinuousLinearMap.hasTemperateGrowth
    (tangentialEmbedding (n := n)).isometry.antilipschitzWith f) y

private theorem norm_schwartz_join_le {n : ℕ} (f : 𝓢(ℝ^(n + 1), ℂ))
    (ξ : ℝ^n) (t : ℝ) :
    ‖f (joinTangentialNormal (ξ, t))‖ ≤
      (SchwartzMap.seminorm ℝ 0 0 f + SchwartzMap.seminorm ℝ 2 0 f) /
        (1 + t ^ 2) := by
  rw [le_div_iff₀ (by positivity)]
  have h0 := f.norm_le_seminorm ℝ (joinTangentialNormal (ξ, t))
  have h2 := f.norm_pow_mul_le_seminorm ℝ 2 (joinTangentialNormal (ξ, t))
  rw [norm_join_sq] at h2
  nlinarith [mul_nonneg (sq_nonneg ‖ξ‖) (norm_nonneg (f (joinTangentialNormal (ξ, t))))]

private theorem integrable_schwartz_normal_bound {n : ℕ} (f : 𝓢(ℝ^(n + 1), ℂ)) :
    Integrable (fun t : ℝ ↦
      (SchwartzMap.seminorm ℝ 0 0 f + SchwartzMap.seminorm ℝ 2 0 f) / (1 + t ^ 2)) := by
  convert (integrable_cauchyPDFReal 0 (γ := 1)).const_mul
    (Real.pi * (SchwartzMap.seminorm ℝ 0 0 f + SchwartzMap.seminorm ℝ 2 0 f)) using 1
  ext t
  unfold cauchyPDFReal
  simp only [NNReal.coe_one, sub_zero, one_pow, mul_one]
  cas using Real.pi_ne_zero

/-- Normal integration of a Schwartz function is continuous in tangential position. -/
theorem continuous_normalIntegral_schwartz {n : ℕ} (f : 𝓢(ℝ^(n + 1), ℂ)) :
    Continuous (fun ξ : ℝ^n ↦ ∫ t : ℝ, f (joinTangentialNormal (ξ, t))) := by
  apply continuous_of_dominated (bound := fun t : ℝ ↦
    (SchwartzMap.seminorm ℝ 0 0 f + SchwartzMap.seminorm ℝ 2 0 f) / (1 + t ^ 2))
  · intro ξ
    exact (f.continuous.comp (tangentialNormalContinuousLinearEquiv.symm.continuous.comp
      (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  · intro ξ
    exact Filter.Eventually.of_forall (norm_schwartz_join_le f ξ)
  · exact integrable_schwartz_normal_bound f
  · filter_upwards with t
    exact f.continuous.comp (tangentialNormalContinuousLinearEquiv.symm.continuous.comp
      (continuous_id.prodMk continuous_const))

/-- The normal integral of a Schwartz function is integrable in tangential position. -/
theorem integrable_normalIntegral_schwartz {n : ℕ} (f : 𝓢(ℝ^(n + 1), ℂ)) :
    Integrable (fun ξ : ℝ^n ↦ ∫ t : ℝ, f (joinTangentialNormal (ξ, t))) := by
  have hm := (measurePreserving_tangentialNormalMeasurableEquiv (n := n)).symm
  have hf : Integrable (fun p : ℝ^n × ℝ ↦ f (joinTangentialNormal p))
      ((volume : Measure ℝ^n).prod (volume : Measure ℝ)) := by
    simpa only [Function.comp_def, tangentialNormalMeasurableEquiv_symm_apply,
      Measure.volume_eq_prod] using hm.integrable_comp_of_integrable f.integrable
  exact hf.integral_prod_left

/-- Fourier transformation of the classical boundary value integrates ambient normal frequency. -/
theorem fourier_schwartzBoundary_eq_normal {n : ℕ} (f : 𝓢(ℝ^(n + 1), ℂ)) (ξ : ℝ^n) :
    (𝓕 (schwartzBoundaryCLM n f) : 𝓢(ℝ^n, ℂ)) ξ =
      ∫ t : ℝ, (𝓕 f : 𝓢(ℝ^(n + 1), ℂ)) (joinTangentialNormal (ξ, t)) := by
  let g : ℝ^n → ℂ := fun ξ ↦
    ∫ t : ℝ, (𝓕 f : 𝓢(ℝ^(n + 1), ℂ)) (joinTangentialNormal (ξ, t))
  have hinv : 𝓕⁻ g = schwartzBoundaryCLM n f := by
    funext y
    exact (schwartz_boundary_eq_fourierInv_normal f y).symm.trans
      (schwartzBoundaryCLM_apply n f y).symm
  have hFourier : Integrable (𝓕 g) := by
    have hneg : (𝓕 g) = fun y ↦ schwartzBoundaryCLM n f (-y) := by
      funext y
      rw [← hinv, Real.fourierInv_eq_fourier_neg, neg_neg]
    rw [hneg]
    exact (schwartzBoundaryCLM n f).integrable.comp_neg
  have h := (continuous_normalIntegral_schwartz (𝓕 f)).fourier_fourierInv_eq
    (integrable_normalIntegral_schwartz (𝓕 f)) hFourier
  rw [hinv] at h
  simpa only [SchwartzMap.fourier_coe] using congrFun h ξ

end SobolevSpace.Fractional.Trace
