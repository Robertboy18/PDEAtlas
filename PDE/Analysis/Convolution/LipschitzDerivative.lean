/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.Rademacher
public import PDE.Analysis.Convolution.SecondDifference

/-!
# Derivatives of convolutions of Lipschitz functions

Integration by parts identifies the derivative of a smooth convolution with
the convolution of the Lipschitz input's almost-everywhere line derivative.
Lebesgue differentiation then gives almost-everywhere convergence of these
derivatives. The input need not be bounded or integrable on the whole space.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open MeasureTheory Filter Function
open scoped Convolution Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure]

/-- A nonnegative smooth convolution of mass one preserves the global
Lipschitz constant, also for unbounded scalar inputs. -/
theorem lipschitzWith_normed_convolution
    (φ : ContDiffBump (0 : E)) {f : E → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) :
    LipschitzWith K (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  apply dist_convolution_le_of_dist_le φ.hasCompactSupport_normed
    φ.nonneg_normed φ.integral_normed hf.continuous
  intro y _
  simpa only [dist_sub_right] using hf.dist_le_mul (x - y) (z - y)

/-- Differentiation of a smooth compactly supported convolution commutes with
the almost-everywhere line derivative of a globally Lipschitz scalar function. -/
theorem fderiv_convolution_lipschitz_apply
    {ρ f : E → ℝ} (hρ : HasCompactSupport ρ) (hρ_smooth : ContDiff ℝ 1 ρ)
    {K : NNReal} (hf : LipschitzWith K f) (x v : E) :
    fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) x v =
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (fun y ↦ lineDeriv ℝ f y v)) x := by
  let ψ : E → ℝ := fun y ↦ ρ (x - y)
  have hψ : HasCompactSupport ψ := hρ.comp_homeomorph (Homeomorph.subLeft x)
  have hψ_smooth : ContDiff ℝ 1 ψ :=
    hρ_smooth.comp (contDiff_const.sub contDiff_id)
  obtain ⟨D, hψ_lip⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hψ hψ_smooth one_ne_zero
  have hψ_deriv (y : E) :
      lineDeriv ℝ ψ y (-v) = fderiv ℝ ρ (x - y) v := by
    have h : HasFDerivAt ψ
        ((fderiv ℝ ρ (x - y)).comp (0 - ContinuousLinearMap.id ℝ E)) y :=
      (hρ_smooth.differentiable one_ne_zero (x - y)).hasFDerivAt.comp y
        ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    rw [h.differentiableAt.lineDeriv_eq_fderiv, h.fderiv]
    simp
  have hibp := hf.integral_lineDeriv_mul_eq (μ := μ) hψ_lip hψ v
  simp_rw [hψ_deriv] at hibp
  rw [(hρ.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    hρ_smooth hf.continuous.locallyIntegrable x).fderiv]
  have hi := (hρ.fderiv ℝ).convolutionExists_left (μ := μ)
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL E)
    (hρ_smooth.continuous_fderiv one_ne_zero) hf.continuous.locallyIntegrable x
  rw [convolution_def, ContinuousLinearMap.integral_apply hi]
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul]
  rw [← integral_sub_left_eq_self _ μ x]
  simp only [sub_sub_self]
  rw [convolution_eq_swap]
  simpa only [ψ, ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_comm] using hibp.symm

/-- The derivatives of normalized smooth convolutions converge almost
everywhere in each fixed direction. Bounded eccentricity is the standard
approximate-identity condition on the inner and outer bump radii. -/
theorem ae_tendsto_fderiv_convolution_apply
    {f : E → ℝ} {K : NNReal} (hf : LipschitzWith K f)
    {ι : Type*} {φ : ι → ContDiffBump (0 : E)} {l : Filter ι} {A : ℝ}
    (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0))
    (hφ_ratio : ∀ᶠ i in l, (φ i).rOut ≤ A * (φ i).rIn) (v : E) :
    ∀ᵐ x ∂μ, Tendsto
      (fun i ↦ fderiv ℝ ((φ i).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) x v)
      l (𝓝 (fderiv ℝ f x v)) := by
  filter_upwards [ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    hφ hφ_ratio (hf.locallyIntegrable_lineDeriv v), hf.ae_differentiableAt (μ := μ)]
      with x hx hdiff
  simpa only [fderiv_convolution_lipschitz_apply (φ _).hasCompactSupport_normed
    (φ _).contDiff_normed hf, hdiff.lineDeriv_eq_fderiv] using hx

end PDE.Analysis
