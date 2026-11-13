/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.ScaleDerivative.Convolution
public import PDE.Spaces.Sobolev.Approximation.Mollification.ScaleDerivative.Profiles
import PDE.Analysis.Convolution.DirectionalDerivative
import PDE.Spaces.Sobolev.Approximation.Mollification.KernelMoment
import PDE.Spaces.Sobolev.Approximation.Mollification.ScaleDerivative.Scaling
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Derivative formulas for scaled mollification

After dilating the integration variable, each derivative has one inverse scale and
an unscaled smooth kernel profile acting by scalar multiplication. The input may take
values in any real normed space and needs only local Bochner integrability.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Convolution Topology

namespace SobolevSpace.Approximation

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A spatial derivative of mollification acts on the kernel, with one inverse scale.
The direction is arbitrary, including the zero direction in dimension zero. -/
theorem fderiv_mollifyVector_apply_scale (μ : Mollifier n) {g : ℝ^n → F}
    (hg : LocallyIntegrable g volume) {t : ℝ} (ht : 0 < t) (x v : ℝ^n) :
    fderiv ℝ (mollifyVector μ t g) x v =
      t⁻¹ • ∫ z, fderiv ℝ μ.ρ z v • g (x - t • z) := by
  have hflip : mollifyVector μ t g =
      g ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] scaled μ t := by
    rw [convolution_flip]
    rfl
  rw [hflip, (scaled_hasCompactSupport μ ht).fderiv_convolution_apply_right
    (ContinuousLinearMap.lsmul ℝ ℝ).flip hg ((scaled_contDiff μ).of_le (by simp)),
    convolution_flip]
  change (∫ y, fderiv ℝ (scaled μ t) y v • g (x - y)) = _
  calc
    (∫ y, fderiv ℝ (scaled μ t) y v • g (x - y)) =
        ∫ y, ((t⁻¹)^n * t⁻¹ * fderiv ℝ μ.ρ (t⁻¹ • y) v) • g (x - y) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y ↦ by
        dsimp only
        rw [fderiv_scaled_apply μ ht]
        rw [mul_assoc]
    _ = t⁻¹ • ∫ z, fderiv ℝ μ.ρ z v • g (x - t • z) :=
      integral_scaled_profile_smul (fun z ↦ fderiv ℝ μ.ρ z v) g ht x

/-- Differentiation in the positive scale commutes with convolution against locally
integrable data, before rewriting the derivative kernel in normalized coordinates. -/
theorem hasDerivAt_mollifyVector_scale_convolution (μ : Mollifier n) {g : ℝ^n → F}
    (hg : LocallyIntegrable g volume) {t : ℝ} (ht : 0 < t) (x : ℝ^n) :
    HasDerivAt (fun r ↦ mollifyVector μ r g x)
      (∫ y, deriv (fun r ↦ scaled μ r y) t • g (x - y)) t := by
  have htx : Ioi 0 ×ˢ (univ : Set (ℝ^n)) ∈ 𝓝 (t, x) :=
    (isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht, mem_univ _⟩
  have hd := (((contDiffOn_mollifyVector_scale μ hg).contDiffAt htx).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have hk (y : ℝ^n) :
      fderiv ℝ (fun q : ℝ × ℝ^n ↦ scaled μ q.1 q.2) (t, y) (1, 0) =
        deriv (fun r ↦ scaled μ r y) t := by
    have hty : Ioi 0 ×ˢ (univ : Set (ℝ^n)) ∈ 𝓝 (t, y) :=
      (isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht, mem_univ _⟩
    exact (((((contDiffOn_scaled μ).contDiffAt hty).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))).deriv).symm
  have hv :
      fderiv ℝ (fun q : ℝ × ℝ^n ↦ mollifyVector μ q.1 g q.2) (t, x) (1, 0) =
        ∫ y, deriv (fun r ↦ scaled μ r y) t • g (x - y) := by
    rw [fderiv_mollifyVector_scale_apply μ hg ht]
    simp_rw [hk]
  apply HasDerivAt.of_isLittleO
  simpa only [Function.comp_def, id_eq, hv] using hd.isLittleO

/-- The height derivative is the signed normal profile averaged at the positive
scale, with the inverse scale prescribed by the chain rule. -/
theorem hasDerivAt_mollifyVector_scale (μ : Mollifier n) {g : ℝ^n → F}
    (hg : LocallyIntegrable g volume) {t : ℝ} (ht : 0 < t) (x : ℝ^n) :
    HasDerivAt (fun r ↦ mollifyVector μ r g x)
      (t⁻¹ • ∫ z, μ.normalDerivativeProfile z • g (x - t • z)) t := by
  have hd := hasDerivAt_mollifyVector_scale_convolution μ hg ht x
  apply hd.congr_deriv
  simp_rw [μ.deriv_scaled ht]
  exact integral_scaled_profile_smul μ.normalDerivativeProfile g ht x

/-- Pointwise height derivative formula for locally integrable input. -/
theorem deriv_mollifyVector_scale (μ : Mollifier n) {g : ℝ^n → F}
    (hg : LocallyIntegrable g volume) {t : ℝ} (ht : 0 < t) (x : ℝ^n) :
    deriv (fun r ↦ mollifyVector μ r g x) t =
      t⁻¹ • ∫ z, μ.normalDerivativeProfile z • g (x - t • z) :=
  (hasDerivAt_mollifyVector_scale μ hg ht x).deriv

/-- A coordinate derivative is the average against the corresponding signed spatial
profile. The shared coordinate notation denotes the classical derivative. -/
theorem partialDeriv_mollifyVector_scale (μ : Mollifier n) {g : ℝ^n → F}
    (hg : LocallyIntegrable g volume) {t : ℝ} (ht : 0 < t) (i : Fin n) (x : ℝ^n) :
    (∂[i] (mollifyVector μ t g)) x =
      t⁻¹ • ∫ z, μ.spatialDerivativeProfile i z • g (x - t • z) :=
  fderiv_mollifyVector_apply_scale μ hg ht x (EuclideanSpace.single i 1)

end SobolevSpace.Approximation
