/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.Core
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The first absolute moment of a differentiated mollifier

For `ε > 0`, the kernel is `ρ_ε(x) = ε⁻ⁿ ρ(ε⁻¹ x)`.
Its derivative contributes one further factor `ε⁻¹`. In
`∫ ‖x‖ ‖Dρ_ε(x) v‖`, the spatial weight contributes `ε` under
`x = ε z`, while the Jacobian contributes `εⁿ`. These factors cancel.

The resulting moment is finite by smoothness and compact support, and is
independent of every positive scale. The direction `v` is arbitrary, so
coordinate derivatives follow by taking `v = EuclideanSpace.single j 1`.
No symmetry or special normalization of the mollifier is used in these estimates.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace SobolevSpace.Approximation

variable {n : ℕ}

/-- The derivative of the current positively scaled kernel includes both its
normalizing factor and the inverse scale from the chain rule. -/
theorem fderiv_scaled_apply
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (x v : ℝ^n) :
    fderiv ℝ (scaled μ ε) x v =
      (ε⁻¹) ^ n * (ε⁻¹ * fderiv ℝ μ.ρ (ε⁻¹ • x) v) := by
  have hρ : HasFDerivAt μ.ρ (fderiv ℝ μ.ρ (ε⁻¹ • x)) (ε⁻¹ • x) :=
    ((μ.smooth.differentiable (by simp)) (ε⁻¹ • x)).hasFDerivAt
  have hid := (hasFDerivAt_id (𝕜 := ℝ) x).const_smul (ε⁻¹ : ℝ)
  have hs : HasFDerivAt (scaled μ ε)
      ((ε⁻¹) ^ n •
        ((fderiv ℝ μ.ρ (ε⁻¹ • x)).comp
          ((ε⁻¹) • ContinuousLinearMap.id ℝ (ℝ^n)))) x := by
    apply HasFDerivAt.of_isLittleO
    simpa only [scaled_of_pos μ hε, Pi.smul_apply, Function.comp_def, smul_eq_mul]
      using ((hρ.comp x hid).const_smul ((ε⁻¹) ^ n)).isLittleO
  rw [hs.fderiv]
  change (ε⁻¹) ^ n * fderiv ℝ μ.ρ (ε⁻¹ • x) (ε⁻¹ • v) = _
  rw [map_smul, smul_eq_mul]

/-- Multiplying the absolute directional derivative of a mollifier kernel by the
distance from the origin remains integrable, by continuity and compact support. -/
theorem integrable_norm_mul_norm_fderiv_scaled_apply
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (v : ℝ^n) :
    Integrable (fun x ↦ ‖x‖ * ‖fderiv ℝ (scaled μ ε) x v‖) volume := by
  have hcont : Continuous (fun x ↦ fderiv ℝ (scaled μ ε) x v) :=
    ((scaled_contDiff μ).continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk continuous_const)
  have hs : HasCompactSupport (fun x ↦ ‖fderiv ℝ (scaled μ ε) x v‖) :=
    ((scaled_hasCompactSupport μ hε).fderiv_apply (𝕜 := ℝ) v).comp_left norm_zero
  exact (continuous_norm.mul hcont.norm).integrable_of_hasCompactSupport hs.mul_left

/-- The first absolute moment of the differentiated kernel is independent of
positive scale. This is the kernel constant in the L² transport commutator bound. -/
theorem integral_norm_mul_norm_fderiv_scaled_apply
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (v : ℝ^n) :
    (∫ x, ‖x‖ * ‖fderiv ℝ (scaled μ ε) x v‖) =
      ∫ x, ‖x‖ * ‖fderiv ℝ μ.ρ x v‖ := by
  let g : ℝ^n → ℝ := fun x ↦ ‖x‖ * ‖fderiv ℝ μ.ρ x v‖
  have hweight (x : ℝ^n) :
      ‖x‖ * ‖fderiv ℝ (scaled μ ε) x v‖ = (ε⁻¹) ^ n * g (ε⁻¹ • x) := by
    dsimp only [g]
    rw [fderiv_scaled_apply μ hε]
    simp only [norm_mul, norm_smul,
      Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr hε.le) n),
      Real.norm_of_nonneg (inv_nonneg.mpr hε.le)]
    ac_rfl
  have hfinrank : Module.finrank ℝ (ℝ^n) = n := by simp
  have hscale : (∫ x, g (ε⁻¹ • x)) = ε ^ n * ∫ x, g x := by
    simpa only [hfinrank, smul_eq_mul] using
      (Measure.integral_comp_inv_smul_of_nonneg
        (μ := (volume : Measure (ℝ^n))) (f := g) hε.le)
  calc
    (∫ x, ‖x‖ * ‖fderiv ℝ (scaled μ ε) x v‖) =
        (ε⁻¹) ^ n * ∫ x, g (ε⁻¹ • x) := by
      simp_rw [hweight]
      exact integral_const_mul _ _
    _ = (ε⁻¹) ^ n * (ε ^ n * ∫ x, g x) := by rw [hscale]
    _ = ∫ x, g x := by
      rw [inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n hε.ne'), one_mul]

end SobolevSpace.Approximation
