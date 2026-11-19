/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CoordinateSystems.Spherical.AxisymmetricIntegration
public import PDE.CoordinateSystems.Spherical.AxisymmetricField
public import PDE.Analysis.MeasureTheory.Integral.NonnegativeSum

/-!
# Energy of a field from its compactified frame components

Let `f : ℝ³ → ℝ³` be continuous off the origin and suppose that at every point of radius
`s tan β` and polar angle `θ ∈ (0, π)` off the axis the frame components of
`(sin β / cos² β) f` are the values `T k β θ` of continuous functions of `(β, θ)`. If the summed
squares `∑ₖ T k β θ²` are symmetric about the equator, the energy of `f` is
`s³ · 4π ∫₀^{π/2} ∫₀^{π/2} (∑ₖ T k β θ²) sin θ dθ dβ` (`lintegral_sq_norm_eq_quadrant`): the
radial compactification `r = s tan β` gives the factor `s³` and the weight, the azimuthal
integral `2π` and the equatorial symmetry another factor `2`. At the poles the identity of the
squared norms extends by continuity from the directions off the axis, which are dense.
-/

@[expose] public noncomputable section

namespace PDE.CoordinateSystems.Spherical

open MeasureTheory Set Real
open scoped ENNReal RealInnerProductSpace BigOperators

variable {f : ℝ^3 → ℝ^3} {s : ℝ}

/-- The squared norm of the compactified field at `β ∈ (0, π/2)` and a unit vector `ω` is the
sum of the squared frame functions at `(β, polarAngle ω)`. -/
theorem norm_sq_compactified_eq_sum_sq (hs : 0 < s) (hc : ∀ x, x ≠ 0 → ContinuousAt f x)
    (T : Fin 3 → ℝ → ℝ → ℝ) (hT : ∀ k, Continuous (Function.uncurry (T k)))
    (hframe : ∀ β ∈ Ioo 0 (π / 2), ∀ θ ∈ Ioo 0 π, ∀ φ k,
      sin β / cos β ^ 2 * ⟪frame θ φ k, f (point (s * tan β) θ φ)⟫ = T k β θ)
    {β : ℝ} (hβ : β ∈ Ioo 0 (π / 2)) (ω : Metric.sphere (0 : ℝ^3) 1) :
    ‖(sin β / cos β ^ 2) • f ((s * tan β) • (ω : ℝ^3))‖ ^ 2 = ∑ k, T k β (polarAngle ω) ^ 2 := by
  have hpos : 0 < s * tan β := mul_pos hs (tan_pos_of_pos_of_lt_pi_div_two hβ.1 hβ.2)
  have hoff : ∀ ω : Metric.sphere (0 : ℝ^3) 1, (ω : ℝ^3) ∉ symmetryAxis →
      ‖(sin β / cos β ^ 2) • f ((s * tan β) • (ω : ℝ^3))‖ ^ 2 =
        ∑ k, T k β (polarAngle ω) ^ 2 := by
    intro ω hω
    have hω0 := ne_zero_of_notMem_symmetryAxis hω
    have hn : ‖(ω : ℝ^3)‖ = 1 := by simp
    have hrf : (ω : ℝ^3) = radialFrame (polarAngle ω) (azimuthalAngle ω) := by
      have h := point_norm_polarAngle_azimuthalAngle hω0
      rw [hn, point, one_smul] at h
      exact h.symm
    have hθ := polarAngle_mem_Ioo hω
    have key : (sin β / cos β ^ 2) • f ((s * tan β) • (ω : ℝ^3)) = (sin β / cos β ^ 2) •
        f (point (s * tan β) (polarAngle ω) (azimuthalAngle ω)) := by
      rw [point, ← hrf]
    rw [key, ← frameVector_inner_frame (polarAngle ω) (azimuthalAngle ω)
      ((sin β / cos β ^ 2) • f (point (s * tan β) (polarAngle ω) (azimuthalAngle ω))),
      norm_sq_frameVector]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [inner_smul_right, hframe β hβ (polarAngle ω) hθ (azimuthalAngle ω) k]
  have hL : Continuous fun ω : Metric.sphere (0 : ℝ^3) 1 ↦
      ‖(sin β / cos β ^ 2) • f ((s * tan β) • (ω : ℝ^3))‖ ^ 2 := by
    refine continuous_iff_continuousAt.mpr fun ω ↦ ?_
    have hne : (s * tan β) • (ω : ℝ^3) ≠ 0 :=
      smul_ne_zero hpos.ne' (ne_zero_of_mem_unit_sphere ω)
    have hcont : Continuous fun ω : Metric.sphere (0 : ℝ^3) 1 ↦ (s * tan β) • (ω : ℝ^3) := by
      fun_prop
    have h1 : ContinuousAt (fun ω : Metric.sphere (0 : ℝ^3) 1 ↦
        f ((s * tan β) • (ω : ℝ^3))) ω :=
      ContinuousAt.comp (g := f)
        (f := fun ω : Metric.sphere (0 : ℝ^3) 1 ↦ (s * tan β) • (ω : ℝ^3))
        (hc _ hne) hcont.continuousAt
    exact ((h1.const_smul (sin β / cos β ^ 2)).norm).pow 2
  have hR : Continuous fun ω : Metric.sphere (0 : ℝ^3) 1 ↦ ∑ k, T k β (polarAngle ω) ^ 2 := by
    have hpol : Continuous fun ω : Metric.sphere (0 : ℝ^3) 1 ↦ polarAngle ω :=
      continuous_iff_continuousAt.mpr fun ω ↦
        (continuousAt_polarAngle (ne_zero_of_mem_unit_sphere ω)).comp
          continuous_subtype_val.continuousAt
    exact continuous_finsetSum _ fun k _ ↦
      (((hT k).comp (Continuous.prodMk_right β)).comp hpol).pow 2
  exact congrFun (Continuous.ext_on dense_sphere_notMem_symmetryAxis hL hR hoff) ω

/-- The energy of a field whose compactified frame components are continuous functions `T`
with summed squares symmetric about the equator, as `s³ · 4π` times the integral over the
quadrant `(β, θ) ∈ [0, π/2]²` of `∑ₖ T k β θ²` against `sin θ`. -/
theorem lintegral_sq_norm_eq_quadrant (hs : 0 < s) (hf : AEStronglyMeasurable f volume)
    (hc : ∀ x, x ≠ 0 → ContinuousAt f x)
    (T : Fin 3 → ℝ → ℝ → ℝ) (hT : ∀ k, Continuous (Function.uncurry (T k)))
    (hframe : ∀ β ∈ Ioo 0 (π / 2), ∀ θ ∈ Ioo 0 π, ∀ φ k,
      sin β / cos β ^ 2 * ⟪frame θ φ k, f (point (s * tan β) θ φ)⟫ = T k β θ)
    (hsym : ∀ β θ, ∑ k, T k β (π - θ) ^ 2 = ∑ k, T k β θ ^ 2) :
    ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) = ENNReal.ofReal (s ^ 3 * (4 * π *
      ∫ β in (0 : ℝ)..(π / 2), ∫ θ in (0 : ℝ)..(π / 2), (∑ k, T k β θ ^ 2) * sin θ)) := by
  have hFc : Continuous fun p : ℝ × ℝ ↦ ∑ k, T k p.1 p.2 ^ 2 :=
    continuous_finsetSum _ fun k _ ↦ (hT k).pow 2
  have hF0 : ∀ β θ, 0 ≤ ∑ k, T k β θ ^ 2 := fun β θ ↦ Finset.sum_nonneg fun k _ ↦ sq_nonneg _
  let H : ℝ → ℝ≥0∞ := fun θ ↦ ∫⁻ β in Ioo 0 (π / 2), ENNReal.ofReal (∑ k, T k β θ ^ 2)
  have h1 : ∀ ω : Metric.sphere (0 : ℝ^3) 1,
      ∫⁻ β in Ioo 0 (π / 2),
        ENNReal.ofReal (‖(sin β / cos β ^ 2) • f ((s * tan β) • (ω : ℝ^3))‖ ^ 2) =
        H (polarAngle ω) := fun ω ↦
    setLIntegral_congr_fun measurableSet_Ioo fun β hβ ↦ by
      rw [norm_sq_compactified_eq_sum_sq hs hc T hT hframe hβ ω]
  have hsymH : ∀ θ, H (π - θ) = H θ := fun θ ↦ by simp only [H, hsym]
  have h2 : ∫⁻ θ in Ioo 0 (π / 2), ENNReal.ofReal (sin θ) * H θ =
      ∫⁻ θ in Ioo 0 (π / 2), ∫⁻ β in Ioo 0 (π / 2),
        ENNReal.ofReal ((∑ k, T k β θ ^ 2) * sin θ) :=
    setLIntegral_congr_fun measurableSet_Ioo fun θ hθ ↦ by
      have hsn : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi hθ.1.le (by linarith [hθ.2, pi_pos])
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun β ↦ ?_
      rw [← ENNReal.ofReal_mul hsn, mul_comm]
  have hmeas : AEMeasurable (Function.uncurry fun θ β ↦
      ENNReal.ofReal ((∑ k, T k β θ ^ 2) * sin θ))
      ((volume.restrict (Ioo 0 (π / 2))).prod (volume.restrict (Ioo 0 (π / 2)))) :=
    ((hFc.comp continuous_swap).mul (continuous_sin.comp continuous_fst)).measurable
      |>.ennreal_ofReal.aemeasurable
  have h3 : ∀ β, ∫⁻ θ in Ioo 0 (π / 2), ENNReal.ofReal ((∑ k, T k β θ ^ 2) * sin θ) =
      ENNReal.ofReal (∫ θ in (0 : ℝ)..(π / 2), (∑ k, T k β θ ^ 2) * sin θ) := fun β ↦
    setLIntegral_Ioo_ofReal_eq_ofReal_intervalIntegral (by linarith [pi_pos])
      ((hFc.comp (Continuous.prodMk_right β)).mul continuous_sin).continuousOn
      fun θ hθ ↦ mul_nonneg (hF0 β θ)
        (sin_nonneg_of_nonneg_of_le_pi hθ.1.le (by linarith [hθ.2, pi_pos]))
  have hG : Continuous fun β ↦ ∫ θ in (0 : ℝ)..(π / 2), (∑ k, T k β θ ^ 2) * sin θ :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun β θ ↦ (∑ k, T k β θ ^ 2) * sin θ)
      (hFc.mul (continuous_sin.comp continuous_snd)) _ _
  rw [lintegral_sq_norm_comp_scaled_tan hs hf, lintegral_congr h1,
    lintegral_sphere_comp_polarAngle_of_symm H hsymH, h2, lintegral_lintegral_swap hmeas,
    lintegral_congr h3,
    setLIntegral_Ioo_ofReal_eq_ofReal_intervalIntegral (by linarith [pi_pos])
      hG.continuousOn fun β _ ↦
      intervalIntegral.integral_nonneg (by linarith [pi_pos]) fun θ hθ ↦
        mul_nonneg (hF0 β θ) (sin_nonneg_of_nonneg_of_le_pi hθ.1
          (by linarith [hθ.2, pi_pos])),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]

end PDE.CoordinateSystems.Spherical
