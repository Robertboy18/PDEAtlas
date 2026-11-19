/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Nonnegative radial integration

An additive Haar measure on a nontrivial finite-dimensional real normed space
decomposes into its angular measure and the radial density `r^(dim E - 1) dr`.
The formulas below use extended nonnegative integrals, so they apply before
integrability is known and retain divergent values.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- A nonnegative radial integral equals the angular mass times the weighted
integral over positive radii, with no finiteness assumption. -/
theorem lintegral_fun_norm_addHaar (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x : E, f ‖x‖ ∂μ) =
      μ.toSphere univ *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) * f r := by
  calc
    (∫⁻ x : E, f ‖x‖ ∂μ) =
        ∫⁻ x : ({(0 : E)}ᶜ : Set E), f ‖x.1‖ ∂(μ.comap (↑)) := by
      rw [lintegral_subtype_comap (measurableSet_singleton _).compl
        (fun x : E ↦ f ‖x‖),
        restrict_compl_singleton]
    _ = ∫⁻ z : Metric.sphere (0 : E) 1 × Ioi (0 : ℝ), f z.2.1
        ∂(μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
      simpa only [Function.comp_def, homeomorphUnitSphereProd_apply_snd_coe] using
        μ.measurePreserving_homeomorphUnitSphereProd.lintegral_comp
          (hf.comp (measurable_subtype_coe.comp measurable_snd))
    _ = μ.toSphere univ *
        ∫⁻ r : Ioi (0 : ℝ), f r.1
          ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1)) := by
      rw [lintegral_prod
        (fun z : Metric.sphere (0 : E) 1 × Ioi (0 : ℝ) ↦ f z.2.1)
        (hf.comp (measurable_subtype_coe.comp measurable_snd)).aemeasurable]
      simp [mul_comm]
    _ = _ := by
      congr 1
      rw [Measure.volumeIoiPow]
      calc
        _ = ∫⁻ r : Ioi (0 : ℝ),
            ENNReal.ofReal (r.1 ^ (Module.finrank ℝ E - 1)) * f r.1
              ∂(Measure.comap Subtype.val volume) :=
          lintegral_withDensity_eq_lintegral_mul _
            (measurable_subtype_coe.pow_const _).ennreal_ofReal
            (hf.comp measurable_subtype_coe)
        _ = _ := lintegral_subtype_comap measurableSet_Ioi
          (fun r ↦ ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) * f r)

/-- The radial formula about any center, using translation invariance of Haar measure. -/
theorem lintegral_fun_norm_sub_addHaar (μ : Measure E) [μ.IsAddHaarMeasure]
    (a : E) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x : E, f ‖x - a‖ ∂μ) =
      μ.toSphere univ *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) * f r := by
  calc
    _ = ∫⁻ x : E, f ‖x‖ ∂μ :=
      (measurePreserving_sub_right μ a).lintegral_comp (hf.comp measurable_norm)
    _ = _ := lintegral_fun_norm_addHaar μ hf

/-- The radial Jacobian cancels the dimension in the normal trace kernel,
leaving the one-dimensional Hardy weight `r^(-p)`. -/
theorem lintegral_norm_rpow_mul_addHaar (μ : Measure E) [μ.IsAddHaarMeasure]
    (p : ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x : E,
      ENNReal.ofReal (‖x‖ ^ (-((Module.finrank ℝ E : ℝ) + p - 1))) * f ‖x‖ ∂μ) =
      μ.toSphere univ * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (-p)) * f r := by
  rw [lintegral_fun_norm_addHaar μ
    (f := fun r : ℝ ↦
      ENNReal.ofReal (r ^ (-((Module.finrank ℝ E : ℝ) + p - 1))) * f r)
    (by fun_prop)]
  congr 1
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hr.le _)]
  congr 2
  rw [← Real.rpow_natCast, ← Real.rpow_add hr]
  congr 1
  rw [Nat.cast_sub (show 1 ≤ Module.finrank ℝ E from Module.finrank_pos)]
  simp

end MeasureTheory
