/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.Polar
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Polar integration with a signed radius

Allowing the radius to range over the whole real line counts every nonzero
point twice, once for each orientation of its radial line. The Jacobian is
`|r|^(dim E - 1)`. We split the radial integral at zero and apply the ordinary
polar formula to the function and its reflection.

The weighted-measure lemmas also expose the integrability needed for this
split. They work for real normed vector space valued integrands.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace PDE.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Integration against the radial power measure is an ordinary integral
on the positive half-line with the corresponding polynomial weight. -/
theorem integral_volumeIoiPow_eq (k : ℕ) (f : ℝ → F) :
    (∫ r : Ioi (0 : ℝ), f r ∂Measure.volumeIoiPow k) =
      ∫ r in Ioi (0 : ℝ), r ^ k • f r := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul
    ((measurable_subtype_coe.pow_const k).real_toNNReal)]
  rw [integral_subtype_comap (μ := (volume : Measure ℝ)) (s := Ioi (0 : ℝ))
    measurableSet_Ioi (fun r : ℝ ↦ Real.toNNReal (r ^ k) • f r)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hr.le k)]

/-- Integrability for the radial power measure is equivalent to integrability
of the weighted function on the positive half-line. -/
theorem integrable_volumeIoiPow_iff (k : ℕ) (f : ℝ → F) :
    Integrable (fun r : Ioi (0 : ℝ) ↦ f r) (Measure.volumeIoiPow k) ↔
      IntegrableOn (fun r : ℝ ↦ r ^ k • f r) (Ioi 0) volume := by
  rw [Measure.volumeIoiPow]
  have hm : Measurable (fun r : Ioi (0 : ℝ) ↦ ENNReal.ofReal (r.1 ^ k)) := by
    fun_prop
  rw [integrable_withDensity_iff_integrable_smul' hm (Filter.Eventually.of_forall
    (fun _ ↦ ENNReal.ofReal_lt_top))]
  rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioi]
  apply integrable_congr
  filter_upwards [] with r
  simp [ENNReal.toReal_ofReal (pow_nonneg r.2.le k)]

private theorem integral_abs_pow_smul_split (k : ℕ) (g : ℝ → F)
    (hp : IntegrableOn (fun r : ℝ ↦ r ^ k • g r) (Ioi 0))
    (hn : IntegrableOn (fun r : ℝ ↦ r ^ k • g (-r)) (Ioi 0)) :
    (∫ r : ℝ, |r| ^ k • g r) =
      (∫ r in Ioi (0 : ℝ), r ^ k • g (-r)) +
        ∫ r in Ioi (0 : ℝ), r ^ k • g r := by
  have hpos : IntegrableOn (fun r : ℝ ↦ |r| ^ k • g r) (Ioi 0) :=
    hp.congr_fun (fun r hr ↦ by rw [abs_of_pos hr]) measurableSet_Ioi
  have hn' : IntegrableOn (fun r : ℝ ↦ |r| ^ k • g (-r)) (Ici 0) := by
    apply Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
    exact hn.congr_fun (fun r hr ↦ by rw [abs_of_pos hr]) measurableSet_Ioi
  have hneg : IntegrableOn (fun r : ℝ ↦ |r| ^ k • g r) (Iic 0) := by
    have hn'' : IntegrableOn (fun r : ℝ ↦ |r| ^ k • g (-r)) (Ici (-0)) := by
      simpa only [neg_zero] using hn'
    simpa only [abs_neg, neg_neg] using hn''.comp_neg_Iic (c := 0)
  calc
    _ = (∫ r in Iic (0 : ℝ), |r| ^ k • g r) +
        ∫ r in Ioi (0 : ℝ), |r| ^ k • g r := by
      rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hneg hpos,
        Iic_union_Ioi, Measure.restrict_univ]
    _ = _ := by
      congr 1
      · rw [← neg_zero, ← integral_comp_neg_Ioi, neg_zero]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        simp only [abs_neg, abs_of_pos (show 0 < r from hr)]
      · apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        simp only [abs_of_pos (show 0 < r from hr)]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The radial integral of an integrable function is integrable over
the unit sphere with its induced Haar measure. -/
theorem integrable_polar_radialIntegral (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → F} (hf : Integrable f μ) :
    Integrable (fun θ : Metric.sphere (0 : E) 1 ↦
      ∫ r in Ioi (0 : ℝ), r ^ (Module.finrank ℝ E - 1) • f (r • (θ : E)))
      μ.toSphere := by
  have h := (integrable_polar_addHaar μ f hf).integral_prod_left
  convert h using 1
  ext θ
  exact (integral_volumeIoiPow_eq _ (fun r ↦ f (r • (θ : E)))).symm

/-- The weighted restriction of an integrable function to almost every
positive radial ray is integrable. -/
theorem ae_integrableOn_polar_ray (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → F} (hf : Integrable f μ) :
    ∀ᵐ θ : Metric.sphere (0 : E) 1 ∂μ.toSphere,
      IntegrableOn (fun r : ℝ ↦ r ^ (Module.finrank ℝ E - 1) • f (r • (θ : E)))
        (Ioi 0) volume := by
  have h := (integrable_polar_addHaar μ f hf).prod_right_ae
  filter_upwards [h] with θ hθ
  exact (integrable_volumeIoiPow_iff _ _).mp hθ

/-- Polar integration over all signed radii counts each point twice.
The absolute radial Jacobian accounts for the negative half-line. -/
theorem integral_polar_addHaar_signedRadius [Nontrivial E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → F} (hf : Integrable f μ) :
    (∫ θ : Metric.sphere (0 : E) 1,
      (∫ r : ℝ, |r| ^ (Module.finrank ℝ E - 1) • f (r • (θ : E))) ∂μ.toSphere) =
      (2 : ℝ) • ∫ x, f x ∂μ := by
  have hneg : Integrable (fun x : E ↦ f (-x)) μ := hf.comp_neg
  have hp := ae_integrableOn_polar_ray μ hf
  have hn := ae_integrableOn_polar_ray μ hneg
  have hsplit : (fun θ : Metric.sphere (0 : E) 1 ↦
      ∫ r : ℝ, |r| ^ (Module.finrank ℝ E - 1) • f (r • (θ : E))) =ᵐ[μ.toSphere]
      fun θ ↦ (∫ r in Ioi (0 : ℝ),
        r ^ (Module.finrank ℝ E - 1) • f (-(r • (θ : E)))) +
        ∫ r in Ioi (0 : ℝ),
          r ^ (Module.finrank ℝ E - 1) • f (r • (θ : E)) := by
    filter_upwards [hp, hn] with θ hpθ hnθ
    simpa only [neg_smul] using
      integral_abs_pow_smul_split _ (fun r ↦ f (r • (θ : E))) hpθ
        (by simpa only [neg_smul] using hnθ)
  rw [integral_congr_ae hsplit,
    integral_add (integrable_polar_radialIntegral μ hneg)
      (integrable_polar_radialIntegral μ hf),
    ← integral_polar_addHaar_iterated_sphereFirst μ _ hneg,
    ← integral_polar_addHaar_iterated_sphereFirst μ _ hf,
    integral_neg_eq_self, two_smul ℝ]

end PDE.Analysis
