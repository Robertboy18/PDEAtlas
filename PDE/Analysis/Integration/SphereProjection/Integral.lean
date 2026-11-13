/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.EuclideanBall
public import PDE.Analysis.Integration.SphereProjection.Domain
public import PDE.Analysis.Integration.SphereProjection.Jacobian
public import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Projecting sphere integrals onto a ball

Comparing polar integration with the signed hemisphere chart gives the density
`2 / √(1 - ‖y‖²)` for coordinate projection of surface measure. The
argument includes a zero-dimensional base ball.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace PDE.Analysis

variable {n : ℕ}

/-- Extend a function on the base ball constantly along ambient rays. -/
def radialCoordinateExtension (f : ℝ^n → ℝ) (y : ℝ^(n + 1)) : ℝ :=
  f (coordinateProjection (NormedSpace.normalize y))

/-- The raywise extension is integrable on the unit ball for continuous data. -/
theorem integrableOn_radialCoordinateExtension {f : ℝ^n → ℝ} (hf : Continuous f) :
    IntegrableOn (radialCoordinateExtension f) (Metric.ball (0 : ℝ^(n + 1)) 1) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℝ^(n + 1)) 1).exists_bound_of_continuousOn
    (hf.comp coordinateProjection.continuous).continuousOn
  have hmeas : Measurable (radialCoordinateExtension f) :=
    hf.measurable.comp (coordinateProjection.continuous.measurable.comp
      (measurable_norm.inv.smul measurable_id))
  refine Measure.integrableOn_of_bounded measure_ball_lt_top.ne
    hmeas.aestronglyMeasurable (M := C) ?_
  filter_upwards with y
  apply hC
  simp only [Metric.mem_closedBall, dist_zero_right]
  by_cases hy : y = 0
  · simp [hy]
  · exact (NormedSpace.norm_normalize hy).le

/-- Along a positive ray the extension is its value on the unit sphere. -/
theorem radialCoordinateExtension_smul_sphere (f : ℝ^n → ℝ)
    (ω : Metric.sphere (0 : ℝ^(n + 1)) 1) {r : ℝ} (hr : 0 < r) :
    radialCoordinateExtension f (r • (ω : ℝ^(n + 1))) =
      f (coordinateProjection ω) := by
  rw [radialCoordinateExtension, NormedSpace.normalize_smul_of_pos hr,
    NormedSpace.normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp ω.property)]

/-- Polar integration of the raywise extension separates its radial factor. -/
theorem integral_ball_radialCoordinateExtension {f : ℝ^n → ℝ} (hf : Continuous f) :
    (∫ y in Metric.ball (0 : ℝ^(n + 1)) 1, radialCoordinateExtension f y) =
      (1 / (n + 1 : ℝ)) * ∫ ω : Metric.sphere (0 : ℝ^(n + 1)) 1,
        f (coordinateProjection ω) ∂(volume : Measure (ℝ^(n + 1))).toSphere := by
  change ballIntegral (n + 1) (radialCoordinateExtension f) 0 1 = _
  rw [coarea_formula_ball _ _ _ (integrableOn_radialCoordinateExtension hf),
    ← setIntegral_congr_set Ioc_ae_eq_Icc]
  have he : Set.EqOn (sphereIntegral (n + 1) (radialCoordinateExtension f) 0)
      (fun r ↦ r ^ n * ∫ ω : Metric.sphere (0 : ℝ^(n + 1)) 1,
        f (coordinateProjection ω) ∂(volume : Measure (ℝ^(n + 1))).toSphere)
      (Set.Ioc 0 1) := by
    intro r hr
    simp only [sphereIntegral, Nat.add_sub_cancel, abs_of_pos hr.1, zero_add]
    congr 1
    apply integral_congr_ae
    filter_upwards with ω
    exact radialCoordinateExtension_smul_sphere f ω hr.1
  rw [setIntegral_congr_fun measurableSet_Ioc he, integral_mul_const]
  congr 1
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_pow]
  simp

/-- Normalizing the radial chart recovers its base parameter. -/
theorem radialCoordinateExtension_hemisphereRadialMap (f : ℝ^n → ℝ)
    {p : ℝ^(n + 1)} (hp : p ∈ hemisphereRadialDomain) :
    radialCoordinateExtension f (hemisphereRadialMap p) =
      f (coordinateProjection p) := by
  unfold radialCoordinateExtension NormedSpace.normalize
  rw [norm_hemisphereRadialMap hp, map_smul, coordinateProjection_hemisphereRadialMap,
    smul_smul, inv_mul_cancel₀ (abs_ne_zero.2 hp.2.2), one_smul]

/-- The absolute Jacobian separates into the ball weight and the radial power. -/
theorem hemisphereRadialMap_weight (f : ℝ^n → ℝ) {p : ℝ^(n + 1)}
    (hp : p ∈ hemisphereRadialDomain) :
    |(fderiv ℝ hemisphereRadialMap p).det| •
        radialCoordinateExtension f (hemisphereRadialMap p) =
      (f (coordinateProjection p) / √(1 - ‖coordinateProjection p‖ ^ 2)) *
        |p (Fin.last n)| ^ n := by
  rw [det_fderiv_hemisphereRadialMap hp,
    radialCoordinateExtension_hemisphereRadialMap f hp,
    abs_of_nonneg (div_nonneg (pow_nonneg (abs_nonneg _) _) (Real.sqrt_nonneg _)),
    smul_eq_mul]
  ring

/-- The radial factor integrates to `2/(n+1)`; puncturing at zero changes no integral. -/
theorem integral_abs_pow_punctured_unitInterval (n : ℕ) :
    (∫ r in Set.Ioo (-1 : ℝ) 1 \ {0}, |r| ^ n) = 2 / (n + 1 : ℝ) := by
  rw [setIntegral_congr_set
    (sdiff_ae_eq_self.2 (measure_mono_null Set.inter_subset_right (measure_singleton 0))),
    setIntegral_congr_set Ioo_ae_eq_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have hc : Continuous (fun r : ℝ ↦ |r| ^ n) := continuous_abs.pow n
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-1) 0) (hc.intervalIntegrable 0 1)]
  have hneg : (∫ r in (-1 : ℝ)..0, |r| ^ n) = ∫ r in (0 : ℝ)..1, |r| ^ n := by
    simpa using (intervalIntegral.integral_comp_neg (fun r : ℝ ↦ |r| ^ n)
      (a := (-1 : ℝ)) (b := 0))
  have hpos : (∫ r in (0 : ℝ)..1, |r| ^ n) = 1 / (n + 1 : ℝ) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    simpa using (integral_pow_abs_sub_uIoc (a := (0 : ℝ)) (b := 1)
      (n := n))
  rw [hneg, hpos]
  ring

/-- Integration over the parameter cylinder separates the base and radial factors. -/
theorem integral_hemisphereRadialDomain_weight (f : ℝ^n → ℝ) :
    (∫ p in hemisphereRadialDomain,
      (f (coordinateProjection p) / √(1 - ‖coordinateProjection p‖ ^ 2)) *
        |p (Fin.last n)| ^ n) =
      (∫ y in Metric.ball (0 : ℝ^n) 1, f y / √(1 - ‖y‖ ^ 2)) *
        (2 / (n + 1 : ℝ)) := by
  let W : ℝ^(n + 1) → ℝ := fun p ↦
    (f (coordinateProjection p) / √(1 - ‖coordinateProjection p‖ ^ 2)) *
      |p (Fin.last n)| ^ n
  have he := (lastCoordinateSplit_measurePreserving.symm
    lastCoordinateSplit).setIntegral_preimage_emb
      lastCoordinateSplit.symm.measurableEmbedding W hemisphereRadialDomain
  rw [preimage_lastCoordinateSplit_domain] at he
  rw [← he]
  simp only [W, coordinateProjection_lastCoordinateSplit_symm, lastCoordinateSplit_symm_last]
  rw [Measure.volume_eq_prod,
    setIntegral_prod_mul (fun y : ℝ^n ↦ f y / √(1 - ‖y‖ ^ 2))
      (fun r : ℝ ↦ |r| ^ n),
    integral_abs_pow_punctured_unitInterval]

/-- Coordinate projection of the unit sphere's surface measure has square-root density.
Both hemispheres contribute equally. -/
theorem integral_sphere_eq_ball_weight {f : ℝ^n → ℝ} (hf : Continuous f) :
    (∫ ω : Metric.sphere (0 : ℝ^(n + 1)) 1,
      f (coordinateProjection ω) ∂(volume : Measure (ℝ^(n + 1))).toSphere) =
      2 * ∫ y in Metric.ball (0 : ℝ^n) 1, f y / √(1 - ‖y‖ ^ 2) := by
  have hchange := integral_image_eq_integral_abs_det_fderiv_smul (μ := volume)
    measurableSet_hemisphereRadialDomain
    (fun p hp ↦ (differentiableAt_hemisphereRadialMap hp).hasFDerivAt.hasFDerivWithinAt)
    injOn_hemisphereRadialMap (radialCoordinateExtension f)
  rw [setIntegral_congr_set image_hemisphereRadialMap_ae_eq_ball,
    integral_ball_radialCoordinateExtension hf] at hchange
  rw [setIntegral_congr_fun measurableSet_hemisphereRadialDomain
    (fun p hp ↦ hemisphereRadialMap_weight f hp),
    integral_hemisphereRadialDomain_weight] at hchange
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp at hchange
  linarith

end PDE.Analysis
