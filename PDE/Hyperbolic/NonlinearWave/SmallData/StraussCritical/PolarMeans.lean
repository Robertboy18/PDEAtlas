/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SphericalMean.Regularity
public import PDE.Analysis.Integration.Polar
public import Mathlib.Analysis.Convex.Integral

/-!
# Spherical Jensen and radial integration

These estimates use the normalized spherical mean and the full Euclidean
surface measure. In three dimensions the spatial integral is the sphere area
times the integral of the mean against `r² dr`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory PDE.Analysis PDE.Common Set

namespace WaveEquation.SmallData

/-- Continuous data are integrable on each sampling sphere. -/
theorem integrable_sphere_sampling {f : ℝ^3 → ℝ} (hf : Continuous f) (r : ℝ) :
    Integrable (fun ω : Metric.sphere (0 : ℝ^3) 1 ↦ f (r • (ω : ℝ^3)))
      (volume : Measure (ℝ^3)).toSphere :=
  (hf.comp (by fun_prop)).integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset isClosed_closure (fun _ _ ↦ mem_univ _))

/-- Spherical averaging preserves nonnegativity. -/
theorem unitSphereAverage_nonneg {f : ℝ^3 → ℝ} (hf : ∀ x, 0 ≤ f x) (r : ℝ) :
    0 ≤ unitSphereAverage 3 f 0 r :=
  div_nonneg (integral_nonneg fun _ ↦ hf _) unitSphereArea_pos.le

/-- Spherical averaging preserves pointwise order of continuous data. -/
theorem unitSphereAverage_mono {f g : ℝ^3 → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hle : ∀ x, f x ≤ g x) (r : ℝ) :
    unitSphereAverage 3 f 0 r ≤ unitSphereAverage 3 g 0 r := by
  unfold unitSphereAverage
  simp only [zero_add]
  exact div_le_div_of_nonneg_right
    (integral_mono (integrable_sphere_sampling hf r) (integrable_sphere_sampling hg r)
      (fun _ ↦ hle _)) unitSphereArea_pos.le

/-- Jensen's power inequality for the normalized spherical mean. -/
theorem abs_unitSphereAverage_rpow_le {f : ℝ^3 → ℝ}
    (hf : Continuous f) {p : ℝ} (hp : 1 ≤ p) (r : ℝ) :
    |unitSphereAverage 3 f 0 r| ^ p ≤ unitSphereAverage 3 (fun x ↦ |f x| ^ p) 0 r := by
  have hconv : ConvexOn ℝ univ (fun x : ℝ ↦ |x| ^ p) := by
    have hn : ConvexOn ℝ univ (fun x : ℝ ↦ ‖x‖ ^ p) := by
      refine ⟨convex_univ, fun x hx y hy a b ha hb hab ↦ ?_⟩
      exact (Real.rpow_le_rpow (norm_nonneg _)
        ((convexOn_univ_norm (E := ℝ)).2 hx hy ha hb hab) (zero_le_one.trans hp)).trans
        ((convexOn_rpow hp).2 (norm_nonneg x) (norm_nonneg y) ha hb hab)
    simpa only [Real.norm_eq_abs] using hn
  have hc : Continuous (fun x : ℝ ↦ |x| ^ p) :=
    continuous_abs.rpow_const (fun _ ↦ Or.inr (zero_le_one.trans hp))
  have hμpos : 0 < ((volume : Measure (ℝ^3)).toSphere univ).toReal := unitSphereArea_pos
  have hj := hconv.map_set_average_le (μ := (volume : Measure (ℝ^3)).toSphere) (t := univ)
    (f := fun ω : Metric.sphere (0 : ℝ^3) 1 ↦ f (r • (ω : ℝ^3))) hc.continuousOn isClosed_univ
    (ENNReal.toReal_pos_iff.mp hμpos).1.ne' (ENNReal.toReal_pos_iff.mp hμpos).2.ne
    (Eventually.of_forall fun _ ↦ mem_univ _) (integrable_sphere_sampling hf r).integrableOn
    (integrable_sphere_sampling (hc.comp hf) r).integrableOn
  simpa only [setAverage_eq, setIntegral_univ, smul_eq_mul, measureReal_def,
    unitSphereAverage, zero_add, unitSphereArea, div_eq_inv_mul] using hj

/-- Polar integration of a three-dimensional function in normalized means. -/
theorem integral_eq_sphericalMean_integral {f : ℝ^3 → ℝ} (hf : Integrable f) :
    (∫ x : ℝ^3, f x) =
      unitSphereArea 3 * ∫ r in Ioi (0 : ℝ), r ^ 2 * unitSphereAverage 3 f 0 r := by
  rw [integral_polar_addHaar_iterated volume f hf, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ ↦ ?_
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul,
    unitSphereAverage, zero_add]
  exact (mul_div_cancel₀ _ unitSphereArea_pos.ne').symm.trans (by ring)

/-- The radial mass density is integrable whenever the original function is. -/
theorem integrableOn_sphericalMean_density {f : ℝ^3 → ℝ} (hf : Integrable f) :
    IntegrableOn (fun r : ℝ ↦ r ^ 2 * unitSphereAverage 3 f 0 r) (Ioi 0) := by
  have hi := (integrableOn_polar_angular volume f hf).div_const (unitSphereArea 3)
  simpa only [IntegrableOn, finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub,
    unitSphereAverage, zero_add, mul_div_assoc] using hi

/-- If the radial mean is supported in a positive annulus, polar integration reduces
to the ordinary integral over that annulus. -/
theorem integral_eq_sphericalMean_annulus {f : ℝ^3 → ℝ} {a b : ℝ} (hf : Integrable f) (ha : 0 ≤ a)
    (hab : a ≤ b) (hs : ∀ r, 0 < r → r ≤ a ∨ b < r → unitSphereAverage 3 f 0 r = 0) :
    (∫ x : ℝ^3, f x) = unitSphereArea 3 * ∫ r in a..b, r ^ 2 * unitSphereAverage 3 f 0 r := by
  rw [integral_eq_sphericalMean_integral hf, intervalIntegral.integral_of_le hab]
  congr 1
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun r hr ↦ ha.trans_lt hr.1)
  intro r hr
  rw [hs r hr.1 (by simpa only [mem_Ioc, not_and_or, not_lt, not_le] using hr.2), mul_zero]

end WaveEquation.SmallData
