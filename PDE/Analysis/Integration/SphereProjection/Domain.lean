/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.SphereProjection.Coordinates
public import PDE.Analysis.Integration.CoordinateSplit

/-!
# The image of the hemisphere radial chart

The signed chart covers the open unit ball except for its equatorial
hyperplane, which has zero volume. Its domain is a ball times a punctured
interval. No positive base dimension is needed for these geometric facts.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace PDE.Analysis

variable {n : ℕ}

/-- The radial parameter domain is measurable. -/
theorem measurableSet_hemisphereRadialDomain :
    MeasurableSet (hemisphereRadialDomain (n := n)) := by
  have h1 : IsOpen {p : ℝ^(n + 1) | ‖coordinateProjection p‖ ^ 2 < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  have h2 : IsOpen {p : ℝ^(n + 1) | |p (Fin.last n)| < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  have h3 : IsOpen {p : ℝ^(n + 1) | p (Fin.last n) ≠ 0} :=
    isOpen_ne.preimage (PiLp.continuous_apply 2 _ (Fin.last n))
  exact (h1.inter (h2.inter h3)).measurableSet

/-- The signed radial chart covers the ball except for its equatorial hyperplane. -/
theorem image_hemisphereRadialMap :
    hemisphereRadialMap '' hemisphereRadialDomain =
      Metric.ball (0 : ℝ^(n + 1)) 1 \ {y | y (Fin.last n) = 0} := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa only [Metric.mem_ball, dist_zero_right, norm_hemisphereRadialMap hp] using hp.2.1
    · change hemisphereRadialMap p (Fin.last n) ≠ 0
      rw [hemisphereRadialMap_last]
      exact mul_ne_zero hp.2.2 (hemisphereRadialDomain_sqrt_pos hp).ne'
  · rintro ⟨hy, hz⟩
    have hz0 : y (Fin.last n) ≠ 0 := hz
    have hn : 0 < ‖y‖ := norm_pos_iff.2 fun he ↦ hz0 (by simp [he])
    let r := ‖y‖ * y (Fin.last n) / |y (Fin.last n)|
    have hr : |r| = ‖y‖ := by
      simp [r, abs_div, abs_mul, abs_norm, abs_abs, abs_ne_zero.2 hz0]
    have hr0 : r ≠ 0 := abs_pos.1 (hr ▸ hn)
    let p : ℝ^(n + 1) := lastCoordinateSplit.symm (‖y‖⁻¹ • coordinateProjection y, r)
    have hpnorm : ‖coordinateProjection p‖ ^ 2 = ‖coordinateProjection y‖ ^ 2 / ‖y‖ ^ 2 := by
      simp [p, norm_smul, norm_inv, div_eq_mul_inv, mul_pow, mul_comm]
    have hrad : 1 - ‖coordinateProjection p‖ ^ 2 = (|y (Fin.last n)| / ‖y‖) ^ 2 := by
      rw [hpnorm, div_pow, sq_abs]
      field_simp
      nlinarith [norm_sq_coordinateProjection y]
    have hs : √(1 - ‖coordinateProjection p‖ ^ 2) = |y (Fin.last n)| / ‖y‖ := by
      rw [hrad, Real.sqrt_sq (div_nonneg (abs_nonneg _) hn.le)]
    have hp : p ∈ hemisphereRadialDomain := by
      refine ⟨?_, ?_, ?_⟩
      · have hpos : 0 < (|y (Fin.last n)| / ‖y‖) ^ 2 :=
          sq_pos_of_pos (div_pos (abs_pos.2 hz0) hn)
        linarith [hrad]
      · simpa [p, hr] using hy
      · simpa [p] using hr0
    refine ⟨p, hp, ?_⟩
    ext i
    cases i using Fin.lastCases with
    | last =>
        rw [hemisphereRadialMap_last, hs]
        simp only [p, lastCoordinateSplit_symm_last, r]
        field_simp
    | cast i =>
        simp [p, hr, PiLp.smul_apply, hn.ne']

/-- The equatorial hyperplane has zero ambient volume. -/
theorem volume_equatorialPlane : volume {y : ℝ^(n + 1) | y (Fin.last n) = 0} = 0 := by
  have h := (lastCoordinateSplit_measurePreserving (n := n)).measure_preimage_equiv
    (Set.univ ×ˢ ({0} : Set ℝ))
  have heq : lastCoordinateSplit ⁻¹' (Set.univ ×ˢ ({0} : Set ℝ)) =
      {y : ℝ^(n + 1) | y (Fin.last n) = 0} := by
    ext y
    simp
  rw [heq] at h
  simpa only [Measure.volume_eq_prod, Measure.prod_prod, measure_singleton, mul_zero] using h

/-- Removing the equator does not change a volume integral on the ball. -/
theorem image_hemisphereRadialMap_ae_eq_ball :
    hemisphereRadialMap '' hemisphereRadialDomain =ᵐ[volume] Metric.ball (0 : ℝ^(n + 1)) 1 := by
  rw [image_hemisphereRadialMap]
  exact MeasureTheory.sdiff_ae_eq_self.2
    (measure_mono_null Set.inter_subset_right volume_equatorialPlane)

/-- The parameter domain is the base ball times a punctured signed interval. -/
theorem preimage_lastCoordinateSplit_domain :
    lastCoordinateSplit.symm ⁻¹' hemisphereRadialDomain =
      Metric.ball (0 : ℝ^n) 1 ×ˢ (Set.Ioo (-1 : ℝ) 1 \ {0}) := by
  ext p
  simp only [Set.mem_preimage, hemisphereRadialDomain, Set.mem_ofPred_eq,
    coordinateProjection_lastCoordinateSplit_symm, lastCoordinateSplit_symm_last,
    Set.mem_prod, Metric.mem_ball, dist_zero_right, Set.mem_sdiff, Set.mem_Ioo,
    Set.mem_singleton_iff, abs_lt]
  have hsq : ‖p.1‖ ^ 2 < 1 ↔ ‖p.1‖ < 1 := by
    constructor <;> intro h <;> nlinarith [norm_nonneg p.1, sq_nonneg (‖p.1‖ - 1)]
  rw [hsq]

end PDE.Analysis
