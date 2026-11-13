/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Cutoff.AnnularStress
import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Annular.Estimate
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The planar cutoff stress estimate

The cutoff Hessian contributes a factor of `R⁻²`, which cancels the area
of its annular support. The remaining bound is a potential value at a
point that escapes to spatial infinity.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE PDE.Common PDE.Analysis SobolevSpace.Approximation

namespace WaveEquation

private theorem realVolume_ball_two {R : ℝ} (hR : 0 ≤ R) :
    volume.real (Metric.ball (0 : ℝ^2) R) = R ^ 2 * Real.pi := by
  simp only [Measure.real, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hR, ENNReal.toReal_ofReal Real.pi_pos.le]

private theorem realVolume_closedBall_two {R : ℝ} (hR : 0 ≤ R) :
    volume.real (Metric.closedBall (0 : ℝ^2) R) = R ^ 2 * Real.pi := by
  simp only [Measure.real, EuclideanSpace.volume_closedBall_fin_two, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hR, ENNReal.toReal_ofReal Real.pi_pos.le]

/-- The cutoff annulus lies in the disk of radius `2 R`. -/
private theorem realVolume_cutoff_annulus_two_le {R : ℝ} (hR : 0 ≤ R) :
    volume.real (Metric.closedBall (0 : ℝ^2) (2 * R) \ Metric.ball 0 R) ≤ 4 * Real.pi * R ^ 2 := by
  calc
    _ ≤ volume.real (Metric.closedBall (0 : ℝ^2) (2 * R)) :=
      measureReal_mono sdiff_subset (isCompact_closedBall (0 : ℝ^2) (2 * R)).measure_ne_top
    _ = _ := by rw [realVolume_closedBall_two (by positivity)]; ring

/-- The enlarged annulus costs at most the area of a disk of radius `3 R`. -/
private theorem realVolume_annulus_two_le {R : ℝ} (hR : 1 ≤ R) :
    volume.real (Metric.closedBall (0 : ℝ^2) (2 * R + 1) \
      Metric.ball 0 (R - 1)) ≤ 9 * Real.pi * R ^ 2 := by
  calc
    _ ≤ volume.real (Metric.closedBall (0 : ℝ^2) (3 * R)) :=
      measureReal_mono (sdiff_subset.trans (Metric.closedBall_subset_closedBall (by linarith)))
        (isCompact_closedBall (0 : ℝ^2) (3 * R)).measure_ne_top
    _ = 9 * Real.pi * R ^ 2 := by
      rw [realVolume_closedBall_two (by linarith)]
      ring

/-- Divide the local averaging estimate by the area of the unit disk.
The resulting bound grows quadratically with the cutoff radius. -/
private theorem annular_kinetic_two_le {K : ℝ^2 → ℝ} {R L M : ℝ} (hR : 1 ≤ R) (hL : 0 ≤ L)
    (hM : 0 ≤ M)
    (hbound : volume.real (Metric.ball (0 : ℝ^2) 1) * (∫ x in Metric.closedBall (0 : ℝ^2) (2 * R) \
      Metric.ball 0 R, K x) ≤ volume.real (Metric.closedBall (0 : ℝ^2) (2 * R + 1) \ Metric.ball 0
      (R - 1)) * volume.real (Metric.ball (0 : ℝ^2) L) * M) :
    (∫ x in Metric.closedBall (0 : ℝ^2) (2 * R) \ Metric.ball 0 R, K x) ≤
      9 * Real.pi * R ^ 2 * L ^ 2 * M := by
  rw [realVolume_ball_two (by norm_num), realVolume_ball_two hL] at hbound
  norm_num only [one_pow, one_mul] at hbound
  have harea := realVolume_annulus_two_le hR
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right harea (show 0 ≤ L ^ 2 * Real.pi by positivity)) hM
  apply (mul_le_mul_iff_right₀ Real.pi_pos).mp
  calc
    _ ≤ _ := hbound.trans hm
    _ = _ := by ring

/-- In the plane the area `O(R²)` of the annulus cancels the factor `R⁻²` from the
cutoff Hessian. For `R` large the stress on `[s, t]` is bounded by a constant times
`|V(u(r, y))|` at a single point with `r ∈ [s, t]` and `‖y‖ ≥ R - (t + 1 - s) - 1`. -/
theorem exists_radius_cutoffStress_le_potential_value_two {V : ℝ → ℝ} {u : ℝ^3 → ℝ}
    (hV : ContDiff ℝ 1 V) (hVzero : V 0 = 0) (hu : ContDiff ℝ 3 u)
    (hwave : ∀ r, 0 < r → ∀ x, semilinearWaveOperator V u (timeSpaceCons r x) = 0)
    (hs : ∀ r, 0 ≤ r → HasCompactSupport (fun x : ℝ^2 ↦ u (timeSpaceCons r x))) {s t : ℝ}
    (hs0 : 0 ≤ s) (hst : s ≤ t) :
    ∃ C ≥ 0, ∃ R₀ > 0, ∀ R, R₀ ≤ R → ∃ r ∈ Icc s t, ∃ y : ℝ^2, R - (t + 1 - s) - 1 ≤ ‖y‖ ∧ ∀ τ ∈
      Icc s t, ‖cutoffStress (cutoff R) V u τ‖ ≤ C * |V (u (timeSpaceCons r y))| := by
  classical
  let L := t + 1 - s
  have hL : 1 ≤ L := by dsimp only [L]; linarith
  choose c hc hb using fun i j : Fin 2 ↦ exists_abs_iteratedPartialDeriv_cutoff_le [j, i]
  let C := ∑ i : Fin 2, ∑ j : Fin 2, c i j
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hc i j
  obtain ⟨R₀, hR₀, hkin⟩ := exists_radius_annular_kinetic_le_potential_value
    hV hVzero hu hwave hs hs0
  refine ⟨C * Real.pi * (9 * L ^ 2 + 4), by positivity,
    R₀ + L + 2, by linarith, ?_⟩
  intro R hR
  have hRone : 1 ≤ R := by linarith
  have hRpos : 0 < R := by linarith
  obtain ⟨r, hr, y, hy, hmax, hK⟩ := hkin t hst R (by dsimp only [L] at hR; linarith)
  have hyfar : R - (t + 1 - s) - 1 ≤ ‖y‖ := by
    have hy' := hy.2
    simp only [Metric.mem_ball, dist_zero_right, not_lt] at hy'
    linarith
  refine ⟨r, hr, y, hyfar, fun τ hτ ↦ ?_⟩
  let M := |V (u (timeSpaceCons r y))|
  let A := Metric.closedBall (0 : ℝ^2) (2 * R) \ Metric.ball 0 R
  have hpot (x : ℝ^2) (hx : x ∈ A) : |V (u (timeSpaceCons τ x))| ≤ M := by
    apply hmax τ hτ x
    simp only [A, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
      dist_zero_right, not_lt] at hx ⊢
    constructor <;> dsimp only [L] at hL <;> linarith
  have hentry (i j : Fin 2) (x : ℝ^2) :
      |(∂[j] (∂[i] (cutoff R))) x| ≤ c i j / R ^ 2 := by
    simpa only [iteratedPartialDeriv, List.length_cons, List.length_nil,
      Nat.reduceAdd, div_eq_mul_inv, inv_pow] using hb i j R hRpos x
  have hnorm := norm_cutoffStress_le_annular (hu.of_le (by norm_num)) hRpos hpot
    (fun i j ↦ div_nonneg (hc i j) (sq_nonneg R)) hentry
  have hsum : (∑ i : Fin 2, ∑ j : Fin 2, c i j / R ^ 2) = C / R ^ 2 := by
    simp only [← Finset.sum_div, C]
  rw [hsum] at hnorm
  have hk := annular_kinetic_two_le hRone (show 0 ≤ L by linarith) (abs_nonneg _) (hK τ hτ)
  have ha := mul_le_mul_of_nonneg_right (realVolume_cutoff_annulus_two_le hRpos.le)
    (show 0 ≤ M from abs_nonneg _)
  calc
    _ ≤ (C / R ^ 2) *
        ((∫ x in A, classicalWaveEnergyDensity u (timeSpaceCons τ x)) + volume.real A * M) := hnorm
    _ ≤ (C / R ^ 2) * (9 * Real.pi * R ^ 2 * L ^ 2 * M + 4 * Real.pi * R ^ 2 * M) :=
      mul_le_mul_of_nonneg_left (add_le_add hk ha) (div_nonneg hC (sq_nonneg R))
    _ = _ := by
      change (C / R ^ 2) * (9 * Real.pi * R ^ 2 * L ^ 2 * M + 4 * Real.pi * R ^ 2 * M) =
        C * Real.pi * (9 * L ^ 2 + 4) * M
      field_simp

end WaveEquation
