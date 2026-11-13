/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.Continuity.Barrier.Calculus

/-!
# Quantitative angular barrier estimates

For the inward unit normal `N`, the angular variable is `⟪N,x⟫ / ‖x‖`. A C¹ boundary
places nearby interior points in `t ≥ -δ`. Choosing `a = 1/(32n)` and `δ = 1/(8n)`
makes the angular power barrier strictly superharmonic, including in dimension two.
The constants below are uniform and leave room in the differential inequality.
-/

@[expose] public noncomputable section

namespace PDE.Elliptic.BoundaryContinuity

open scoped InnerProductSpace

variable {n : ℕ}

private theorem angular_profile_bounds {t : ℝ} (ht : |t| ≤ 1) :
    3 / 4 ≤ 2 + t - t ^ 2 / 4 ∧ 2 + t - t ^ 2 / 4 ≤ 3 := by
  have hsq : t ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one t).mpr ht
  constructor <;> nlinarith [(abs_le.mp ht).1, (abs_le.mp ht).2, sq_nonneg t]

/-- The polynomial multiplying the radial factor is uniformly negative on the enlarged
inward hemisphere. The hypotheses isolate the two smallness choices used below. -/
theorem angular_laplacian_coefficient_le
    {N a δ t : ℝ} (hN : 2 ≤ N) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (haN : a * N ≤ 1 / 32) (hδ1 : δ ≤ 1 / 16)
    (hδN : δ * N ≤ 1 / 8) (ht0 : -δ ≤ t) (ht1 : t ≤ 1) :
    a * (a + N - 2) * (2 + t - t ^ 2 / 4) -
      1 / 2 - (N - 1) * t + N / 2 * t ^ 2 ≤ -1 / 4 := by
  have hTabs : |t| ≤ 1 := abs_le.mpr ⟨by linarith, ht1⟩
  have hprofile := angular_profile_bounds hTabs
  have hA0 : 0 ≤ a * (a + N - 2) := mul_nonneg ha (by linarith)
  have hA1 : a * (a + N - 2) ≤ 1 / 32 := by
    have := mul_le_mul_of_nonneg_left (show a + N - 2 ≤ N by linarith) ha
    linarith
  have hfirst : a * (a + N - 2) * (2 + t - t ^ 2 / 4) ≤ 3 / 32 := by
    have := mul_le_mul_of_nonneg_left hprofile.2 hA0
    linarith
  rcases le_total 0 t with ht | ht
  · have ht2 : t ^ 2 ≤ t := by nlinarith
    have hNt2 := mul_le_mul_of_nonneg_left ht2 (show 0 ≤ N by linarith)
    have hNt := mul_nonneg (show 0 ≤ N - 2 by linarith) ht
    nlinarith
  · have hNt : N * (-t) ≤ 1 / 8 := by
      have := mul_le_mul_of_nonneg_left (show -t ≤ δ by linarith)
        (show 0 ≤ N by linarith)
      nlinarith
    have htδ : -t ≤ 1 / 16 := by linarith
    have hNtt : N * t ^ 2 ≤ 1 / 128 := by
      have hmul := mul_le_mul hNt htδ (by linarith : 0 ≤ -t) (by norm_num : (0 : ℝ) ≤ 1 / 8)
      nlinarith
    nlinarith

/-- The barrier is its angular profile times the positive radial power. -/
theorem angularPowerBarrier_eq_profile (a : ℝ) (N : ℝ^n) {x : ℝ^n} (hx : x ≠ 0) :
    angularPowerBarrier a N x =
      ‖x‖ ^ a * (2 + inner ℝ N x / ‖x‖ - (inner ℝ N x / ‖x‖) ^ 2 / 4) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  unfold angularPowerBarrier
  rw [Real.rpow_sub hr, Real.rpow_one, Real.rpow_sub hr, Real.rpow_two]
  field_simp

/-- Two-sided positive bounds for the barrier on every ray, not just in the inward cone. -/
theorem angularPowerBarrier_bounds (a : ℝ) {N x : ℝ^n} (hN : ‖N‖ = 1) (hx : x ≠ 0) :
    (3 / 4) * ‖x‖ ^ a ≤ angularPowerBarrier a N x ∧
      angularPowerBarrier a N x ≤ 3 * ‖x‖ ^ a := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have ht : |inner ℝ N x / ‖x‖| ≤ 1 := by
    rw [abs_div, abs_of_pos hr, div_le_one hr]
    simpa [hN] using abs_real_inner_le_norm N x
  rw [angularPowerBarrier_eq_profile a N hx]
  have hprofile := angular_profile_bounds ht
  constructor
  · simpa [mul_comm] using
      mul_le_mul_of_nonneg_left hprofile.1 (Real.rpow_nonneg hr.le a)
  · simpa [mul_comm] using
      mul_le_mul_of_nonneg_left hprofile.2 (Real.rpow_nonneg hr.le a)

/-- Angular form of the Laplacian. -/
theorem laplacian_angularPowerBarrier_eq_profile (a : ℝ)
    {N x : ℝ^n} (hN : ‖N‖ = 1) (hx : x ≠ 0) :
    laplacian (angularPowerBarrier a N) x =
      ‖x‖ ^ (a - 2) *
        (a * (a + (n : ℝ) - 2) *
          (2 + inner ℝ N x / ‖x‖ - (inner ℝ N x / ‖x‖) ^ 2 / 4) -
          1 / 2 - ((n : ℝ) - 1) * (inner ℝ N x / ‖x‖) +
          (n : ℝ) / 2 * (inner ℝ N x / ‖x‖) ^ 2) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h3 : ‖x‖ ^ (a - 3) = ‖x‖ ^ (a - 2) / ‖x‖ := by
    rw [show a - 3 = (a - 2) - 1 by ring,
      Real.rpow_sub hr (a - 2) 1, Real.rpow_one]
  have h4 : ‖x‖ ^ (a - 4) = ‖x‖ ^ (a - 2) / ‖x‖ ^ 2 := by
    rw [show a - 4 = (a - 2) - 2 by ring,
      Real.rpow_sub hr (a - 2) 2, Real.rpow_two]
  rw [laplacian_angularPowerBarrier a N hx, hN]
  rw [h3, h4]
  field_simp
  ring

/-- An explicit strictly superharmonic barrier in every dimension at least two. -/
theorem laplacian_angularPowerBarrier_le (hn : 2 ≤ n)
    {N x : ℝ^n} (hN : ‖N‖ = 1) (hx : x ≠ 0)
    (hcone : -(1 / (8 * (n : ℝ))) * ‖x‖ ≤ inner ℝ N x) :
    laplacian (angularPowerBarrier (1 / (32 * (n : ℝ))) N) x ≤
      -(1 / 4) * ‖x‖ ^ (1 / (32 * (n : ℝ)) - 2) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hcoef := angular_laplacian_coefficient_le (N := (n : ℝ))
    (a := 1 / (32 * (n : ℝ))) (δ := 1 / (8 * (n : ℝ)))
    (t := inner ℝ N x / ‖x‖) hnR
    (by positivity) (by rw [div_le_one (by positivity)]; linarith)
    (by field_simp; norm_num)
    (by rw [div_le_iff₀ (by positivity)]; linarith)
    (by field_simp; norm_num)
    ((le_div_iff₀ hr).mpr hcone)
    ((div_le_one hr).mpr (by simpa [hN] using real_inner_le_norm N x))
  rw [laplacian_angularPowerBarrier_eq_profile _ hN hx]
  simpa only [neg_div, mul_comm] using
    mul_le_mul_of_nonneg_left hcoef
      (Real.rpow_nonneg hr.le (1 / (32 * (n : ℝ)) - 2))

end PDE.Elliptic.BoundaryContinuity
