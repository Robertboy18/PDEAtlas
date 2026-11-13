/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Inequality
public import PDE.Hyperbolic.NonlinearWave.SmallData.KatoCritical

/-!
# The critical mass endpoint for the power-source wave equation

The mass identity, finite-propagation ball estimate, and positive initial
mass velocity exclude a global jointly C² wave when `(n-1)*(p-1) ≤ 2`, `p>1`.
The equality case uses the newly derived logarithmic velocity growth and critical
Kato contradiction. In three dimensions this includes the quadratic source.

This is a nonexistence result for global fields with the stated support cone.
It does not construct local or maximal solutions, prove a terminal norm blowup,
or reach the larger three-dimensional Strauss range.
-/

@[expose] public noncomputable section

open MeasureTheory PDE.Common

namespace WaveEquation.SmallData

variable {n : ℕ}

/-- Global classical power-source waves are impossible in the mass range including
its critical endpoint. The solution and initial displacement may have either sign. -/
theorem not_global_cauchy_solution_of_le {u : ℝ^(n + 1) → ℝ} {h : ℝ^n → ℝ} {R p : ℝ}
    (hu : ContDiff ℝ 2 u) (hs : HasForwardSupport u R) (hR : 0 < R) (hp : 1 < p)
    (hcrit : ((n : ℝ) - 1) * (p - 1) ≤ 2)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^n, waveOperator u (timeSpaceCons t x) =
      |u (timeSpaceCons t x)| ^ p)
    (hinitial : ∀ x : ℝ^n, (∂[0] u) (timeSpaceCons 0 x) = h x) (hpositive : 0 < ∫ x : ℝ^n, h x) :
    False := by
  let H := ∫ x : ℝ^n, h x
  let F := spatialMass u
  let P := spatialMass (∂[0] u)
  let a := max 1 (R + 2 * |F 0| / H)
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨hest, hgrowth⟩ := cauchy_spatialMass_estimates hu hs hR hp hwave hinitial hpositive
  have hH : 0 < H := hpositive
  have hlinear (t : ℝ) (ht : a ≤ t) : (H / 2) * (R + t) ≤ F t := by
    have hta : R + 2 * |F 0| / H ≤ t := (le_max_right _ _).trans ht
    have hmul := mul_le_mul_of_nonneg_left hta hH.le
    have hid : H * (R + 2 * |F 0| / H) = H * R + 2 * |F 0| := by
      have hH0 := hH.ne'
      field_simp
    rw [hid] at hmul
    have hg := hgrowth t (ha.le.trans ht)
    change F 0 + H * t ≤ F t at hg
    nlinarith [neg_abs_le (F 0)]
  apply Kato.not_weighted_second_order_on_Ici_of_le
    (F := F) (P := P) (C := massCoefficient n p) (q := (n : ℝ) * (p - 1))
    (δ := H / 2) (a := a) (R := R)
    (massCoefficient_pos n p) hp (mul_nonneg (Nat.cast_nonneg n) (by linarith))
    (by nlinarith [hcrit]) (div_pos hH (by norm_num)) (add_pos hR ha)
  · exact fun t ht ↦ hasDerivAt_spatialMass (hu.of_le (by norm_num)) hs (ha.trans_le ht)
  · exact fun t ht ↦ (hasDerivAt_spatialMass_time hu hs (ha.trans_le ht)).differentiableAt
  · intro t ht
    have hd := hasDerivAt_spatialMass (hu.of_le (by norm_num)) hs (ha.trans_le ht)
    change 0 ≤ spatialMass (∂[0] u) t
    rw [← hd.deriv]
    exact (hest t (ha.trans_le ht)).2.2.le
  · exact hlinear
  · intro t ht
    have ht0 := ha.trans_le ht
    have hFpos : 0 < F t :=
      (mul_pos (div_pos hH (by norm_num)) (add_pos hR ht0)).trans_le (hlinear t ht)
    have hd := hasDerivAt_spatialMass_time_eq_source hu hs ht0 (hwave t ht0)
    rw [hd.deriv]
    have hi := (hest t ht0).2.1
    rw [(hest t ht0).1] at hi
    change massCoefficient n p * (R + t) ^ (-(n : ℝ) * (p - 1)) *
      |F t| ^ p ≤ _ at hi
    simpa only [neg_mul, abs_of_pos hFpos] using hi

/-- In three dimensions the mass argument includes the endpoint `p=2`. -/
theorem not_global_cauchy_solution_three_of_le {u : ℝ^4 → ℝ} {h : ℝ^3 → ℝ} {R p : ℝ}
    (hu : ContDiff ℝ 2 u) (hs : HasForwardSupport u R) (hR : 0 < R) (hp : 1 < p) (hp2 : p ≤ 2)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^3, waveOperator u (timeSpaceCons t x) =
      |u (timeSpaceCons t x)| ^ p)
    (hinitial : ∀ x : ℝ^3, (∂[0] u) (timeSpaceCons 0 x) = h x) (hpositive : 0 < ∫ x : ℝ^3, h x) :
    False := by
  apply not_global_cauchy_solution_of_le hu hs hR hp _ hwave hinitial hpositive
  norm_num
  linarith

/-- Three-dimensional quadratic-source waves with positive initial mass velocity
cannot persist globally with finite propagation, regardless of the positive data amplitude. -/
theorem not_global_quadratic_cauchy_solution_three {u : ℝ^4 → ℝ} {h : ℝ^3 → ℝ} {R : ℝ}
    (hu : ContDiff ℝ 2 u) (hs : HasForwardSupport u R) (hR : 0 < R)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^3, waveOperator u (timeSpaceCons t x) = u (timeSpaceCons t x) ^ 2)
    (hinitial : ∀ x : ℝ^3, (∂[0] u) (timeSpaceCons 0 x) = h x) (hpositive : 0 < ∫ x : ℝ^3, h x) :
    False := by
  apply not_global_cauchy_solution_three_of_le hu hs hR
    (p := 2) (by norm_num) le_rfl _ hinitial hpositive
  intro t ht x
  simpa only [Real.rpow_two, sq_abs] using hwave t ht x

end WaveEquation.SmallData
