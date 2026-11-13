/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.RadialDatum
import CAS.ExactTactic

/-! # Small-ball superlevels of the singular finite-energy datum -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition

/-- The unit ball has strictly positive finite real volume. -/
theorem volume_real_unitBall_pos :
    0 < volume.real (Metric.ball (0 : ℝ^3) 1) :=
  ENNReal.toReal_pos (Metric.measure_ball_pos volume _ zero_lt_one).ne' measure_ball_lt_top.ne

/-- Restriction to the unit ball preserves the exact volume of every smaller
ball with radius `s^6`. -/
theorem volume_real_restrict_unitBall_ball_pow_six {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    (volume.restrict (Metric.ball (0 : ℝ^3) 1)).real (Metric.ball 0 (s ^ 6)) =
      volume.real (Metric.ball (0 : ℝ^3) 1) * s ^ 18 := by
  have hsmall : Metric.ball (0 : ℝ^3) (s ^ 6) ⊆ Metric.ball 0 1 :=
    Metric.ball_subset_ball (pow_le_one₀ hs hs1)
  rw [measureReal_def, Measure.restrict_apply measurableSet_ball,
    inter_eq_left.mpr hsmall, volume.addHaar_ball _ (pow_nonneg hs 6)]
  simp only [finrank_euclideanSpace, Fintype.card_fin, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (s ^ 6) ^ 3)]
  rw [← pow_mul]
  exact mul_comm _ _

/-- At every nonzero point in the ball of radius `s^6`, the datum exceeds the
reaction threshold used by the shrinking-cylinder estimate. -/
theorem one_div_sq_add_one_le_singularRadialDatum {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1 / 2) {x : ℝ^3}
    (hx0 : x ≠ 0) (hx : x ∈ Metric.ball 0 (s ^ 6)) :
    1 / (2 * s ^ 2) + 1 ≤ singularRadialDatum x := by
  have hnorm : ‖x‖ ≤ s ^ 6 := (by simpa using hx : ‖x‖ < s ^ 6).le
  have hpower := Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr hx0) hnorm
    (by norm_num : -(1 / 3 : ℝ) ≤ 0)
  have hidentity : (s ^ 6) ^ (-(1 / 3 : ℝ)) = 1 / s ^ 2 := by
    cas using hs
  rw [hidentity] at hpower
  have hs2 : s ^ 2 ≤ 1 / 4 := by nlinarith
  have hlarge : 4 ≤ 1 / s ^ 2 := (le_div_iff₀ (sq_pos_of_pos hs)).mpr (by nlinarith)
  have hhalf : 1 / (2 * s ^ 2) = (1 / s ^ 2) / 2 := by cas
  rw [hhalf]
  exact (show (1 / s ^ 2) / 2 + 1 ≤ ‖x‖ ^ (-(1 / 3 : ℝ)) - 1 by linarith).trans (le_max_left _ _)

/-- The exceptional value at the origin does not affect the superlevel estimate
for volume restricted to the small ball. -/
theorem ae_one_div_sq_add_one_le_singularRadialDatum {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1 / 2) :
    ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) 1)).restrict
      (Metric.ball 0 (s ^ 6)), 1 / (2 * s ^ 2) + 1 ≤ singularRadialDatum x := by
  filter_upwards [ae_restrict_mem measurableSet_ball, (volume.ae_ne (0 : ℝ^3)).filter_mono
      (ae_mono (Measure.restrict_le_self.trans Measure.restrict_le_self))] with x hx hx0
  exact one_div_sq_add_one_le_singularRadialDatum hs hs1 hx0 hx

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition
