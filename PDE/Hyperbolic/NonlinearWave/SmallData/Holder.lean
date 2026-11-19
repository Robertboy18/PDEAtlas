/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Geometry.EuclideanBall
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import CAS.ExactTactic

/-!
# The spatial mass bound on a propagation ball

Jensen's inequality on the support ball gives
`volume(B)^(1-p) * |∫ f|^p ≤ ∫ |f|^p`. Factoring the Euclidean ball volume produces
the dimension-dependent radius exponent. The function need not be nonnegative.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open PDE.Analysis (unitBallVolume)

namespace WaveEquation.SmallData

variable {n : ℕ}

/-- The closed unit ball of `ℝⁿ` has real volume `unitBallVolume n`, also in dimension zero. -/
theorem volume_real_closedBall_zero_one (n : ℕ) :
    volume.real (Metric.closedBall (0 : ℝ^n) 1) = unitBallVolume n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [measureReal_def, volume_euclideanSpace_eq_dirac,
      Measure.dirac_apply_of_mem (Metric.mem_closedBall_self zero_le_one)]
    simp [unitBallVolume]
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hV : 0 ≤ unitBallVolume n := by unfold unitBallVolume; positivity
    rw [measureReal_def, EuclideanSpace.volume_closedBall (Fin n) 0 1, ENNReal.ofReal_one,
      one_pow, one_mul, Fintype.card_fin]
    exact ENNReal.toReal_ofReal hV

/-- `x ↦ |x|^p` is convex on `ℝ` for `p ≥ 1`. -/
theorem convexOn_abs_rpow {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ univ (fun x : ℝ ↦ |x| ^ p) := by
  have hn : ConvexOn ℝ univ (fun x : ℝ ↦ ‖x‖ ^ p) := by
    refine ⟨convex_univ, fun x hx y hy a b ha hb hab ↦ ?_⟩
    exact (Real.rpow_le_rpow (norm_nonneg _)
      ((convexOn_univ_norm (E := ℝ)).2 hx hy ha hb hab) (zero_le_one.trans hp)).trans
        ((convexOn_rpow hp).2 (norm_nonneg x) (norm_nonneg y) ha hb hab)
  simpa only [Real.norm_eq_abs] using hn

/-- Jensen's inequality on a ball, retaining its exact volume constant. -/
theorem ball_volume_mass_bound {f : ℝ^n → ℝ} {r p : ℝ} (hf : Continuous f) (hr : 0 < r) (hp : 1 ≤ p)
    (hs : ∀ x : ℝ^n, r < ‖x‖ → f x = 0) :
    volume.real (Metric.closedBall (0 : ℝ^n) r) ^ (1 - p) *
      |∫ x : ℝ^n, f x| ^ p ≤ ∫ x : ℝ^n, |f x| ^ p := by
  let K := Metric.closedBall (0 : ℝ^n) r
  let V := volume.real K
  have hK : IsCompact K := isCompact_closedBall _ _
  have hV : 0 < V := ENNReal.toReal_pos
    (Metric.measure_closedBall_pos volume _ hr).ne' measure_closedBall_lt_top.ne
  have hpc : Continuous (fun x : ℝ ↦ |x| ^ p) :=
    continuous_abs.rpow_const (fun _ ↦ Or.inr (zero_le_one.trans hp))
  have hj := (convexOn_abs_rpow hp).map_set_average_le
    (μ := volume) (t := K) (f := f) hpc.continuousOn isClosed_univ
    (Metric.measure_closedBall_pos volume _ hr).ne' measure_closedBall_lt_top.ne
    (Eventually.of_forall fun _ ↦ mem_univ _) (hf.continuousOn.integrableOn_compact hK)
    ((hpc.comp hf).continuousOn.integrableOn_compact hK)
  have hfzero (x : ℝ^n) (hx : x ∉ K) : f x = 0 :=
    hs x (by simpa only [K, Metric.mem_closedBall, dist_zero_right, not_le] using hx)
  have hpzero (x : ℝ^n) (hx : x ∉ K) : |f x| ^ p = 0 := by
    rw [hfzero x hx, abs_zero, Real.zero_rpow (ne_of_gt (zero_lt_one.trans_le hp))]
  simp only [setAverage_eq, smul_eq_mul] at hj
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hfzero,
    setIntegral_eq_integral_of_forall_compl_eq_zero hpzero] at hj
  have hscaled := mul_le_mul_of_nonneg_left hj hV.le
  have hid (A : ℝ) : V * |V⁻¹ * A| ^ p = V ^ (1 - p) * |A| ^ p := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hV), Real.mul_rpow (inv_nonneg.mpr hV.le) (abs_nonneg _),
      Real.inv_rpow hV.le, Real.rpow_sub hV, Real.rpow_one]
    ring
  change V * |V⁻¹ * ∫ x : ℝ^n, f x| ^ p ≤ V * (V⁻¹ * ∫ x : ℝ^n, |f x| ^ p) at hscaled
  simpa only [hid, mul_inv_cancel_left₀ hV.ne'] using hscaled

/-- The same bound with the radius power factored out of the ball volume. -/
theorem radius_mass_bound {f : ℝ^n → ℝ} {r p : ℝ} (hf : Continuous f) (hr : 0 < r) (hp : 1 ≤ p)
    (hs : ∀ x : ℝ^n, r < ‖x‖ → f x = 0) :
    unitBallVolume n ^ (1 - p) * r ^ (-(n : ℝ) * (p - 1)) *
      |∫ x : ℝ^n, f x| ^ p ≤ ∫ x : ℝ^n, |f x| ^ p := by
  have hv : volume.real (Metric.closedBall (0 : ℝ^n) r) =
      r ^ n * unitBallVolume n := by
    simpa only [volume_real_closedBall_zero_one, finrank_euclideanSpace, Fintype.card_fin] using
      Measure.addHaar_real_closedBall' volume (0 : ℝ^n) hr.le
  have hpower : volume.real (Metric.closedBall (0 : ℝ^n) r) ^ (1 - p) =
      unitBallVolume n ^ (1 - p) * r ^ (-(n : ℝ) * (p - 1)) := by
    rw [hv, Real.mul_rpow (pow_nonneg hr.le n) (by unfold unitBallVolume; positivity),
      ← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    rw [show (n : ℝ) * (1 - p) = -(n : ℝ) * (p - 1) by cas, mul_comm]
  rw [← hpower]
  exact ball_volume_mass_bound hf hr hp hs

end WaveEquation.SmallData
