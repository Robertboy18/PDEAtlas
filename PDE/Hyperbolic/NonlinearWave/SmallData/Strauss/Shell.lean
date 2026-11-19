/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Holder
import Mathlib.Analysis.Convex.Integral
import CAS.ExactTactic

/-!
# Jensen's inequality on an outgoing shell

A three-dimensional shell of fixed width has volume of order `t²`.
Combining its volume with Jensen keeps the improved growth mechanism
separate from the coarser support-ball mass inequality.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open PDE.Analysis (unitBallVolume)

namespace WaveEquation.SmallData

variable {n : ℕ}

/-- Jensen's inequality on a compact support set, with its positive volume. -/
theorem compact_volume_mass_bound {f : ℝ^n → ℝ} {K : Set (ℝ^n)} {p : ℝ} (hf : Continuous f)
    (hK : IsCompact K) (hV : 0 < volume.real K) (hp : 1 ≤ p) (hs : ∀ x : ℝ^n, x ∉ K → f x = 0) :
    volume.real K ^ (1 - p) * |∫ x : ℝ^n, f x| ^ p ≤ ∫ x : ℝ^n, |f x| ^ p := by
  let V := volume.real K
  have hKzero : volume K ≠ 0 := (ENNReal.toReal_pos_iff.mp hV).1.ne'
  have hKtop : volume K ≠ ⊤ := (ENNReal.toReal_pos_iff.mp hV).2.ne
  have hpc : Continuous (fun x : ℝ ↦ |x| ^ p) :=
    continuous_abs.rpow_const (fun _ ↦ Or.inr (zero_le_one.trans hp))
  have hj := (convexOn_abs_rpow hp).map_set_average_le
    (μ := volume) (t := K) (f := f) hpc.continuousOn isClosed_univ hKzero hKtop
    (Eventually.of_forall fun _ ↦ mem_univ _) (hf.continuousOn.integrableOn_compact hK)
    ((hpc.comp hf).continuousOn.integrableOn_compact hK)
  have hfzero (x : ℝ^n) (hx : x ∉ K) : f x = 0 := hs x hx
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
  have hV0 : V ≠ 0 := hV.ne'
  simpa only [hid, mul_inv_cancel_left₀ hV0] using hscaled

/-- The closed outgoing shell containing the free wave of radius-`R` data. -/
def outgoingShell (R t : ℝ) : Set (ℝ^3) :=
  Metric.closedBall 0 (t + R) \ Metric.ball 0 (t - R)

/-- The outgoing shell is compact. -/
theorem isCompact_outgoingShell (R t : ℝ) : IsCompact (outgoingShell R t) :=
  (isCompact_closedBall _ _).diff Metric.isOpen_ball

/-- The exact shell volume is the difference of its two ball volumes. -/
theorem volume_outgoingShell {R t : ℝ} (hR : 0 ≤ R) (ht : R ≤ t) :
    volume.real (outgoingShell R t) = ((t + R) ^ 3 - (t - R) ^ 3) * unitBallVolume 3 := by
  have hsub : Metric.ball (0 : ℝ^3) (t - R) ⊆ Metric.closedBall 0 (t + R) := by
    intro x hx
    apply Metric.mem_closedBall.mpr
    exact (Metric.mem_ball.mp hx).le.trans (by linarith)
  rw [outgoingShell, measureReal_sdiff hsub measurableSet_ball measure_closedBall_lt_top.ne,
    ← Measure.addHaar_real_closedBall_eq_addHaar_real_ball volume (0 : ℝ^3) (t - R)]
  have hv (r : ℝ) (hr : 0 ≤ r) : volume.real (Metric.closedBall (0 : ℝ^3) r) =
      r ^ 3 * unitBallVolume 3 := by
    simpa only [volume_real_closedBall_zero_one, finrank_euclideanSpace, Fintype.card_fin] using
      Measure.addHaar_real_closedBall' volume (0 : ℝ^3) hr
  rw [hv _ (by linarith), hv _ (by linarith)]
  ring

/-- The positive shell volume is at most `8 R |B₁| t²` for `t≥R>0`. -/
theorem volume_outgoingShell_bounds {R t : ℝ} (hR : 0 < R) (ht : R ≤ t) :
    0 < volume.real (outgoingShell R t) ∧
      volume.real (outgoingShell R t) ≤ 8 * R * unitBallVolume 3 * t ^ 2 := by
  rw [volume_outgoingShell hR.le ht]
  have hid : (t + R) ^ 3 - (t - R) ^ 3 = 6 * t ^ 2 * R + 2 * R ^ 3 := by cas
  rw [hid]
  constructor
  · exact mul_pos (by positivity) (by unfold unitBallVolume; positivity)
  · have hr2 : R ^ 2 ≤ t ^ 2 := sq_le_sq₀ hR.le (hR.le.trans ht) |>.mpr ht
    have ha : 6 * t ^ 2 * R + 2 * R ^ 3 ≤ 8 * R * t ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right ha (show 0 ≤ unitBallVolume 3 by
      unfold unitBallVolume; positivity)]

/-- A signed comparison field controls the power integral through its positive part. -/
theorem compact_volume_mass_bound_of_le {n : ℕ} {f g : ℝ^n → ℝ} {K : Set (ℝ^n)} {p : ℝ}
    (hf : Continuous f) (hK : IsCompact K) (hV : 0 < volume.real K) (hp : 1 ≤ p)
    (hs : ∀ x, x ∉ K → f x = 0) (hm : 0 ≤ ∫ x, f x) (hg : Integrable (fun x ↦ |g x| ^ p))
    (hle : ∀ x, f x ≤ g x) :
    volume.real K ^ (1 - p) * (∫ x, f x) ^ p ≤ ∫ x, |g x| ^ p := by
  let fpos : ℝ^n → ℝ := fun x ↦ max (f x) 0
  have hc : Continuous fpos := hf.max continuous_const
  have hz : ∀ x, x ∉ K → fpos x = 0 := by
    intro x hx
    simp [fpos, hs x hx]
  have hk : HasCompactSupport fpos := HasCompactSupport.intro hK hz
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport (HasCompactSupport.intro hK hs)
  have hpi : Integrable fpos := hc.integrable_of_hasCompactSupport hk
  have hmass : (∫ x, f x) ≤ ∫ x, fpos x := integral_mono hfi hpi (fun x ↦ le_max_left _ _)
  have hmasspos : 0 ≤ ∫ x, fpos x := integral_nonneg (fun x ↦ le_max_right _ _)
  have hpower : Continuous (fun y : ℝ ↦ |y| ^ p) :=
    continuous_abs.rpow_const (fun _ ↦ Or.inr (zero_le_one.trans hp))
  have hip : Integrable (fun x ↦ |fpos x| ^ p) := (hpower.comp hc).integrable_of_hasCompactSupport
      (hk.comp_left (by simp [Real.zero_rpow (zero_lt_one.trans_le hp).ne']))
  calc
    _ ≤ volume.real K ^ (1 - p) * |∫ x, fpos x| ^ p := by
      rw [abs_of_nonneg hmasspos]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hm hmass
        (zero_le_one.trans hp)) (Real.rpow_nonneg hV.le _)
    _ ≤ ∫ x, |fpos x| ^ p := compact_volume_mass_bound hc hK hV hp hz
    _ ≤ _ := integral_mono hip hg (fun x ↦ by
      rw [abs_of_nonneg (show 0 ≤ fpos x from le_max_right _ _)]
      apply Real.rpow_le_rpow (le_max_right _ _) _ (zero_le_one.trans hp)
      exact max_le ((hle x).trans (le_abs_self _)) (abs_nonneg _))

end WaveEquation.SmallData
