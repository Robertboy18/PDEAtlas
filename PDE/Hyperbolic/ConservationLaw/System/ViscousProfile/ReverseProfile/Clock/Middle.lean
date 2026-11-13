/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Clock.Density
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Pulses

import CAS.IntegrationTactic

/-!
# The middle clock obtained from the two gate pulses

The positive curvature is the weighted sum of the two gate pulses, their
reflections, and a slowly scaled positive density. Two oriented primitives
with base point zero define the clock. The pulse masses bound its slope, and
their first moments bound its value at 210. On the central interval the pulse
terms vanish and the density is one, giving an exact quadratic clock.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PDE.Analysis PDE.Analysis.ClockDensity
open scoped ContDiff Interval

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.MiddleClock

/-- The positive, even curvature of the middle clock. -/
def curvature (y : ℝ) : ℝ :=
  (qMinus y + 4 * qPlus y + qMinus (-y) + 4 * qPlus (-y)) / 100 +
    (1 / 1000000) * rho0 (y / 100)

/-- The primitive of the curvature with value zero at the origin. -/
def slope (y : ℝ) : ℝ := ∫ v in (0 : ℝ)..y, curvature v

/-- The middle clock, defined by two oriented integrals from the origin. -/
def g (y : ℝ) : ℝ := ∫ u in (0 : ℝ)..y, slope u

/-- The curvature is globally infinitely differentiable. -/
theorem contDiff_curvature : ContDiff ℝ ∞ curvature := by
  have := contDiff_qMinus; have := contDiff_qPlus; have := contDiff_rho0
  unfold curvature
  fun_prop

/-- The density term makes the curvature strictly positive everywhere. -/
theorem curvature_pos (y : ℝ) : 0 < curvature y := by
  have hq : 0 ≤ qMinus y + 4 * qPlus y + qMinus (-y) + 4 * qPlus (-y) :=
    add_nonneg (add_nonneg (add_nonneg (qMinus_nonneg y)
      (mul_nonneg (by norm_num) (qPlus_nonneg y))) (qMinus_nonneg (-y)))
      (mul_nonneg (by norm_num) (qPlus_nonneg (-y)))
  exact add_pos_of_nonneg_of_pos (div_nonneg hq (by norm_num))
    (mul_pos (by norm_num) (rho0_pos (y / 100)))

/-- Reflection leaves the curvature unchanged. -/
theorem curvature_neg (y : ℝ) : curvature (-y) = curvature y := by
  unfold curvature
  simp only [neg_neg, neg_div, rho0_neg]
  ring

/-- Integration preserves the global smoothness of the curvature. -/
theorem contDiff_slope : ContDiff ℝ ∞ slope :=
  (contDiff_intervalIntegral_of_contDiff (n := ⊤) contDiff_curvature 0).of_le (by simp)

/-- The middle clock is globally infinitely differentiable. -/
theorem contDiff_g : ContDiff ℝ ∞ g :=
  (contDiff_intervalIntegral_of_contDiff (n := ⊤) contDiff_slope 0).of_le (by simp)

/-- The derivative of the first primitive is the prescribed curvature. -/
theorem hasDerivAt_slope (y : ℝ) : HasDerivAt slope (curvature y) y :=
  (contDiff_curvature.continuous.integral_hasStrictDerivAt 0 y).hasDerivAt

/-- The ordinary derivative of the first primitive is the curvature. -/
theorem deriv_slope (y : ℝ) : deriv slope y = curvature y :=
  (hasDerivAt_slope y).deriv

/-- The derivative of the clock is its first primitive. -/
theorem hasDerivAt_g (y : ℝ) : HasDerivAt g (slope y) y :=
  (contDiff_slope.continuous.integral_hasStrictDerivAt 0 y).hasDerivAt

/-- The ordinary derivative of the clock is its first primitive. -/
theorem deriv_g (y : ℝ) : deriv g y = slope y := (hasDerivAt_g y).deriv

/-- The clock has exactly the prescribed second derivative. -/
theorem deriv_deriv_g (y : ℝ) : deriv (deriv g) y = curvature y := by
  rw [show deriv g = slope from funext deriv_g]
  exact deriv_slope y

/-- The first primitive vanishes at the base point. -/
theorem slope_zero : slope 0 = 0 := by simp only [slope, intervalIntegral.integral_same]

/-- The clock vanishes at the base point. -/
theorem g_zero : g 0 = 0 := by simp only [g, intervalIntegral.integral_same]

/-- The clock has zero first derivative at the origin. -/
theorem deriv_g_zero : deriv g 0 = 0 := by rw [deriv_g, slope_zero]

/-- The oriented primitive of the even curvature is odd. -/
theorem slope_neg (y : ℝ) : slope (-y) = -slope y := by
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := -y) curvature
  simp only [curvature_neg, neg_neg, neg_zero] at h
  rw [slope, slope, h, intervalIntegral.integral_symm]

/-- The clock is even, with the orientation of both primitives taken into account. -/
theorem g_neg (y : ℝ) : g (-y) = g y := by
  change (∫ s in (0 : ℝ)..(-y), slope s) = ∫ s in (0 : ℝ)..y, slope s
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := -y) slope
  simp only [slope_neg, intervalIntegral.integral_neg, neg_neg, neg_zero] at h
  rw [intervalIntegral.integral_symm 0 y] at h
  exact neg_inj.mp h

private theorem qMinus_eq_zero_of_le {y : ℝ} (hy : y ≤ 100) : qMinus y = 0 :=
  Function.notMem_support.mp fun hs ↦ (support_qMinus.subset hs).1.not_ge hy

private theorem qPlus_eq_zero_of_le {y : ℝ} (hy : y ≤ 100) : qPlus y = 0 :=
  Function.notMem_support.mp fun hs ↦ by linarith [(support_qPlus.subset hs).1]

private theorem curvature_of_nonneg {y : ℝ} (hy : 0 ≤ y) :
    curvature y = (qMinus y + 4 * qPlus y) / 100 + (1 / 1000000) * rho0 (y / 100) := by
  rw [curvature, qMinus_eq_zero_of_le (y := -y) (by linarith),
    qPlus_eq_zero_of_le (y := -y) (by linarith)]
  ring

private theorem integral_pulse_le_one {q : ℝ → ℝ} (hq : Integrable q)
    (hn : ∀ y, 0 ≤ q y) (hm : (∫ y : ℝ, q y) = 1) {y : ℝ} (hy : 0 ≤ y) :
    (∫ s in (0 : ℝ)..y, q s) ≤ 1 := by
  rw [intervalIntegral.integral_of_le hy]
  exact (setIntegral_le_integral hq (Filter.Eventually.of_forall hn)).trans_eq hm

private theorem integral_scaled_rho0_le {y : ℝ} (hy : 0 ≤ y) :
    (∫ s in (0 : ℝ)..y, rho0 (s / 100)) ≤ 250 := by
  have hi : (∫ s in (0 : ℝ)..(y / 100), rho0 s) ≤ 5 / 2 := by
    rw [intervalIntegral.integral_of_le (div_nonneg hy (by norm_num))]
    exact (setIntegral_mono_set integrable_rho0.integrableOn
      (Filter.Eventually.of_forall fun s ↦ (rho0_pos s).le)
      (Filter.Eventually.of_forall fun s hs ↦ hs.1)).trans integral_Ioi_zero_rho0_le
  have h := intervalIntegral.integral_comp_div (a := 0) (b := y) rho0 (c := 100) (by norm_num)
  simp only [zero_div, smul_eq_mul] at h
  linarith

private theorem slope_eq_of_nonneg {y : ℝ} (hy : 0 ≤ y) :
    slope y = ((∫ s in (0 : ℝ)..y, qMinus s) + 4 * ∫ s in (0 : ℝ)..y, qPlus s) / 100 +
      (1 / 1000000) * ∫ s in (0 : ℝ)..y, rho0 (s / 100) := by
  have := contDiff_qMinus.continuous; have := contDiff_qPlus.continuous
  have := contDiff_rho0.continuous
  rw [slope, intervalIntegral.integral_congr fun s hs ↦
      curvature_of_nonneg ((uIcc_of_le hy).subset hs).1,
    intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) 0 y)
      (Continuous.intervalIntegrable (by fun_prop) 0 y), intervalIntegral.integral_div,
    intervalIntegral.integral_add (f := qMinus) (g := fun s : ℝ ↦ 4 * qPlus s)
      (Continuous.intervalIntegrable (by fun_prop) 0 y)
      (Continuous.intervalIntegrable (by fun_prop) 0 y)]
  simp only [intervalIntegral.integral_const_mul]

private theorem abs_slope_le_of_nonneg {y : ℝ} (hy : 0 ≤ y) :
    |slope y| ≤ 201 / 4000 := by
  rw [abs_of_nonneg (show 0 ≤ slope y from
    intervalIntegral.integral_nonneg_of_forall hy fun s ↦ (curvature_pos s).le),
    slope_eq_of_nonneg hy]
  linarith [integral_pulse_le_one integrable_qMinus qMinus_nonneg integral_qMinus hy,
    integral_pulse_le_one integrable_qPlus qPlus_nonneg integral_qPlus hy,
    integral_scaled_rho0_le hy]

/-- The pulse masses and the density half-line mass give a global slope bound. -/
theorem abs_deriv_g_le (y : ℝ) : |deriv g y| ≤ 201 / 4000 := by
  rw [deriv_g]
  rcases le_total 0 y with hy | hy
  · exact abs_slope_le_of_nonneg hy
  · simpa only [slope_neg, abs_neg] using abs_slope_le_of_nonneg (neg_nonneg.mpr hy)

/-- Positive curvature makes the clock nondecreasing on the nonnegative half-line. -/
theorem monotoneOn_g_nonneg : MonotoneOn g (Ici 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) contDiff_g.continuous.continuousOn
    (contDiff_g.differentiable (by simp)).differentiableOn fun s hs ↦ ?_
  rw [deriv_g]
  exact intervalIntegral.integral_nonneg_of_forall (interior_subset hs) fun v ↦
    (curvature_pos v).le

/-- The even clock has its global minimum, zero, at the origin. -/
theorem g_nonneg (y : ℝ) : 0 ≤ g y := by
  have hpos {s : ℝ} (hs : 0 ≤ s) : 0 ≤ g s := by
    simpa only [g_zero] using monotoneOn_g_nonneg (le_refl 0) hs hs
  rcases le_total 0 y with hy | hy
  · exact hpos hy
  · simpa only [g_neg] using hpos (neg_nonneg.mpr hy)

/-- The global slope bound gives a linear upper bound on the nonnegative half-line. -/
theorem g_le_mul {y : ℝ} (hy : 0 ≤ y) : g y ≤ (201 / 4000 : ℝ) * y := by
  simpa only [g_zero, sub_zero] using image_sub_le_mul_sub_of_deriv_le
    (fun s ↦ (hasDerivAt_g s).differentiableAt)
    (fun s ↦ (abs_le.mp (abs_deriv_g_le s)).2) (x := 0) (y := y) hy

/-- The primitive is globally Lipschitz with the constant supplied by the pulse masses. -/
theorem lipschitzWith_g :
    LipschitzWith (201 / 4000) g := by
  refine lipschitzWith_of_nnnorm_deriv_le (fun s ↦ (hasDerivAt_g s).differentiableAt) fun s ↦ ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs]
  exact abs_deriv_g_le s

/-- All pulse terms vanish on the central interval and the density is one there. -/
theorem curvature_of_abs_le {y : ℝ} (hy : |y| ≤ 100) :
    curvature y = 1 / 1000000 := by
  have hbounds := abs_le.mp hy
  rw [curvature, qMinus_eq_zero_of_le hbounds.2, qPlus_eq_zero_of_le hbounds.2,
    qMinus_eq_zero_of_le (y := -y) (by linarith [hbounds.1]),
    qPlus_eq_zero_of_le (y := -y) (by linarith [hbounds.1]),
    rho0_eq_one_of_abs_le_one (abs_le.mpr ⟨by linarith, by linarith⟩)]
  norm_num

private theorem abs_le_of_mem_uIcc {y s : ℝ} (hy : |y| ≤ 100)
    (hs : s ∈ uIcc (0 : ℝ) y) : |s| ≤ 100 :=
  abs_le.mpr (ordConnected_Icc.uIcc_subset
    (show (0 : ℝ) ∈ Icc (-100 : ℝ) 100 by norm_num) (abs_le.mp hy) hs)

/-- The first primitive is exactly linear on the central interval. -/
theorem slope_of_abs_le {y : ℝ} (hy : |y| ≤ 100) :
    slope y = (1 / 1000000) * y := by
  rw [slope, intervalIntegral.integral_congr fun s hs ↦
    curvature_of_abs_le (abs_le_of_mem_uIcc hy hs)]
  cas

/-- On the entire central interval the clock is the exact quadratic with curvature `10⁻⁶`. -/
theorem g_of_abs_le {y : ℝ} (hy : |y| ≤ 100) :
    g y = (1 / 1000000) * y ^ 2 / 2 := by
  rw [g, intervalIntegral.integral_congr fun s hs ↦ slope_of_abs_le (abs_le_of_mem_uIcc hy hs)]
  cas

/-- Integration by parts gives the weighted-curvature formula for both orientations. -/
theorem g_eq_weighted_integral (y : ℝ) :
    g y = ∫ s in (0 : ℝ)..y, (y - s) * curvature s := by
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := 0) (b := y) (u := fun s : ℝ ↦ s) (v := slope)
    (u' := fun _ : ℝ ↦ (1 : ℝ)) (v' := curvature)
    (fun s _ ↦ hasDerivAt_id s) (fun s _ ↦ hasDerivAt_slope s)
    (continuous_const.intervalIntegrable 0 y)
    (contDiff_curvature.continuous.intervalIntegrable 0 y)
  simp only [sub_mul]
  rw [intervalIntegral.integral_sub
    (f := fun s : ℝ ↦ y * curvature s) (g := fun s : ℝ ↦ s * curvature s)
    ((continuous_const.mul contDiff_curvature.continuous).intervalIntegrable 0 y)
    ((continuous_id.mul contDiff_curvature.continuous).intervalIntegrable 0 y),
    intervalIntegral.integral_const_mul, hibp]
  simp only [g, slope, zero_mul, sub_zero, one_mul]
  ring

private theorem weighted_pulse_integral {q : ℝ → ℝ} (hs : Function.support q ⊆ Ioc (0 : ℝ) 210)
    (hq : Integrable q) (hm : Integrable (fun s : ℝ ↦ s * q s)) :
    (∫ s in (0 : ℝ)..210, (210 - s) * q s) = 210 * (∫ s : ℝ, q s) - ∫ s : ℝ, s * q s := by
  rw [intervalIntegral.integral_eq_integral_of_support_subset (f := fun s ↦ (210 - s) * q s)
    fun s hs' ↦ hs (mul_ne_zero_iff.mp hs').2]
  simp_rw [sub_mul]
  rw [integral_sub (hq.const_mul 210) hm, integral_const_mul]

/-- Pulse first moments and the pointwise density bound control the clock at 210. -/
theorem g_210_le : g 210 ≤ 27941 / 20000 := by
  have hm : (∫ s in (0 : ℝ)..210, (210 - s) * qMinus s) = 215 / 2 := by
    rw [weighted_pulse_integral (q := qMinus)
      (support_qMinus.trans_subset fun s hs ↦ ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      integrable_qMinus integrable_mul_qMinus, integral_qMinus, integral_mul_qMinus]
    norm_num
  have hp : (∫ s in (0 : ℝ)..210, (210 - s) * qPlus s) = 15 / 2 := by
    rw [weighted_pulse_integral (q := qPlus)
      (support_qPlus.trans_subset fun s hs ↦ ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      integrable_qPlus integrable_mul_qPlus, integral_qPlus, integral_mul_qPlus]
    norm_num
  have := contDiff_qMinus.continuous; have := contDiff_qPlus.continuous
  have := contDiff_rho0.continuous
  have hr : (∫ s in (0 : ℝ)..210, (210 - s) * rho0 (s / 100)) ≤ 22050 := by
    refine (intervalIntegral.integral_mono_on (by norm_num)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _) fun s hs ↦
        mul_le_of_le_one_right (sub_nonneg.mpr hs.2) (rho0_le_one (s / 100))).trans_eq ?_
    cas
  rw [g_eq_weighted_integral, intervalIntegral.integral_congr (g := fun s ↦
      ((210 - s) * qMinus s + 4 * ((210 - s) * qPlus s)) / 100 +
        1 / 1000000 * ((210 - s) * rho0 (s / 100))) fun s hs ↦ by
      rw [curvature_of_nonneg ((uIcc_of_le (by norm_num)).subset hs).1]
      ring,
    intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_div,
    intervalIntegral.integral_add (f := fun s ↦ (210 - s) * qMinus s)
      (g := fun s ↦ 4 * ((210 - s) * qPlus s)) (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [intervalIntegral.integral_const_mul, hm, hp]
  linarith

/-- The middle clock at 210 is strictly below `1.4`. -/
theorem g_210_lt : g 210 < 7 / 5 := lt_of_le_of_lt g_210_le (by norm_num)

end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.MiddleClock
