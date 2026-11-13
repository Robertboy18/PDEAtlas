/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Pulses

import CAS.ExactTactic

/-!
# The scalar gate cutoff defined by the pulse primitive

The difference of the two translated normalized transitions is integrated once
more to define the cutoff. Its lower plateau follows from the pulse support.
Integration by parts, using the means of the two pulses, proves
that the transition difference has integral 100 beyond its support. This gives
the upper plateau.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PDE.Analysis PDE.Analysis.NormalizedPulse
open scoped ContDiff Interval

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile

/-- The difference of the cumulative masses of the two translated pulses. -/
def transitionGap (y : ℝ) : ℝ :=
  transition ((y - 100) / 5) - transition ((y - 200) / 5)

/-- The cutoff obtained by integrating the normalized transition difference. -/
def cutoff (y : ℝ) : ℝ := 1 - (1 / 100) * ∫ s in (0 : ℝ)..y, transitionGap s

/-- The transition difference is globally smooth. -/
theorem contDiff_transitionGap : ContDiff ℝ ∞ transitionGap := by
  change ContDiff ℝ ∞ (fun y : ℝ ↦ transition ((y - 100) / 5) - transition ((y - 200) / 5))
  exact (contDiff_transition.comp ((contDiff_id.sub contDiff_const).div_const 5)).sub
    (contDiff_transition.comp ((contDiff_id.sub contDiff_const).div_const 5))

private theorem hasDerivAt_shifted_transition (a y : ℝ) :
    HasDerivAt (fun s : ℝ ↦ transition ((s - a) / 5)) (density ((y - a) / 5) / 5) y := by
  have ha : HasDerivAt (fun s : ℝ ↦ (s - a) / 5) ((1 : ℝ) / 5) y := by
    cas
  simpa only [div_eq_mul_inv, one_mul, Function.comp_def] using
    (hasDerivAt_transition ((y - a) / 5)).comp y ha

/-- The derivative of the transition difference is the first pulse minus the second. -/
theorem hasDerivAt_transitionGap (y : ℝ) :
    HasDerivAt transitionGap (qMinus y - qPlus y) y :=
  (hasDerivAt_shifted_transition 100 y).sub (hasDerivAt_shifted_transition 200 y)

/-- The transition difference is zero on the half-line ending at 100. -/
theorem transitionGap_of_le {y : ℝ} (hy : y ≤ 100) : transitionGap y = 0 := by
  have hm : transition ((y - 100) / 5) = 0 := transition_of_nonpos (by linarith)
  have hp : transition ((y - 200) / 5) = 0 := transition_of_nonpos (by linarith)
  rw [transitionGap, hm, hp, sub_self]

/-- The transition difference is zero on the half-line starting at 205. -/
theorem transitionGap_of_ge {y : ℝ} (hy : 205 ≤ y) : transitionGap y = 0 := by
  have hm : transition ((y - 100) / 5) = 1 := transition_of_one_le (by linarith)
  have hp : transition ((y - 200) / 5) = 1 := transition_of_one_le (by linarith)
  rw [transitionGap, hm, hp, sub_self]

/-- Separation of the pulse supports makes their cumulative difference nonnegative. -/
theorem transitionGap_nonneg (y : ℝ) : 0 ≤ transitionGap y := by
  by_cases hy : y ≤ 200
  · have hp : transition ((y - 200) / 5) = 0 := transition_of_nonpos (by linarith)
    rw [transitionGap, hp, sub_zero]
    exact transition_nonneg _
  · have hm : transition ((y - 100) / 5) = 1 := transition_of_one_le (by linarith)
    rw [transitionGap, hm]
    exact sub_nonneg.mpr (transition_le_one _)

/-- The cumulative difference is bounded above by one unit of mass. -/
theorem transitionGap_le_one (y : ℝ) : transitionGap y ≤ 1 := by
  have hm := transition_le_one ((y - 100) / 5)
  have hp := transition_nonneg ((y - 200) / 5)
  dsimp [transitionGap]
  linarith

/-- The cutoff is globally infinitely differentiable. -/
theorem contDiff_cutoff : ContDiff ℝ ∞ cutoff := by
  have hi : ContDiff ℝ ∞ (fun y : ℝ ↦ ∫ s in (0 : ℝ)..y, transitionGap s) :=
    (contDiff_intervalIntegral_of_contDiff (n := ⊤) contDiff_transitionGap 0).of_le (by simp)
  change ContDiff ℝ ∞ (fun y : ℝ ↦ 1 - (1 / 100) * ∫ s in (0 : ℝ)..y, transitionGap s)
  exact contDiff_const.sub (contDiff_const.mul hi)

/-- The derivative of the cutoff is minus the transition difference divided by 100. -/
theorem hasDerivAt_cutoff (y : ℝ) :
    HasDerivAt cutoff (-transitionGap y / 100) y := by
  have hi := (contDiff_transitionGap.continuous.integral_hasStrictDerivAt 0 y).hasDerivAt
  change HasDerivAt (fun t : ℝ ↦ 1 - (1 / 100) * ∫ s in (0 : ℝ)..t, transitionGap s)
    (-transitionGap y / 100) y
  convert (hi.const_mul ((1 : ℝ) / 100)).const_sub 1 using 1
  cas

/-- The ordinary first derivative has the formula given by the transitions. -/
theorem deriv_cutoff (y : ℝ) : deriv cutoff y = -transitionGap y / 100 :=
  (hasDerivAt_cutoff y).deriv

/-- The derivative of the first derivative is the signed pulse difference divided by 100. -/
theorem hasDerivAt_deriv_cutoff (y : ℝ) :
    HasDerivAt (deriv cutoff) ((qPlus y - qMinus y) / 100) y := by
  have heq : deriv cutoff = fun s : ℝ ↦ -transitionGap s / 100 := funext deriv_cutoff
  rw [heq]
  convert (hasDerivAt_transitionGap y).neg.div_const 100 using 1
  cas

/-- The ordinary second derivative is exactly `(qPlus - qMinus) / 100`. -/
theorem deriv_deriv_cutoff (y : ℝ) :
    deriv (deriv cutoff) y = (qPlus y - qMinus y) / 100 :=
  (hasDerivAt_deriv_cutoff y).deriv

/-- The cutoff slope is bounded below by `-1 / 100`. -/
theorem neg_one_div_le_deriv_cutoff (y : ℝ) : -(1 : ℝ) / 100 ≤ deriv cutoff y := by
  rw [deriv_cutoff]
  have h := transitionGap_le_one y
  linarith

/-- The cutoff slope is nonpositive everywhere. -/
theorem deriv_cutoff_nonpos (y : ℝ) : deriv cutoff y ≤ 0 := by
  rw [deriv_cutoff]
  have h := transitionGap_nonneg y
  linarith

/-- The integral defining the cutoff is zero at and below the lower pulse support. -/
theorem integral_transitionGap_of_le {y : ℝ} (hy : y ≤ 100) :
    (∫ s in (0 : ℝ)..y, transitionGap s) = 0 := by
  refine intervalIntegral.integral_zero_ae (Filter.Eventually.of_forall ?_)
  intro s hs
  change min 0 y < s ∧ s ≤ max 0 y at hs
  exact transitionGap_of_le (hs.2.trans (max_le (by norm_num) hy))

/-- The cutoff equals one on the entire half-line ending at 100. -/
theorem cutoff_of_le {y : ℝ} (hy : y ≤ 100) : cutoff y = 1 := by
  rw [cutoff, integral_transitionGap_of_le hy, mul_zero, sub_zero]

private theorem integral_mul_eq_of_support {q : ℝ → ℝ} {a b y : ℝ}
    (hq : Function.support q ⊆ Ioo a b) (ha : 0 ≤ a) (hy : b ≤ y) :
    (∫ s in (0 : ℝ)..y, s * q s) = ∫ s : ℝ, s * q s := by
  refine intervalIntegral.integral_eq_integral_of_support_subset fun s hs ↦ ?_
  change s * q s ≠ 0 at hs
  have hsupp : s ∈ Ioo a b := hq (mul_ne_zero_iff.mp hs).2
  exact ⟨ha.trans_lt hsupp.1, hsupp.2.le.trans hy⟩

/-- The full transition-difference integral is 100, as follows from the pulse moments. -/
theorem integral_transitionGap_of_ge {y : ℝ} (hy : 205 ≤ y) :
    (∫ s in (0 : ℝ)..y, transitionGap s) = 100 := by
  have hm : (∫ s in (0 : ℝ)..y, s * qMinus s) = 205 / 2 := by
    calc
      (∫ s in (0 : ℝ)..y, s * qMinus s) = ∫ s : ℝ, s * qMinus s :=
        integral_mul_eq_of_support support_qMinus.subset (by norm_num) (by linarith)
      _ = 205 / 2 := integral_mul_qMinus
  have hp : (∫ s in (0 : ℝ)..y, s * qPlus s) = 405 / 2 := by
    calc
      (∫ s in (0 : ℝ)..y, s * qPlus s) = ∫ s : ℝ, s * qPlus s :=
        integral_mul_eq_of_support support_qPlus.subset (by norm_num) hy
      _ = 405 / 2 := integral_mul_qPlus
  have hsplit : (∫ s in (0 : ℝ)..y, s * (qMinus s - qPlus s)) = 205 / 2 - 405 / 2 := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub
      (f := fun s : ℝ ↦ s * qMinus s) (g := fun s : ℝ ↦ s * qPlus s) (μ := volume)
      ((continuous_id.mul contDiff_qMinus.continuous).intervalIntegrable 0 y)
      ((continuous_id.mul contDiff_qPlus.continuous).intervalIntegrable 0 y), hm, hp]
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := 0) (b := y) (u := fun s : ℝ ↦ s) (v := transitionGap)
    (u' := fun _ : ℝ ↦ (1 : ℝ)) (v' := fun s : ℝ ↦ qMinus s - qPlus s)
    (fun s _ ↦ hasDerivAt_id s) (fun s _ ↦ hasDerivAt_transitionGap s)
    (continuous_const.intervalIntegrable 0 y)
    ((contDiff_qMinus.continuous.sub contDiff_qPlus.continuous).intervalIntegrable 0 y)
  rw [transitionGap_of_ge hy] at hibp
  simp only [mul_zero, zero_mul, sub_zero, one_mul, zero_sub] at hibp
  rw [hsplit] at hibp
  linarith

/-- The cutoff equals zero on the entire half-line starting at 205. -/
theorem cutoff_of_ge {y : ℝ} (hy : 205 ≤ y) : cutoff y = 0 := by
  rw [cutoff, integral_transitionGap_of_ge hy]
  norm_num

/-- The cutoff decreases from its lower plateau to its upper plateau. -/
theorem antitone_cutoff : Antitone cutoff :=
  antitone_of_deriv_nonpos (fun y ↦ (hasDerivAt_cutoff y).differentiableAt) deriv_cutoff_nonpos

/-- The cutoff is nonnegative everywhere. -/
theorem cutoff_nonneg (y : ℝ) : 0 ≤ cutoff y := by
  by_cases hy : 205 ≤ y
  · exact (cutoff_of_ge hy).ge
  · have h := antitone_cutoff (le_of_lt (lt_of_not_ge hy))
    rwa [cutoff_of_ge (y := 205) le_rfl] at h

/-- The cutoff never exceeds its lower plateau value. -/
theorem cutoff_le_one (y : ℝ) : cutoff y ≤ 1 := by
  by_cases hy : y ≤ 100
  · exact (cutoff_of_le hy).le
  · have h := antitone_cutoff (le_of_lt (lt_of_not_ge hy))
    rwa [cutoff_of_le (y := 100) le_rfl] at h

end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
