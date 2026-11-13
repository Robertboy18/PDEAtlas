/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flow.Events.Speed

import PDE.Analysis.Integration.Primitive.Quotient
import CAS.ExactTactic

/-!
# Primitive identities on prescribed clock branches

A reciprocal primitive changes at constant rate along a supplied scalar solution.
The two clock applications use the same supplied family at one fixed physical
parameter. Its vector equation and the stated switching margins imply the
appropriate scalar equation on each closed branch interval.

The lower denominator retains the cutoff on the entire integration segment.
The anchors are the supplied upward 205 event and the supplied zero.
-/

@[expose] public noncomputable section

open MeasureTheory Set


namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

open MiddleClock PDE.Analysis.NormalizedPulse

/-- The speed window already supplied by the family keeps both denominators
positive throughout the closed state interval. -/
private theorem speed_denominators_pos {μ y : ℝ} (hμ : |μ| < 1 / 410) (hy : y ∈ Icc (0 : ℝ) 210) :
    0 < g y + 1 - μ * y ∧ 0 < 4 - g y + 4 * cutoff y + μ * y := by
  have hm := abs_lt.mp hμ
  have hleft : -(1 : ℝ) < μ * y := by linarith [mul_le_mul_of_nonneg_right hm.1.le hy.1, hy.2]
  have hright : μ * y < 1 := by linarith [mul_le_mul_of_nonneg_right hm.2.le hy.1, hy.2]
  exact ⟨by linarith [g_nonneg y],
    by linarith [MiddleClock.thirteen_fifths_lt_lower_denominator hy.1 hy.2]⟩

/-- On a supplied pre-switch branch, the upward 205 anchor plus the
speed-dependent primitive is elapsed time. The primitive is signed if the
trajectory level is below 205. All time endpoints are included. -/
theorem prescribed_speed_up_primitive_eq {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {A B : ℝ} {p : ℝ × ℝ}
    {s e b₀ : ℝ} (hAB : A ^ 2 < B ^ 2) (hμ : |p.1| < 1 / 410)
    (hF : ∀ t ∈ Icc s e, HasDerivAt (fun u ↦ F (u, p)) (prescribedSpeedField A B (p.1, F (t, p))) t)
    (hinner : ∀ t ∈ Icc s e, 2 < (F (t, p)).2) (houter : ∀ t ∈ Icc s e, (F (t, p)).2 ^ 2 < A ^ 2)
    (hband : ∀ t ∈ Icc s e, (F (t, p)).1 ∈ Icc (0 : ℝ) 210) (hb₀ : b₀ ∈ Icc s e)
    (hhit : (F (b₀, p)).1 = 205) :
    ∀ t ∈ Icc s e, b₀ + (∫ v in (205 : ℝ)..(F (t, p)).1, 1 / (g v + 1 - p.1 * v)) = t := by
  let X : ℝ → ℝ := fun t ↦ (F (t, p)).1
  let d : ℝ → ℝ := fun v ↦ g v + 1 - p.1 * v
  have hd : Continuous d :=
    (contDiff_g.continuous.add continuous_const).sub (continuous_const.mul continuous_id)
  have hX (t : ℝ) (ht : t ∈ Icc s e) : HasDerivAt X (d (X t) * 1) t := by
    have hi : transition ((F (t, p)).2 ^ 2 - 1) = 1 := by
      apply PDE.Analysis.NormalizedPulse.transition_of_one_le
      nlinarith [hinner t ht]
    have hx : HasDerivAt X (prescribedSpeedField A B (p.1, F (t, p))).1 t :=
      (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hF t ht)
    simpa only [X, d, prescribedSpeedField, prescribedClockField,
      clockFeedback_of_sq_le hAB (houter t ht).le,
      outerTransition_of_sq_le hAB (houter t ht).le, hi, mul_zero, sub_zero, mul_one] using hx
  have hne : ∀ t ∈ Icc s e, ∀ v ∈ uIcc (205 : ℝ) (X t), d v ≠ 0 := by
    intro t ht v hv
    have hvK : v ∈ Icc (0 : ℝ) 210 := ordConnected_Icc.uIcc_subset
        (show (205 : ℝ) ∈ Icc (0 : ℝ) 210 from ⟨by norm_num, by norm_num⟩) (hband t ht) hv
    exact ne_of_gt (speed_denominators_pos hμ hvK).1
  have hconst := PDE.Analysis.integral_reciprocal_comp_sub_eq hd hX hne
  have hbase : X b₀ = 205 := hhit
  intro t ht
  have hc := (hconst t ht).trans (hconst b₀ hb₀).symm
  change (∫ v in (205 : ℝ)..X t, 1 / d v) - 1 * t = (∫ v in (205 : ℝ)..X b₀, 1 / d v) - 1 * b₀ at hc
  simp only [one_mul, hbase, intervalIntegral.integral_same, zero_sub] at hc
  change b₀ + (∫ v in (205 : ℝ)..X t, 1 / d v) = t
  linarith

/-- On a supplied completed-switch branch, the zero anchor minus the
full remaining-time primitive is elapsed time. The cutoff is retained below
205, so the denominator at zero is eight for every fixed speed. -/
theorem prescribed_speed_down_primitive_eq {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {A B : ℝ} {p : ℝ × ℝ}
    {s e τ : ℝ} (hAB : A ^ 2 < B ^ 2) (hμ : |p.1| < 1 / 410)
    (hF : ∀ t ∈ Icc s e, HasDerivAt (fun u ↦ F (u, p)) (prescribedSpeedField A B (p.1, F (t, p))) t)
    (hafter : ∀ t ∈ Icc s e, B ^ 2 < (F (t, p)).2 ^ 2)
    (hband : ∀ t ∈ Icc s e, (F (t, p)).1 ∈ Icc (0 : ℝ) 210) (hτ : τ ∈ Icc s e)
    (hzero : (F (τ, p)).1 = 0) :
    ∀ t ∈ Icc s e, τ - (∫ v in (0 : ℝ)..(F (t, p)).1, 1 / (4 - g v + 4 * cutoff v + p.1 * v)) =
      t := by
  let X : ℝ → ℝ := fun t ↦ (F (t, p)).1
  let d : ℝ → ℝ := fun v ↦ 4 - g v + 4 * cutoff v + p.1 * v
  have hd : Continuous d := ((continuous_const.sub contDiff_g.continuous).add
      (continuous_const.mul contDiff_cutoff.continuous)).add (continuous_const.mul continuous_id)
  have hX (t : ℝ) (ht : t ∈ Icc s e) : HasDerivAt X (d (X t) * (-1)) t := by
    have hx : HasDerivAt X (prescribedSpeedField A B (p.1, F (t, p))).1 t :=
      (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hF t ht)
    change HasDerivAt X (prescribedClockField A B (F (t, p)).2 (X t) - p.1 * X t) t at hx
    rw [prescribedClockField_eq_lower hAB (hafter t ht).le] at hx
    have hfield : lowerClockField (X t) - p.1 * X t = d (X t) * (-1) := by
      change g (X t) - 4 - 4 * cutoff (X t) - p.1 * X t =
        (4 - g (X t) + 4 * cutoff (X t) + p.1 * X t) * (-1)
      ring
    exact hx.congr_deriv hfield
  have hne : ∀ t ∈ Icc s e, ∀ v ∈ uIcc (0 : ℝ) (X t), d v ≠ 0 := by
    intro t ht v hv
    have hvK : v ∈ Icc (0 : ℝ) 210 :=
      ordConnected_Icc.uIcc_subset (show (0 : ℝ) ∈ Icc (0 : ℝ) 210 from ⟨by norm_num, by norm_num⟩)
        (hband t ht) hv
    exact ne_of_gt (speed_denominators_pos hμ hvK).2
  have hconst := PDE.Analysis.integral_reciprocal_comp_sub_eq hd hX hne
  have hbase : X τ = 0 := hzero
  intro t ht
  have hc := (hconst t ht).trans (hconst τ hτ).symm
  change (∫ v in (0 : ℝ)..X t, 1 / d v) - (-1) * t = (∫ v in (0 : ℝ)..X τ, 1 / d v) - (-1) * τ at hc
  simp only [neg_one_mul, sub_neg_eq_add, hbase, intervalIntegral.integral_same, zero_add] at hc
  change τ - (∫ v in (0 : ℝ)..X t, 1 / d v) = t
  linarith

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
