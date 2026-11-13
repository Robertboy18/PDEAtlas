/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.BumpMoments.NormalizedPulse.Basic
public import PDE.Analysis.Integration.Primitive.Regularity

/-!
# The primitive of the normalized pulse

Integrating the normalized glue-product density from zero gives a globally smooth
transition from zero to one. The definition uses the oriented interval integral
for every real argument, including negative arguments. Reflection of the density
becomes the identity `transition (1 - t) = 1 - transition t`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff Interval

namespace PDE.Analysis.NormalizedPulse

/-- The integral from zero to `t` of the actual normalized glue-product density. -/
def transition (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, density s

/-- The normalized pulse primitive is infinitely differentiable everywhere. -/
theorem contDiff_transition : ContDiff ℝ ∞ transition := by
  change ContDiff ℝ ∞ (fun t : ℝ ↦ ∫ s in (0 : ℝ)..t, density s)
  exact (contDiff_intervalIntegral_of_contDiff (n := ⊤) contDiff_density 0).of_le (by simp)

/-- The normalized density is the derivative of its primitive at every real argument. -/
theorem hasDerivAt_transition (t : ℝ) : HasDerivAt transition (density t) t :=
  (contDiff_density.continuous.integral_hasStrictDerivAt 0 t).hasDerivAt

/-- The ordinary derivative of the normalized pulse primitive is its density. -/
theorem deriv_transition (t : ℝ) : deriv transition t = density t :=
  (hasDerivAt_transition t).deriv

/-- The pulse primitive vanishes on the nonpositive half-line, including zero. -/
theorem transition_of_nonpos {t : ℝ} (ht : t ≤ 0) : transition t = 0 := by
  change (∫ s in (0 : ℝ)..t, density s) = 0
  refine intervalIntegral.integral_zero_ae (Filter.Eventually.of_forall ?_)
  intro s hs
  rw [uIoc_of_ge ht] at hs
  apply Function.notMem_support.mp
  rw [support_density]
  exact fun hpos ↦ (not_lt_of_ge hs.2) hpos.1

/-- The pulse primitive equals one on the half-line starting at one. -/
theorem transition_of_one_le {t : ℝ} (ht : 1 ≤ t) : transition t = 1 := by
  have hsupp : Function.support density ⊆ Ioc (0 : ℝ) t := by
    rw [support_density]
    intro s hs
    exact ⟨hs.1, hs.2.le.trans ht⟩
  exact (intervalIntegral.integral_eq_integral_of_support_subset hsupp).trans integral_density

/-- The pulse primitive is nonnegative for every real argument. -/
theorem transition_nonneg (t : ℝ) : 0 ≤ transition t := by
  rcases le_total 0 t with ht | ht
  · exact intervalIntegral.integral_nonneg_of_forall ht density_nonneg
  · exact (transition_of_nonpos ht).ge

/-- The pulse primitive is bounded above by its total mass, which is one. -/
theorem transition_le_one (t : ℝ) : transition t ≤ 1 := by
  rcases le_total 0 t with ht | ht
  · change (∫ s in (0 : ℝ)..t, density s) ≤ 1
    rw [intervalIntegral.integral_of_le ht]
    exact (setIntegral_le_integral integrable_density
      (Filter.Eventually.of_forall density_nonneg)).trans_eq integral_density
  · exact (transition_of_nonpos ht).le.trans zero_le_one

/-- Reflection about the midpoint exchanges the pulse primitive with its complement. -/
theorem transition_one_sub (t : ℝ) : transition (1 - t) = 1 - transition t := by
  have hreflect : transition t = ∫ s in (1 - t)..1, density s := by
    simpa only [transition, density_one_sub, sub_zero] using
      (intervalIntegral.integral_comp_sub_left (a := 0) (b := t) density 1)
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (contDiff_density.continuous.intervalIntegrable 0 (1 - t))
    (contDiff_density.continuous.intervalIntegrable (1 - t) 1)
  change transition (1 - t) + (∫ s in (1 - t)..1, density s) = transition 1 at hadd
  rw [← hreflect, transition_of_one_le le_rfl] at hadd
  exact eq_sub_of_add_eq hadd

end PDE.Analysis.NormalizedPulse
