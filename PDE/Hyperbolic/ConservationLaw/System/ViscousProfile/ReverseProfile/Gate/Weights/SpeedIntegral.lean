/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.ParametricIntervalSmooth.ReciprocalAffine
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Weights.Derivatives

/-!
# Speed derivatives of the passage integrals

The shared reciprocal-integral theorem differentiates both oriented passage
integrals. Their full denominators are retained, including the lower cutoff.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace Gate.Weights.GateRegularity

/-- The passage-integral speed derivatives follow from gate regularity.
The compact segments may have either orientation; no global nonvanishing
assumption or derivative of a parameter integral is an input. -/
theorem speedIntegralDifferentiation {D : PassageData} {I : Set ℝ}
    (h : GateRegularity D I) : SpeedIntegralDifferentiation D I := by
  constructor
  · intro y hy
    have hne : ∀ v ∈ uIcc (0 : ℝ) y, D.downSpeed v + (0 : ℝ) * v ≠ 0 := by
      simpa only [zero_mul, add_zero] using h.down_nonzero y hy
    have hi := PDE.Analysis.hasDerivAt_intervalIntegral_reciprocal_affine
      (d := D.downSpeed) (c := fun v : ℝ ↦ v) (a := 0) (b := y) (μ₀ := 0)
      h.continuous_downSpeed.continuousOn continuous_id.continuousOn hne
    simpa only [PassageData.downRemaining, PassageData.downMoment,
      zero_mul, add_zero, neg_div, intervalIntegral.integral_neg] using hi
  · intro y hy
    have hne : ∀ v ∈ uIcc D.base y, D.g v + 1 + (0 : ℝ) * (-v) ≠ 0 := by
      simpa only [zero_mul, add_zero] using h.up_nonzero y hy
    have hi := PDE.Analysis.hasDerivAt_intervalIntegral_reciprocal_affine
      (d := fun v ↦ D.g v + 1) (c := fun v : ℝ ↦ -v) (a := D.base) (b := y) (μ₀ := 0)
      (h.continuous_g.add continuous_const).continuousOn continuous_id.neg.continuousOn hne
    simpa only [PassageData.upPassageIntegral, PassageData.upMoment,
      zero_mul, add_zero, neg_zero, neg_neg, mul_neg, sub_eq_add_neg] using hi

end Gate.Weights.GateRegularity
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
