/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Linear.Scalar.Constant
public import PDE.Common.Euclidean
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Moments.Variation

import CAS.ExactTactic

/-!
# The terminal ratio of the supplied coupled trajectory

Agreement with the prescribed candidate identifies its first and third coordinates.
The shared scalar ODE representation gives the fast coordinate's exponential value
and positivity at the supplied terminal event. Its cancellation leaves the
zero-initial scalar solution, whose normal form is the localized weight moment.

Both agreement and localization are explicit inputs for the same clock, gate,
parameter, and event maps.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open PDE.Analysis.Evolution
open scoped Interval

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

/-- The terminal ratio equals the signed weight moment once the
supplied trajectory agrees with the exact prescribed candidate and its time integral
has been localized. The fast ODE and its unit initial value prove positivity of the
denominator. The terminal time is the same `L p` throughout. -/
theorem prescribed_clock_terminal_ratio_eq_weight_moment {X Z b : ℝ → ℝ} {L Bhit : ℝ × ℝ → ℝ}
    {p : ℝ × ℝ} {H : ℝ} {q : ℝ → ℝ^3} (hZcontinuous : ContinuousOn Z (Icc 0 H))
    (hfast : ∀ t ∈ Icc 0 H, HasDerivAt Z ((2 - p.1) * Z t) t) (hZzero : Z 0 = 1)
    (hterminal : L p ∈ Icc 0 H)
    (hagreement : EqOn q (fun t ↦ !₂[Z t * scalarLinearSolution (fun _ : ℝ ↦ 4) (fun s ↦ b (X s)) 0
      0 t, X t, Z t]) (Icc 0 H))
    (hmoment : (∫ t in (0 : ℝ)..L p, b (X t) * Real.exp (-4 * (L p - t))) =
      prescribedClockWeightMoment b L Bhit p) :
    (q (L p)) 0 / (q (L p)) 2 = prescribedClockWeightMoment b L Bhit p := by
  have hZend : Z (L p) = Real.exp ((2 - p.1) * L p) := by
    have heq := eq_scalarLinearSolution_const_of_hasDerivAt
      (r := Z) (f := fun _ ↦ 0) (κ := -(2 - p.1)) hterminal.1
      (hZcontinuous.mono (Icc_subset_Icc le_rfl hterminal.2)) continuousOn_const
      (fun t ht ↦ by
        simpa only [neg_neg, add_zero] using hfast t ⟨ht.1.le, ht.2.le.trans hterminal.2⟩)
    rw [scalarLinearSolution_const_eq_exp_mul_add_integral] at heq
    simpa only [hZzero, neg_neg, sub_zero, mul_one, mul_zero,
      intervalIntegral.integral_zero, add_zero] using heq
  have hZpositive : 0 < Z (L p) := by
    rw [hZend]
    exact Real.exp_pos _
  let r := scalarLinearSolution (fun _ : ℝ ↦ 4) (fun s ↦ b (X s)) 0 0
  calc
    (q (L p)) 0 / (q (L p)) 2 = Z (L p) * r (L p) / Z (L p) :=
      congrArg (fun v : ℝ^3 ↦ v 0 / v 2) (hagreement hterminal)
    _ = r (L p) := by
      have hZne : Z (L p) ≠ 0 := ne_of_gt hZpositive
      generalize Z (L p) = z at hZne ⊢
      generalize r (L p) = R
      cas using hZne
    _ = ∫ t in (0 : ℝ)..L p, b (X t) * Real.exp (-4 * (L p - t)) := by
      dsimp only [r]
      rw [scalarLinearSolution_const_eq_exp_mul_add_integral]
      simp only [mul_zero, zero_add]
      exact intervalIntegral.integral_congr (fun _ _ ↦ mul_comm _ _)
    _ = prescribedClockWeightMoment b L Bhit p := hmoment

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
