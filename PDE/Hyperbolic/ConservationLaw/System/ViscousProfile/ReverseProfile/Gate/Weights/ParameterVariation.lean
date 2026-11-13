/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flow.Variation.Speed
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Weights.Concrete
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Weights.SpeedIntegral

import CAS.ExactTactic

/-!
# Parameter derivatives of the prescribed clock's integral weights

The supplied event maps determine one family of the `PassageData`.
Speed changes `g` to `g - μ*y`; displacement changes only the event times.
The speed constant is the event-gap derivative from the previous theorem.

Rewriting the weights into their parameter forms allows the
shared reciprocal-integral derivative theorem to supply both speed derivatives.
The lower travel integral retains its entire cutoff term. These are derivatives of integral weights.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

open Gate.Weights MiddleClock

/-- Passage data for the same supplied event maps, with the upward anchor fixed at 205.
Only the scalar drift and event times vary; the speed constant is already determined. -/
def parameterizedClockPassageData (L Bhit : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : PassageData :=
  { clockPassageData 205 (Bhit p) (L p) (prescribedSpeedAnchorConstant L Bhit) with
    g := fun y ↦ g y - p.1 * y }

/-- At the base parameter these are exactly the original clock passage data,
with the speed constant derived from the supplied events. -/
@[simp] theorem parameterizedClockPassageData_zero (L Bhit : ℝ × ℝ → ℝ) :
    parameterizedClockPassageData L Bhit (0, 0) =
      clockPassageData 205 (Bhit (0, 0)) (L (0, 0))
        (prescribedSpeedAnchorConstant L Bhit) := by
  simp [parameterizedClockPassageData, clockPassageData]

/-- Base gate regularity is supplied by the original clock bounds. -/
theorem gateRegularity_parameterizedClockPassageData_zero (L Bhit : ℝ × ℝ → ℝ) :
    GateRegularity (parameterizedClockPassageData L Bhit (0, 0)) (Ioo (205 : ℝ) (2051 / 10)) := by
  rw [parameterizedClockPassageData_zero]
  exact gateRegularity_clockPassageData 205 (Bhit (0, 0)) (L (0, 0))
    (prescribedSpeedAnchorConstant L Bhit)

private theorem parameterizedClockPassageData_downSpeed (L Bhit : ℝ × ℝ → ℝ) (μ a y : ℝ) :
    (parameterizedClockPassageData L Bhit (μ, a)).downSpeed y =
      (parameterizedClockPassageData L Bhit (0, 0)).downSpeed y + μ * y := by
  simp only [parameterizedClockPassageData, clockPassageData, PassageData.downSpeed,
    zero_mul, sub_zero]
  ring

private theorem parameterizedClockPassageData_upDenominator (L Bhit : ℝ × ℝ → ℝ) (μ a y : ℝ) :
    (parameterizedClockPassageData L Bhit (μ, a)).g y + 1 =
      (parameterizedClockPassageData L Bhit (0, 0)).g y + 1 - μ * y := by
  simp only [parameterizedClockPassageData, clockPassageData, zero_mul, sub_zero]
  ring

/-- The downward time is exactly the speed-dependent integral,
including the full lower cutoff on the entire oriented segment. -/
theorem parameterizedClockPassageData_downTime (L Bhit : ℝ × ℝ → ℝ) (μ a y : ℝ) :
    (parameterizedClockPassageData L Bhit (μ, a)).downTime y =
      (parameterizedClockPassageData L Bhit (0, 0)).downRemaining μ y := by
  unfold PassageData.downTime PassageData.downRemaining
  apply intervalIntegral.integral_congr
  intro v _
  change 1 / (parameterizedClockPassageData L Bhit (μ, a)).downSpeed v =
    1 / ((parameterizedClockPassageData L Bhit (0, 0)).downSpeed v + μ * v)
  rw [parameterizedClockPassageData_downSpeed L Bhit μ a v]

/-- The same supplied upward event anchors the passage integral. -/
theorem parameterizedClockPassageData_tPlus (L Bhit : ℝ × ℝ → ℝ) (μ a y : ℝ) :
    (parameterizedClockPassageData L Bhit (μ, a)).tPlus y =
      Bhit (μ, a) + (parameterizedClockPassageData L Bhit (0, 0)).upPassageIntegral μ y := by
  unfold PassageData.tPlus PassageData.upPassageIntegral
  change Bhit (μ, a) + (∫ v in (205 : ℝ)..y,
      1 / ((parameterizedClockPassageData L Bhit (μ, a)).g v + 1)) =
    Bhit (μ, a) + (∫ v in (205 : ℝ)..y,
      1 / ((parameterizedClockPassageData L Bhit (0, 0)).g v + 1 - μ * v))
  congr 1
  apply intervalIntegral.integral_congr
  intro v _
  change 1 / ((parameterizedClockPassageData L Bhit (μ, a)).g v + 1) =
    1 / ((parameterizedClockPassageData L Bhit (0, 0)).g v + 1 - μ * v)
  rw [parameterizedClockPassageData_upDenominator L Bhit μ a v]

/-- The lower weight agrees with its speed-parameter form.
The event times cancel exactly, for every displacement. -/
theorem parameterizedClockPassageData_wMinus (L Bhit : ℝ × ℝ → ℝ) (μ a y : ℝ) :
    (parameterizedClockPassageData L Bhit (μ, a)).wMinus y =
      (parameterizedClockPassageData L Bhit (0, 0)).parameterWeightMinus y μ := by
  rw [PassageData.wMinus_eq_downTime, parameterizedClockPassageData_downTime]
  unfold PassageData.parameterWeightMinus
  congr 1
  simp only [parameterizedClockPassageData, clockPassageData, zero_mul, sub_zero]
  ring

/-- The upper weight uses the moving event gap, with no frozen anchor. -/
theorem parameterizedClockPassageData_wPlus (L Bhit : ℝ × ℝ → ℝ) (μ a y : ℝ) :
    (parameterizedClockPassageData L Bhit (μ, a)).wPlus y = (parameterizedClockPassageData L Bhit
      (0, 0)).parameterWeightPlus (fun ν ↦ L (ν, a) - Bhit (ν, a)) y μ := by
  have ht : (parameterizedClockPassageData L Bhit (μ, a)).terminalTime -
          (parameterizedClockPassageData L Bhit (μ, a)).tPlus y =
        (parameterizedClockPassageData L Bhit (0, 0)).upRemaining
          (fun ν ↦ L (ν, a) - Bhit (ν, a)) μ y := by
    rw [parameterizedClockPassageData_tPlus]
    unfold PassageData.upRemaining
    change L (μ, a) -
        (Bhit (μ, a) + (parameterizedClockPassageData L Bhit (0, 0)).upPassageIntegral μ y) =
      L (μ, a) - Bhit (μ, a) - (parameterizedClockPassageData L Bhit (0, 0)).upPassageIntegral μ y
    ring
  exact congrArg₂ (fun r d : ℝ ↦ Real.exp (-4 * r) / d) ht
    (parameterizedClockPassageData_upDenominator L Bhit μ a y)

/-- The speed derivative of the lower integral weight.
Gate regularity proves the parameter-integral derivative rather than assuming it. -/
theorem hasDerivAt_parameterizedClockWeightMinus_speed (L Bhit : ℝ × ℝ → ℝ)
    {y : ℝ} (hy : y ∈ Ioo (205 : ℝ) (2051 / 10)) :
    HasDerivAt (fun μ ↦ (parameterizedClockPassageData L Bhit (μ, 0)).wMinus y)
      ((parameterizedClockPassageData L Bhit (0, 0)).wMinus y *
        (parameterizedClockPassageData L Bhit (0, 0)).qMinus y) 0 := by
  have hw : (fun μ ↦ (parameterizedClockPassageData L Bhit (μ, 0)).wMinus y) =
      (parameterizedClockPassageData L Bhit (0, 0)).parameterWeightMinus y :=
    funext fun μ ↦ parameterizedClockPassageData_wMinus L Bhit μ 0 y
  rw [hw]
  have hreg := gateRegularity_parameterizedClockPassageData_zero L Bhit
  exact SpeedIntegralDifferentiation.hasDerivAt_parameterWeightMinus
    hreg hreg.speedIntegralDifferentiation hy

/-- The speed derivative of the upper integral weight. Differentiability
of the same event maps supplies the anchor derivative represented by `qPlus`. -/
theorem hasDerivAt_parameterizedClockWeightPlus_speed {L Bhit : ℝ × ℝ → ℝ}
    (hL : DifferentiableAt ℝ L (0, 0)) (hBhit : DifferentiableAt ℝ Bhit (0, 0)) {y : ℝ}
    (hy : y ∈ Ioo (205 : ℝ) (2051 / 10)) :
    HasDerivAt (fun μ ↦ (parameterizedClockPassageData L Bhit (μ, 0)).wPlus y)
      ((parameterizedClockPassageData L Bhit (0, 0)).wPlus y *
        (parameterizedClockPassageData L Bhit (0, 0)).qPlus y) 0 := by
  have hA : DifferentiableAt ℝ (fun μ ↦ L (μ, 0) - Bhit (μ, 0)) 0 := by
    simpa only [Function.comp_def, id_eq] using
      (hL.fun_sub hBhit).comp (f := fun μ : ℝ ↦ (μ, 0)) (0 : ℝ) (((hasDerivAt_id (0 : ℝ)).prodMk
          (hasDerivAt_const (0 : ℝ) (0 : ℝ))).differentiableAt)
  have hA' : HasDerivAt (fun μ ↦ L (μ, 0) - Bhit (μ, 0))
      (-(parameterizedClockPassageData L Bhit (0, 0)).speedConstant / 4) 0 := by
    apply hA.hasDerivAt.congr_deriv
    change deriv (fun μ ↦ L (μ, 0) - Bhit (μ, 0)) 0 = -prescribedSpeedAnchorConstant L Bhit / 4
    unfold prescribedSpeedAnchorConstant
    ring
  have hw : (fun μ ↦ (parameterizedClockPassageData L Bhit (μ, 0)).wPlus y) =
      (parameterizedClockPassageData L Bhit (0, 0)).parameterWeightPlus
        (fun μ ↦ L (μ, 0) - Bhit (μ, 0)) y :=
    funext fun μ ↦ parameterizedClockPassageData_wPlus L Bhit μ 0 y
  rw [hw]
  have hreg := gateRegularity_parameterizedClockPassageData_zero L Bhit
  exact SpeedIntegralDifferentiation.hasDerivAt_parameterWeightPlus
    hreg hreg.speedIntegralDifferentiation hy rfl hA'

/-- Displacement has no effect on the lower integral weight, even before differentiation. -/
theorem hasDerivAt_parameterizedClockWeightMinus_displacement (L Bhit : ℝ × ℝ → ℝ) (y : ℝ) :
    HasDerivAt (fun a ↦ (parameterizedClockPassageData L Bhit (0, a)).wMinus y) 0 0 := by
  have hw : (fun a ↦ (parameterizedClockPassageData L Bhit (0, a)).wMinus y) =
      (fun _ : ℝ ↦ (parameterizedClockPassageData L Bhit (0, 0)).parameterWeightMinus y 0) :=
    funext fun a ↦ parameterizedClockPassageData_wMinus L Bhit 0 a y
  rw [hw]
  exact hasDerivAt_const 0 _

/-- The upper displacement derivative retains the derivative of the event gap.
The travel integral and denominator are independent of displacement. -/
theorem hasDerivAt_parameterizedClockWeightPlus_displacement {L Bhit : ℝ × ℝ → ℝ}
    (hL : DifferentiableAt ℝ L (0, 0)) (hBhit : DifferentiableAt ℝ Bhit (0, 0)) (y : ℝ) :
    HasDerivAt (fun a ↦ (parameterizedClockPassageData L Bhit (0, a)).wPlus y)
      (-4 * deriv (fun a ↦ L (0, a) - Bhit (0, a)) 0 *
        (parameterizedClockPassageData L Bhit (0, 0)).wPlus y) 0 := by
  let D := parameterizedClockPassageData L Bhit (0, 0)
  let A : ℝ → ℝ := fun a ↦ L (0, a) - Bhit (0, a)
  have hA : DifferentiableAt ℝ A 0 := by
    simpa only [A, Function.comp_def, id_eq] using
      (hL.fun_sub hBhit).comp (f := fun a : ℝ ↦ (0, a)) (0 : ℝ)
        (((hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk (hasDerivAt_id (0 : ℝ))).differentiableAt)
  have hw : (fun a ↦ (parameterizedClockPassageData L Bhit (0, a)).wPlus y) =
      (fun a ↦ Real.exp (-4 * (A a - D.upPassageIntegral 0 y)) / (D.g y + 1)) := by
    funext a
    rw [parameterizedClockPassageData_wPlus]
    simp only [PassageData.parameterWeightPlus, PassageData.upRemaining, zero_mul, sub_zero, A, D]
  have hw0 : Real.exp (-4 * (A 0 - D.upPassageIntegral 0 y)) / (D.g y + 1) =
      D.wPlus y := by
    simpa only [PassageData.parameterWeightPlus, PassageData.upRemaining,
      zero_mul, sub_zero] using D.parameterWeightPlus_zero A rfl y
  have hu : D.g y + 1 ≠ 0 := by
    simpa only [D, parameterizedClockPassageData, clockPassageData, zero_mul, sub_zero] using
      (ne_of_gt (add_pos_of_nonneg_of_pos (g_nonneg y) zero_lt_one))
  rw [hw]
  apply ((((hA.hasDerivAt.sub_const (D.upPassageIntegral 0 y)).const_mul (-4)).exp).div_const
    (D.g y + 1)).congr_deriv
  change Real.exp (-4 * (A 0 - D.upPassageIntegral 0 y)) * (-4 * deriv A 0) /
      (D.g y + 1) = -4 * deriv A 0 * D.wPlus y
  rw [← hw0]
  field_simp

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
