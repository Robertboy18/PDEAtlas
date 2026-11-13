/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Moments.Base
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Moments.Variation

import CAS.ExactTactic

/-!
# A fixed signed gate for the supplied event moments

The selected bumps and signed coefficients determine one gate, normalized only
by the base lower weight. The fixed-gate theorem transfers their
normalized moments to the integral weights. The moment
variation theorems then identify the speed and displacement derivatives for
the same supplied event maps. The speed constant remains the one derived from
those events, and the displacement coefficient retains their gap derivative.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped BigOperators ContDiff

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

open Gate.Weights

/-- The same selected normalized moments give one fixed smooth signed gate.
Its base moment is `v 0 + v 1`, its speed derivative is `v 2`, and its
displacement derivative is the event-gap coefficient times `v 1`.
The gate retains the original small supports and uses only the base normalizer. -/
theorem prescribed_clock_fixed_gate_of_selected_moments (L Bhit : ℝ × ℝ → ℝ) {N : Set (ℝ × ℝ)}
    (hN : IsOpen N) (h0 : (0, 0) ∈ N) (hL : ContDiffOn ℝ ∞ L N) (hBhit : ContDiffOn ℝ ∞ Bhit N)
    (β : Fin 3 → ℝ → ℝ) (c v : Fin 3 → ℝ) (hβsmooth : ∀ j, ContDiff ℝ ∞ (β j))
    (hβcompact : ∀ j, HasCompactSupport (β j))
    (hβsupport : ∀ j, tsupport (β j) ⊆ Ioo (20501 / 100 : ℝ) (20509 / 100))
    (hβint : let D0 := parameterizedClockPassageData L Bhit (0, 0); ∀ j i : Fin 3,
      Integrable (fun y ↦ β j y * (![1, D0.R y, D0.Q y] : Fin 3 → ℝ) i))
    (hc : let D0 := parameterizedClockPassageData L Bhit (0, 0);
      (fun i : Fin 3 ↦ ∫ y, (∑ j, c j * β j y) * (![1, D0.R y, D0.Q y] : Fin 3 → ℝ) i) = v) :
    let D0 := parameterizedClockPassageData L Bhit (0, 0)
    let b : ℝ → ℝ := (Ioo (205 : ℝ) (2051 / 10)).indicator
      (fun y ↦ (∑ j, c j * β j y) / D0.wMinus y)
    ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
      tsupport b ⊆ (⋃ j, tsupport (β j)) ∧
      tsupport b ⊆ Ioo (20501 / 100 : ℝ) (20509 / 100) ∧
      (∀ y, D0.wMinus y * b y = ∑ j, c j * β j y) ∧
      Integrable (fun y ↦ b y * (D0.wMinus y + D0.wPlus y)) ∧
      prescribedClockWeightMoment b L Bhit (0, 0) = v 0 + v 1 ∧
      HasDerivAt (fun μ ↦ prescribedClockWeightMoment b L Bhit (μ, 0)) (v 2) 0 ∧
      HasDerivAt (fun a ↦ prescribedClockWeightMoment b L Bhit (0, a))
        (-4 * deriv (fun a ↦ L (0, a) - Bhit (0, a)) 0 * v 1) 0 := by
  classical
  dsimp only
  let D0 := parameterizedClockPassageData L Bhit (0, 0)
  let b : ℝ → ℝ := (Ioo (205 : ℝ) (2051 / 10)).indicator (fun y ↦ (∑ j, c j * β j y) / D0.wMinus y)
  have hselected := fixed_base_clock_gate_of_selected_moments
    205 (Bhit (0, 0)) (L (0, 0)) (prescribedSpeedAnchorConstant L Bhit)
    β c v hβsmooth hβcompact hβsupport
    (by simpa only [parameterizedClockPassageData_zero] using hβint)
    (by simpa only [parameterizedClockPassageData_zero] using hc)
  rw [← parameterizedClockPassageData_zero L Bhit] at hselected
  obtain ⟨hb, hbcompact, hbsupport, hbsmall, hwb, hmoments⟩ := hselected
  have hbsupp : tsupport b ⊆ Ioo (205 : ℝ) (2051 / 10) :=
    hbsmall.trans (Ioo_subset_Ioo (by cas) (by cas))
  have hminus : Integrable (fun y ↦ b y * D0.wMinus y) ∧
      (∫ y, b y * D0.wMinus y) = v 0 := hmoments (0 : Fin 3)
  have hplus : Integrable (fun y ↦ b y * D0.wPlus y) ∧
      (∫ y, b y * D0.wPlus y) = v 1 := hmoments (1 : Fin 3)
  have hsumInt : Integrable (fun y ↦ b y * (D0.wMinus y + D0.wPlus y)) := by
    simpa only [mul_add] using (hminus.1.fun_add hplus.1)
  have hbase : prescribedClockWeightMoment b L Bhit (0, 0) = v 0 + v 1 := by
    change (∫ y, b y * (D0.wMinus y + D0.wPlus y)) = v 0 + v 1
    simp_rw [mul_add]
    rw [integral_add hminus.1 hplus.1, hminus.2, hplus.2]
  have hthird : (∫ y, b y * (D0.wPlus y * D0.qPlus y + D0.wMinus y * D0.qMinus y)) = v 2 :=
    (hmoments (2 : Fin 3)).2
  -- The moment derivative lists the two summands in the opposite order.
  have hspeedValue : (∫ y, b y *
      (D0.wMinus y * D0.qMinus y + D0.wPlus y * D0.qPlus y)) = v 2 := by
    simpa only [add_comm] using hthird
  have hspeed := (prescribedClockWeightMoment_speed_variation hN h0 hL hBhit hb hbcompact hbsupp).2
  have hdisplacement :=
    (prescribedClockWeightMoment_displacement_variation hN h0 hL hBhit hb hbcompact hbsupp).2
  refine ⟨hb, hbcompact, hbsupport, hbsmall, hwb, hsumInt, hbase,
    hspeed.congr_deriv hspeedValue, ?_⟩
  exact hdisplacement.congr_deriv
    (congrArg (fun r : ℝ ↦ -4 * deriv (fun a ↦ L (0, a) - Bhit (0, a)) 0 * r) hplus.2)

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
