/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.LocalFreeField
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat.FreeField
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat.Incoming.Profile
import CAS.ExactTactic

/-!
# Cauchy data for the incoming free wave

The compact incoming radial data have the prescribed annular traces and their Kirchhoff field
equals the radial free solution.
-/

@[expose] public noncomputable section

section

open Set Filter Metric PDE PDE.Analysis PDE.Common WaveEquation
open PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
open scoped ContDiff Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

/-- The initial displacement of the explicit incoming free baseline. -/
def incomingDisplacement (x : ℝ^3) : ℝ := radialFreeField incomingProfile (0, x)

/-- The initial velocity of the explicit incoming free baseline. -/
def incomingVelocity (x : ℝ^3) : ℝ :=
  fderiv ℝ (radialFreeField incomingProfile) (0, x) (1, 0)

/-- The baseline displacement is `C³`. -/
theorem contDiff_incomingDisplacement : ContDiff ℝ 3 incomingDisplacement :=
  (contDiff_three_radialFreeField contDiff_incomingProfile).comp (contDiff_const.prodMk contDiff_id)

/-- The baseline velocity is `C²`. -/
theorem contDiff_incomingVelocity : ContDiff ℝ 2 incomingVelocity :=
  (((contDiff_three_radialFreeField contDiff_incomingProfile).fderiv_right
    (by norm_num)).comp (contDiff_const.prodMk contDiff_id)).clm_apply contDiff_const

/-- The velocity is the ordinary initial time derivative of the baseline field. -/
theorem hasDerivAt_incoming_free_initial (x : ℝ^3) :
    HasDerivAt (fun t : ℝ ↦ radialFreeField incomingProfile (t, x)) (incomingVelocity x) 0 := by
  exact ((contDiff_three_radialFreeField contDiff_incomingProfile).differentiable
    (by norm_num) (0, x)).hasFDerivAt.comp_hasDerivAt 0
      ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) x))

private theorem incoming_free_zero_outside {t : ℝ} {x : ℝ^3}
    (ht : |t| < 1) (hx : 3 < ‖x‖) : radialFreeField incomingProfile (t, x) = 0 := by
  have hr : ‖x‖ ≠ 0 := ne_of_gt (by linarith)
  have hleft : incomingProfile (t - ‖x‖) = 0 :=
    incomingProfile_eq_zero (by linarith [(abs_lt.mp ht).2])
  have hright : incomingProfile (t + ‖x‖) = 0 := by
    have hone : Real.smoothTransition (2 * (t + ‖x‖) - 3) = 1 :=
      Real.smoothTransition.one_of_one_le (by linarith [(abs_lt.mp ht).1])
    simp only [incomingProfile, hone, sub_self, mul_zero]
  rw [radialFreeField, radialFreeProfile_eq_div _ _ hr, hleft, hright, sub_self, zero_div]

/-- One closed ball supports both baseline Cauchy traces. -/
theorem incoming_data_zero_outside {x : ℝ^3} (hx : 3 < ‖x‖) :
    incomingDisplacement x = 0 ∧ incomingVelocity x = 0 := by
  refine ⟨incoming_free_zero_outside (by norm_num) hx, ?_⟩
  have hgerm : (fun t : ℝ ↦ radialFreeField incomingProfile (t, x)) =ᶠ[𝓝 0]
      fun _ ↦ (0 : ℝ) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-1) 1 by
      constructor <;> norm_num)] with t ht
    exact incoming_free_zero_outside (abs_lt.mpr ht) hx
  exact (hasDerivAt_incoming_free_initial x).unique
    ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hgerm)

/-- The baseline displacement and velocity are compactly supported. -/
theorem hasCompactSupport_incoming_data :
    HasCompactSupport incomingDisplacement ∧ HasCompactSupport incomingVelocity := by
  constructor
  · apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ^3) 3)
    intro x hx
    by_contra hmem
    have hr : 3 < ‖x‖ := by simpa only [mem_closedBall, dist_zero_right, not_le] using hmem
    exact hx (incoming_data_zero_outside hr).1
  · apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ^3) 3)
    intro x hx
    by_contra hmem
    have hr : 3 < ‖x‖ := by simpa only [mem_closedBall, dist_zero_right, not_le] using hmem
    exact hx (incoming_data_zero_outside hr).2

/-- The compact baseline agrees with the linear Goursat displacement
and velocity on a fixed open annulus. -/
theorem incoming_data_on_annulus {x : ℝ^3} (hx : |‖x‖ - 1| < 1 / 4) :
    incomingDisplacement x = (‖x‖ - 1) / ‖x‖ ∧ incomingVelocity x = 1 / ‖x‖ := by
  have hx' := abs_lt.mp hx
  have hr : ‖x‖ ≠ 0 := ne_of_gt (by linarith)
  have hlin : ∀ᶠ t : ℝ in 𝓝 0, t + ‖x‖ ∈ Ioo (3 / 4) (5 / 4) :=
    (continuous_id.add continuous_const).continuousAt.eventually
      (isOpen_Ioo.mem_nhds (by change 0 + ‖x‖ ∈ _; constructor <;> linarith))
  have hleft : ∀ᶠ t : ℝ in 𝓝 0, t - ‖x‖ < -1 / 2 :=
    (continuous_id.sub continuous_const).continuousAt.eventually
      (isOpen_Iio.mem_nhds (by change 0 - ‖x‖ < _; linarith))
  have hgerm : (fun t : ℝ ↦ radialFreeField incomingProfile (t, x)) =ᶠ[𝓝 0]
      fun t ↦ (t + ‖x‖ - 1) / ‖x‖ := by
    filter_upwards [hlin, hleft] with t ht htleft
    rw [radialFreeField, radialFreeProfile_eq_div _ _ hr,
      incomingProfile_eq_linear ⟨ht.1.le, ht.2.le⟩, incomingProfile_eq_zero htleft.le, sub_zero]
  refine ⟨by simpa only [incomingDisplacement, zero_add] using hgerm.eq_of_nhds, ?_⟩
  have hd : HasDerivAt (fun t : ℝ ↦ (t + ‖x‖ - 1) / ‖x‖) (1 / ‖x‖) 0 := by
    generalize ‖x‖ = r at hr ⊢
    cas using hr
  exact (hasDerivAt_incoming_free_initial x).unique (hd.congr_of_eventuallyEq hgerm)

/-- Kirchhoff's formula for the compact baseline data equals the constructed
radial field at every forward time, including the axis and initial face. -/
theorem cauchyFreeField_incoming_data {t : ℝ} (ht : 0 ≤ t) (x : ℝ^3) :
    cauchyFreeField incomingDisplacement incomingVelocity (t, x) =
      radialFreeField incomingProfile (t, x) := by
  let U : ℝ^4 → ℝ := fun z ↦ radialFreeField incomingProfile (timeSpaceContinuousLinearEquiv 3 z)
  have hU : ContDiff ℝ 2 U :=
    ((contDiff_three_radialFreeField contDiff_incomingProfile).of_le (by norm_num)).comp
      (timeSpaceContinuousLinearEquiv 3).contDiff
  have hvelocity (y : ℝ^3) : (∂[0] U) (timeSpaceCons 0 y) = incomingVelocity y := by
    rw [partialDeriv_timeSpaceCons_eq_deriv U y 0 (hU.differentiable (by norm_num) _)]
    simpa only [U, timeSpaceContinuousLinearEquiv_apply, time, timeSpaceCons_zero,
      spatialPart_timeSpaceCons] using (hasDerivAt_incoming_free_initial y).deriv
  have hsol : SatisfiesPDEProblem
      (waveResidualAssignedCauchyDataProblem incomingDisplacement incomingVelocity) U := by
    refine forcedWaveResidualAssignedCauchyDataProblem.of_residual_initial ?_ ?_ ?_
    · intro z _
      have he := waveOperator_radialFreeField contDiff_incomingProfile (z 0) (spatialPartCLM 3 z)
      simpa only [timeSpaceCons_spatialPartCLM] using he
    · intro z hz
      change radialFreeField incomingProfile (time z, spatialPart z) =
        incomingDisplacement (spatialPart z)
      simp only [time, hz, incomingDisplacement]
    · intro z hz
      have he := hvelocity (spatialPartCLM 3 z)
      rw [← hz, timeSpaceCons_spatialPartCLM] at he
      simpa only [spatialPartCLM_eq_spatialPart] using he
  have he := eq_on_nonnegative_time_of_satisfiesResidualAssignedCauchyData hU
    (contDiff_two_kirchhoffFormula contDiff_incomingDisplacement contDiff_incomingVelocity)
    hsol (kirchhoffFormula_satisfiesResidualAssignedCauchyData
      contDiff_incomingDisplacement contDiff_incomingVelocity) ht x
  simpa only [U, timeSpaceContinuousLinearEquiv_apply, time, timeSpaceCons_zero,
    spatialPart_timeSpaceCons, cauchyFreeField] using he.symm

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

end

section

open PDE.Analysis
open scoped ContDiff

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

/-- The already fixed incoming displacement is smooth. -/
theorem contDiff_infty_incomingDisplacement : ContDiff ℝ ∞ incomingDisplacement :=
  (contDiff_infty_radialFreeField contDiff_incomingProfile).comp (contDiff_const.prodMk contDiff_id)

/-- The already fixed incoming velocity is smooth. -/
theorem contDiff_infty_incomingVelocity : ContDiff ℝ ∞ incomingVelocity := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ (radialFreeField incomingProfile)) :=
    (contDiff_infty_radialFreeField contDiff_incomingProfile).fderiv_right (by simp)
  exact (hd.comp (contDiff_const.prodMk contDiff_id)).clm_apply contDiff_const

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

end
