/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Clock.GateBounds
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Weights.Denominator
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Weights.Derivatives

/-!
# Integral weights for the constructed middle clock

The pulse clock and its cutoff supply the regularity and nonzero denominators
needed by the passage integrals. Their proved value and derivative bounds then
control the relative curvature of those integrals. A passage-time gap is
a hypothesis.
-/

@[expose] public section

noncomputable section

open Set

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile

open Gate.Weights MiddleClock

/-- Passage data with the constructed clock and cutoff. The four scalar choices
specify the upward anchor and the two additive time and speed constants. -/
def clockPassageData (base upTime terminalTime speedConstant : ℝ) : PassageData where
  g := g
  C := cutoff
  base := base
  upBaseTime := upTime
  terminalTime := terminalTime
  speedConstant := speedConstant

/-- The regularity and denominator facts about the integral weights follow from the constructed
smooth clock and its bounds. -/
theorem gateRegularity_clockPassageData (base upTime terminalTime speedConstant : ℝ) :
    GateRegularity (clockPassageData base upTime terminalTime speedConstant)
      (Ioo (205 : ℝ) (2051 / 10)) := by
  refine
    { isOpen := isOpen_Ioo
      continuous_g := contDiff_g.continuous
      continuous_C := contDiff_cutoff.continuous
      differentiable_g := fun y _ ↦ (hasDerivAt_g y).differentiableAt
      differentiable_deriv_g := ?_
      cutoff_zero := fun y hy ↦ cutoff_of_ge hy.1.le
      up_nonzero := ?_
      down_nonzero := ?_ }
  · intro y _
    change DifferentiableAt ℝ (deriv g) y
    rw [show deriv g = slope from funext deriv_g]
    exact (hasDerivAt_slope y).differentiableAt
  · intro y _ v _
    change g v + 1 ≠ 0
    have hg := g_nonneg v
    linarith only [hg]
  · intro y hy v hv
    have hy0 : (0 : ℝ) ≤ y := by linarith only [hy.1]
    rw [uIcc_of_le hy0] at hv
    have hv210 : v ≤ (210 : ℝ) := by linarith only [hv.2, hy.2]
    exact ne_of_gt (MiddleClock.lower_denominator_pos hv.1 hv210)

/-- The ratio of the two integral value weights is strictly increasing on the
gate, independently of the additive time and speed constants. -/
theorem deriv_clock_weight_ratio_pos (base upTime terminalTime speedConstant : ℝ)
    {y : ℝ} (hy : y ∈ Ioo (205 : ℝ) (2051 / 10)) :
    0 < deriv (clockPassageData base upTime terminalTime speedConstant).R y := by
  let D := clockPassageData base upTime terminalTime speedConstant
  have hreg := gateRegularity_clockPassageData base upTime terminalTime speedConstant
  rw [(hreg.hasDerivAt_R hy).deriv]
  have hg := g_mem_Icc_gate ⟨hy.1.le, hy.2.le⟩
  have hv := deriv_g_mem_Icc_gate ⟨hy.1.le, hy.2.le⟩
  have hu : 0 < g y + 1 := by linarith only [hg.1]
  have hd : 0 < 4 - g y := by linarith only [hg.2]
  have hJ : 0 < 4 - deriv g y := by linarith only [hv.2]
  change 0 < D.H y * D.R y
  unfold PassageData.H PassageData.R
  change 0 < (5 * (4 - deriv g y) / ((g y + 1) * (4 - g y))) *
    ((4 - g y) / (g y + 1) * Real.exp (-4 * (D.tMinus y - D.tPlus y)))
  exact mul_pos (div_pos (mul_pos (by norm_num) hJ) (mul_pos hu hd))
    (mul_pos (div_pos hd hu) (Real.exp_pos _))

/-- A sufficiently separated pair of passages gives negative relative curvature
for the integral weights, with the full upward-weight term retained. -/
theorem clock_weight_relative_curvature_lt (base upTime terminalTime speedConstant : ℝ) {y : ℝ}
    (hy : y ∈ Ioo (205 : ℝ) (2051 / 10))
    (hgap : (8 / 5 : ℝ) ≤ (clockPassageData base upTime terminalTime speedConstant).tMinus y -
      (clockPassageData base upTime terminalTime speedConstant).tPlus y) :
    let D := clockPassageData base upTime terminalTime speedConstant
    deriv (deriv D.Q) y - deriv (deriv D.R) y / deriv D.R y * deriv D.Q y < -260 := by
  let D := clockPassageData base upTime terminalTime speedConstant
  have hreg := gateRegularity_clockPassageData base upTime terminalTime speedConstant
  have hg := g_mem_Icc_gate ⟨hy.1.le, hy.2.le⟩
  have hv := deriv_g_mem_Icc_gate ⟨hy.1.le, hy.2.le⟩
  have hw := deriv_deriv_g_mem_Icc_gate ⟨hy.1.le, hy.2.le⟩
  have hJ : 4 - deriv g y ≠ 0 := by linarith only [hv.2]
  have hr : D.R y ∈ Icc (0 : ℝ) (1 / 100) := by
    constructor
    · change 0 ≤ (4 - g y) / (g y + 1) * Real.exp (-4 * (D.tMinus y - D.tPlus y))
      exact mul_nonneg (div_nonneg (by linarith only [hg.2])
        (by linarith only [hg.1])) (Real.exp_pos _).le
    · exact (linear_fast_weight_ratio_lt hg hgap).le
  change deriv (deriv D.Q) y - deriv (deriv D.R) y / deriv D.R y * deriv D.Q y < -260
  rw [hreg.relative_curvature_eq hy hJ]
  exact linear_fast_weight_curvature_lt ⟨hy.1.le, hy.2.le⟩ hg hv hw hr

end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
