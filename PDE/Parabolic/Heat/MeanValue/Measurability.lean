/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.MeanValue.HeatBall
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Measurability of heat balls

The Euclidean heat kernel is jointly
measurable in space and time, including its zero extension to nonpositive
time. Composing with LeanPDE's continuous spacetime projections gives
measurability of the shifted kernel and Watson weight.

## Main results

* `measurable_fundamentalSolutionHeat`: joint measurability of the heat kernel.
* `measurable_shiftedFundamentalSolutionHeat`: measurability of the shifted
  kernel on canonical spacetime.
* `measurable_heatBallWeight`: measurability of Watson's heat-ball weight.
* `measurableSet_heatBall`: heat balls are measurable sets.
-/

@[expose] public section

open PDE (SpaceTime time)

noncomputable section

namespace HeatEquation

open PDE.Common

variable {n : ℕ}

/-- The zero-extended Euclidean heat kernel is jointly measurable in space and time. -/
theorem measurable_fundamentalSolutionHeat :
    Measurable fun p : ℝ^n × ℝ ↦
      fundamentalSolutionHeat (n := n) p.1 p.2 := by
  let g : ℝ^n × ℝ → ℝ := fun p ↦
    if p.2 ≤ 0 then 0
    else
      Real.exp
          (Real.log (4 * Real.pi * p.2) * (-(n : ℝ) / 2)) *
        Real.exp (-(‖p.1‖ ^ 2 / (4 * p.2)))
  have hg : Measurable g := by
    unfold g
    apply Measurable.ite
    · exact measurableSet_le measurable_snd measurable_const
    · exact measurable_const
    · have hbase :
          Measurable fun p : ℝ^n × ℝ ↦ 4 * Real.pi * p.2 :=
        measurable_const.mul measurable_snd
      have hscale :
          Measurable fun p : ℝ^n × ℝ ↦
            Real.exp
              (Real.log (4 * Real.pi * p.2) * (-(n : ℝ) / 2)) :=
        (hbase.log.mul measurable_const).exp
      have hgaussian :
          Measurable fun p : ℝ^n × ℝ ↦
            Real.exp (-(‖p.1‖ ^ 2 / (4 * p.2))) :=
        (((measurable_fst.norm.pow_const 2).div
          (measurable_const.mul measurable_snd)).neg).exp
      exact hscale.mul hgaussian
  convert hg using 1
  funext p
  by_cases hp : p.2 ≤ 0
  · simp [g, fundamentalSolutionHeat, hp]
  · have ht : 0 < p.2 := lt_of_not_ge hp
    have hbase : 0 < 4 * Real.pi * p.2 := by positivity
    simp [g, fundamentalSolutionHeat, hp,
      Real.rpow_def_of_pos hbase]

/-- The heat kernel shifted by a fixed spacetime pole is measurable on spacetime. -/
theorem measurable_shiftedFundamentalSolutionHeat (x : ℝ^n) (t : ℝ) :
    Measurable fun p : SpaceTime n ↦
      shiftedFundamentalSolutionHeat x (spatialPart p) t (time p) := by
  have hspace : Measurable fun p : SpaceTime n ↦ spatialPart p := by
    have hfun :
        (fun p : SpaceTime n ↦ spatialPart p) =
          fun p ↦ spatialPartCLM n p := by
      funext p
      exact (spatialPartCLM_eq_spatialPart n p).symm
    rw [hfun]
    exact (spatialPartCLM n).continuous.measurable
  have htime : Measurable fun p : SpaceTime n ↦ time p := by
    have hfun :
        (fun p : SpaceTime n ↦ time p) =
          fun p ↦ timeCLM n p := by
      funext p
      exact (timeCLM_apply n p).symm
    rw [hfun]
    exact (timeCLM n).continuous.measurable
  change Measurable
    ((fun q : ℝ^n × ℝ ↦
        fundamentalSolutionHeat (n := n) q.1 q.2) ∘
      fun p : SpaceTime n ↦
        (x - spatialPart p, t - time p))
  exact
    (measurable_fundamentalSolutionHeat (n := n)).comp
      ((measurable_const.sub hspace).prodMk
        (measurable_const.sub htime))

/-- Watson's heat-ball weight is measurable on spacetime. -/
theorem measurable_heatBallWeight (x : ℝ^n) (t : ℝ) :
    Measurable (heatBallWeight x t) := by
  have hspace : Measurable fun p : SpaceTime n ↦ spatialPart p := by
    have hfun :
        (fun p : SpaceTime n ↦ spatialPart p) =
          fun p ↦ spatialPartCLM n p := by
      funext p
      exact (spatialPartCLM_eq_spatialPart n p).symm
    rw [hfun]
    exact (spatialPartCLM n).continuous.measurable
  have htime : Measurable fun p : SpaceTime n ↦ time p := by
    have hfun :
        (fun p : SpaceTime n ↦ time p) =
          fun p ↦ timeCLM n p := by
      funext p
      exact (timeCLM_apply n p).symm
    rw [hfun]
    exact (timeCLM n).continuous.measurable
  unfold heatBallWeight
  exact ((measurable_const.sub hspace).norm.pow_const 2).div
    ((measurable_const.sub htime).pow_const 2)

/-- Every heat ball is a measurable subset of canonical spacetime. -/
theorem measurableSet_heatBall (x : ℝ^n) (t r : ℝ) :
    MeasurableSet (heatBall x t r) := by
  simpa only [heatBall] using
    (measurableSet_lt measurable_const
      (measurable_shiftedFundamentalSolutionHeat (n := n) x t))

end HeatEquation
