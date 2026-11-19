/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.Constraints.Multiplier
public import PDE.Analysis.Calculus.IntegralPotential.LevelSets
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import CAS.ExactTactic

/-!
# A nonlinear integral constraint on the disk

The potential `s² + sin(s²)/4 - a`, for `a > 0`, has a linearly growing
derivative. A supported smooth bump and the intermediate value theorem prove
that its zero integral level is nonempty. The constrained Dirichlet minimizer
is nonzero and satisfies the nonlinear weak Euler–Lagrange equation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev

namespace PDE.Examples.CalculusOfVariations.Constraints

/-- A quadratic potential with a bounded oscillatory perturbation. -/
def oscillatoryPotential (a s : ℝ) : ℝ := s ^ 2 + (1 / 4) * Real.sin (s ^ 2) - a

/-- The derivative of the oscillatory potential. -/
def oscillatorySlope (s : ℝ) : ℝ := 2 * s + (1 / 2) * s * Real.cos (s ^ 2)

/-- The derivative of `oscillatoryPotential a` is `oscillatorySlope`. -/
theorem oscillatoryPotential_hasDerivAt (a s : ℝ) :
    HasDerivAt (oscillatoryPotential a) (oscillatorySlope s) s := by
  unfold oscillatoryPotential oscillatorySlope
  cas

/-- The potential is smooth at every real value. -/
theorem contDiff_oscillatoryPotential (a : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (oscillatoryPotential a) := by
  unfold oscillatoryPotential
  fun_prop

/-- The slope grows at most linearly: `|oscillatorySlope s| ≤ (5/2)(1 + |s|)`. -/
theorem oscillatorySlope_growth (s : ℝ) :
    |oscillatorySlope s| ≤ (5 / 2) * (1 + |s|) := by
  have hc := Real.abs_cos_le_one (s ^ 2)
  have ht := abs_add_le (2 * s) ((1 / 2) * s * Real.cos (s ^ 2))
  have hm := mul_le_mul_of_nonneg_left hc (abs_nonneg ((1 / 2 : ℝ) * s))
  norm_num [abs_mul] at ht hm
  unfold oscillatorySlope
  nlinarith [abs_nonneg s]

/-- The quadratic lower bound `(3/4) s² - a ≤ oscillatoryPotential a s`. -/
theorem oscillatoryPotential_lower (a s : ℝ) :
    (3 / 4) * s ^ 2 - a ≤ oscillatoryPotential a s := by
  have hs := Real.abs_sin_le_abs (x := s ^ 2)
  rw [abs_of_nonneg (sq_nonneg s)] at hs
  have hl := neg_abs_le (Real.sin (s ^ 2))
  unfold oscillatoryPotential
  nlinarith

/-- The geometric domain of the nonlinear example. -/
def disk : Set (ℝ^2) := Metric.ball 0 1

/-- A concrete radial smooth bump supported strictly inside the disk. -/
def diskBump : ContDiffBump (0 : ℝ^2) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- The bump as a compactly supported test function. -/
def diskTestFunction : TestFunctionOn 2 disk :=
  ⟨_root_.TestFunction.mk (diskBump : ℝ^2 → ℝ) diskBump.contDiff
    diskBump.hasCompactSupport (subset_univ _), by
      change tsupport (diskBump : ℝ^2 → ℝ) ⊆ Metric.ball 0 1
      rw [diskBump.tsupport_eq]
      exact Metric.closedBall_subset_ball (by norm_num [diskBump])⟩

/-- The bump is nonzero as an element of `L²`. -/
theorem baseCoordCLM_diskTestFunction_ne_zero :
    baseCoordCLM (testFunctionToH10 diskTestFunction) ≠ 0 := by
  intro h
  have hae := baseCoordCLM_testFunction_apply_ae diskTestFunction
  rw [h] at hae
  have hz : (diskBump : ℝ^2 → ℝ) =ᵐ[volume.restrict disk] 0 :=
    hae.symm.trans (Lp.coeFn_zero ℝ 2 (domainMeasure 2 disk))
  have heq := Measure.eqOn_open_of_ae_eq hz Metric.isOpen_ball
    diskBump.continuous.continuousOn continuous_const.continuousOn
  have hc := heq (show (0 : ℝ^2) ∈ disk from Metric.mem_ball_self (by norm_num))
  have hone : diskBump (0 : ℝ^2) = 1 :=
    diskBump.one_of_mem_closedBall (Metric.mem_closedBall_self diskBump.rIn_pos.le)
  simp only [hone, Pi.zero_apply, one_ne_zero] at hc

/-- The disk has finite positive volume, so a negative constant has negative
integral. -/
theorem disk_volume_real_pos : 0 < (domainMeasure 2 disk).real univ := by
  change 0 < (volume.restrict disk univ).toReal
  rw [Measure.restrict_apply_univ]
  exact ENNReal.toReal_pos (Metric.isOpen_ball.measure_pos volume
    (Metric.nonempty_ball.mpr (by norm_num))).ne'
    (Metric.isBounded_ball.measure_lt_top (μ := volume)).ne

/-- Scaling a smooth bump gives a point on the zero constraint level. -/
theorem oscillatoryPotential_disk_feasible (a : ℝ) (ha : 0 < a) :
    {u : H¹₀(disk) | integralConstraint (oscillatoryPotential a) u = 0}.Nonempty := by
  let : IsFiniteMeasure (domainMeasure 2 disk) :=
    ⟨by simpa [domainMeasure, disk] using
      (Metric.isBounded_ball (x := (0 : ℝ^2)) (r := 1)).measure_lt_top (μ := volume)⟩
  have hz : (domainMeasure 2 disk).real univ * oscillatoryPotential a 0 < 0 := by
    simpa [oscillatoryPotential] using
      mul_neg_of_pos_of_neg disk_volume_real_pos (neg_neg_of_pos ha)
  obtain ⟨t, _, ht⟩ := exists_smul_integral_eq_zero_of_quadratic_lower
    (by norm_num : (0 : ℝ) ≤ 5 / 2) (oscillatoryPotential_hasDerivAt a)
    oscillatorySlope_growth hz (by norm_num : (0 : ℝ) < 3 / 4)
    (oscillatoryPotential_lower a)
    (baseCoordCLM (testFunctionToH10 diskTestFunction)) baseCoordCLM_diskTestFunction_ne_zero
  refine ⟨t • testFunctionToH10 diskTestFunction, ?_⟩
  simpa only [mem_ofPred_eq, integralConstraint, map_smul] using ht

/-- A nonzero constrained minimizer on the disk, with its multiplier and the weak
equation against every zero-boundary test function. -/
theorem exists_nonzero_oscillatory_minimizer (a : ℝ) (ha : 0 < a) :
    ∃ (u : H¹₀(disk)) (lam : ℝ), u ≠ 0 ∧
      integralConstraint (oscillatoryPotential a) u = 0 ∧
      IsMinOn (dirichletEnergy 0)
        {v : H¹₀(disk) | integralConstraint (oscillatoryPotential a) v = 0} u ∧
      ∀ v : H¹₀(disk),
        (∫ x, inner ℝ (∇ (u : H¹(disk)) x) (∇ (v : H¹(disk)) x) ∂domainMeasure 2 disk) =
          lam * ∫ x, oscillatorySlope (baseCoordCLM u x) * baseCoordCLM v x
            ∂domainMeasure 2 disk := by
  obtain ⟨u, lam, hu, hmin, heq⟩ := exists_minimizer_multiplier_integralConstraint
    (n := 2) (Ω := disk)
    (by norm_num : 0 < 2) Metric.isOpen_ball Metric.isBounded_ball
    (contDiff_oscillatoryPotential a)
    (fun s ↦ by rw [(oscillatoryPotential_hasDerivAt a s).deriv]; exact oscillatorySlope_growth s)
    (oscillatoryPotential_disk_feasible a ha)
  refine ⟨u, lam, ?_, hu, hmin, ?_⟩
  · intro h
    rw [h, integralConstraint_zero] at hu
    have hz := mul_neg_of_pos_of_neg disk_volume_real_pos (neg_neg_of_pos ha)
    rw [show oscillatoryPotential a 0 = -a by simp [oscillatoryPotential]] at hu
    exact hz.ne hu
  · intro v
    simpa only [(oscillatoryPotential_hasDerivAt a _).deriv, gradientCLM,
      ContinuousLinearMap.comp_apply, h10SubtypeL_apply] using heq v

end PDE.Examples.CalculusOfVariations.Constraints
