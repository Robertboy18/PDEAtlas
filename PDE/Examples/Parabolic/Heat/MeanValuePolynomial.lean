/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.MeanValue.Classical
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# A nonzero caloric polynomial at the terminal time

For `u(x,t) = x² + 2t + 1`, the closed heat ball of radius one centered at
`(0,1)` lies in `ℝ × (0,1]`. We prove the spatial and time derivatives, the heat
equation, and this containment. The mean value theorem for solutions that are `C²` in
space and `C¹` in time then gives the weighted integral `12`.
-/

@[expose] public noncomputable section

namespace PDE.Examples.HeatMeanValue

open HeatEquation MeasureTheory Set
open PDE.Common

/-- A caloric polynomial with nonzero spatial curvature and time derivative. -/
def polynomial (x : ℝ^1) (t : ℝ) : ℝ := x 0 ^ 2 + 2 * t + 1

/-- The first spatial derivative of the caloric polynomial. -/
def polynomialDx (p : ℝ^1 × ℝ) : ℝ^1 →L[ℝ] ℝ :=
  (2 * p.1 0) • EuclideanSpace.proj 0

/-- Its constant bilinear spatial Hessian. -/
def polynomialDxx : ℝ^1 →L[ℝ] ℝ^1 →L[ℝ] ℝ :=
  ((2 : ℝ) • (EuclideanSpace.proj 0 : ℝ^1 →L[ℝ] ℝ)).smulRight (EuclideanSpace.proj 0)

/-- The terminal closed-region mean value is nonzero. The derivative
identities are supplied by checked symbolic certificates. -/
theorem polynomial_terminal_meanValue :
    (∫ p in insert (timeSpaceCons 1 (0 : ℝ^1))
      {p | 1 ≤ shiftedFundamentalSolutionHeat 0 (spatialPart p) 1 (time p)},
      heatBallWeight 0 1 p * spaceTimeUncurry polynomial p) = 12 := by
  have hspace (p : ℝ^1 × ℝ) :
      HasFDerivAt (fun y ↦ polynomial y p.2) (polynomialDx p) p.1 := by
    have h : HasDerivAt (fun y : ℝ ↦ y ^ 2 + 2 * p.2 + 1)
        (2 * p.1 0) (p.1 0) := by
      cas
    simpa only [polynomial, polynomialDx, Function.comp_def, EuclideanSpace.coe_proj] using
      h.comp_hasFDerivAt (f := fun y : ℝ^1 ↦ y 0) p.1
        (EuclideanSpace.proj (0 : Fin 1) : ℝ^1 →L[ℝ] ℝ).hasFDerivAt
  have hhessian (p : ℝ^1 × ℝ) :
      HasFDerivAt (fun y ↦ polynomialDx (y, p.2)) polynomialDxx p.1 := by
    have h : HasFDerivAt (fun y : ℝ^1 ↦ 2 * y 0)
        ((2 : ℝ) • (EuclideanSpace.proj 0 : ℝ^1 →L[ℝ] ℝ)) p.1 :=
      (EuclideanSpace.proj (0 : Fin 1) : ℝ^1 →L[ℝ] ℝ).hasFDerivAt.const_mul 2
    simpa only [polynomialDx, polynomialDxx] using
      h.smul_const (EuclideanSpace.proj (0 : Fin 1) : ℝ^1 →L[ℝ] ℝ)
  have htime (p : ℝ^1 × ℝ) : HasDerivAt (polynomial p.1) 2 p.2 := by
    unfold polynomial
    cas
  have hnative (x : ℝ^1) (t : ℝ) : heatParabolicOperator polynomial x t = 0 := by
    unfold heatParabolicOperator polynomial
    cas
  have hu : Continuous (Function.uncurry polynomial) := by unfold polynomial; fun_prop
  have hDx : Continuous polynomialDx := by unfold polynomialDx; fun_prop
  have hclosure : closure (heatBall (0 : ℝ^1) 1 1) ⊆
      {p | spatialPart p ∈ (univ : Set (ℝ^1)) ∧ time p ∈ Ioc 0 1} := by
    have hclosed : IsClosed {p : SpaceTime 1 | time p ∈ Icc (1 - 1 / (4 * Real.pi)) 1} :=
      isClosed_Icc.preimage (timeCLM 1).continuous
    have hsub : heatBall (0 : ℝ^1) 1 1 ⊆
        {p : SpaceTime 1 | time p ∈ Icc (1 - 1 / (4 * Real.pi)) 1} := by
      intro p hp
      simpa only [one_pow, mem_ofPred_eq] using
        Ioo_subset_Icc_self (time_mem_Ioo_of_mem_heatBall (by norm_num) zero_lt_one hp)
    intro p hp
    have htimeBound := closure_minimal hsub hclosed hp
    refine ⟨mem_univ _, ?_, htimeBound.2⟩
    have hmargin : 0 < 1 - 1 / (4 * Real.pi) := by
      have hpi := Real.one_le_pi_div_two
      rw [sub_pos, div_lt_one (by positivity)]
      linarith
    exact hmargin.trans_le htimeBound.1
  obtain ⟨_, hmean⟩ := heatBall_meanValue_of_space_time_derivatives
    (by norm_num : 0 < 1) isOpen_univ (T := 1)
    hu.continuousOn hDx.continuousOn (Dt := fun _ ↦ 2) continuousOn_const
    (Dxx := fun _ ↦ polynomialDxx) continuousOn_const
    (fun p _ ↦ hspace p) (fun p _ ↦ (htime p).hasDerivWithinAt)
    (fun p _ ↦ hhessian p) (fun x _ t _ ↦ hnative x t)
    0 1 zero_lt_one hclosure
  rw [closure_heatBall_eq_insert_pole (by norm_num) zero_lt_one] at hmean
  norm_num [polynomial] at hmean
  exact hmean

end PDE.Examples.HeatMeanValue
