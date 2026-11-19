/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Harnack.Classical
import CAS.ExactTactic

/-!
# Harnack's inequality with space-time dependent coefficients

On the whole real line, the coefficient `2 + sin(x+t)` is uniformly
elliptic, the drift is one and the potential `sin(x+t)` changes sign.
The solution `exp(x+t)` is unbounded in space. We check the equation, the
derivatives of the solution, and the terminal-time Harnack comparison on `[-1,1]`.
-/

@[expose] public noncomputable section

namespace PDE.Examples.Parabolic.Harnack

open PDE.Analysis ParabolicMaximum ParabolicHarnack Set Metric
open scoped RealInnerProductSpace

/-- The nonconstant uniformly elliptic one-dimensional coefficient. -/
def principal (x : ℝ^1) (t : ℝ) : Matrix (Fin 1) (Fin 1) ℝ :=
  fun _ _ ↦ 2 + Real.sin (x 0 + t)

/-- The signed, nonconstant potential. -/
def potential (x : ℝ^1) (t : ℝ) : ℝ := Real.sin (x 0 + t)

/-- The explicit positive solution. -/
def solution (x : ℝ^1) (t : ℝ) : ℝ := Real.exp (x 0 + t)

/-- Its first spatial derivative. -/
def spaceJet (p : ℝ^1 × ℝ) : ℝ^1 →L[ℝ] ℝ :=
  solution p.1 p.2 • EuclideanSpace.proj 0

/-- Its second spatial derivative, as a bilinear map. -/
def spaceHessian (p : ℝ^1 × ℝ) : ℝ^1 →L[ℝ] ℝ^1 →L[ℝ] ℝ :=
  (spaceJet p).smulRight (EuclideanSpace.proj 0)

/-- Spatial differentiation of the explicit exponential solution. -/
theorem hasFDerivAt_solution (x : ℝ^1) (t : ℝ) :
    HasFDerivAt (fun y ↦ solution y t) (spaceJet (x, t)) x := by
  have h : HasDerivAt (fun s : ℝ ↦ Real.exp (s + t)) (Real.exp (x 0 + t)) (x 0) := by
    cas
  simpa only [solution, spaceJet, Function.comp_def, EuclideanSpace.coe_proj] using
    h.comp_hasFDerivAt (f := fun y : ℝ^1 ↦ y 0) x
      (EuclideanSpace.proj (0 : Fin 1) : ℝ^1 →L[ℝ] ℝ).hasFDerivAt

/-- Differentiating the first jet gives the stated bilinear Hessian. -/
theorem hasFDerivAt_spaceJet (x : ℝ^1) (t : ℝ) :
    HasFDerivAt (fun y ↦ spaceJet (y, t)) (spaceHessian (x, t)) x := by
  simpa only [spaceJet, spaceHessian] using
    (hasFDerivAt_solution x t).smul_const
      (EuclideanSpace.proj (0 : Fin 1) : ℝ^1 →L[ℝ] ℝ)

/-- The checked first time derivative of the exponential solution. -/
theorem hasDerivAt_solution (x : ℝ^1) (t : ℝ) :
    HasDerivAt (solution x) (solution x t) t := by
  unfold solution
  cas

/-- The space-time dependent coefficients cancel in the residual. -/
theorem solution_native_equation (x : ℝ^1) (t : ℝ) :
    matrixParabolicOperator principal (fun _ _ ↦ EuclideanSpace.single 0 1)
      potential solution x t = 0 := by
  rw [matrixParabolicOperator_eq_of_hasDerivAt _ _ _
    (Filter.Eventually.of_forall fun y ↦ hasFDerivAt_solution y t)
    (hasFDerivAt_spaceJet x t) (hasDerivAt_solution x t)]
  simp only [principal, spaceHessian, spaceJet, potential, solution,
    Fin.sum_univ_one, ContinuousLinearMap.smulRight_apply,
    smul_apply, EuclideanSpace.coe_proj, PiLp.single_apply,
    ite_true, smul_eq_mul, mul_one]
  cas

/-- The principal coefficient has the uniform ellipticity constant one. -/
theorem principal_uniformly_elliptic (x : ℝ^1) (t : ℝ) (w : ℝ^1) :
    ‖w‖ ^ 2 ≤ ⟪w, (principal x t).toEuclideanLin w⟫ := by
  rw [inner_toEuclideanLin_self, EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_one, principal]
  have hs := Real.neg_one_le_sin (x 0 + t)
  nlinarith [sq_nonneg (w 0)]

/-- Harnack's inequality in its supremum/infimum form for the explicit solution, with the
later time equal to the terminal time. -/
theorem variable_coefficients_terminal_harnack :
    ∃ C : ℝ, 0 < C ∧
      (∀ x ∈ closedBall (0 : ℝ^1) 1, ∀ y ∈ closedBall (0 : ℝ^1) 1,
        solution x (1 / 2) ≤ C * solution y 1) ∧
      sSup ((fun x ↦ solution x (1 / 2)) '' ball (0 : ℝ^1) 1) ≤
        C * sInf ((fun x ↦ solution x 1) '' ball (0 : ℝ^1) 1) := by
  have hclosure : closure (ball (0 : ℝ^1) 1) = closedBall 0 1 :=
    closure_ball _ (by norm_num)
  obtain ⟨C, hC, hcompare⟩ := exists_harnack_constant_of_space_time_derivatives
    (U := univ) (V := ball (0 : ℝ^1) 1)
    isOpen_univ isBounded_ball.isCompact_closure (convex_ball _ _).isPreconnected
    (subset_univ _)
    (T := 1) (s := 1 / 2) (t := 1) (by norm_num) (by norm_num) le_rfl
    (a := principal) (d := fun _ _ ↦ EuclideanSpace.single 0 1) (c := potential)
    (by unfold principal; fun_prop) continuousOn_const
    (by unfold potential; fun_prop)
    (fun _ _ ↦ by ext i j; rfl)
    ⟨1, zero_lt_one, by
      intro p _ w
      simpa only [one_mul] using principal_uniformly_elliptic p.1 p.2 w⟩
  have hu : Continuous (Function.uncurry solution) := by unfold solution; fun_prop
  have hDx : Continuous spaceJet := by unfold spaceJet; exact hu.smul continuous_const
  have hDxx : Continuous spaceHessian :=
    isBoundedBilinearMap_smulRight.continuous.comp (hDx.prodMk continuous_const)
  have hresult := hcompare solution spaceJet (Function.uncurry solution) spaceHessian
    hu.continuousOn hDx.continuousOn hu.continuousOn hDxx.continuousOn
    (fun p _ ↦ hasFDerivAt_solution p.1 p.2)
    (fun p _ ↦ hasFDerivAt_spaceJet p.1 p.2)
    (fun p _ ↦ hasDerivAt_solution p.1 p.2)
    (fun p _ ↦ (Real.exp_pos _).le) (fun p _ ↦ solution_native_equation p.1 p.2)
  exact ⟨C, hC, by simpa only [hclosure] using hresult.1, hresult.2⟩

end PDE.Examples.Parabolic.Harnack
