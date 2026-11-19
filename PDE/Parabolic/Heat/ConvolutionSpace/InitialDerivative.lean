/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.ConvolutionSpace.Scaling
public import PDE.Parabolic.Heat.Kernel.Integrability
public import PDE.FDeriv.PartialDeriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Passing a derivative of the initial datum through heat evolution

For bounded `C¹` data with bounded first derivative, spatial differentiation
commutes with the heat convolution. The fixed-Gaussian representation places
the derivative on the datum; its uniform bound supplies an integrable majorant.
The identity also holds at nonpositive time under the initial-value convention.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open PDE (partialDeriv)
open scoped Topology

namespace HeatEquation

variable {n : ℕ}

/-- The derivative of `C¹` data with bounded derivative can be passed through the
fixed-Gaussian integral. The data grow at most linearly, and the Gaussian has a finite first
moment, so the data need not be bounded. -/
theorem hasFDerivAt_initialValueSolution_of_bounded_derivative
    (g : ℝ^n → ℝ) (hg : ContDiff ℝ 1 g)
    (hdgb : ∃ M, ∀ y, ‖fderiv ℝ g y‖ ≤ M) (x : ℝ^n) (t : ℝ) :
    HasFDerivAt (fun z ↦ initialValueSolution g z t)
      (∫ y : ℝ^n, fundamentalSolutionHeat (0 - y) 1 •
        fderiv ℝ g (x + Real.sqrt t • y)) x := by
  obtain ⟨D, hD⟩ := hdgb
  let K : ℝ^n → ℝ := fun y ↦ fundamentalSolutionHeat (0 - y) 1
  have hK : Integrable K :=
    (fundamentalSolutionHeat_integrable 1 zero_lt_one).comp_sub_left 0
  have hKpos (y : ℝ^n) : 0 ≤ K y :=
    (fundamentalSolutionHeat_pos (0 - y) 1 zero_lt_one).le
  have hg' : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  have hgrowth (z : ℝ^n) : ‖g z‖ ≤ ‖g 0‖ + D * ‖z‖ := by
    have h := convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun w _ ↦ hg.differentiable (by norm_num) w) (fun w _ ↦ hD w) (mem_univ 0) (mem_univ z)
    rw [sub_zero] at h
    linarith [norm_sub_norm_le (g z) (g 0)]
  have hmom : Integrable (fun y : ℝ^n ↦ ‖y‖ * K y) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h0 : (fun y : ℝ^0 ↦ ‖y‖ * K y) = 0 :=
        funext fun y ↦ by simp [Subsingleton.elim y 0]
      rw [h0]
      exact integrable_zero _ _ _
    have h2 : Integrable (fun w : ℝ^n ↦ ‖w‖ ^ 2 * fundamentalSolutionHeat w 1) :=
      Integrable.of_integral_ne_zero (by
        rw [integral_norm_sq_mul_fundamentalSolutionHeat_one]
        exact mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr hn.ne'))
    have h2' : Integrable (fun y : ℝ^n ↦ ‖y‖ ^ 2 * K y) := by
      simpa [K] using h2.comp_sub_left (0 : ℝ^n)
    refine (hK.add h2').mono' (continuous_norm.aestronglyMeasurable.mul hK.aestronglyMeasurable)
      (Eventually.of_forall fun y ↦ ?_)
    rw [norm_mul, norm_norm, Real.norm_of_nonneg (hKpos y)]
    have hy : ‖y‖ ≤ 1 + ‖y‖ ^ 2 := by nlinarith [sq_nonneg (‖y‖ - 1)]
    have := mul_le_mul_of_nonneg_right hy (hKpos y)
    simp only [Pi.add_apply]
    linarith
  have hmain : HasFDerivAt
      (fun z ↦ ∫ y : ℝ^n, K y * g (z + Real.sqrt t • y))
      (∫ y : ℝ^n, K y • fderiv ℝ g (x + Real.sqrt t • y)) x := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F' := fun z y ↦ K y • fderiv ℝ g (z + Real.sqrt t • y))
      (s := univ) (bound := fun y ↦ K y * D) (univ_mem)
    · exact Eventually.of_forall fun z ↦ hK.aestronglyMeasurable.mul
        (hg.continuous.comp (by fun_prop)).aestronglyMeasurable
    · refine ((hK.const_mul (‖g 0‖ + D * ‖x‖)).add (hmom.const_mul (D * Real.sqrt t))).mono'
        (hK.aestronglyMeasurable.mul (hg.continuous.comp (by fun_prop)).aestronglyMeasurable)
        (Eventually.of_forall fun y ↦ ?_)
      rw [norm_mul, Real.norm_of_nonneg (hKpos y)]
      have h1 := hgrowth (x + Real.sqrt t • y)
      have h2 : ‖x + Real.sqrt t • y‖ ≤ ‖x‖ + Real.sqrt t * ‖y‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      have h3 : ‖g (x + Real.sqrt t • y)‖ ≤ ‖g 0‖ + D * ‖x‖ + D * Real.sqrt t * ‖y‖ := by
        nlinarith [mul_le_mul_of_nonneg_left h2 hD0]
      have := mul_le_mul_of_nonneg_left h3 (hKpos y)
      simp only [Pi.add_apply]
      linarith
    · exact hK.aestronglyMeasurable.smul
        (hg'.comp (by fun_prop)).aestronglyMeasurable
    · exact Eventually.of_forall fun y z _ ↦ by
        rw [norm_smul, Real.norm_of_nonneg (hKpos y)]
        exact mul_le_mul_of_nonneg_left (hD _) (hKpos y)
    · exact hK.mul_const D
    · exact Eventually.of_forall fun y z _ ↦ by
        simpa only [ContinuousLinearMap.comp_id, id_eq, Function.comp_apply] using
          (((hg.differentiable (by norm_num) _).hasFDerivAt).comp z
            ((hasFDerivAt_id z).add_const (Real.sqrt t • y))).const_mul (K y)
  simpa only [initialValueSolution_eq_fixed_gaussian, K] using hmain

/-- Each spatial partial derivative commutes with heat evolution of `C¹` data
whose first derivative is bounded. -/
theorem partialDeriv_initialValueSolution_eq_initialValueSolution_partialDeriv
    (g : ℝ^n → ℝ) (hg : ContDiff ℝ 1 g)
    (hdgb : ∃ M, ∀ y, ‖fderiv ℝ g y‖ ≤ M) (x : ℝ^n) (t : ℝ) (i : Fin n) :
    (∂[i] (fun z ↦ initialValueSolution g z t)) x =
      initialValueSolution (∂[i] g) x t := by
  obtain ⟨D, hD⟩ := hdgb
  have hK := (fundamentalSolutionHeat_integrable (n := n) 1 zero_lt_one).comp_sub_left 0
  have hI : Integrable (fun y : ℝ^n ↦ fundamentalSolutionHeat (0 - y) 1 •
      fderiv ℝ g (x + Real.sqrt t • y)) :=
    hK.smul_bdd D
      ((hg.continuous_fderiv (by norm_num)).comp (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun y ↦ hD _)
  rw [partialDeriv, (hasFDerivAt_initialValueSolution_of_bounded_derivative
    g hg ⟨D, hD⟩ x t).fderiv, ContinuousLinearMap.integral_apply hI,
    initialValueSolution_eq_fixed_gaussian]
  rfl

end HeatEquation
