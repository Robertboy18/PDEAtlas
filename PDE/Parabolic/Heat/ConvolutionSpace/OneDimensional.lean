/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.ConvolutionSpace.Equation
public import PDE.Parabolic.Heat.ConvolutionSpace.JointSmoothness
public import PDE.Parabolic.Heat.ConvolutionSpace.InitialDerivative
public import PDE.FDeriv.SpaceTime
public import PDE.FDeriv.Calculus

/-!
# One-dimensional heat convolution in spacetime coordinates

For `n = 1`, the heat equation and differentiation-under-the-integral theorems for the
heat convolution are restated with the time and space coordinate derivatives on `ℝ²`.
-/

@[expose] public noncomputable section

open PDE (laplacian)
open PDE.Common

namespace HeatEquation

/-- The bounded-data heat convolution satisfies `vₜ = vₓₓ` in two spacetime coordinates. -/
theorem initialValueSolution_oneDimensional_heat_equation
    (g : ℝ^1 → ℝ) (hg : Continuous g) (hgb : ∃ M, ∀ y, |g y| ≤ M)
    (p : ℝ^2) (hp : 0 < p 0) :
    (∂[0] (fun q : ℝ^2 ↦ initialValueSolution g (spatialPartCLM 1 q) (q 0))) p =
      (∂[1] (∂[1]
        (fun q : ℝ^2 ↦ initialValueSolution g (spatialPartCLM 1 q) (q 0)))) p := by
  let v : ℝ^2 → ℝ := fun q ↦ initialValueSolution g (spatialPartCLM 1 q) (q 0)
  have hv (q : ℝ^2) (hq : 0 < q 0) : ContDiffAt ℝ 2 v q := by
    exact ((contDiffOn_initialValueSolution_spacetime g hg hgb).contDiffAt
      ((isOpen_lt continuous_const
        (EuclideanSpace.proj (0 : Fin 2)).continuous).mem_nhds hq)).of_le (by norm_num)
  have hslice : (fun x : ℝ^1 ↦ v (timeSpaceCons (p 0) x)) =
      fun x ↦ initialValueSolution g x (p 0) := by
    simp only [v, spatialPartCLM_timeSpaceCons, timeSpaceCons_zero]
  have hfirst : (∂[0] (fun x : ℝ^1 ↦ v (timeSpaceCons (p 0) x))) =
      fun x ↦ (∂[1] v) (timeSpaceCons (p 0) x) := by
    funext x
    exact PDE.partialDeriv_timeSpaceCons_spatial 0 v (p 0) x
      ((hv _ (by simpa using hp)).differentiableAt (by norm_num))
  have hsecond := PDE.partialDeriv_timeSpaceCons_spatial 0 (∂[1] v)
    (p 0) (spatialPartCLM 1 p)
    (by simpa only [timeSpaceCons_spatialPartCLM] using
      (PDE.contDiffAt_partialDeriv 1 (hv p hp) 1).differentiableAt (by norm_num))
  have htime := PDE.partialDeriv_timeSpaceCons_eq_deriv v (spatialPartCLM 1 p) (p 0)
    (by simpa only [timeSpaceCons_spatialPartCLM] using
      (hv p hp).differentiableAt (by norm_num))
  change (∂[0] v) p = (∂[1] (∂[1] v)) p
  have hheat := deriv_initialValueSolution_time_eq_laplacian
    g (spatialPartCLM 1 p) (p 0) hp hg hgb
  simp only [laplacian, Fin.sum_univ_one] at hheat
  rw [← hslice, hfirst] at hheat
  simpa only [timeSpaceCons_spatialPartCLM, v, spatialPartCLM_timeSpaceCons,
    timeSpaceCons_zero, Fin.succ_zero_eq_one] using htime.trans (hheat.trans hsecond)

/-- At positive time the spacetime spatial derivative is heat evolution of the
initial spatial derivative, under bounded `C¹` assumptions. -/
theorem partialDeriv_initialValueSolution_spacetime_of_bounded_derivative
    {n : ℕ} (g : ℝ^n → ℝ) (hg : ContDiff ℝ 1 g)
    (hgb : ∃ M, ∀ y, ‖g y‖ ≤ M) (hdgb : ∃ M, ∀ y, ‖fderiv ℝ g y‖ ≤ M)
    (p : ℝ^(n + 1)) (hp : 0 < p 0) (i : Fin n) :
    (∂[i.succ] (fun q : ℝ^(n + 1) ↦
      initialValueSolution g (spatialPartCLM n q) (q 0))) p =
        initialValueSolution (∂[i] g) (spatialPartCLM n p) (p 0) := by
  have hv := (contDiffOn_initialValueSolution_spacetime g hg.continuous hgb).contDiffAt
    ((isOpen_lt continuous_const
      (EuclideanSpace.proj (0 : Fin (n + 1))).continuous).mem_nhds hp)
  have h := PDE.partialDeriv_timeSpaceCons_spatial i
    (fun q : ℝ^(n + 1) ↦ initialValueSolution g (spatialPartCLM n q) (q 0))
    (p 0) (spatialPartCLM n p)
    (by simpa only [timeSpaceCons_spatialPartCLM] using hv.differentiableAt (by simp))
  simp only [spatialPartCLM_timeSpaceCons, timeSpaceCons_zero,
    timeSpaceCons_spatialPartCLM] at h
  rw [← h]
  exact partialDeriv_initialValueSolution_eq_initialValueSolution_partialDeriv
    g hg hdgb _ _ i

end HeatEquation
