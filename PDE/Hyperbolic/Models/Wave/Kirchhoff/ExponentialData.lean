/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Laplacian of exponentially separated data

The exponential of the second coordinate is an eigenfunction of the
second transverse derivative. A function `exp Z * h Y`, independent of the
third coordinate, therefore satisfies `Δf = ∂Y∂Yf + f`.
-/

@[expose] public noncomputable section

namespace WaveEquation

/-- The first derivative of separated data has contributions only in the
profile direction and the exponential direction. -/
theorem partialDeriv_exp_mul_comp_zero {h : ℝ → ℝ} {x : ℝ^3}
    (hh : DifferentiableAt ℝ h (x 0)) (i : Fin 3) :
    (∂[i] (fun y : ℝ^3 ↦ Real.exp (y 1) * h (y 0))) x =
      (if i = 1 then Real.exp (x 1) * h (x 0) else 0) +
        (if i = 0 then Real.exp (x 1) * deriv h (x 0) else 0) := by
  have hexp : DifferentiableAt ℝ (fun y : ℝ^3 ↦ Real.exp (y 1)) x :=
    Real.differentiableAt_exp.comp x (EuclideanSpace.proj 1 : ℝ^3 →L[ℝ] ℝ).differentiableAt
  have hprofile : DifferentiableAt ℝ (fun y : ℝ^3 ↦ h (y 0)) x :=
    hh.comp x (EuclideanSpace.proj 0 : ℝ^3 →L[ℝ] ℝ).differentiableAt
  rw [PDE.partialDeriv_mul hexp hprofile, PDE.partialDeriv_comp_coord i 1 Real.differentiableAt_exp,
    PDE.partialDeriv_comp_coord i 0 hh]
  simp [smul_eq_mul, ite_mul, mul_ite]

/-- The total coordinate Laplacian of separated differentiable data reduces to its repeated
profile derivative plus the data itself. With `C²` data this is the classical identity.
No support or growth condition is needed. -/
theorem laplacian_exp_mul_comp_zero {h : ℝ → ℝ} (hh : Differentiable ℝ h) :
    PDE.laplacian (fun p : ℝ^3 ↦ Real.exp (p 1) * h (p 0)) = fun p ↦
      (∂[0] (∂[0] (fun y : ℝ^3 ↦ Real.exp (y 1) * h (y 0)))) p + Real.exp (p 1) * h (p 0) := by
  have hone : (∂[1] (fun p : ℝ^3 ↦ Real.exp (p 1) * h (p 0))) =
      fun p : ℝ^3 ↦ Real.exp (p 1) * h (p 0) := by
    funext p
    simpa using partialDeriv_exp_mul_comp_zero (hh (p 0)) 1
  have htwo : (∂[2] (fun p : ℝ^3 ↦ Real.exp (p 1) * h (p 0))) =
      fun _ ↦ 0 := by
    funext p
    simpa using partialDeriv_exp_mul_comp_zero (hh (p 0)) 2
  funext p
  simp [PDE.laplacian, Fin.sum_univ_succ, hone, htwo]

end WaveEquation
