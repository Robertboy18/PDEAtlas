/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.Models.Wave.DAlembert.ContinuousDerivative
public import PDE.Hyperbolic.Models.Wave.Duhamel.OneDimension.Construction

/-!
# First smoothing of continuous one-dimensional forcing

The d’Alembert retarded field is jointly C¹ for merely continuous forcing.
This supplies the first step in the classical nonlinear bootstrap.
-/

@[expose] public noncomputable section

open PDE.Common PDE.Analysis

namespace WaveEquation

/-- Merely continuous forcing produces a continuously differentiable retarded field. -/
theorem contDiff_one_dAlembertDuhamelSolution {f : ℝ^2 → ℝ} (hf : Continuous f) :
    ContDiff ℝ 1 (dAlembertDuhamelSolution f) := by
  let h (s r : ℝ) := f (timeSpaceCons (max 0 s) (EuclideanSpace.single (0 : Fin 1) r))
  let F (s : ℝ) (p : ℝ^2) := dAlembertFormula (fun _ ↦ 0) (h s) (p 1) (p 0)
  let L := (spaceTimeContinuousLinearEquiv 1).symm.toContinuousLinearMap
  have hh : Continuous (fun p : ℝ × ℝ ↦ h p.1 p.2) :=
    hf.comp ((contDiff_timeSpaceCons_uncurry 1 (m := 0)).continuous.comp
      ((continuous_const.max continuous_fst).prodMk
        ((PiLp.continuous_toLp 2 (fun _ : Fin 1 ↦ ℝ)).comp
          (continuous_pi fun i ↦ by
            fin_cases i
            simpa using (continuous_snd : Continuous (fun p : ℝ × ℝ ↦ p.2))))))
  have hc : Continuous (fun p : ℝ × ℝ^2 ↦ F p.1 p.2) :=
    continuous_dAlembert_zero_displacement_family hh
  have hD : Continuous (fun p : ℝ × ℝ^2 ↦ fderiv ℝ (F p.1) p.2) :=
    continuous_fderiv_dAlembert_zero_displacement_family hh
  have hd (s : ℝ) : Differentiable ℝ (F s) := fun p ↦
    (hasFDerivAt_dAlembertFormula (fun _ ↦ 0) (h s) (differentiable_const 0)
      (hh.comp (continuous_const.prodMk continuous_id)) p).differentiableAt
  have hdL (s : ℝ) : fderiv ℝ (F s ∘ L) = fun p ↦ (fderiv ℝ (F s) (L p)).comp L := by
    funext p
    simpa only [L.fderiv] using fderiv_comp p (hd s (L p)) L.differentiableAt
  have hDL : Continuous (fun p : ℝ × (ℝ^1 × ℝ) ↦ fderiv ℝ (F p.1 ∘ L) p.2) := by
    simp_rw [hdL]
    exact (hD.comp (continuous_fst.prodMk (L.continuous.comp continuous_snd))).clm_comp
      continuous_const
  have hreg := contDiff_one_retardedIntegral (fun s ↦ (hd s).comp L.differentiable)
    (hc.comp (continuous_fst.prodMk (L.continuous.comp continuous_snd))) hDL
  exact hreg.comp (spaceTimeContinuousLinearEquiv 1).contDiff

end WaveEquation
