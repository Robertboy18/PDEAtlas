/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.ParametricInterval
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Derivatives of retarded integrals

The forcing index is an integration variable, independent of the spatial and
age variables being differentiated. Joint continuity of the parameter
derivative suffices, with compact intervals supplying local bounds.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open MeasureTheory

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The oriented retarded integral, defined at signed times without extending the kernel by zero. -/
def retardedIntegral (F : ℝ → E × ℝ → V) (p : E × ℝ) : V :=
  ∫ s in (0 : ℝ)..p.2, F s (p.1, p.2 - s)

omit [NormedSpace ℝ E] in
/-- Continuous kernels have continuous retarded integrals, also at time zero. -/
theorem continuous_retardedIntegral
    {F : ℝ → E × ℝ → V}
    (hF : Continuous (fun p : ℝ × (E × ℝ) ↦ F p.1 p.2)) :
    Continuous (retardedIntegral F) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun (q : E × ℝ) (s : ℝ) ↦ F s (q.1, q.2 - s))
    (hF.comp (continuous_snd.prodMk
      (continuous_fst.fst.prodMk (continuous_fst.snd.sub continuous_snd)))) continuous_snd

variable [FiniteDimensional ℝ E] [CompleteSpace V]

/-- The derivative consists of the age-zero endpoint and the integral
of the spatial and age derivative. No derivative in the forcing index is used. -/
theorem hasFDerivAt_retardedIntegral
    {F : ℝ → E × ℝ → V}
    (hF : ∀ s, Differentiable ℝ (F s))
    (hcont : Continuous (fun p : ℝ × (E × ℝ) ↦ F p.1 p.2))
    (hD : Continuous (fun p : ℝ × (E × ℝ) ↦ fderiv ℝ (F p.1) p.2))
    (p : E × ℝ) :
    HasFDerivAt (retardedIntegral F)
      ((ContinuousLinearMap.snd ℝ E ℝ).smulRight (F p.2 (p.1, 0)) +
        retardedIntegral (fun s ↦ fderiv ℝ (F s)) p) p := by
  have hshift (s : ℝ) (q : E × ℝ) :
      HasFDerivAt (fun y : E × ℝ ↦ (y.1, y.2 - s))
        (ContinuousLinearMap.id ℝ (E × ℝ)) q := by
    simpa only [Prod.sub_def, sub_zero, id_eq] using
      (hasFDerivAt_id (𝕜 := ℝ) q).sub_const (0, s)
  have hd (q : E × ℝ) (s : ℝ) :
      HasFDerivAt (fun y : E × ℝ ↦ F s (y.1, y.2 - s))
        (fderiv ℝ (F s) (q.1, q.2 - s)) q := by
    simpa only [ContinuousLinearMap.comp_id, Function.comp_def] using
      (hF s (q.1, q.2 - s)).hasFDerivAt.comp q (hshift s q)
  change HasFDerivAt (fun q ↦ ∫ s in (0 : ℝ)..q.2, F s (q.1, q.2 - s))
    ((ContinuousLinearMap.snd ℝ E ℝ).smulRight (F p.2 (p.1, 0)) +
      ∫ s in (0 : ℝ)..p.2, fderiv ℝ (F s) (p.1, p.2 - s)) p
  simpa only [retardedIntegral, sub_self] using
    hasFDerivAt_intervalIntegral_moving_right_of_continuous
      (fun q s ↦ F s (q.1, q.2 - s))
      (fun q s ↦ fderiv ℝ (F s) (q.1, q.2 - s)) 0 Prod.snd
      (hcont.comp (continuous_snd.prodMk
        (continuous_fst.fst.prodMk (continuous_fst.snd.sub continuous_snd))))
      (hD.comp (continuous_snd.prodMk
        (continuous_fst.fst.prodMk (continuous_fst.snd.sub continuous_snd))))
      hd p (ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt

end PDE.Analysis
