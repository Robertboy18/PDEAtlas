/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Trace
public import PDE.Analysis.Calculus.Divergence

/-!
# Coordinate divergence and the trace of the derivative

At differentiability points, the coordinate divergence used by the Euclidean
ball integration theorem equals the basis-independent trace.
-/

@[expose] public section

namespace PDE.Analysis

variable {n : ℕ}

/-- The coordinate divergence is the trace of the Fréchet derivative
at every differentiability point. -/
theorem divergence_eq_trace_fderiv
    {F : ℝ^n → ℝ^n} {x : ℝ^n} (hF : DifferentiableAt ℝ F x) :
    ∇· F x = LinearMap.trace ℝ (ℝ^n) (fderiv ℝ F x).toLinearMap := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin n) ℝ)]
  unfold divergence
  apply Finset.sum_congr rfl
  intro i _
  rw [EuclideanSpace.basisFun_inner, EuclideanSpace.basisFun_apply]
  have hcoord : HasFDerivAt (fun y ↦ F y i)
      ((EuclideanSpace.proj i).comp (fderiv ℝ F x)) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x hF.hasFDerivAt
  rw [partialDeriv, hcoord.fderiv]
  rfl

end PDE.Analysis
