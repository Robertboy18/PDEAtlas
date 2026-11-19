/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.InnerProductSpace.Euclidean.CoordinateProjection
public import PDE.FDeriv.Calculus

/-!
# Calculus of constant coordinate lifts

A function independent of the last coordinate retains its original Laplacian.
The first derivative identities apply to every differentiable function; only
the second-derivative identity requires `C²` regularity.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

variable {n : ℕ}

/-- Retained-coordinate partial derivatives commute with a constant lift. -/
theorem partialDeriv_comp_coordinateProjection {f : ℝ^n → ℝ} (hf : Differentiable ℝ f)
    (i : Fin n) :
    (∂[i.castSucc] (f ∘ coordinateProjection)) =
      (∂[i] f) ∘ coordinateProjection := by
  funext y
  simp only [partialDeriv, fderiv_comp y (hf _) coordinateProjection.differentiableAt,
    coordinateProjection.fderiv, ContinuousLinearMap.comp_apply, Function.comp_apply,
    coordinateProjection_single_castSucc i]

/-- The derivative in the suppressed coordinate vanishes. -/
theorem partialDeriv_last_comp_coordinateProjection {f : ℝ^n → ℝ}
    (hf : Differentiable ℝ f) :
    (∂[(Fin.last n)] (f ∘ coordinateProjection)) = fun _ ↦ 0 := by
  funext y
  simp only [partialDeriv, fderiv_comp y (hf _) coordinateProjection.differentiableAt,
    coordinateProjection.fderiv, ContinuousLinearMap.comp_apply,
    coordinateProjection_single_last, map_zero]

/-- A constant lift has exactly the retained-coordinate Laplacian. -/
theorem laplacian_comp_coordinateProjection {f : ℝ^n → ℝ} (hf : ContDiff ℝ 2 f) (y : ℝ^(n + 1)) :
    laplacian (f ∘ coordinateProjection) y = laplacian f (coordinateProjection y) := by
  have hd := hf.differentiable (by norm_num)
  have he (i : Fin n) :
      (∂[i.castSucc] (∂[i.castSucc] (f ∘ coordinateProjection))) =
        (∂[i] (∂[i] f)) ∘ coordinateProjection := by
    rw [partialDeriv_comp_coordinateProjection hd i,
      partialDeriv_comp_coordinateProjection
        ((contDiff_partialDeriv_of_succ (m := 1) hf).differentiable one_ne_zero) i]
  simp only [laplacian, Fin.sum_univ_castSucc]
  simp_rw [he, partialDeriv_last_comp_coordinateProjection hd]
  simp only [Function.comp_apply, partialDeriv_const, add_zero]

end PDE.Analysis
