/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Supporting hyperplanes of differentiable convex functions

A derivative of a convex real-valued function supports its graph. The same
inequality bounds the function below by a norm cone and makes its derivative
monotone in the dual pairing. No inner product or finite dimension is needed.
-/

@[expose] public section

namespace PDE.Analysis

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The first-order supporting-hyperplane inequality for a differentiable
convex functional on an admissible set. The derivative is taken at `u`, and
only the segment from `u` to `v` is used. -/
theorem fderiv_apply_sub_le_sub_of_convex
    {F : E → ℝ} {A : Set E} {u : E} {DF : E →L[ℝ] ℝ}
    (hconvex : ConvexOn ℝ A F)
    (hF : HasFDerivAt F DF u) (v : E) (hu : u ∈ A) (hv : v ∈ A) :
    DF (v - u) ≤ F v - F u := by
  let g : ℝ →ᵃ[ℝ] E := AffineMap.lineMap (k := ℝ) u v
  have hconvexLine : ConvexOn ℝ (g ⁻¹' A) (F ∘ g) :=
    hconvex.comp_affineMap g
  have hFat : HasFDerivAt F DF (g 0) := by
    simpa only [g, AffineMap.lineMap_apply_zero] using hF
  have hderivLine : HasDerivAt (F ∘ g) (DF (v - u)) 0 := by
    simpa only using
      hFat.comp_hasDerivAt (0 : ℝ)
        (AffineMap.hasDerivAt_lineMap (a := u) (b := v))
  have hslope : DF (v - u) ≤ slope (F ∘ g) 0 1 :=
    hconvexLine.le_slope_of_hasDerivAt
      (by simpa [g] using hu) (by simpa [g] using hv) zero_lt_one hderivLine
  simpa [slope_def_field, g] using hslope

/-- A differentiable convex functional is bounded below by the norm cone
determined by any one of its supporting hyperplanes. -/
theorem sub_norm_mul_norm_sub_le_of_convex_of_hasFDerivAt
    {F : E → ℝ} {u : E} {DF : E →L[ℝ] ℝ}
    (hconvex : ConvexOn ℝ Set.univ F)
    (hF : HasFDerivAt F DF u) (v : E) :
    F u - ‖DF‖ * ‖v - u‖ ≤ F v := by
  have hsupport :=
    fderiv_apply_sub_le_sub_of_convex hconvex hF v (mem_univ _) (mem_univ _)
  have hdualAbs :
      |DF (v - u)| ≤ ‖DF‖ * ‖v - u‖ := by
    rw [← Real.norm_eq_abs]
    exact DF.le_opNorm (v - u)
  have hdualLower :
      -(‖DF‖ * ‖v - u‖) ≤ DF (v - u) := by
    calc
      -(‖DF‖ * ‖v - u‖) ≤ -|DF (v - u)| :=
        neg_le_neg hdualAbs
      _ ≤ DF (v - u) := neg_abs_le _
  linarith

/-- The derivative of a convex functional is monotone in the dual pairing. -/
theorem sub_apply_sub_nonneg_of_convex_of_hasFDerivAt
    {F : E → ℝ} {u v : E} {DFu DFv : E →L[ℝ] ℝ}
    (hconvex : ConvexOn ℝ Set.univ F)
    (hu : HasFDerivAt F DFu u)
    (hv : HasFDerivAt F DFv v) :
    0 ≤ (DFu - DFv) (u - v) := by
  have huv := fderiv_apply_sub_le_sub_of_convex hconvex hu v (mem_univ _) (mem_univ _)
  have hvu := fderiv_apply_sub_le_sub_of_convex hconvex hv u (mem_univ _) (mem_univ _)
  rw [map_sub] at huv hvu
  simp only [sub_apply, map_sub]
  linarith

end PDE.Analysis
