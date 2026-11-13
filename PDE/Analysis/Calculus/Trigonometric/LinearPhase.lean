/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Derivative bounds for trigonometric linear phases

Composing sine or cosine with a continuous linear functional costs one
factor of its operator norm per derivative. The bounds hold in arbitrary
real normed spaces and include derivative order zero.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every differential of a sine with linear phase is bounded by the
corresponding power of the phase's operator norm. -/
theorem norm_iteratedFDeriv_sin_linear_le
    (L : E →L[ℝ] ℝ) (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k (fun y ↦ Real.sin (L y)) x‖ ≤ ‖L‖ ^ k := by
  rw [show (fun y ↦ Real.sin (L y)) = Real.sin ∘ L from rfl,
    L.iteratedFDeriv_comp_right (n := k) Real.contDiff_sin x le_rfl]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact (mul_le_mul_of_nonneg_right (Real.abs_iteratedDeriv_sin_le_one k (L x))
    (by positivity)).trans_eq (one_mul _)

/-- The same operator norm bound holds for every differential of cosine. -/
theorem norm_iteratedFDeriv_cos_linear_le
    (L : E →L[ℝ] ℝ) (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k (fun y ↦ Real.cos (L y)) x‖ ≤ ‖L‖ ^ k := by
  rw [show (fun y ↦ Real.cos (L y)) = Real.cos ∘ L from rfl,
    L.iteratedFDeriv_comp_right (n := k) Real.contDiff_cos x le_rfl]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact (mul_le_mul_of_nonneg_right (Real.abs_iteratedDeriv_cos_le_one k (L x))
    (by positivity)).trans_eq (one_mul _)

end PDE.Analysis
