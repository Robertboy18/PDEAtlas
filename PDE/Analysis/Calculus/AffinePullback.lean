/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Calculus

/-!
# Derivatives under translation and scalar dilation

The total Fréchet derivative commutes with translation and scalar dilation.
The coordinate formulas below consequently hold without regularity assumptions;
they include the zero dilation, where both sides vanish.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

/-- A specified derivative pulls back by translation and scalar dilation,
including a zero dilation. The range may itself be a space of linear maps. -/
theorem hasFDerivAt_comp_const_add_smul
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E → F} {Du : E →L[ℝ] F} {z x : E} {r : ℝ}
    (hu : HasFDerivAt u Du (z + r • x)) :
    HasFDerivAt (fun y ↦ u (z + r • y)) (r • Du) x := by
  simpa only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id,
    Function.comp_def, Pi.smul_apply, id_eq] using
    hu.comp x (((hasFDerivAt_id x).const_smul r).const_add z)

variable {n : ℕ}

/-- First derivative of a translated and dilated function. -/
theorem fderiv_comp_const_add_smul
    (u : ℝ^n → ℝ) (z x : ℝ^n) (r : ℝ) :
    fderiv ℝ (fun y ↦ u (z + r • y)) x = r • fderiv ℝ u (z + r • x) := by
  have h := fderiv_comp_smul (𝕜 := ℝ) (f := fun y ↦ u (z + y)) (x := x) r
  rw [fderiv_comp_add_left] at h
  exact h

/-- Coordinate derivative of a translated and dilated function. -/
theorem partialDeriv_comp_const_add_smul
    (u : ℝ^n → ℝ) (z x : ℝ^n) (r : ℝ) (i : Fin n) :
    (∂[i] (fun y ↦ u (z + r • y))) x =
      r * (∂[i] u) (z + r • x) := by
  unfold partialDeriv
  rw [fderiv_comp_const_add_smul]
  rfl

/-- Second coordinate derivative gains the square of the dilation factor. -/
theorem secondPartialDeriv_comp_const_add_smul
    (u : ℝ^n → ℝ) (z x : ℝ^n) (r : ℝ) (i j : Fin n) :
    (∂[i] (∂[j] (fun y ↦ u (z + r • y)))) x =
      r ^ 2 * (∂[i] (∂[j] u)) (z + r • x) := by
  have hfirst : (∂[j] (fun y ↦ u (z + r • y))) =
      fun y ↦ r * (∂[j] u) (z + r • y) :=
    funext (fun y ↦ partialDeriv_comp_const_add_smul u z y r j)
  rw [hfirst]
  have h := partialDeriv_const_smul (i := i)
    (f := fun y ↦ (∂[j] u) (z + r • y)) (x := x) r
  change (∂[i] (fun y ↦ r * (∂[j] u) (z + r • y))) x =
    r * (∂[i] (fun y ↦ (∂[j] u) (z + r • y))) x at h
  rw [h, partialDeriv_comp_const_add_smul]
  simp only [pow_two, mul_assoc]

end PDE.Analysis
