/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Reflection across a translated hyperplane

We translate Mathlib's orthogonal reflection by twice the signed displacement
of the hyperplane. For a unit vector `e`, this is reflection across `⟪x,e⟫ = a`.
The linear part is Mathlib's `Submodule.reflection` in the orthogonal
complement of `e`.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Reflection in the hyperplane with unit normal `e` and signed displacement `a`,
expressed using Mathlib's orthogonal reflection. -/
def reflectHyperplane (e : E) (a : ℝ) (x : E) : E :=
  (ℝ ∙ e)ᗮ.reflection x + (2 * a) • e

/-- The usual formula for reflection across `⟪x,e⟫ = a`. -/
theorem reflectHyperplane_eq {e : E} (he : ‖e‖ = 1) (a : ℝ) (x : E) :
    reflectHyperplane e a x = x + (2 * (a - ⟪x, e⟫)) • e := by
  simp only [reflectHyperplane, Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply, he, real_inner_comm e x]
  module

/-- Reflection varies continuously with the displacement and point. -/
theorem continuous_reflectHyperplane (e : E) :
    Continuous (fun p : ℝ × E ↦ reflectHyperplane e p.1 p.2) :=
  (((ℝ ∙ e)ᗮ.reflection.continuous.comp continuous_snd).add
    ((continuous_const.mul continuous_fst).smul continuous_const))

/-- Reflection reverses the signed coordinate relative to its hyperplane. -/
theorem inner_reflectHyperplane {e : E} (he : ‖e‖ = 1) (a : ℝ) (x : E) :
    ⟪reflectHyperplane e a x, e⟫ = 2 * a - ⟪x, e⟫ := by
  rw [reflectHyperplane_eq he, inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, he]
  ring

/-- The reflecting hyperplane is fixed pointwise. -/
theorem reflectHyperplane_eq_self {e x : E} {a : ℝ} (he : ‖e‖ = 1)
    (hx : ⟪x, e⟫ = a) : reflectHyperplane e a x = x := by
  simp [reflectHyperplane_eq he, hx]

/-- Reflecting twice gives the original point. -/
theorem reflectHyperplane_involutive {e : E} (he : ‖e‖ = 1) (a : ℝ) :
    Function.Involutive (reflectHyperplane e a) := by
  intro x
  rw [reflectHyperplane_eq he, inner_reflectHyperplane he, reflectHyperplane_eq he]
  module

/-- Changing the normal's orientation and the displacement's sign gives the same reflection. -/
theorem reflectHyperplane_neg {e : E} (he : ‖e‖ = 1) (a : ℝ) (x : E) :
    reflectHyperplane (-e) (-a) x = reflectHyperplane e a x := by
  rw [reflectHyperplane_eq (by simpa using he), reflectHyperplane_eq he, inner_neg_right]
  module

end PDE.Analysis
