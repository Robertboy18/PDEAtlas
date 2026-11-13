/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.FDeriv.PartialDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Coordinate derivatives bounded by the full derivative

Each coordinate direction is a unit vector. A finite word of coordinate
partials is therefore bounded by the norm of the corresponding Fréchet
derivative. The statement uses only the finite regularity needed at the point.
-/

@[expose] public section

namespace PDE

/-- A coordinate word evaluates the full derivative on unit directions, so
its norm is at most the operator norm of that derivative. -/
theorem norm_iteratedPartialDeriv_le_norm_iteratedFDeriv
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (indices : List (Fin n)) {f : ℝ^n → E} {x : ℝ^n}
    (hf : ContDiffAt ℝ indices.length f x) :
    ‖iteratedPartialDeriv indices f x‖ ≤ ‖iteratedFDeriv ℝ indices.length f x‖ := by
  induction indices using List.reverseRecOn generalizing f with
  | nil => simp [iteratedPartialDeriv, norm_iteratedFDeriv_zero]
  | append_singleton rest i ih =>
      have hfd : ContDiffAt ℝ rest.length (fderiv ℝ f) x :=
        hf.fderiv_right (by simp)
      have hp : ContDiffAt ℝ rest.length (∂[i] f) x := by
        change ContDiffAt ℝ rest.length
          (fun y ↦ (fderiv ℝ f y) (EuclideanSpace.single i (1 : ℝ))) x
        exact hfd.clm_apply contDiffAt_const
      have hbound := norm_iteratedFDeriv_clm_apply_const
        (c := EuclideanSpace.single i (1 : ℝ)) hfd (le_refl _)
      have hstep :
          ‖iteratedFDeriv ℝ rest.length (∂[i] f) x‖ ≤
            ‖iteratedFDeriv ℝ (rest ++ [i]).length f x‖ := by
        rw [List.length_append, List.length_singleton]
        change ‖iteratedFDeriv ℝ rest.length
          (fun y ↦ (fderiv ℝ f y) (EuclideanSpace.single i (1 : ℝ))) x‖ ≤ _
        simpa only [PiLp.norm_single, norm_one, one_mul, norm_iteratedFDeriv_fderiv] using hbound
      rw [iteratedPartialDeriv_append_single]
      exact (ih hp).trans hstep

end PDE
