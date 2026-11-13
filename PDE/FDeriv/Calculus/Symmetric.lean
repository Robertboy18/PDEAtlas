/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Commuting fixed directional derivatives

Local `C²` regularity makes successive derivatives in two fixed directions commute.
The domain and codomain may be arbitrary real normed spaces. This form of symmetry
applies directly to coordinate derivatives and spacetime slices.
-/

@[expose] public section

namespace PDE

/-- At a point of `C²` regularity, differentiation in two fixed directions commutes. -/
theorem fderiv_fderiv_apply_comm
    {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : D → E) (q v w : D) (hf : ContDiffAt ℝ 2 f q) :
    fderiv ℝ (fun r ↦ fderiv ℝ f r v) q w =
      fderiv ℝ (fun r ↦ fderiv ℝ f r w) q v := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) q :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [fderiv_clm_apply hdf (differentiableAt_const v),
    fderiv_clm_apply hdf (differentiableAt_const w)]
  simpa using (hf.isSymmSndFDerivAt (by simp)).eq w v

end PDE
