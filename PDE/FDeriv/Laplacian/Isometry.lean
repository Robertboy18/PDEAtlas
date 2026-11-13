/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Operators
public import PDE.Analysis.Calculus.Laplacian.Composition
import PDE.FDeriv.Calculus

/-!
# Invariance of the Laplacian under isometries

Mathlib's intrinsic Laplacian is unchanged by an orthogonal change of variables:
transport an orthonormal basis and use the iterated derivative composition theorem.
LeanPDE's coordinate Laplacian has the same property under local `C²` hypotheses.
Translation invariance then gives the affine version.
-/

@[expose] public noncomputable section

open PDE (laplacian)

namespace PDE

/-- The coordinate Laplacian is invariant under a linear isometry at a `C²` point. -/
theorem laplacian_comp_linearIsometryEquiv_at {n : ℕ} (A : ℝ^n ≃ₗᵢ[ℝ] ℝ^n)
    {f : ℝ^n → ℝ} {x : ℝ^n} (hf : ContDiffAt ℝ 2 f (A x)) :
    laplacian (f ∘ A) x = laplacian f (A x) := by
  rw [(hf.comp x A.contDiff.contDiffAt).coordinate_laplacian_eq_laplacian,
    hf.coordinate_laplacian_eq_laplacian,
    InnerProductSpace.laplacian_comp_linearIsometryEquiv]
  rfl

/-- An affine isometry preserves the native coordinate Laplacian under local `C²` regularity. -/
theorem laplacian_comp_isometry_add_at {n : ℕ} (A : ℝ^n ≃ₗᵢ[ℝ] ℝ^n)
    (b : ℝ^n) {f : ℝ^n → ℝ} {x : ℝ^n} (hf : ContDiffAt ℝ 2 f (A x + b)) :
    laplacian (fun y ↦ f (A y + b)) x = laplacian f (A x + b) := by
  have hshift : ContDiffAt ℝ 2 (fun y ↦ f (y + b)) (A x) :=
    hf.comp (A x) (contDiffAt_id.add contDiffAt_const)
  change laplacian ((fun y ↦ f (y + b)) ∘ A) x = _
  rw [laplacian_comp_linearIsometryEquiv_at A hshift]
  simpa only [add_comm] using laplacian_comp_add_left f b (A x)
    (by simpa only [add_comm] using hf)

end PDE
