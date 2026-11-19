/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
import PDE.Analysis.Calculus.Prod.SliceDerivative

/-!
# Regularity of the spatial Laplacian

For a function of space and a real parameter, the Laplacian in the space variable loses
two joint derivatives. The proof writes Mathlib's Laplacian as an orthonormal trace and
applies the first-factor slice derivative theorem twice.
-/

@[expose] public noncomputable section

open scoped Laplacian

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace PDE

/-- The spatial Laplacian of a jointly `C^(m + 2)` map is jointly `C^m`. -/
theorem contDiff_laplacian_prod_firstSlice
    {m : ℕ} {f : E × ℝ → F} (hf : ContDiff ℝ (m + 2) f) :
    ContDiff ℝ m (fun z : E × ℝ ↦ Δ (fun x ↦ f (x, z.2)) z.1) := by
  classical
  simp_rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  apply ContDiff.sum
  intro i _
  let v := (stdOrthonormalBasis ℝ E) i
  have hfirst := contDiff_fderiv_prod_firstSlice (m := m + 1)
    (f := f) (by convert hf using 1; norm_num [Nat.cast_add, add_assoc]) v
  have hsecond := contDiff_fderiv_prod_firstSlice (m := m) hfirst v
  convert hsecond using 1
  funext z
  have hs : ContDiffAt ℝ 2 (fun x : E ↦ f (x, z.2)) z.1 :=
    ((hf.of_le (by norm_num)).comp (contDiff_id.prodMk contDiff_const)).contDiffAt
  have hdf : DifferentiableAt ℝ (fderiv ℝ (fun x : E ↦ f (x, z.2))) z.1 :=
    (hs.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  rw [iteratedFDeriv_two_apply, fderiv_clm_apply hdf (differentiableAt_const v)]
  simp [v]

end PDE
