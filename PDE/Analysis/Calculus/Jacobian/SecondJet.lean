/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Jacobian.Basic
public import Mathlib.Analysis.Matrix.Normed

/-!
# The derivative of the Jacobian

The derivative of a rectangular Jacobian records the full second Fréchet derivative:
its row `k`, column `i` entry in direction `v` is `D²u(x)[v,eᵢ]ₖ`. The order of the
two directions comes directly from differentiating the Jacobian, without first using
symmetry. Both dimensions may be zero.
-/

@[expose] public section

noncomputable section

open scoped Matrix.Norms.Elementwise Topology

namespace PDE.Analysis

variable {n m : ℕ}

/-- On a `C²` germ the rectangular Jacobian has a `C¹` germ. -/
theorem contDiffAt_jacobianMatrix {u : ℝ^n → ℝ^m} {x : ℝ^n}
    (hu : ContDiffAt ℝ 2 u x) : ContDiffAt ℝ 1 (jacobianMatrix u) x := by
  apply contDiffAt_pi.mpr
  intro k
  apply contDiffAt_pi.mpr
  intro i
  have hk : ContDiffAt ℝ 2 (fun y ↦ u y k) x :=
    (EuclideanSpace.proj k : ℝ^m →L[ℝ] ℝ).contDiff.contDiffAt.comp x hu
  exact contDiffAt_partialDeriv 1 hk i

/-- The outer direction is `v`; the inner direction is the column basis vector.
This is an identity of Fréchet derivatives, including at singular Jacobians. -/
theorem fderiv_jacobianMatrix_apply {u : ℝ^n → ℝ^m} {x : ℝ^n}
    (hu : ContDiffAt ℝ 2 u x) (v : ℝ^n) (k : Fin m) (i : Fin n) :
    fderiv ℝ (jacobianMatrix u) x v k i =
      fderiv ℝ (fderiv ℝ u) x v (EuclideanSpace.single i (1 : ℝ)) k := by
  have hJ := (contDiffAt_jacobianMatrix hu).differentiableAt (by norm_num)
  have hrow := differentiableAt_pi.mp hJ k
  have hentry :
      fderiv ℝ (fun y ↦ jacobianMatrix u y k i) x v =
        fderiv ℝ (jacobianMatrix u) x v k i := by
    rw [fderiv_apply hrow, fderiv_apply hJ]
    rfl
  rw [← hentry]
  have hnear : (fun y ↦ jacobianMatrix u y k i) =ᶠ[𝓝 x]
      (fun y ↦ fderiv ℝ u y (EuclideanSpace.single i (1 : ℝ)) k) := by
    filter_upwards [hu.eventually (by simp)] with y hy
    exact jacobianMatrix_apply_eq_fderiv (hy.differentiableAt (by norm_num)) k i
  rw [hnear.fderiv_eq]
  have hdu := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have happ := hdu.hasFDerivAt.clm_apply
    (hasFDerivAt_const (EuclideanSpace.single i (1 : ℝ)) x)
  have hproj := (EuclideanSpace.proj k : ℝ^m →L[ℝ] ℝ).hasFDerivAt.comp x happ
  simpa [Function.comp_def] using congrArg (fun A : ℝ^n →L[ℝ] ℝ ↦ A v) hproj.fderiv

/-- Equality of the complete second derivatives gives equality of Jacobian derivatives. -/
theorem fderiv_jacobianMatrix_eq_of_secondJet
    {u v : ℝ^n → ℝ^m} {x : ℝ^n}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x)
    (hsecond : fderiv ℝ (fderiv ℝ u) x = fderiv ℝ (fderiv ℝ v) x) :
    fderiv ℝ (jacobianMatrix u) x = fderiv ℝ (jacobianMatrix v) x := by
  ext w k i
  rw [fderiv_jacobianMatrix_apply hu, fderiv_jacobianMatrix_apply hv, hsecond]

end PDE.Analysis
