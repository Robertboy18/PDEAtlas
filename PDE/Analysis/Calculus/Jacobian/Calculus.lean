/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Jacobian.Basic
public import Mathlib.Analysis.Matrix.Normed

/-!
# Affine operations and regularity of Jacobian matrices

The scalar coordinate definition of the Jacobian respects affine variations.
Taking the Jacobian lowers finite classical regularity by one.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Elementwise

namespace PDE.Analysis

variable {n m : ℕ} {u v : ℝ^n → ℝ^m} {x : ℝ^n}

/-- Maps agreeing near a point have the same Jacobian matrix there. -/
theorem jacobianMatrix_eq_of_eventuallyEq
    (h : u =ᶠ[nhds x] v) : jacobianMatrix u x = jacobianMatrix v x := by
  ext k i
  exact ((h.fun_comp (fun z : ℝ^m ↦ z k)).partialDeriv i).eq_of_nhds

/-- The Jacobian matrix of the identity map is the identity matrix. -/
@[simp]
theorem jacobianMatrix_id (y : ℝ^n) :
    jacobianMatrix (fun z : ℝ^n ↦ z) y = 1 := by
  ext k i
  have h := jacobianMatrix_apply_eq_fderiv
    (u := fun z : ℝ^n ↦ z) (x := y) differentiableAt_id k i
  simpa [PiLp.single_apply, Matrix.one_apply, eq_comm] using h

/-- The Jacobian of a sum at a common differentiability point. -/
theorem jacobianMatrix_add (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) :
    jacobianMatrix (fun y ↦ u y + v y) x = jacobianMatrix u x + jacobianMatrix v x := by
  ext k i
  exact partialDeriv_add
    ((EuclideanSpace.proj k : ℝ^m →L[ℝ] ℝ).differentiableAt.comp x hu)
    ((EuclideanSpace.proj k : ℝ^m →L[ℝ] ℝ).differentiableAt.comp x hv)

/-- Adding a constant field leaves the coordinate Jacobian unchanged, including
at points where the totalized derivative is zero. -/
theorem jacobianMatrix_add_const (u : ℝ^n → ℝ^m) (b : ℝ^m) (x : ℝ^n) :
    jacobianMatrix (fun y ↦ u y + b) x = jacobianMatrix u x := by
  ext k i
  change fderiv ℝ (fun y ↦ u y k + b k) x _ = fderiv ℝ (fun y ↦ u y k) x _
  rw [fderiv_add_const]

/-- Translating the argument translates the coordinate Jacobian. No
differentiability assumption is needed for this identity of total derivatives. -/
theorem jacobianMatrix_comp_sub (u : ℝ^n → ℝ^m) (a x : ℝ^n) :
    jacobianMatrix (fun y ↦ u (y - a)) x = jacobianMatrix u (x - a) := by
  ext k i
  change fderiv ℝ (fun y ↦ u (y - a) k) x _ = fderiv ℝ (fun y ↦ u y k) (x - a) _
  rw [fderiv_comp_sub (𝕜 := ℝ) (f := fun y ↦ u y k) a]

/-- Scalar multiplication commutes with the totalized coordinate Jacobian. -/
theorem jacobianMatrix_const_smul (c : ℝ) :
    jacobianMatrix (fun y ↦ c • u y) x = c • jacobianMatrix u x := by
  ext k i
  exact partialDeriv_const_smul c

/-- The Jacobian of a difference at a common differentiability point. -/
theorem jacobianMatrix_sub (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) :
    jacobianMatrix (fun y ↦ u y - v y) x = jacobianMatrix u x - jacobianMatrix v x := by
  ext k i
  exact partialDeriv_sub
    ((EuclideanSpace.proj k : ℝ^m →L[ℝ] ℝ).differentiableAt.comp x hu)
    ((EuclideanSpace.proj k : ℝ^m →L[ℝ] ℝ).differentiableAt.comp x hv)

/-- A Jacobian lowers finite global classical regularity by one. -/
theorem contDiff_jacobianMatrix {r : ℕ} (hu : ContDiff ℝ (r + 1) u) :
    ContDiff ℝ r (jacobianMatrix u) := by
  apply contDiff_pi.mpr
  intro k
  apply contDiff_pi.mpr
  intro i
  exact contDiff_partialDeriv_of_succ
    ((EuclideanSpace.proj k : ℝ^m →L[ℝ] ℝ).contDiff.comp hu)

end PDE.Analysis
