/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# Regularity of Mathlib's Laplacian

On a finite-dimensional real inner product space, `Δ` loses two orders of
differentiability. The order comparison includes finite orders, smooth maps,
and analytic maps, and the codomain may be any real normed space.
For the total ambient Laplacian on a set, openness is required.
-/

@[expose] public noncomputable section

open scoped Laplacian

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {f : E → F} {x : E} {s : Set E} {k r : WithTop ℕ∞}

/-- Mathlib's Laplacian loses two derivatives locally. -/
theorem ContDiffAt.laplacian (hf : ContDiffAt ℝ r f x) (hkr : k + 2 ≤ r) :
    ContDiffAt ℝ k (Δ f) x := by
  have hk : (k + 1) + 1 ≤ r := by convert hkr using 1; norm_num [add_assoc]
  have hdd := (hf.fderiv_right hk).fderiv_right (m := k) le_rfl
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  exact ContDiffAt.sum fun _ _ ↦
    (hdd.clm_apply contDiffAt_const).clm_apply contDiffAt_const

/-- Mathlib's Laplacian loses two derivatives globally, including at infinite order. -/
theorem ContDiff.laplacian (hf : ContDiff ℝ r f) (hkr : k + 2 ≤ r) :
    ContDiff ℝ k (Δ f) :=
  contDiff_iff_contDiffAt.mpr fun _ ↦ hf.contDiffAt.laplacian hkr

/-- On an open set, regularity controls the total ambient Laplacian. -/
theorem ContDiffOn.laplacian (hf : ContDiffOn ℝ r f s) (hs : IsOpen s)
    (hkr : k + 2 ≤ r) : ContDiffOn ℝ k (Δ f) s :=
  fun _ hx ↦ ((hf.contDiffAt (hs.mem_nhds hx)).laplacian hkr).contDiffWithinAt
