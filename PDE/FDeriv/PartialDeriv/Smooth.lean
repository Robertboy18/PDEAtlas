/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Operators

/-!
# Coordinate calculus of smooth fields

For a smooth scalar function the coordinate Laplacian is smooth and commutes with every
coordinate derivative. The divergence is the sum of the coordinate derivatives of the
components, and a coordinate derivative of one component is bounded by the operator norm of the
full derivative.
-/

@[expose] public section

open scoped ContDiff

variable {n : ℕ}

namespace PDE

/-- On smooth functions the coordinate Laplacian commutes with coordinate derivatives. -/
theorem laplacian_partialDeriv_eq {g : ℝ^n → ℝ} (hg : ContDiff ℝ ∞ g) (i : Fin n) (x : ℝ^n) :
    PDE.laplacian (fun z ↦ PDE.partialDeriv i g z) x =
      PDE.partialDeriv i (fun z ↦ PDE.laplacian g z) x := by
  simp only [PDE.laplacian]
  rw [partialDeriv_sum]
  · apply Finset.sum_congr rfl
    intro j _
    have h1 : (fun y ↦ PDE.partialDeriv j (fun z ↦ PDE.partialDeriv i g z) y) =
        fun y ↦ PDE.partialDeriv i (fun z ↦ PDE.partialDeriv j g z) y :=
      partialDeriv_partialDeriv_comm_of_contDiff j i (hg.of_le (by simp))
    rw [h1]
    exact partialDeriv_partialDeriv_comm j i
      ((contDiff_top_partialDeriv (i := j) hg).of_le (by simp)) x
  · intro j _
    exact ((contDiff_top_partialDeriv (i := j)
      (contDiff_top_partialDeriv (i := j) hg)).differentiable (by simp)).differentiableAt

/-- The coordinate Laplacian of a smooth function is smooth. -/
theorem contDiff_laplacian_coord {g : ℝ^n → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x ↦ PDE.laplacian g x) := by
  simp only [PDE.laplacian]
  exact ContDiff.sum fun j _ ↦ contDiff_top_partialDeriv (i := j)
    (contDiff_top_partialDeriv (i := j) hg)

/-- The divergence is the sum of the coordinate derivatives of the components. -/
theorem divergence_eq_sum (φ : ℝ^n → ℝ^n) (x : ℝ^n) :
    PDE.divergence φ x = ∑ k, PDE.partialDeriv k (fun y ↦ φ y k) x := rfl

/-- A coordinate derivative of one component of a field is bounded by the operator norm of its
derivative. -/
theorem norm_partialDeriv_component_le {u : ℝ^n → ℝ^n} {x : ℝ^n} (hu : DifferentiableAt ℝ u x)
    (j k : Fin n) : ‖PDE.partialDeriv j (fun y ↦ u y k) x‖ ≤ ‖fderiv ℝ u x‖ := by
  rw [← partialDeriv_apply j k hu]
  refine (PiLp.norm_apply_le _ k).trans ?_
  refine ((fderiv ℝ u x).le_opNorm _).trans (le_of_eq ?_)
  simp

end PDE
