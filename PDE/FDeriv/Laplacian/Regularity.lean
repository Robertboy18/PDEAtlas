/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Operators
public import PDE.FDeriv.PartialDeriv.Regularity

/-!
# Regularity of the coordinate Laplacian

The coordinate Laplacian loses two orders of differentiability, for maps
into any real normed space. The order comparison includes finite orders,
smooth maps, and analytic maps. On a set, openness ensures that the total
ambient coordinate derivatives are the derivatives controlled by the
regularity hypothesis.
-/

@[expose] public noncomputable section

open PDE

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : ℝ^n → E} {x : ℝ^n} {s : Set (ℝ^n)} {k r : WithTop ℕ∞}

/-- Local regularity of the coordinate Laplacian, losing two derivatives. -/
theorem ContDiffAt.coordinate_laplacian (hf : ContDiffAt ℝ r f x)
    (hkr : k + 2 ≤ r) : ContDiffAt ℝ k (laplacian f) x := by
  have hk : (k + 1) + 1 ≤ r := by convert hkr using 1; norm_num [add_assoc]
  change ContDiffAt ℝ k (fun y ↦ ∑ i : Fin n, (∂[i] (∂[i] f)) y) x
  exact ContDiffAt.sum fun i _ ↦ (hf.partialDeriv i hk).partialDeriv i le_rfl

/-- Global regularity of the coordinate Laplacian, at finite or infinite order. -/
theorem ContDiff.coordinate_laplacian (hf : ContDiff ℝ r f)
    (hkr : k + 2 ≤ r) : ContDiff ℝ k (laplacian f) := by
  have hk : (k + 1) + 1 ≤ r := by convert hkr using 1; norm_num [add_assoc]
  change ContDiff ℝ k (fun y ↦ ∑ i : Fin n, (∂[i] (∂[i] f)) y)
  exact ContDiff.sum fun i _ ↦ (hf.partialDeriv i hk).partialDeriv i le_rfl

/-- Regularity on an open set controls the ambient coordinate Laplacian there. -/
theorem ContDiffOn.coordinate_laplacian (hf : ContDiffOn ℝ r f s)
    (hs : IsOpen s) (hkr : k + 2 ≤ r) : ContDiffOn ℝ k (laplacian f) s := by
  have hk : (k + 1) + 1 ≤ r := by convert hkr using 1; norm_num [add_assoc]
  change ContDiffOn ℝ k (fun y ↦ ∑ i : Fin n, (∂[i] (∂[i] f)) y) s
  exact ContDiffOn.sum fun i _ ↦ (hf.partialDeriv i hs hk).partialDeriv i hs le_rfl
