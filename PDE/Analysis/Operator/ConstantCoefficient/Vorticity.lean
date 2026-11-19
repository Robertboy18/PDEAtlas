/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Vorticity identities for commuting derivatives

For commuting linear derivatives, the divergence of the antisymmetric
derivative tensor is the componentwise Laplacian minus the derivative of the
divergence. A closed Laplacian-plus-force residual therefore gives a
divergence-form equation for each vorticity component.

These are algebraic identities. Ordinary distributional derivatives provide
the commuting operators in the Stokes application, so the identities require
no second classical derivatives.
-/

@[expose] public section

namespace PDE.Analysis

variable {R V ι : Type*} [Semiring R] [AddCommGroup V] [Module R V] [Fintype ι]

/-- A derivative commutes with the sum of squares of a finite commuting family. -/
theorem map_sum_second_of_commute (D : ι → Module.End R V)
    (hD : ∀ i j, Commute (D i) (D j)) (i : ι) (u : V) :
    D i (∑ k, D k (D k u)) = ∑ k, D k (D k (D i u)) := by
  have hswap (j k : ι) (v : V) : D j (D k v) = D k (D j v) :=
    congrArg (fun A : Module.End R V ↦ A v) (hD j k).eq
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [hswap i k, hswap i k]

/-- Incompressibility identifies the divergence of the antisymmetric derivative
tensor with the componentwise Laplacian. The index set may be empty. -/
theorem sum_deriv_antisymmetric_eq_of_divergence_zero
    (D : ι → Module.End R V) (hD : ∀ i j, Commute (D i) (D j))
    (u : ι → V) (hu : ∑ i, D i (u i) = 0) (j : ι) :
    (∑ i, D i (D i (u j) - D j (u i))) = ∑ i, D i (D i (u j)) := by
  have hswap (i : ι) : D i (D j (u i)) = D j (D i (u i)) :=
    congrArg (fun A : Module.End R V ↦ A (u i)) (hD i j).eq
  simp only [map_sub, Finset.sum_sub_distrib, hswap, ← map_sum, hu, map_zero, sub_zero]

/-- A closed Laplacian-plus-force residual gives the vorticity equation with
the distributional force signs kept explicit. -/
theorem sum_second_antisymmetric_eq_of_closed_residual
    (D : ι → Module.End R V) (hD : ∀ i j, Commute (D i) (D j))
    (u f : ι → V)
    (hclosed : ∀ i j, D i ((∑ k, D k (D k (u j))) + f j) =
      D j ((∑ k, D k (D k (u i))) + f i))
    (i j : ι) :
    (∑ k, D k (D k (D i (u j) - D j (u i)))) = D j (f i) - D i (f j) := by
  have h := hclosed i j
  simp only [map_add, map_sum_second_of_commute D hD] at h
  simp only [map_sub, Finset.sum_sub_distrib]
  exact sub_eq_sub_iff_add_eq_add.mpr (h.trans (add_comm _ _))

end PDE.Analysis
