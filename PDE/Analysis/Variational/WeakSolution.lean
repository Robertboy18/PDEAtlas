/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.EReal.Inv

/-!
# Abstract variational weak solutions

The tested equation

`B u v = ell v`

for a bounded bilinear form on a real normed space, and the linear operations
on its solutions. With `V = H¹₀(U)`, the bilinear form (8) of a divergence form elliptic
operator and the load `v ↦ (f, v)`, or a functional in `H⁻¹(U)`, `IsWeakSolution` is Evans's
definition of a weak solution, the identity (9) for every test function `v`.

## Main definitions

* `IsWeakSolution B ell u`: `B u v = ell v` for every test vector `v`.

## Main results

* `IsWeakSolution.add`, `IsWeakSolution.smul`, `IsWeakSolution.linear_combination`: the
  solutions depend linearly on the load.
* `IsWeakSolution.sub_same_load`: two solutions with the same load differ by a solution of the
  homogeneous equation.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.1.2, Definitions (8) and (9), p. 314, and the
  definition of a weak solution of (10), p. 315. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Analysis.Variational

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- `u` is a variational weak solution of `B u = ell` when the equation
holds against every test vector. -/
def IsWeakSolution
    (B : V →L[ℝ] V →L[ℝ] ℝ) (ell : StrongDual ℝ V) (u : V) : Prop :=
  ∀ v, B u v = ell v

/-- Evaluate a variational weak solution at a test vector. -/
theorem IsWeakSolution.apply
    {B : V →L[ℝ] V →L[ℝ] ℝ} {ell : StrongDual ℝ V} {u : V}
    (hu : IsWeakSolution B ell u) (v : V) :
    B u v = ell v :=
  hu v

/-- The zero vector solves the homogeneous variational equation. -/
@[simp]
theorem IsWeakSolution.zero (B : V →L[ℝ] V →L[ℝ] ℝ) :
    IsWeakSolution B 0 0 := by
  intro v
  simp

/-- The sum of two weak solutions solves the equation with the sum load. -/
theorem IsWeakSolution.add
    {B : V →L[ℝ] V →L[ℝ] ℝ}
    {ell₁ ell₂ : StrongDual ℝ V} {u₁ u₂ : V}
    (h₁ : IsWeakSolution B ell₁ u₁)
    (h₂ : IsWeakSolution B ell₂ u₂) :
    IsWeakSolution B (ell₁ + ell₂) (u₁ + u₂) := by
  intro v
  calc
    B (u₁ + u₂) v = B u₁ v + B u₂ v := by simp
    _ = ell₁ v + ell₂ v := by rw [h₁ v, h₂ v]
    _ = (ell₁ + ell₂) v := by rfl

/-- Negating both the state and load preserves the weak equation. -/
theorem IsWeakSolution.neg
    {B : V →L[ℝ] V →L[ℝ] ℝ} {ell : StrongDual ℝ V} {u : V}
    (h : IsWeakSolution B ell u) :
    IsWeakSolution B (-ell) (-u) := by
  intro v
  calc
    B (-u) v = -B u v := by simp
    _ = -ell v := by rw [h v]
    _ = (-ell) v := by rfl

/-- The difference of weak solutions solves the equation with difference
load. -/
theorem IsWeakSolution.sub
    {B : V →L[ℝ] V →L[ℝ] ℝ}
    {ell₁ ell₂ : StrongDual ℝ V} {u₁ u₂ : V}
    (h₁ : IsWeakSolution B ell₁ u₁)
    (h₂ : IsWeakSolution B ell₂ u₂) :
    IsWeakSolution B (ell₁ - ell₂) (u₁ - u₂) := by
  simpa [sub_eq_add_neg] using h₁.add h₂.neg

/-- Scaling a weak solution scales its load by the same real scalar. -/
theorem IsWeakSolution.smul
    {B : V →L[ℝ] V →L[ℝ] ℝ} {ell : StrongDual ℝ V} {u : V}
    (c : ℝ) (h : IsWeakSolution B ell u) :
    IsWeakSolution B (c • ell) (c • u) := by
  intro v
  calc
    B (c • u) v = c * B u v := by simp
    _ = c * ell v := by rw [h v]
    _ = (c • ell) v := by rfl

/-- A linear combination of weak solutions solves the corresponding
linear combination of loads. -/
theorem IsWeakSolution.linear_combination
    {B : V →L[ℝ] V →L[ℝ] ℝ}
    {ell₁ ell₂ : StrongDual ℝ V} {u₁ u₂ : V}
    (c₁ c₂ : ℝ)
    (h₁ : IsWeakSolution B ell₁ u₁)
    (h₂ : IsWeakSolution B ell₂ u₂) :
    IsWeakSolution B (c₁ • ell₁ + c₂ • ell₂) (c₁ • u₁ + c₂ • u₂) :=
  (h₁.smul c₁).add (h₂.smul c₂)

/-- The difference of two weak solutions with the same load solves the
homogeneous equation. -/
theorem IsWeakSolution.sub_same_load
    {B : V →L[ℝ] V →L[ℝ] ℝ} {ell : StrongDual ℝ V} {u₁ u₂ : V}
    (h₁ : IsWeakSolution B ell u₁)
    (h₂ : IsWeakSolution B ell u₂) :
    IsWeakSolution B 0 (u₁ - u₂) := by
  simpa using h₁.sub h₂

end PDE.Analysis.Variational
