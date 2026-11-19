/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fredholm.WeakForm.Reduction
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# The weak Fredholm alternative

The Fredholm dichotomy for a shifted-coercive weak form with compact mass
operator. Eigenvalue `1` of the compact reduction is
identified with a nonzero homogeneous weak solution; otherwise every forcing
has a unique weak solution.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.2.3, Theorem 4(i), p. 321, and steps 1-4 of its proof,
  pp. 321-323. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open Set Function
open scoped InnerProductSpace
open PDE.Analysis.Variational

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- `fredholmOperator` has eigenvalue `1` exactly when the homogeneous weak equation of `form`
has a nonzero solution. -/
theorem hasEigenvalue_one_fredholmOperator_iff
    (form shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) (lambda : ℝ)
    (hshift : ∀ u v, shiftedForm u v = form u v + lambda * massForm u v) :
    Module.End.HasEigenvalue
        (fredholmOperator shiftedForm massForm coercive lambda : Module.End ℝ V) 1 ↔
      ∃ u : V, u ≠ 0 ∧ IsWeakSolution form 0 u := by
  constructor
  · intro hEigen
    obtain ⟨u, hu⟩ := hEigen.exists_hasEigenvector
    have hKu : fredholmOperator shiftedForm massForm coercive lambda u = u := by
      simpa using hu.apply_eq_smul
    refine ⟨u, hu.2, ?_⟩
    apply (isWeakSolution_iff_sub_fredholmOperator_eq
      form shiftedForm massForm coercive lambda hshift 0 u).2
    rw [hKu, sub_self, map_zero]
  · rintro ⟨u, hu_ne, hu⟩
    apply Module.End.hasEigenvalue_of_hasEigenvector
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hu_ne⟩
    have hred := (isWeakSolution_iff_sub_fredholmOperator_eq
      form shiftedForm massForm coercive lambda hshift 0 u).1 hu
    rw [map_zero] at hred
    have hKu : fredholmOperator shiftedForm massForm coercive lambda u = u :=
      (sub_eq_zero.mp hred).symm
    simpa using hKu

/-- Either the homogeneous weak equation has a nonzero solution or `1` is in the resolvent set
of `fredholmOperator`, by Mathlib's `IsCompactOperator.hasEigenvalue_or_mem_resolventSet`. -/
theorem fredholm_dichotomy
    (form shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) (lambda : ℝ)
    (hshift : ∀ u v, shiftedForm u v = form u v + lambda * massForm u v)
    (hcompactMass : IsCompactOperator massForm) :
    (∃ u : V, u ≠ 0 ∧ IsWeakSolution form 0 u) ∨
      (1 : ℝ) ∈ resolventSet ℝ
        (fredholmOperator shiftedForm massForm coercive lambda) := by
  have hcompact :=
    isCompactOperator_fredholmOperator shiftedForm massForm coercive lambda hcompactMass
  rcases hcompact.hasEigenvalue_or_mem_resolventSet (by norm_num : (1 : ℝ) ≠ 0) with
    hEigen | hResolvent
  · exact Or.inl ((hasEigenvalue_one_fredholmOperator_iff
      form shiftedForm massForm coercive lambda hshift).1 hEigen)
  · exact Or.inr hResolvent

/-- The Fredholm alternative in weak form, Evans, §6.2.3, Theorem 4(i): either the homogeneous
problem has a nonzero solution, or every continuous forcing has a unique weak
solution. Compactness of the mass operator is a hypothesis; in Evans's setting it comes from
the Rellich–Kondrachov theorem. -/
theorem fredholmAlternative_weak_solution
    (form shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) (lambda : ℝ)
    (hshift : ∀ u v, shiftedForm u v = form u v + lambda * massForm u v)
    (hcompactMass : IsCompactOperator massForm) :
    (∃ u : V, u ≠ 0 ∧ IsWeakSolution form 0 u) ∨
      ∀ ell : StrongDual ℝ V, ∃! u : V, IsWeakSolution form ell u := by
  rcases fredholm_dichotomy form shiftedForm massForm coercive lambda hshift hcompactMass with
    hKernel | hResolvent
  · exact Or.inl hKernel
  · right
    let K := fredholmOperator shiftedForm massForm coercive lambda
    have hbij : Function.Bijective (K - (1 : V →L[ℝ] V)) := by
      rw [spectrum.mem_resolventSet_iff, ← IsUnit.neg_iff,
        ContinuousLinearMap.isUnit_iff_bijective] at hResolvent
      simpa [K] using hResolvent
    intro ell
    let rhs := solveCLM shiftedForm coercive ell
    obtain ⟨u, hu⟩ := hbij.surjective (-rhs)
    have huEq : u - K u = rhs := by
      change K u - u = -rhs at hu
      linear_combination (norm := module) -hu
    refine ⟨u, (isWeakSolution_iff_sub_fredholmOperator_eq
      form shiftedForm massForm coercive lambda hshift ell u).2 huEq, ?_⟩
    intro v hv
    apply hbij.injective
    have hvEq := (isWeakSolution_iff_sub_fredholmOperator_eq
      form shiftedForm massForm coercive lambda hshift ell v).1 hv
    change K v - v = K u - u
    linear_combination (norm := module) -hvEq + huEq

/-- Exactly one of the two alternatives of `fredholmAlternative_weak_solution` holds, as in
Evans, §6.2.3, Theorem 4(i): uniqueness for zero forcing rules out a nonzero homogeneous
solution. -/
theorem fredholmAlternative_weak_solution_exactlyOne
    (form shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) (lambda : ℝ)
    (hshift : ∀ u v, shiftedForm u v = form u v + lambda * massForm u v)
    (hcompactMass : IsCompactOperator massForm) :
    Xor
      (∃ u : V, u ≠ 0 ∧ IsWeakSolution form 0 u)
      (∀ ell : StrongDual ℝ V, ∃! u : V, IsWeakSolution form ell u) := by
  have hexclusive :
      ¬ ((∃ u : V, u ≠ 0 ∧ IsWeakSolution form 0 u) ∧
          ∀ ell : StrongDual ℝ V, ∃! u : V, IsWeakSolution form ell u) := by
    rintro ⟨⟨u, hu_ne, hu⟩, hunique⟩
    obtain ⟨u₀, hu₀, huniq⟩ := hunique 0
    have hzero : IsWeakSolution form 0 (0 : V) :=
      IsWeakSolution.zero form
    have hu_eq : u = 0 :=
      (huniq u hu).trans (huniq 0 hzero).symm
    exact hu_ne hu_eq
  rcases fredholmAlternative_weak_solution
      form shiftedForm massForm coercive lambda hshift hcompactMass with
    hkernel | hunique
  · exact Or.inl ⟨hkernel, fun h ↦ hexclusive ⟨hkernel, h⟩⟩
  · exact Or.inr ⟨hunique, fun h ↦ hexclusive ⟨h, hunique⟩⟩

end PDE.Analysis
