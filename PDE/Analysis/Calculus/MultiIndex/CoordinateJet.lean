/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Jet.Finite
public import PDE.Combinatorics.SymmetricPower.SortedTuple
public import PDE.Common.Euclidean

/-!
# Coordinate derivatives and normal Cauchy data

A multiset of coordinate indices is a multiindex: its multiplicities are the
usual nonnegative exponents. Evaluating an ordinary iterated Fréchet derivative
on its sorted coordinate tuple gives the corresponding mixed partial.

Normal data evaluate the ordinary iterated Fréchet derivative on copies of the
normal at the base point. Expanding in coordinates counts every ordered tuple:
the mixed partial of multiindex `α` consequently has weight `j! / ∏ αᵢ!`.
The normal is held fixed during differentiation, including on curved hypersurfaces.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace PDE.Analysis.MultiIndex

variable {n j k : ℕ}

/-- The coordinate vectors for a mixed partial, in sorted order. -/
def directions (α : Sym (Fin n) j) : Fin j → ℝ^n :=
  fun i ↦ EuclideanSpace.basisFun (Fin n) ℝ (α.sortedTuple i)

/-- The actual mixed partial associated with a multiindex. -/
def coordinateDeriv (α : Sym (Fin n) j) (u : ℝ^n → ℝ) (x : ℝ^n) : ℝ :=
  iteratedFDeriv ℝ j u x (directions α)

/-- The coordinate monomial with the multiplicities of the multiindex. -/
def monomial (α : Sym (Fin n) j) (ν : ℝ^n) : ℝ :=
  ∏ i, ν i ^ (α : Multiset (Fin n)).count i

/-- Coordinate monomials are products of the conormal on the coordinate
directions; no factorial normalization is present. -/
theorem monomial_eq_prod_inner (α : Sym (Fin n) j) (ν : ℝ^n) :
    monomial α ν = ∏ i, inner ℝ ν (directions α i) := by
  simp only [directions, EuclideanSpace.inner_basisFun_real]
  exact (α.prod_sortedTuple_eq_prod_pow_count ν).symm

/-- Repeating one coordinate gives its ordinary power. -/
theorem monomial_replicate (i : Fin n) (ν : ℝ^n) :
    monomial (Sym.replicate j i) ν = ν i ^ j := by
  rw [monomial_eq_prod_inner]
  simp only [directions, EuclideanSpace.inner_basisFun_real]
  exact Sym.prod_sortedTuple_replicate i ν

/-- Every nonzero normal is detected by a pure coordinate multiindex. -/
theorem exists_monomial_ne_zero {ν : ℝ^n} (hν : ν ≠ 0) (j : ℕ) :
    ∃ α : Sym (Fin n) j, monomial α ν ≠ 0 := by
  have hi : ∃ i, ν i ≠ 0 := by
    by_contra! h
    apply hν
    ext i
    exact h i
  obtain ⟨i, hi⟩ := hi
  exact ⟨Sym.replicate j i, by rw [monomial_replicate]; exact pow_ne_zero _ hi⟩

/-- The ordinary repeated directional derivative in the fixed direction `ν`.
For a unit normal this is the standard normal Cauchy datum. -/
def normalData (j : ℕ) (u : ℝ^n → ℝ) (ν x : ℝ^n) : ℝ :=
  iteratedFDeriv ℝ j u x (fun _ ↦ ν)

/-- Zeroth normal data are the value of the function. -/
@[simp]
theorem normalData_zero (u : ℝ^n → ℝ) (ν x : ℝ^n) :
    normalData 0 u ν x = u x := by
  simp only [normalData, iteratedFDeriv_zero_apply]

/-- Coordinate evaluation of a finite tuple of multilinear derivatives. -/
def coordinateJetMap (n k : ℕ) :
    (∀ i : Fin k, (ℝ^n) [×(i : ℕ)]→L[ℝ] ℝ) →L[ℝ]
      (∀ i : Fin k, Sym (Fin n) (i : ℕ) → ℝ) :=
  ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.pi fun α ↦
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (i : ℕ) ↦ ℝ^n) ℝ (directions α)).comp
      (ContinuousLinearMap.proj i)

/-- The lower coordinate jets are the actual mixed partials, including the
value at order zero. -/
def coordinateJetLT (k : ℕ) (u : ℝ^n → ℝ) (x : ℝ^n) :
    ∀ i : Fin k, Sym (Fin n) (i : ℕ) → ℝ :=
  coordinateJetMap n k (jetLT ℝ k u x)

end PDE.Analysis.MultiIndex
