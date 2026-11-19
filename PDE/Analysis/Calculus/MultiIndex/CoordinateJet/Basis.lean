/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.MultiIndex.CoordinateJet

/-!
# Normal Cauchy data in a coordinate direction

At a coordinate unit vector, the only nonzero monomial is the corresponding
pure multiindex. The normal derivative is therefore the pure
coordinate derivative, including order zero.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.MultiIndex

variable {n j : ℕ}

/-- Evaluation at a coordinate unit vector selects its pure multiindex. -/
theorem monomial_basisFun (α : Sym (Fin n) j) (i : Fin n) :
    monomial α (EuclideanSpace.basisFun (Fin n) ℝ i) =
      if α = Sym.replicate j i then 1 else 0 := by
  classical
  by_cases hα : α = Sym.replicate j i
  · rw [hα, ite_eq_left rfl, monomial_replicate]
    simp
  · rw [ite_eq_right hα]
    have hex : ∃ b ∈ α, b ≠ i := by
      by_contra! h
      exact hα (Sym.eq_replicate_iff.mpr h)
    obtain ⟨b, hb, hbi⟩ := hex
    have hcount : (α : Multiset (Fin n)).count b ≠ 0 :=
      (Multiset.count_pos.mpr hb).ne'
    have hval : EuclideanSpace.basisFun (Fin n) ℝ i b = 0 := by
      simp [EuclideanSpace.basisFun_apply, Ne.symm hbi]
    unfold monomial
    exact Finset.prod_eq_zero (Finset.mem_univ b) (by rw [hval, zero_pow hcount])

/-- Normal data in a coordinate unit direction are precisely the
ordinary pure coordinate derivatives, with no combinatorial factor. -/
theorem normalData_basisFun (u : ℝ^n → ℝ) (i : Fin n) (x : ℝ^n) :
    normalData j u (EuclideanSpace.basisFun (Fin n) ℝ i) x =
      coordinateDeriv (Sym.replicate j i) u x := by
  unfold normalData coordinateDeriv
  congr 1
  funext r
  simp only [directions, Sym.sortedTuple_replicate]

end PDE.Analysis.MultiIndex
