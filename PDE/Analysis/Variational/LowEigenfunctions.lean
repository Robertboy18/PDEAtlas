/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.Spectral
public import PDE.Analysis.Variational.MinMax
import PDE.Analysis.InnerProductSpace.FactorThrough

/-!
# Rayleigh bounds orthogonal to the low eigenfunctions

Let `B` be a symmetric coercive form on a real Hilbert space `V` and `j : V →L[ℝ] H` a compact
map into a real Hilbert space. A weak eigenfunction of eigenvalue `λ` is a vector `w` with
`B(w, v) = λ ⟪j w, j v⟫` for every `v`. If the image `j u` is orthogonal to `j w` for every
weak eigenfunction `w` of eigenvalue `λ < r`, then `r ‖j u‖² ≤ B(u, u)`
(`mul_norm_sq_le_of_inner_weakEigenfunction_eq_zero`).

The proof diagonalizes the problem in the closure of the range of `j`, where `j` has dense
range (`exists_hilbertBasis_weakEigenfunctions`, `LinearMap.denseRange_closureRangeRestrict`),
and applies Parseval's identity with the low modes removed
(`mul_norm_sq_le_energy_of_orthogonal`). Neither dense range nor injectivity of `j` nor
infinite dimension is assumed, and `r` is any real number.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Variational

open scoped InnerProductSpace

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Rayleigh bound orthogonal to the low eigenfunctions.** If the image `j u` is orthogonal to
the image of every weak eigenfunction of eigenvalue below `r`, then `r ‖j u‖² ≤ B(u, u)`. -/
theorem mul_norm_sq_le_of_inner_weakEigenfunction_eq_zero
    (B : V →L[ℝ] StrongDual ℝ V) (hB : IsCoercive B)
    (hsymm : ∀ v w, B v w = B w v) (j : V →L[ℝ] H)
    (hcompact : IsCompactOperator j) (r : ℝ) (u : V)
    (horth : ∀ (lambda : ℝ) (w : V), lambda < r →
      (∀ v, B w v = lambda * ⟪j w, j v⟫_ℝ) → ⟪j w, j u⟫_ℝ = 0) :
    r * ‖j u‖ ^ 2 ≤ B u u := by
  set K : Submodule ℝ H := (LinearMap.range (j : V →ₗ[ℝ] H)).topologicalClosure
  have hKclosed : IsClosed (K : Set H) := Submodule.isClosed_topologicalClosure _
  have : CompleteSpace K := hKclosed.completeSpace_coe
  have hmem : ∀ v, j v ∈ K := fun v ↦ Submodule.le_topologicalClosure _ ⟨v, rfl⟩
  set j' : V →L[ℝ] K := j.codRestrict K hmem
  have hcompact' : IsCompactOperator j' := hcompact.codRestrict hmem hKclosed
  obtain ⟨ι, b, lambda, w, h⟩ := exists_hilbertBasis_weakEigenfunctions B hB hsymm j'
    hcompact' (LinearMap.denseRange_closureRangeRestrict (j : V →ₗ[ℝ] H))
  have hnonneg (v : V) : 0 ≤ B v v := by
    obtain ⟨c, hc, hcoercive⟩ := hB
    exact (mul_nonneg (mul_nonneg hc.le (norm_nonneg v)) (norm_nonneg v)).trans (hcoercive v)
  have hlow (i : ι) (hi : lambda i < r) : ⟪b i, j' u⟫_ℝ = 0 := by
    have hw (v : V) : B (w i) v = lambda i * ⟪j (w i), j v⟫_ℝ := by
      rw [(h i).2.2 v, ← (h i).2.1, Submodule.coe_inner]
      rfl
    rw [← (h i).2.1, Submodule.coe_inner]
    exact horth (lambda i) (w i) hi hw
  exact mul_norm_sq_le_energy_of_orthogonal B hnonneg hsymm j' b lambda w (fun i ↦ (h i).2.1)
    (fun i v ↦ (h i).2.2 v) {i | lambda i < r} r (fun i hi ↦ not_lt.mp hi) u hlow

end PDE.Analysis.Variational
