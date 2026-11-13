/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.Spectral
public import PDE.Analysis.Variational.MinMax
import PDE.Analysis.Spectral.Enumeration

/-!
# Ordered variational spectrum and minmax

A symmetric coercive form with a compact, dense map into an infinite-dimensional
pivot Hilbert space admits a sequence of positive weak eigenvalues tending to
infinity. The sequence is nondecreasing and counts multiplicities. The pivot
images of the corresponding weak eigenfunctions form a Hilbert basis.

The eigenvalue at index `k` is the least uniform Rayleigh bound on a subspace of
dimension `k + 1`. This formulation uses `B v v ≤ r * ‖j v‖²`, avoiding division
at zero. It also permits a kernel for `j`: a subspace with such a finite bound
cannot contain a nonzero vector in that kernel.

Infinite dimension is used only to obtain an enumeration by all of `ℕ`. The
finite-mode minmax theorem in `Variational.MinMax` also applies to finite spectra.

Without the minmax clause, this is an abstract form of the ordering and growth of the
eigenvalues in Evans, §6.5.1, Theorem 1 (ii), and of the eigenbasis of Theorem 1 (iii). There
`V = H¹₀(U)`, `H = L²(U)`, `j` is the inclusion and the weak eigenfunctions solve (4).

## Main results

* `exists_ordered_hilbertBasis_weakEigenfunctions`: if `H` is infinite-dimensional, there are
  a Hilbert basis `b` of `H` indexed by `ℕ`, nondecreasing eigenvalues `λ k > 0` tending to
  infinity and weak eigenfunctions `u k` with `j (u k) = b k`, and `λ k` is the least `r`
  such that some subspace of dimension `k + 1` satisfies `B v v ≤ r ‖j v‖²` on it.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.5.1, Theorem 1 (Eigenvalues of symmetric elliptic
  operators) (ii) and (iii), p. 355. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Variational

open Filter
open scoped InnerProductSpace

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A compact, densely mapped symmetric coercive problem on an infinite-dimensional
pivot space has an ordered complete weak eigenfamily. Its positive eigenvalues
tend to infinity and satisfy the minmax principle, with multiplicities retained
and indexing beginning at zero. -/
theorem exists_ordered_hilbertBasis_weakEigenfunctions
    (B : V →L[ℝ] StrongDual ℝ V) (hB : IsCoercive B)
    (hsymm : ∀ v w, B v w = B w v) (j : V →L[ℝ] H)
    (hcompact : IsCompactOperator j) (hdense : DenseRange j)
    (hH : ¬FiniteDimensional ℝ H) :
    ∃ (b : HilbertBasis ℕ ℝ H) (lambda : ℕ → ℝ) (u : ℕ → V),
      Monotone lambda ∧ Tendsto lambda atTop atTop ∧
      (∀ i, 0 < lambda i ∧ j (u i) = b i ∧
        ∀ v, B (u i) v = lambda i * ⟪b i, j v⟫_ℝ) ∧
      ∀ k, IsLeast {r : ℝ | ∃ W : Submodule ℝ V,
        Module.finrank ℝ W = k + 1 ∧ ∀ v ∈ W, B v v ≤ r * ‖j v‖ ^ 2}
        (lambda k) := by
  classical
  obtain ⟨ι, b, lambda, u, h⟩ :=
    exists_hilbertBasis_weakEigenfunctions B hB hsymm j hcompact hdense
  let R := pivotSolutionOperator B hB j
  have hRcompact : IsCompactOperator R :=
    isCompactOperator_pivotSolutionOperator B hB j hcompact
  have heigen (i : ι) :
      Module.End.HasEigenvector (R : Module.End ℝ H) (lambda i)⁻¹ (b i) := by
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, b.orthonormal.ne_zero i⟩
    have hsolve : solveCLM B hB (pivotLoadCLM j (b i)) = (lambda i)⁻¹ • u i := by
      refine IsWeakSolution.unique B hB (pivotLoadCLM j (b i))
        (solveCLM.isWeakSolution B hB (pivotLoadCLM j (b i))) ?_
      intro v
      rw [map_smul, smul_apply, smul_eq_mul, (h i).2.2 v, ← mul_assoc,
        inv_mul_cancel₀ (h i).1.ne', one_mul, pivotLoadCLM_apply]
    change j (solveCLM B hB (pivotLoadCLM j (b i))) = (lambda i)⁻¹ • b i
    rw [hsolve, map_smul, (h i).2.1]
  have hfinite (r : ℝ) : {i | lambda i ≤ r}.Finite := by
    by_cases hr : 0 < r
    · refine (Spectral.finite_eigenvector_indices_norm_ge R hRcompact
        (fun i ↦ (lambda i)⁻¹) b b.orthonormal.linearIndependent heigen
        (inv_pos.mpr hr)).subset ?_
      intro i hi
      change r⁻¹ ≤ ‖(lambda i)⁻¹‖
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (h i).1)]
      exact inv_anti₀ (h i).1 hi
    · exact Set.finite_empty.subset fun i hi ↦ (hr ((h i).1.trans_le hi)).elim
  have : Infinite ι := ⟨fun hfiniteIndex ↦ by
    let : Fintype ι := @Fintype.ofFinite ι hfiniteIndex
    exact hH b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite⟩
  obtain ⟨e, hmono, htendsto⟩ :=
    Spectral.exists_equiv_nat_monotone_of_finite_sublevel lambda hfinite
  have hrange : Set.range (fun n ↦ b (e n)) = Set.range b := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨e n, rfl⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨n, rfl⟩ := e.surjective i
      exact ⟨n, rfl⟩
  have htotal :
      ⊤ ≤ (Submodule.span ℝ (Set.range (fun n ↦ b (e n)))).topologicalClosure := by
    rw [hrange, b.dense_span]
  let b' : HilbertBasis ℕ ℝ H :=
    HilbertBasis.mk (b.orthonormal.comp e e.injective) htotal
  have hb' (n : ℕ) : b' n = b (e n) := by
    simp only [b', HilbertBasis.coe_mk, Function.comp_apply]
  refine ⟨b', fun n ↦ lambda (e n), fun n ↦ u (e n), hmono, htendsto, ?_, ?_⟩
  · intro i
    simpa only [hb'] using h (e i)
  · intro k
    have hpos (v : V) (hv : v ≠ 0) : 0 < B v v := by
      have hBcopy : IsCoercive B := hB
      obtain ⟨c, hc, hcoercive⟩ := hBcopy
      exact (mul_pos (mul_pos hc (norm_pos_iff.mpr hv))
        (norm_pos_iff.mpr hv)).trans_le (hcoercive v)
    have hmin := isLeast_eigenvalue_minmax B hpos hsymm j b'
      (fun n ↦ lambda (e n)) (fun n ↦ u (e n))
      (fun n ↦ (h (e n)).2.1.trans (hb' n).symm)
      (fun n v ↦ by rw [hb']; exact (h (e n)).2.2 v)
      (Finset.range (k + 1)) k (by simp)
      (fun i hi ↦ hmono (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
      (fun i hi ↦ hmono (Nat.le_trans (Nat.le_succ k)
        (Nat.le_of_not_gt (fun hlt ↦ hi (Finset.mem_range.mpr hlt)))))
    simpa only [Finset.card_range] using hmin

end PDE.Analysis.Variational
