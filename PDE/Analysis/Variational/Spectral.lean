/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Spectral.CompactSelfAdjoint
public import PDE.Analysis.Variational.LaxMilgram

/-!
# Eigenfunctions of symmetric coercive variational forms

Let `B` be a symmetric coercive form on a real Hilbert space `V`, and let `j : V →L[ℝ] H`
be compact with dense range in a second Hilbert space. Solving
`B(u,v) = ⟪f, j v⟫` and mapping the solution into `H` gives a compact self-adjoint operator
on `H`. Its quadratic form is strictly positive by coercivity and density.

The compact spectral theorem therefore supplies a Hilbert basis `b` of `H` and lifts
`u i : V` satisfying `j (u i) = b i` and `B(u i,v) = λ i * ⟪b i, j v⟫`, with `λ i > 0`.
The map `j` need not be injective. No ordering or natural-number enumeration is asserted.

The Hilbert structure used for diagonalization is the one on `H`. Symmetry of `B` does
not generally make the mass-to-solution operator self-adjoint in the original norm on `V`.

## Main definitions

* `pivotLoadCLM j f`: the load `v ↦ ⟪f, j v⟫` on `V`.
* `pivotSolutionOperator B hB j`: the map `f ↦ j u`, where `u ∈ V` solves
  `B(u, v) = ⟪f, j v⟫` for all `v`.

## Main results

* `isCompactOperator_pivotSolutionOperator`, `isSymmetric_pivotSolutionOperator`,
  `inner_pivotSolutionOperator_pos`: the solution operator is compact, symmetric when `B` is,
  and positive definite.
* `exists_hilbertBasis_weakEigenfunctions`: a Hilbert basis `b` of `H`, positive eigenvalues
  `λ i` and lifts `u i` with `j (u i) = b i` and `B(u i, v) = λ i ⟪b i, j v⟫`.

## How it works

This is Evans, §6.5.1, Theorem 1(iii), for an abstract form, with `V`, `H` and `j` in place of
`H¹₀(U)`, `L²(U)` and the inclusion. Steps 1-3 of his proof show that `S = L⁻¹` is compact,
symmetric and nonnegative on `L²(U)`. Our counterparts are
`isCompactOperator_pivotSolutionOperator`, `isSymmetric_pivotSolutionOperator` and
`inner_pivotSolutionOperator_pos`, and `inner_pivotSolutionOperator` is his identity
`(f, Sg) = B[u, v]`. Where Evans has `(Sf, f) ≥ 0`,
coercivity and the density of the range of `j` give strict positivity, so every eigenvalue `η`
of `S` is positive and `λ = 1 / η`. The spectral theorem for compact symmetric operators,
Evans's Appendix D.6, Theorem 7, is `PDE.Analysis.Spectral.exists_hilbertBasis_eigenvectors`.
We do not prove the ordering and the growth `λ_k → ∞` of his part (ii).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.5.1, Theorem 1 (Eigenvalues of symmetric elliptic
  operators) and its proof, pp. 355-356, and Appendix D.6, Theorem 7, pp. 728-729.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

universe u v

namespace PDE.Analysis.Variational

open scoped InnerProductSpace

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A vector in the pivot Hilbert space acts on test functions through `v ↦ ⟪f, j v⟫`. -/
def pivotLoadCLM (j : V →L[ℝ] H) : H →L[ℝ] StrongDual ℝ V :=
  (InnerProductSpace.toDual ℝ V).toContinuousLinearEquiv.toContinuousLinearMap.comp j.adjoint

/-- Evaluation of the load induced by the pivot pairing. -/
@[simp]
theorem pivotLoadCLM_apply (j : V →L[ℝ] H) (f : H) (v : V) :
    pivotLoadCLM j f v = ⟪f, j v⟫_ℝ := by
  change ⟪j.adjoint f, v⟫_ℝ = ⟪f, j v⟫_ℝ
  exact j.adjoint_inner_left v f

/-- Dense range ensures that testing against `j v` distinguishes pivot-space loads. -/
theorem pivotLoadCLM_injective (j : V →L[ℝ] H) (hdense : DenseRange j) :
    Function.Injective (pivotLoadCLM j) := by
  intro f g h
  apply ext_inner_right ℝ
  intro y
  refine hdense.induction_on y (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro v
  simpa using DFunLike.congr_fun h v

/-- Solve the coercive equation for a pivot-space load, then view its solution in the
pivot space. The resulting operator is compact when `j` is compact. -/
def pivotSolutionOperator (B : V →L[ℝ] StrongDual ℝ V) (hB : IsCoercive B)
    (j : V →L[ℝ] H) : H →L[ℝ] H :=
  j.comp ((solveCLM B hB).comp (pivotLoadCLM j))

/-- The pivot pairing of a load with a solution equals the form evaluated on the two
variational solutions. This identity transfers symmetry and positivity from the form. -/
theorem inner_pivotSolutionOperator
    (B : V →L[ℝ] StrongDual ℝ V) (hB : IsCoercive B) (j : V →L[ℝ] H) (f g : H) :
    ⟪f, pivotSolutionOperator B hB j g⟫_ℝ =
      B (solveCLM B hB (pivotLoadCLM j f)) (solveCLM B hB (pivotLoadCLM j g)) := by
  simpa [pivotSolutionOperator] using
    (solveCLM.isWeakSolution B hB (pivotLoadCLM j f)
      (solveCLM B hB (pivotLoadCLM j g))).symm

/-- Compactness of the map into the pivot space makes the pivot solution operator compact. -/
theorem isCompactOperator_pivotSolutionOperator
    (B : V →L[ℝ] StrongDual ℝ V) (hB : IsCoercive B)
    (j : V →L[ℝ] H) (hcompact : IsCompactOperator j) :
    IsCompactOperator (pivotSolutionOperator B hB j) :=
  hcompact.comp_clm ((solveCLM B hB).comp (pivotLoadCLM j))

/-- A symmetric form gives a self-adjoint solution operator on the pivot Hilbert space. -/
theorem isSymmetric_pivotSolutionOperator
    (B : V →L[ℝ] StrongDual ℝ V) (hB : IsCoercive B)
    (hsymm : ∀ u v, B u v = B v u) (j : V →L[ℝ] H) :
    (pivotSolutionOperator B hB j).IsSymmetric := by
  intro f g
  simp only [ContinuousLinearMap.coe_coe]
  rw [real_inner_comm g (pivotSolutionOperator B hB j f),
    inner_pivotSolutionOperator, inner_pivotSolutionOperator]
  exact hsymm _ _

/-- Coercivity and dense range make the quadratic form of the pivot solution operator
strictly positive on nonzero loads. Neither symmetry nor compactness is needed here. -/
theorem inner_pivotSolutionOperator_pos
    (B : V →L[ℝ] StrongDual ℝ V) (hB : IsCoercive B)
    (j : V →L[ℝ] H) (hdense : DenseRange j) {f : H} (hf : f ≠ 0) :
    0 < ⟪f, pivotSolutionOperator B hB j f⟫_ℝ := by
  have hload : pivotLoadCLM j f ≠ 0 := by
    intro h
    exact hf (pivotLoadCLM_injective j hdense (h.trans (map_zero _).symm))
  have hsolution : solveCLM B hB (pivotLoadCLM j f) ≠ 0 := by
    intro h
    apply hload
    ext v
    have hweak := solveCLM.isWeakSolution B hB (pivotLoadCLM j f) v
    rw [h] at hweak
    simpa using hweak.symm
  have hBcopy : IsCoercive B := hB
  obtain ⟨c, hc, hcoercive⟩ := hBcopy
  rw [inner_pivotSolutionOperator]
  exact (mul_pos (mul_pos hc (norm_pos_iff.mpr hsolution))
    (norm_pos_iff.mpr hsolution)).trans_le (hcoercive _)

/-- A symmetric coercive form and a compact map with dense range into `H` admit a complete
orthonormal family in `H` whose lifts solve the weak eigenvalue equation. The eigenvalues
are positive. Completeness is expressed by a Mathlib `HilbertBasis`, so its expansion and
Parseval APIs apply directly. -/
theorem exists_hilbertBasis_weakEigenfunctions
    (B : V →L[ℝ] StrongDual ℝ V) (hB : IsCoercive B)
    (hsymm : ∀ u v, B u v = B v u) (j : V →L[ℝ] H)
    (hcompact : IsCompactOperator j) (hdense : DenseRange j) :
    ∃ (ι : Type v) (b : HilbertBasis ι ℝ H) (lambda : ι → ℝ) (u : ι → V),
      ∀ i, 0 < lambda i ∧ j (u i) = b i ∧
        ∀ v, B (u i) v = lambda i * ⟪b i, j v⟫_ℝ := by
  obtain ⟨ι, b, μ, heigen⟩ := Spectral.exists_hilbertBasis_eigenvectors
    (pivotSolutionOperator B hB j) (isCompactOperator_pivotSolutionOperator B hB j hcompact)
    (isSymmetric_pivotSolutionOperator B hB hsymm j)
  have happly (i : ι) : pivotSolutionOperator B hB j (b i) = μ i • b i :=
    Module.End.mem_eigenspace_iff.mp (heigen i).1
  have hpos (i : ι) : 0 < μ i := by
    have h := inner_pivotSolutionOperator_pos B hB j hdense (heigen i).2
    rwa [happly i, real_inner_smul_right, real_inner_self_eq_norm_sq,
      b.orthonormal.1 i, one_pow, mul_one] at h
  let u (i : ι) : V := (μ i)⁻¹ • solveCLM B hB (pivotLoadCLM j (b i))
  refine ⟨ι, b, fun i ↦ (μ i)⁻¹, u, fun i ↦ ⟨inv_pos.mpr (hpos i), ?_, ?_⟩⟩
  · change j ((μ i)⁻¹ • solveCLM B hB (pivotLoadCLM j (b i))) = b i
    rw [map_smul]
    change (μ i)⁻¹ • pivotSolutionOperator B hB j (b i) = b i
    rw [happly, smul_smul, inv_mul_cancel₀ (hpos i).ne', one_smul]
  · intro v
    change B ((μ i)⁻¹ • solveCLM B hB (pivotLoadCLM j (b i))) v =
      (μ i)⁻¹ * ⟪b i, j v⟫_ℝ
    rw [map_smul, smul_apply, smul_eq_mul,
      solveCLM.isWeakSolution B hB (pivotLoadCLM j (b i)) v, pivotLoadCLM_apply]

end PDE.Analysis.Variational
