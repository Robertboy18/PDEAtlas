/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import PDE.LinearAlgebra.Eigenbasis

/-!
# The inner-product dual of an eigenbasis

Riesz representation transports the algebraic dual basis back to the original
real inner product space. It diagonalizes the adjoint with the same eigenvalues.
No symmetry or orthogonality assumption on the original basis is needed.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace Module.Basis

variable {ι E : Type*} [Finite ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

open scoped Classical in
/-- The basis representing the coordinate functionals by the inner product. -/
def innerDual (b : Basis ι ℝ E) : Basis ι ℝ E :=
  (b.dualBasis.map LinearMap.toContinuousLinearMap).map
    (InnerProductSpace.toDual ℝ E).symm.toLinearEquiv

/-- Pairing with the inner-product dual basis recovers the corresponding coordinate. -/
theorem inner_innerDual (b : Basis ι ℝ E) (i : ι) (x : E) :
    ⟪b.innerDual i, x⟫_ℝ = b.equivFun x i := by
  classical
  simp [innerDual]

/-- The inner-product dual of a diagonalizing basis diagonalizes the adjoint. -/
theorem adjoint_apply_innerDual (b : Basis ι ℝ E) (A : E →L[ℝ] E)
    (eig : ι → ℝ) (hA : ∀ i, A (b i) = eig i • b i) (i : ι) :
    ContinuousLinearMap.adjoint A (b.innerDual i) = eig i • b.innerDual i := by
  apply ext_inner_right ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_left, inner_innerDual, real_inner_smul_left,
    inner_innerDual]
  exact b.equivFun_apply_of_apply_basis_eq_smul A.toLinearMap eig hA x i

/-- A nonzero adjoint eigenvector pairs nontrivially with precisely the matching
vector of a simple eigenbasis. Unit normalization does not force this pairing to be one. -/
theorem inner_adjoint_eigenvector_eq_zero_iff
    (b : Basis ι ℝ E) (A : E →L[ℝ] E) (eig : ι → ℝ)
    (hinj : Function.Injective eig) (hA : ∀ i, A (b i) = eig i • b i)
    {w : E} (hw : w ≠ 0) (k : ι)
    (hAw : ContinuousLinearMap.adjoint A w = eig k • w) (i : ι) :
    ⟪w, b i⟫_ℝ = 0 ↔ i ≠ k := by
  classical
  obtain ⟨c, hc, rfl⟩ := b.innerDual.exists_ne_zero_smul_eq_of_eigenvectors
    (ContinuousLinearMap.adjoint A).toLinearMap eig hinj
    (b.adjoint_apply_innerDual A eig hA) (b.innerDual.ne_zero k) hw
    (b.adjoint_apply_innerDual A eig hA k) hAw
  rw [real_inner_smul_left, inner_innerDual]
  simp [hc, eq_comm]

end Module.Basis
