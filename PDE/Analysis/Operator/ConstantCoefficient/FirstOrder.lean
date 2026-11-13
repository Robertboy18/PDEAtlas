/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Operator.ConstantCoefficient.Polynomial

/-!
# First-order matrix symbols and their determinant operators

The homogeneous polynomial matrix associated with constant matrices `Aₖ`
is `∑ₖ Aₖ Xₖ`. Evaluating its determinant on a real covector gives the
determinant of the usual matrix symbol. Evaluating at commuting derivatives
gives the component equations, and the adjugate identity gives their
scalar determinant equation.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

variable {R M ι κ : Type*} [CommRing R] [Fintype ι]

/-- The homogeneous polynomial matrix of a constant first-order system. -/
def firstOrderPolynomialMatrix (A : ι → Matrix κ κ R) :
    Matrix κ κ (MvPolynomial ι R) :=
  fun i j ↦ ∑ k, MvPolynomial.C (A k i j) * MvPolynomial.X k

/-- Evaluation on a covector gives the usual matrix symbol. -/
theorem firstOrderPolynomialMatrix_eval (A : ι → Matrix κ κ R) (ξ : ι → R) :
    (firstOrderPolynomialMatrix A).map (MvPolynomial.eval ξ) = ∑ k, ξ k • A k := by
  ext i j
  simp [firstOrderPolynomialMatrix, Matrix.sum_apply, mul_comm]

/-- The determinant polynomial evaluated on a covector is exactly the
determinant of the matrix symbol; this is the noncharacteristic condition. -/
theorem firstOrderPolynomialMatrix_det_eval [Fintype κ] [DecidableEq κ]
    (A : ι → Matrix κ κ R) (ξ : ι → R) :
    MvPolynomial.eval ξ (firstOrderPolynomialMatrix A).det = (∑ k, ξ k • A k).det := by
  rw [← firstOrderPolynomialMatrix_eval A ξ]
  exact (MvPolynomial.eval₂Hom (RingHom.id R) ξ).map_det _

variable [AddCommGroup M] [Module R M]

/-- Evaluation at commuting operators gives the original first-order
component expression, including every signed matrix entry. -/
theorem firstOrderPolynomialMatrix_apply
    (D : ι → Module.End R M) (hD : ∀ i j, Commute (D i) (D j))
    (A : ι → Matrix κ κ R) (i j : κ) (u : M) :
    commutingPolynomialEval D hD (firstOrderPolynomialMatrix A i j) u =
      ∑ k, A k i j • D k u := by
  simp [firstOrderPolynomialMatrix, map_sum, map_mul, Module.End.mul_apply]

/-- Every component of a constant first-order system satisfies its determinant
operator equation. The entries act on arbitrary module elements. -/
theorem firstOrderPolynomialMatrix_determinant_annihilates
    [Fintype κ] [DecidableEq κ]
    (D : ι → Module.End R M) (hD : ∀ i j, Commute (D i) (D j))
    (A : ι → Matrix κ κ R) (u : κ → M)
    (hu : ∀ i, ∑ j, ∑ k, A k i j • D k (u j) = 0) :
    ∀ i, commutingPolynomialEval D hD (firstOrderPolynomialMatrix A).det (u i) = 0 := by
  apply polynomialDeterminant_annihilates
  intro i
  simpa only [firstOrderPolynomialMatrix_apply] using hu i

end PDE.Analysis
