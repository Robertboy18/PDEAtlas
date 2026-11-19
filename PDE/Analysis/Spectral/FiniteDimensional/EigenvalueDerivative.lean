/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.LinearAlgebra.Eigenbasis
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Differentiating an eigenvalue in fixed eigenvector coordinates

Differentiate a local eigenvector equation and apply its left
coordinate at the base point. The derivatives of the eigenvector cancel.
The result uses a finite eigenbasis, without orthogonality or symmetry.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace Module.Basis

variable {ι X E : Type*} [Finite ι]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative of an eigenvalue is obtained by applying its left coordinate
to the derivative of the operator acting on its right eigenvector. The local
eigenvector and eigenvalue equations hold identically near the base point. -/
theorem fderiv_eigenvalue_apply
    (b : Basis ι ℝ E) {A : X → E →L[ℝ] E} {r : X → E} {a : X → ℝ}
    {x : X} (eig : ι → ℝ) (k : ι)
    (hdiag : ∀ j, A x (b j) = eig j • b j)
    (hA : DifferentiableAt ℝ A x) (hr : DifferentiableAt ℝ r x)
    (ha : DifferentiableAt ℝ a x) (hrx : r x = b k) (hax : a x = eig k)
    (heigen : ∀ᶠ y in 𝓝 x, A y (r y) = a y • r y) (v : X) :
    fderiv ℝ a x v = b.equivFun (fderiv ℝ A x v (b k)) k := by
  classical
  have hl := hA.hasFDerivAt.clm_apply hr.hasFDerivAt
  have hr' := ha.hasFDerivAt.smul hr.hasFDerivAt
  have hd := hl.unique (hr'.congr_of_eventuallyEq heigen)
  have hc := congrArg (fun D : X →L[ℝ] E ↦ b.equivFun (D v) k) hd
  change b.equivFun (A x (fderiv ℝ r x v) + fderiv ℝ A x v (r x)) k =
    b.equivFun (a x • fderiv ℝ r x v + (fderiv ℝ a x v) • r x) k at hc
  have hcoord : b.equivFun (A x (fderiv ℝ r x v)) k =
      eig k * b.equivFun (fderiv ℝ r x v) k :=
    b.equivFun_apply_of_apply_basis_eq_smul
      (A x).toLinearMap eig hdiag (fderiv ℝ r x v) k
  simp only [hrx, hax, map_add, map_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Basis.equivFun_self, ite_eq_left, mul_one] at hc
  rw [hcoord] at hc
  exact (add_left_cancel hc).symm

end Module.Basis
