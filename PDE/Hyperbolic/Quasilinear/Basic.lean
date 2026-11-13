/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# One-dimensional quasilinear systems

The coefficient field in `u_t + B(u)u_x = 0` is an arbitrary field of real
linear endomorphisms. It need not be the Jacobian of a flux. Time is coordinate
zero and space is coordinate one. The system is (21) of Evans, §11.1.2, where `B` is also an
arbitrary matrix field.

Strict hyperbolicity is expressed by a real eigenbasis with distinct speeds.
At each state this is equivalent to Evans's definition in §11.1.2, `m` distinct real
eigenvalues (`isStrictlyHyperbolicAt_iff_hasEigenvalue`); the eigenbasis consists of the right
eigenvectors (25).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.1.2, equation (21), the definition of strictly
  hyperbolic, and Notation (24)-(25).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.Quasilinear

variable {m : ℕ}

/-- The quasilinear residual for a general coefficient field. -/
def residual (B : ℝ^m → ℝ^m →L[ℝ] ℝ^m) (u : ℝ^2 → ℝ^m) (p : ℝ^2) : ℝ^m :=
  (∂[0] u) p + B (u p) ((∂[1] u) p)

/-- A differentiable solution of the general quasilinear system on a set. -/
structure IsClassicalSolutionOn
    (B : ℝ^m → ℝ^m →L[ℝ] ℝ^m) (U : Set ℝ^2) (u : ℝ^2 → ℝ^m) : Prop where
  /-- The solution is differentiable at every point of the domain. -/
  differentiableAt : ∀ p ∈ U, DifferentiableAt ℝ u p
  /-- The equation holds at every point of the domain. -/
  residual_eq_zero : ∀ p ∈ U, residual B u p = 0

/-- Strict hyperbolicity of a coefficient field at a state: a full real
eigenbasis with pairwise distinct characteristic speeds. -/
def IsStrictlyHyperbolicAt (B : ℝ^m → ℝ^m →L[ℝ] ℝ^m) (state : ℝ^m) : Prop :=
  ∃ b : Module.Basis (Fin m) ℝ (ℝ^m), ∃ speed : Fin m → ℝ,
    Function.Injective speed ∧
      ∀ k, Module.End.HasEigenvector (B state).toLinearMap (speed k) (b k)

/-- In dimension `m`, the spectral hypothesis of `m` distinct real eigenvalues
already supplies the full eigenbasis in the strict hyperbolicity predicate. -/
theorem isStrictlyHyperbolicAt_iff_hasEigenvalue {B : ℝ^m → ℝ^m →L[ℝ] ℝ^m} {state : ℝ^m} :
    IsStrictlyHyperbolicAt B state ↔ ∃ speed : Fin m → ℝ, Function.Injective speed ∧ ∀ k,
      Module.End.HasEigenvalue (B state).toLinearMap (speed k) := by
  classical
  constructor
  · rintro ⟨b, speed, hinj, heigen⟩
    exact ⟨speed, hinj, fun k ↦ Module.End.hasEigenvalue_of_hasEigenvector (heigen k)⟩
  · rintro ⟨speed, hinj, heigen⟩
    choose v hv using fun k ↦ (heigen k).exists_hasEigenvector
    have hli := Module.End.eigenvectors_linearIndependent' (B state).toLinearMap speed hinj v hv
    let b := basisOfLinearIndependentOfCardEqFinrank' v hli (by simp)
    exact ⟨b, speed, hinj, by simpa only [b, coe_basisOfLinearIndependentOfCardEqFinrank'] using hv⟩

end PDE.Hyperbolic.Quasilinear
