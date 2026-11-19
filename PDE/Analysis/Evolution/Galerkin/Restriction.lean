/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Subspace
public import PDE.Analysis.Evolution.Core.WeakEvolution
import Mathlib.Tactic.Positivity.Finset

/-!
# Restriction to Galerkin trial spaces

Continuous functionals and bilinear forms on a Hilbert space restrict to any
linear trial subspace without increasing their ambient norm bounds.  The
restriction preserves linear operations, coercivity, nonnegativity, and the
pointwise weak evolution equation tested against trial vectors.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, equations (14)-(16).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section


open Set

namespace PDE.Analysis.Evolution

open Function Filter
open scoped Topology InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

section Galerkin
/-! ## Galerkin restriction

Galerkin approximate solutions (Evans §7.1.2) live in finite-dimensional
subspaces of the energy space. The estimates follow from restricting the form
and forcing to the trial space, a dimension-independent step that works for
arbitrary linear subspaces. Finite-dimensional Galerkin spaces are the
principal special case.
-/

/-- Continuous restriction map from the ambient dual to the dual of a trial
subspace. -/
def restrictFunctionalMap (S : Submodule ℝ V) :
    StrongDual ℝ V →L[ℝ] StrongDual ℝ S :=
  (ContinuousLinearMap.compL ℝ S V ℝ).flip S.subtypeL

/-- Restriction of a dual vector to a trial subspace. -/
def restrictFunctional (S : Submodule ℝ V)
    (ell : StrongDual ℝ V) : StrongDual ℝ S :=
  restrictFunctionalMap S ell

/-- Restricting a functional evaluates it on the underlying ambient trial vector. -/
@[simp]
theorem restrictFunctional_apply (S : Submodule ℝ V)
    (ell : StrongDual ℝ V) (v : S) :
    restrictFunctional S ell v = ell (v : V) :=
  rfl

/-- Restriction to a trial space cannot increase the dual norm. -/
theorem norm_restrictFunctional_le (S : Submodule ℝ V)
    (ell : StrongDual ℝ V) : ‖restrictFunctional S ell‖ ≤ ‖ell‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg ell) (fun v ↦ ?_)
  simpa using ell.le_opNorm (v : V)

/-- Restriction sends the zero functional to zero. -/
@[simp]
theorem restrictFunctional_zero (S : Submodule ℝ V) :
    restrictFunctional S 0 = 0 := by
  rfl

/-- Restriction preserves addition of functionals. -/
@[simp]
theorem restrictFunctional_add (S : Submodule ℝ V)
    (ell₁ ell₂ : StrongDual ℝ V) :
    restrictFunctional S (ell₁ + ell₂) =
      restrictFunctional S ell₁ + restrictFunctional S ell₂ := by
  rfl

/-- Restriction preserves negation of functionals. -/
@[simp]
theorem restrictFunctional_neg (S : Submodule ℝ V)
    (ell : StrongDual ℝ V) :
    restrictFunctional S (-ell) = -restrictFunctional S ell := by
  rfl

/-- Restriction preserves subtraction of functionals. -/
@[simp]
theorem restrictFunctional_sub (S : Submodule ℝ V)
    (ell₁ ell₂ : StrongDual ℝ V) :
    restrictFunctional S (ell₁ - ell₂) =
      restrictFunctional S ell₁ - restrictFunctional S ell₂ := by
  rfl

/-- Restriction preserves real scalar multiplication of functionals. -/
@[simp]
theorem restrictFunctional_smul (S : Submodule ℝ V)
    (c : ℝ) (ell : StrongDual ℝ V) :
    restrictFunctional S (c • ell) = c • restrictFunctional S ell := by
  rfl

/-- Continuous ambient forcing remains continuous after restriction to any
trial space. -/
theorem continuousOn_restrictFunctional
    (S : Submodule ℝ V) {ell : ℝ → StrongDual ℝ V} {s : Set ℝ}
    (hell : ContinuousOn ell s) :
    ContinuousOn (fun t ↦ restrictFunctional S (ell t)) s :=
  (restrictFunctionalMap S).continuous.comp_continuousOn hell

/-- Restriction of both arguments of a continuous bilinear form to a trial
subspace (closedness is not required). -/
def restrictForm (S : Submodule ℝ V)
    (B : V →L[ℝ] StrongDual ℝ V) : S →L[ℝ] StrongDual ℝ S :=
  ((ContinuousLinearMap.precompR S B).flip S.subtypeL).comp S.subtypeL

/-- The restricted bilinear form agrees with the ambient form on trial vectors. -/
@[simp]
theorem restrictForm_apply (S : Submodule ℝ V)
    (B : V →L[ℝ] StrongDual ℝ V) (u v : S) :
    restrictForm S B u v = B (u : V) (v : V) :=
  by simp [restrictForm]

/-- Restricting the form at a trial vector is the restriction of the ambient
functional represented by that vector. -/
theorem restrictForm_apply_eq_restrictFunctional
    (S : Submodule ℝ V) (B : V →L[ℝ] StrongDual ℝ V) (u : S) :
    restrictForm S B u = restrictFunctional S (B (u : V)) := by
  ext v
  simp

/-- Pointwise restriction of a form cannot increase its ambient norm bound. -/
theorem norm_restrictForm_apply_le
    (S : Submodule ℝ V) (B : V →L[ℝ] StrongDual ℝ V) (u : S) :
    ‖restrictForm S B u‖ ≤ ‖B‖ * ‖u‖ := by
  rw [restrictForm_apply_eq_restrictFunctional]
  exact (norm_restrictFunctional_le S (B (u : V))).trans (B.le_opNorm (u : V))

/-- Restriction sends the zero bilinear form to zero. -/
@[simp]
theorem restrictForm_zero (S : Submodule ℝ V) :
    restrictForm S (0 : V →L[ℝ] StrongDual ℝ V) = 0 := by
  ext u v
  simp

/-- Restriction preserves addition of bilinear forms. -/
@[simp]
theorem restrictForm_add (S : Submodule ℝ V)
    (B₁ B₂ : V →L[ℝ] StrongDual ℝ V) :
    restrictForm S (B₁ + B₂) = restrictForm S B₁ + restrictForm S B₂ := by
  ext u v
  simp

/-- Restriction preserves negation of bilinear forms. -/
@[simp]
theorem restrictForm_neg (S : Submodule ℝ V)
    (B : V →L[ℝ] StrongDual ℝ V) :
    restrictForm S (-B) = -restrictForm S B := by
  ext u v
  simp

/-- Restriction preserves subtraction of bilinear forms. -/
@[simp]
theorem restrictForm_sub (S : Submodule ℝ V)
    (B₁ B₂ : V →L[ℝ] StrongDual ℝ V) :
    restrictForm S (B₁ - B₂) = restrictForm S B₁ - restrictForm S B₂ := by
  ext u v
  simp

/-- Restriction preserves real scalar multiplication of bilinear forms. -/
@[simp]
theorem restrictForm_smul (S : Submodule ℝ V)
    (c : ℝ) (B : V →L[ℝ] StrongDual ℝ V) :
    restrictForm S (c • B) = c • restrictForm S B := by
  ext u v
  simp

/-- Ambient coercivity is inherited by every Galerkin trial space with the
same constant.  This is why the energy estimates are uniform in the Galerkin
dimension. -/
theorem restrictForm_coercive (S : Submodule ℝ V)
    (B : V →L[ℝ] StrongDual ℝ V) {C : ℝ}
    (hB : ∀ u : V, C * ‖u‖ ^ 2 ≤ B u u) :
    ∀ u : S, C * ‖u‖ ^ 2 ≤ restrictForm S B u u := by
  intro u
  simpa using hB (u : V)

/-- Nonnegativity of the ambient form is inherited by every trial space. -/
theorem restrictForm_nonnegative (S : Submodule ℝ V)
    (B : V →L[ℝ] StrongDual ℝ V)
    (hB : ∀ u : V, 0 ≤ B u u) :
    ∀ u : S, 0 ≤ restrictForm S B u u := by
  intro u
  simpa using hB (u : V)

/-- The restricted weak equation is exactly the ambient equation tested only
against vectors in the trial space. -/
theorem satisfiesWeakEvolutionAt_restrict_iff
    (S : Submodule ℝ V) (B : V →L[ℝ] StrongDual ℝ V)
    (ell : StrongDual ℝ V) (u du : S) :
    SatisfiesWeakEvolutionAt (restrictForm S B) (restrictFunctional S ell) u du ↔
      ∀ v : S, inner ℝ (du : V) (v : V) + B (u : V) (v : V) = ell (v : V) := by
  simp only [SatisfiesWeakEvolutionAt, restrictForm_apply, restrictFunctional_apply]
  rfl

end Galerkin

end PDE.Analysis.Evolution
