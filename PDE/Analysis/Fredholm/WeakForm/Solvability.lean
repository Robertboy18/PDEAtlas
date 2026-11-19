/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fredholm.WeakForm.Adjoint
import PDE.Analysis.Fredholm.CompactPerturbation.ClosedRange
import PDE.Analysis.Fredholm.WeakForm.Reduction

/-!
# Solvability of shifted Fredholm weak forms

Closed range passes from the compact perturbation `I - K` back to the original
dual-valued weak operator and its Riesz representative. Under the shifted-coercive,
compact-mass assumptions, the adjoint orthogonality criterion therefore holds with
no separate closed-range hypothesis.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.2.3, Theorem 4(iii), p. 321, and step 5 of its proof,
  p. 323. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open Set
open scoped InnerProductSpace
open PDE.Analysis.Variational

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- Compactness of the mass term implies closed range for the original
dual-valued weak operator, not merely for the conjugate `I-K`. -/
theorem isClosed_range_form_of_compact_mass
    (form shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) (lambda : ℝ)
    (hshift : ∀ u v, shiftedForm u v = form u v + lambda * massForm u v)
    (hcompactMass : IsCompactOperator massForm) :
    IsClosed (form.range : Set (StrongDual ℝ V)) := by
  let E := coerciveSolveEquiv shiftedForm coercive
  let K := fredholmOperator shiftedForm massForm coercive lambda
  have hK : IsCompactOperator K :=
    isCompactOperator_fredholmOperator
      shiftedForm massForm coercive lambda hcompactMass
  have hcompClosed : IsClosed ((E.toContinuousLinearMap.comp form).range : Set V) := by
    rw [coerciveSolveEquiv_comp_form_eq_one_sub_fredholmOperator
      form shiftedForm massForm coercive lambda hshift]
    have hrange : ((1 : V →L[ℝ] V) - K).range =
        (K - (1 : V →L[ℝ] V)).range := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        refine ⟨-x, ?_⟩
        simp
        abel
      · rintro ⟨x, rfl⟩
        refine ⟨-x, ?_⟩
        simp
        abel
    rw [hrange]
    exact isClosed_range_sub_identity K hK
  have hrange : (form.range : Set (StrongDual ℝ V)) =
      E ⁻¹' ((E.toContinuousLinearMap.comp form).range : Set V) := by
    ext ell
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, rfl⟩
    · rintro ⟨u, hu⟩
      refine ⟨u, ?_⟩
      apply E.injective
      exact hu
  rw [hrange]
  exact hcompClosed.preimage E.continuous

/-- The Riesz-represented operator of the original weak form has closed
range under the shifted-coercive, compact-mass hypotheses. -/
theorem isClosed_range_hilbertOperator_of_compact_mass
    (form shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) (lambda : ℝ)
    (hshift : ∀ u v, shiftedForm u v = form u v + lambda * massForm u v)
    (hcompactMass : IsCompactOperator massForm) :
    IsClosed ((hilbertOperator form).range : Set V) := by
  let R : StrongDual ℝ V ≃L[ℝ] V :=
    (InnerProductSpace.toDual ℝ V).symm.toContinuousLinearEquiv
  have hformClosed := isClosed_range_form_of_compact_mass
    form shiftedForm massForm coercive lambda hshift hcompactMass
  have himage : IsClosed (R '' (form.range : Set (StrongDual ℝ V))) :=
    R.toHomeomorph.isClosedMap _ hformClosed
  have hrange : ((hilbertOperator form).range : Set V) =
      R '' (form.range : Set (StrongDual ℝ V)) := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨form u, ⟨u, rfl⟩, ?_⟩
      rfl
    · rintro ⟨ell, ⟨u, hu⟩, hell⟩
      refine ⟨u, ?_⟩
      change R (form u) = y
      exact (congrArg R hu).trans hell
  rw [hrange]
  exact himage

/-- Evans §6.2.3, Theorem 4(iii), abstract weak form. Under the
shifted-coercive and compact-mass hypotheses, the original equation is
solvable exactly when the forcing annihilates every homogeneous solution of
the adjoint problem. Closed range is proved, not assumed. -/
theorem exists_isWeakSolution_iff_forall_adjoint_homogeneous_orthogonal_of_compact_mass
    (form shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) (lambda : ℝ)
    (hshift : ∀ u v, shiftedForm u v = form u v + lambda * massForm u v)
    (hcompactMass : IsCompactOperator massForm) (ell : StrongDual ℝ V) :
    (∃ u : V, IsWeakSolution form ell u) ↔
      ∀ v : V, IsWeakSolution (adjointForm form) 0 v → ell v = 0 := by
  exact exists_isWeakSolution_iff_forall_adjoint_homogeneous_orthogonal form
    (isClosed_range_hilbertOperator_of_compact_mass
      form shiftedForm massForm coercive lambda hshift hcompactMass) ell

end PDE.Analysis
