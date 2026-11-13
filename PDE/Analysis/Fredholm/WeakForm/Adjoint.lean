/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.WeakSolution
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import PDE.Analysis.Fredholm.CompactPerturbation.ClosedRange

/-!
# Adjoint weak forms and closed-range solvability

A dual-valued bilinear form has an associated Hilbert-space operator and an
adjoint form. If the operator has closed range, a weak equation is solvable
exactly when its forcing annihilates every homogeneous solution of the adjoint
problem.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.2.3, p. 320 (the adjoint form), and Theorem 4(iii),
  p. 321. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open Set
open scoped InnerProductSpace
open PDE.Analysis.Variational

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- Riesz-represented Hilbert operator associated with a continuous
bilinear form. -/
def hilbertOperator
    (form : V →L[ℝ] StrongDual ℝ V) : V →L[ℝ] V :=
  (InnerProductSpace.toDual ℝ V).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp form

/-- Adjoint bilinear form, defined through the Hilbert adjoint of the
Riesz-represented operator. -/
def adjointForm
    (form : V →L[ℝ] StrongDual ℝ V) : V →L[ℝ] StrongDual ℝ V :=
  (InnerProductSpace.toDual ℝ V).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (hilbertOperator form).adjoint

/-- The adjoint form satisfies `adjointForm form v u = form u v`, Evans's definition
`B*[v, u] = B[u, v]` in §6.2.3. -/
@[simp]
theorem adjointForm_apply (form : V →L[ℝ] StrongDual ℝ V) (v u : V) :
    adjointForm form v u = form u v := by
  change ⟪(hilbertOperator form).adjoint v, u⟫_ℝ = form u v
  rw [(hilbertOperator form).adjoint_inner_left]
  rw [real_inner_comm]
  exact InnerProductSpace.toDual_symm_apply

/-- Homogeneous weak solutions of the adjoint form are exactly the kernel
of the Hilbert adjoint. -/
theorem isWeakSolution_adjointForm_zero_iff
    (form : V →L[ℝ] StrongDual ℝ V) (v : V) :
    IsWeakSolution (adjointForm form) 0 v ↔
      (hilbertOperator form).adjoint v = 0 := by
  constructor
  · intro hv
    apply (InnerProductSpace.toDual ℝ V).injective
    ext u
    simpa [adjointForm] using hv u
  · intro hv u
    simp [adjointForm, hv]

/-- The kernel of the dual-valued adjoint form is exactly the kernel of the
Hilbert adjoint of the Riesz-represented original operator. -/
theorem ker_adjointForm_eq_ker_adjoint_hilbertOperator
    (form : V →L[ℝ] StrongDual ℝ V) :
    (adjointForm form).ker = (hilbertOperator form).adjoint.ker := by
  ext v
  change adjointForm form v = 0 ↔ (hilbertOperator form).adjoint v = 0
  constructor
  · intro hv
    apply (InnerProductSpace.toDual ℝ V).injective
    simpa [adjointForm] using hv
  · intro hv
    change (InnerProductSpace.toDual ℝ V) ((hilbertOperator form).adjoint v) = 0
    rw [hv, map_zero]

/-- If the Riesz representative of `form` has closed range, the weak equation with right side
`ell` is solvable exactly when `ell` vanishes on every homogeneous weak solution of the adjoint
form, the criterion of Evans, §6.2.3, Theorem 4(iii). -/
theorem exists_isWeakSolution_iff_forall_adjoint_homogeneous_orthogonal
    (form : V →L[ℝ] StrongDual ℝ V)
    (hclosed : IsClosed ((hilbertOperator form).range : Set V))
    (ell : StrongDual ℝ V) :
    (∃ u : V, IsWeakSolution form ell u) ↔
      ∀ v : V, IsWeakSolution (adjointForm form) 0 v → ell v = 0 := by
  let y : V := (InnerProductSpace.toDual ℝ V).symm ell
  have hrange := mem_range_iff_forall_adjoint_ker_orthogonal
    (hilbertOperator form) hclosed y
  constructor
  · rintro ⟨u, hu⟩ v hv
    have hy : y = hilbertOperator form u := by
      apply (InnerProductSpace.toDual ℝ V).injective
      ext w
      simpa [y, hilbertOperator] using (hu w).symm
    have hvker := (isWeakSolution_adjointForm_zero_iff form v).1 hv
    calc
      ell v = ⟪y, v⟫_ℝ := (InnerProductSpace.toDual_symm_apply).symm
      _ = ⟪hilbertOperator form u, v⟫_ℝ := by rw [hy]
      _ = ⟪u, (hilbertOperator form).adjoint v⟫_ℝ := by
        rw [(hilbertOperator form).adjoint_inner_right]
      _ = 0 := by simp [hvker]
  · intro hortho
    have hyRange : y ∈ (hilbertOperator form).range := hrange.2 fun v hv ↦ by
      have hvWeak := (isWeakSolution_adjointForm_zero_iff form v).2 hv
      have := hortho v hvWeak
      simpa [y] using this
    obtain ⟨u, hu⟩ := hyRange
    refine ⟨u, fun v ↦ ?_⟩
    have huDual := congrArg (InnerProductSpace.toDual ℝ V) hu
    simpa [y, hilbertOperator] using congrArg (fun L : StrongDual ℝ V ↦ L v) huDual

/-- The same criterion when the Riesz representative of `form` is `K - 1` with `K` compact;
the range is then closed by `isClosed_range_sub_identity`. -/
theorem exists_isWeakSolution_iff_forall_adjoint_homogeneous_orthogonal_of_compact_sub_identity
    (form : V →L[ℝ] StrongDual ℝ V) (K : V →L[ℝ] V)
    (hK : IsCompactOperator K)
    (hform : hilbertOperator form = K - (1 : V →L[ℝ] V))
    (ell : StrongDual ℝ V) :
    (∃ u : V, IsWeakSolution form ell u) ↔
      ∀ v : V, IsWeakSolution (adjointForm form) 0 v → ell v = 0 := by
  apply exists_isWeakSolution_iff_forall_adjoint_homogeneous_orthogonal form
  rw [hform]
  exact isClosed_range_sub_identity K hK

end PDE.Analysis
