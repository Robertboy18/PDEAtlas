/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Algebraic factorization through a linear map

A linear map which vanishes on the kernel of another factors through it.
The factor on the range extends algebraically to the entire codomain.
The construction is purely algebraic.
-/

@[expose] public noncomputable section

namespace LinearMap

/-- Kernel containment gives an algebraic factorization, including when the
first map is not onto. -/
theorem exists_comp_eq_of_ker_le
    {K V W Z : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup Z] [Module K Z]
    (A : V →ₗ[K] W) (f : V →ₗ[K] Z) (h : A.ker ≤ f.ker) :
    ∃ g : W →ₗ[K] Z, g.comp A = f := by
  let F := (A.ker.liftQ f h).comp A.quotKerEquivRange.symm.toLinearMap
  obtain ⟨g, hg⟩ := F.exists_extend
  refine ⟨g, ?_⟩
  ext x
  have heq := congrArg (fun L : A.range →ₗ[K] Z ↦
    L (A.quotKerEquivRange (A.ker.mkQ x))) hg
  change g (A x) = (A.ker.liftQ f h)
    (A.quotKerEquivRange.symm (A.quotKerEquivRange (A.ker.mkQ x))) at heq
  rw [A.quotKerEquivRange.symm_apply_apply] at heq
  exact heq

end LinearMap
