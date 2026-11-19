/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Factoring linear relations through a Hilbert space

A linear map controlled by the norm of another linear map extends over the
closure of its range. Orthogonal projection gives a bounded map on the full
Hilbert space with the same bound. Continuous scalar pairings extend along
this construction without requiring the original range to be dense. For a scalar
functional, the Riesz representation of the factor is a vector `p` with
`⟪p, A x⟫ = f x` and `‖p‖ ≤ C`; the range of `A` need not be closed.
-/

@[expose] public section

open Set

namespace LinearMap

variable {𝕜 E H Y : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]

/-- A linear map with codomain restricted to the closure of its range. -/
noncomputable def closureRangeRestrict (A : E →ₗ[𝕜] H) :
    E →ₗ[𝕜] (range A).topologicalClosure :=
  A.codRestrict (range A).topologicalClosure fun x ↦
    Submodule.le_topologicalClosure (range A) (mem_range_self A x)

omit [CompleteSpace H] in
/-- The restriction to the closed range has dense range. -/
theorem denseRange_closureRangeRestrict (A : E →ₗ[𝕜] H) :
    DenseRange A.closureRangeRestrict := by
  have hd : DenseRange (Set.inclusion (subset_closure :
      (range A : Set H) ⊆ closure (range A : Set H))) :=
    (denseRange_inclusion_iff subset_closure).2 subset_rfl
  exact hd.comp Set.rangeFactorization_surjective.denseRange
    (continuous_inclusion subset_closure)

/-- Factor a bounded linear relation through a Hilbert space, extending over the
closed range and taking zero on its orthogonal complement. -/
noncomputable def factorThroughHilbert (f : E →ₗ[𝕜] Y) (A : E →ₗ[𝕜] H) : H →L[𝕜] Y :=
  (f.extendOfNorm A.closureRangeRestrict).comp
    (range A).topologicalClosure.orthogonalProjectionOnto

/-- The factor agrees with the original linear relation on its actual range. -/
theorem factorThroughHilbert_apply (f : E →ₗ[𝕜] Y) (A : E →ₗ[𝕜] H)
    {C : ℝ} (hbound : ∀ x, ‖f x‖ ≤ C * ‖A x‖) (x : E) :
    f.factorThroughHilbert A (A x) = f x := by
  change f.extendOfNorm A.closureRangeRestrict
    ((range A).topologicalClosure.orthogonalProjectionOnto
      (A.closureRangeRestrict x : H)) = f x
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  exact extendOfNorm_eq A.denseRange_closureRangeRestrict ⟨C, hbound⟩ x

/-- The factor preserves the bound of the original linear relation. -/
theorem norm_factorThroughHilbert_le (f : E →ₗ[𝕜] Y) (A : E →ₗ[𝕜] H)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, ‖f x‖ ≤ C * ‖A x‖) :
    ‖f.factorThroughHilbert A‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro h
  exact (norm_extendOfNorm_apply_le A.denseRange_closureRangeRestrict C hbound _).trans
    (mul_le_mul_of_nonneg_left
      ((range A).topologicalClosure.norm_orthogonalProjectionOnto_apply_le h) hC)

/-- A continuous functional agreeing with an inner product on the original
range agrees with that inner product on the full Hilbert-space factor. -/
theorem apply_factorThroughHilbert_eq_inner (f : E →ₗ[𝕜] Y) (A : E →ₗ[𝕜] H)
    {C : ℝ} (hbound : ∀ x, ‖f x‖ ≤ C * ‖A x‖) (l : Y →L[𝕜] 𝕜) (z : E)
    (hpair : ∀ x, l (f x) = inner 𝕜 (A z) (A x)) (h : H) :
    l (f.factorThroughHilbert A h) = inner 𝕜 (A z) h := by
  have he (k : (range A).topologicalClosure) :
      l (f.extendOfNorm A.closureRangeRestrict k) = inner 𝕜 (A z) (k : H) := by
    refine A.denseRange_closureRangeRestrict.induction ?_
      (isClosed_eq (by fun_prop) (by fun_prop)) k
    rintro _ ⟨x, rfl⟩
    rw [extendOfNorm_eq A.denseRange_closureRangeRestrict ⟨C, hbound⟩]
    exact hpair x
  calc
    _ = inner 𝕜 (A z)
        ((range A).topologicalClosure.orthogonalProjectionOnto h : H) := he _
    _ = _ := (range A).topologicalClosure.inner_orthogonalProjectionOnto_eq_of_mem_left
      (A.closureRangeRestrict z) h

/-- A functional controlled by the norm of a linear image has a Hilbert-space
representative with the same bound: the Riesz vector of `f.factorThroughHilbert A`.
No closed-range assumption is needed. -/
theorem exists_norm_le_inner_apply_eq_of_bound
    (A : E →ₗ[𝕜] H) (f : E →ₗ[𝕜] 𝕜) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖f x‖ ≤ C * ‖A x‖) :
    ∃ p : H, ‖p‖ ≤ C ∧ ∀ x, inner 𝕜 p (A x) = f x := by
  refine ⟨(InnerProductSpace.toDual 𝕜 H).symm (f.factorThroughHilbert A), ?_, fun x ↦ ?_⟩
  · simpa only [LinearIsometryEquiv.norm_map] using f.norm_factorThroughHilbert_le A hC hbound
  · rw [InnerProductSpace.toDual_symm_apply]
    exact f.factorThroughHilbert_apply A hbound x

end LinearMap
