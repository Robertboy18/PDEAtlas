/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.Maps.Strict.Module
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Factorization through closed operator ranges

If a continuous linear map `L` vanishes on the kernel of a closed-range map
`T`, then `L` factors continuously through `range T`. This is the
reconstruction step behind Lagrange multipliers and weak pressure recovery.

For scalar-valued `L` and a Hilbert codomain, the factor has a canonical
Fréchet–Riesz representative in `range T`. This representative is the unique
range-valued multiplier `p` satisfying

```text
inner p (T x) = L x.
```

In incompressible weak formulations, `T` may be a divergence operator and the multiplier is the
abstract pressure.
-/

@[expose] public section

set_option linter.missingDocs true

noncomputable section

open scoped InnerProductSpace


namespace ContinuousLinearMap.ClosedRange

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section Factor

variable {F G : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A continuous linear map vanishing on `ker T` factors through a closed range of `T`. -/
def factorThroughRange (T : E →L[ℝ] F) (L : E →L[ℝ] G)
    (hker : T.ker ≤ L.ker) (hclosed : IsClosed (T.range : Set F)) :
    T.range →L[ℝ] G :=
  let _ : CompleteSpace T.range := hclosed.completeSpace_coe
  let e : (E ⧸ T.ker) ≃L[ℝ] T.range := .quotKerEquivRange
    (T.toLinearMap.isStrictMap_iff_isOpenQuotientMap_rangeRestrict.mpr
      ⟨T.toLinearMap.surjective_rangeRestrict, T.rangeRestrict.continuous,
        T.rangeRestrict.isOpenMap T.toLinearMap.surjective_rangeRestrict⟩)
  (T.ker.liftQL L hker).comp e.symm.toContinuousLinearMap

/-- The closed-range factor agrees with `L` on every value of `T`. -/
@[simp]
theorem factorThroughRange_apply (T : E →L[ℝ] F) (L : E →L[ℝ] G)
    (hker : T.ker ≤ L.ker) (hclosed : IsClosed (T.range : Set F)) (x : E) :
    factorThroughRange T L hker hclosed (Set.rangeFactorization (⇑T) x) = L x := by
  change T.ker.liftQ L.toLinearMap hker
    (T.toLinearMap.quotKerEquivRange.symm
      ⟨T.toLinearMap x, show T.toLinearMap x ∈ T.toLinearMap.range from ⟨x, rfl⟩⟩) = L x
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

end Factor

section HilbertCodomain

variable {F : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/--
The canonical multiplier in the range of `T` representing a functional that
vanishes on `ker T`.
-/
def multiplierInRange (T : E →L[ℝ] F) (ell : E →L[ℝ] ℝ)
    (hker : T.ker ≤ ell.ker) (hclosed : IsClosed (T.range : Set F)) :
    T.range :=
  let _ : CompleteSpace T.range := hclosed.completeSpace_coe
  (InnerProductSpace.toDual ℝ T.range).symm
    (factorThroughRange T ell hker hclosed)

/-- The range-valued multiplier represents the functional after composition with `T`. -/
theorem inner_multiplierInRange_apply
    (T : E →L[ℝ] F) (ell : E →L[ℝ] ℝ)
    (hker : T.ker ≤ ell.ker) (hclosed : IsClosed (T.range : Set F))
    (x : E) :
    ⟪multiplierInRange T ell hker hclosed, T.rangeRestrict x⟫_ℝ =
      ell x := by
  let _ : CompleteSpace T.range := hclosed.completeSpace_coe
  rw [multiplierInRange, InnerProductSpace.toDual_symm_apply]
  exact factorThroughRange_apply T ell hker hclosed x

/-- The canonical ambient-space multiplier associated with `ell` and `T`. -/
def multiplier (T : E →L[ℝ] F) (ell : E →L[ℝ] ℝ)
    (hker : T.ker ≤ ell.ker) (hclosed : IsClosed (T.range : Set F)) :
    F :=
  multiplierInRange T ell hker hclosed

/-- The canonical multiplier belongs to the range of `T`. -/
theorem multiplier_mem_range (T : E →L[ℝ] F) (ell : E →L[ℝ] ℝ)
    (hker : T.ker ≤ ell.ker) (hclosed : IsClosed (T.range : Set F)) :
    multiplier T ell hker hclosed ∈ T.range :=
  (multiplierInRange T ell hker hclosed).property

/-- The canonical multiplier represents the functional after composition with `T`. -/
theorem inner_multiplier_apply (T : E →L[ℝ] F) (ell : E →L[ℝ] ℝ)
    (hker : T.ker ≤ ell.ker) (hclosed : IsClosed (T.range : Set F))
    (x : E) :
    ⟪multiplier T ell hker hclosed, T x⟫_ℝ = ell x := by
  exact inner_multiplierInRange_apply T ell hker hclosed x

/--
The canonical multiplier is the unique multiplier in `range T` that
represents `ell` after composition with `T`.
-/
theorem multiplier_unique_of_mem_range
    (T : E →L[ℝ] F) (ell : E →L[ℝ] ℝ)
    (hker : T.ker ≤ ell.ker) (hclosed : IsClosed (T.range : Set F))
    (p : F) (hp : p ∈ T.range)
    (hrep : ∀ x : E, ⟪p, T x⟫_ℝ = ell x) :
    p = multiplier T ell hker hclosed := by
  let pRange : T.range := ⟨p, hp⟩
  have heq : pRange = multiplierInRange T ell hker hclosed := by
    apply ext_inner_right ℝ
    intro z
    obtain ⟨x, hx⟩ := z.property
    change ⟪p, z.1⟫_ℝ =
      ⟪multiplier T ell hker hclosed, z.1⟫_ℝ
    rw [← hx]
    exact (hrep x).trans
      (inner_multiplier_apply T ell hker hclosed x).symm
  exact congrArg Subtype.val heq

/--
There is a unique range-valued multiplier representing every continuous
functional that vanishes on the kernel of a closed-range operator.
-/
theorem existsUnique_multiplier_mem_range
    (T : E →L[ℝ] F) (ell : E →L[ℝ] ℝ)
    (hker : T.ker ≤ ell.ker) (hclosed : IsClosed (T.range : Set F)) :
    ∃! p : F, p ∈ T.range ∧ ∀ x : E, ⟪p, T x⟫_ℝ = ell x := by
  refine ⟨multiplier T ell hker hclosed, ⟨
    multiplier_mem_range T ell hker hclosed,
    inner_multiplier_apply T ell hker hclosed⟩, ?_⟩
  rintro p ⟨hp, hrep⟩
  exact multiplier_unique_of_mem_range
    T ell hker hclosed p hp hrep

/-- The canonical multiplier solves the corresponding adjoint equation. -/
theorem adjoint_multiplier_eq (T : E →L[ℝ] F) (ell : E →L[ℝ] ℝ)
    (hker : T.ker ≤ ell.ker) (hclosed : IsClosed (T.range : Set F)) :
    T.adjoint (multiplier T ell hker hclosed) =
      (InnerProductSpace.toDual ℝ E).symm ell := by
  apply ext_inner_right ℝ
  intro x
  rw [T.adjoint_inner_left, inner_multiplier_apply,
    InnerProductSpace.toDual_symm_apply]

end HilbertCodomain

end ContinuousLinearMap.ClosedRange
