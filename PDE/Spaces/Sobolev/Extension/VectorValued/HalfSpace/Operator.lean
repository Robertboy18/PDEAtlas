/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.VectorValued.HalfSpace.WeakDerivatives
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Restriction
import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Derivatives

/-!
# Higher-order Sobolev reflection with Banach values

Weighted normal reflection gives a bounded linear extension
`W^{k,p}(ℝ^n₊; F) → W^{k,p}(ℝ^n; F)` for arbitrary complete real normed `F`,
every finite order `k`, and both exponent endpoints `1 ≤ p ≤ ∞`.
The graph uses the finite `PiLp p` norm of its derivative coordinates.
Restriction recovers every source coordinate.

Each derivative word is built from the Banach-valued one-step reflection theorem.
Its moment-cancelled boundary argument supplies the global weak identities without
a trace assumption or a density argument at infinity.
The construction is the scalar weighted normal reflection of
`Extension.HalfSpace.Reflection.HigherOrder.Operator`, with the same coefficients for every
codomain; Evans, *Partial Differential Equations*, §5.4, gives the two-term case and remarks
that higher orders need such a higher-order reflection.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.4, Theorem 1, pp. 268-271, whose proof extends `C¹`
  functions by the two-term reflection (3), p. 269, and Remarks (i) and (ii), p. 271: the same
  operator is bounded on `W^{2,p}` when the boundary is `C²`, and `k > 2` needs a more complicated
  higher-order reflection.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued.HigherOrderReflection

open GraphSpace

variable (n k : ℕ) [Fact (0 < n)] (p : ℝ≥0∞) [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Reflect each derivative coordinate with the weight given by its normal multiplicity. -/
def weightedReflectAmbient :
    WkpAmbientOn n k p ⟨ℝ^n₊, HalfSpace.isOpen_upper n⟩ F →L[ℝ]
      WkpAmbientOn n k p ⊤ F :=
  (PiLp.continuousLinearEquiv p ℝ
    (fun _ : DerivIndex n k ↦ Lp F p (domainMeasure n univ))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun a ↦
      (weightedExtendLp n k p (a.multiplicity (PDE.Common.lastIndex (n := n)))).comp
        (PiLp.proj p (fun _ : DerivIndex n k ↦ Lp F p (domainMeasure n ℝ^n₊)) a))

/-- Every reflected coordinate is the corresponding bounded `Lp` extension row. -/
@[simp] theorem weightedReflectAmbient_apply
    (U : WkpAmbientOn n k p ⟨ℝ^n₊, HalfSpace.isOpen_upper n⟩ F) (a : DerivIndex n k) :
    weightedReflectAmbient n k p U a =
      weightedExtendLp n k p (a.multiplicity (PDE.Common.lastIndex (n := n))) (U a) :=
  rfl

variable [CompleteSpace F]

/-- The reflected coordinates satisfy every Banach-valued weak-derivative constraint.
The one-step theorem builds each derivative word, including across the boundary. -/
theorem weightedReflectAmbient_isWkpOn
    (U : WkpAmbientOn n k p ⟨ℝ^n₊, HalfSpace.isOpen_upper n⟩ F) (hU : IsWkpOn U) :
    IsWkpOn (weightedReflectAmbient n k p U) := by
  let D : List (Fin n) → ℝ^n → F := fun α ↦
    if hα : α.length ≤ k then
      weightedExtendLp n k p (α.count (PDE.Common.lastIndex (n := n)))
        (U (derivIndexOfList α hα))
    else 0
  have hloc (α : List (Fin n)) (hα : α.length ≤ k) :
      LocallyIntegrableOn (D α) univ volume := by
    simp only [D, dite_eq_left hα]
    exact locallyIntegrableOn_of_locallyIntegrable_restrict
      ((Lp.memLp _).locallyIntegrable Fact.out)
  have hstep (α : List (Fin n)) (i : Fin n) (hα : α.length < k) :
      HasWeakDerivativeOn ⊤ [i] (D α) (D (α ++ [i])) := by
    have hαle : α.length ≤ k := hα.le
    have hnext : (α ++ [i]).length ≤ k := by
      simp only [List.length_append, List.length_singleton]
      omega
    have hr : α.count (PDE.Common.lastIndex (n := n)) ≤ k :=
      (List.count_le_length ..).trans hαle
    have hw := WkpSpaceOn.hasWeakDerivativeOn_from_coordinate
      (⟨U, hU⟩ : W^{k,p}(⟨ℝ^n₊, HalfSpace.isOpen_upper n⟩; F)) α [i] (by
        simpa only [List.length_append, List.length_singleton] using hnext)
    have he := hasWeakDerivativeOn_weightedExtendLp n k p _ hr i _ _ hw
    simpa only [D, dite_eq_left hαle, dite_eq_left hnext, List.count_append,
      List.count_singleton, beq_iff_eq] using he
  intro a
  have h : HasWeakDerivativeOn ⊤ a.toList (D []) (D a.toList) := by
    apply (hasWeakDerivativeOn_iff_forall_dual
      (hloc [] (Nat.zero_le k)) (hloc a.toList a.toList_length_le)).mpr
    intro L
    exact hasWeakDerivativeOn_of_append_single_chain_order k
      (fun α ↦ L ∘ D α) (L.locallyIntegrableOn_comp (hloc [] (Nat.zero_le k)))
      (fun α i hα ↦ hasWeakDerivativeOn_real_iff.mp ((hstep α i hα).map L))
      a.toList a.toList_length_le
  simpa only [D, dite_eq_left a.toList_length_le, List.length_nil, Nat.zero_le,
    ↓reduceDIte, List.count_nil, derivIndexOfList_nil, derivIndexOfList_toList,
    DerivIndex.toList_count, weightedReflectAmbient_apply, baseIndex_multiplicity] using h

/-- The weighted normal reflection as a bounded linear map
`W^{k,p}(ℝ^n₊; F) → W^{k,p}(ℝ^n; F)` of Banach-valued Sobolev graphs, with no boundary
compatibility assumption on the source. -/
def weightedReflection :
    W^{k,p}(⟨ℝ^n₊, HalfSpace.isOpen_upper n⟩; F) →L[ℝ] W^{k,p}(ℝ^n; F) :=
  ((weightedReflectAmbient n k p).comp
    (wkpSubmoduleOn n k p ⟨ℝ^n₊, HalfSpace.isOpen_upper n⟩ F).subtypeL).codRestrict
      (wkpSubmoduleOn n k p ⊤ F) (fun U ↦
        weightedReflectAmbient_isWkpOn n k p U.val U.property)

/-- The Sobolev extension retains exactly the constructed ambient derivative bundle. -/
@[simp] theorem weightedReflection_apply_coe
    (U : W^{k,p}(⟨ℝ^n₊, HalfSpace.isOpen_upper n⟩; F)) :
    (weightedReflection n k p U).val = weightedReflectAmbient n k p U.val :=
  rfl

/-- The derivative with index `a` has the reflected weight determined by its normal count. -/
@[simp] theorem weightedReflection_coordinate
    (U : W^{k,p}(⟨ℝ^n₊, HalfSpace.isOpen_upper n⟩; F)) (a : DerivIndex n k) :
    (weightedReflection n k p U).val a =
      weightedExtendLp n k p (a.multiplicity (PDE.Common.lastIndex (n := n))) (U.val a) :=
  rfl

/-- Every weak derivative is represented by its original upper branch and the literal
weighted normal dilations on the lower half-space. The boundary is a null set. -/
theorem weightedReflection_coordinate_apply_ae
    (U : W^{k,p}(⟨ℝ^n₊, HalfSpace.isOpen_upper n⟩; F)) (a : DerivIndex n k) :
    ((weightedReflection n k p U).val a : ℝ^n → F) =ᵐ[volume]
      fun x ↦ ℝ^n₊.indicator (U.val a : ℝ^n → F) x +
        ℝ^n₋.indicator (fun y ↦ ∑ j : Fin (k + 1),
          (GraphSpace.HigherOrderReflection.reflectionCoeff k j *
            GraphSpace.HigherOrderReflection.reflectionNode k j ^
              a.multiplicity (PDE.Common.lastIndex (n := n))) •
                U.val a (GraphSpace.HigherOrderReflection.normalDilation
                  (PDE.Common.lastIndex (n := n))
                  (GraphSpace.HigherOrderReflection.reflectionNode k j) y)) x :=
  weightedExtendLp_apply_ae n k p _ _

/-- Restriction is a left inverse on the Sobolev graph, including all derivative rows. -/
@[simp] theorem restrict_weightedReflection
    (U : W^{k,p}(⟨ℝ^n₊, HalfSpace.isOpen_upper n⟩; F)) :
    restrictCLM (show (⟨ℝ^n₊, HalfSpace.isOpen_upper n⟩ : Opens ℝ^n) ≤ ⊤ from le_top)
      (weightedReflection n k p U) = U := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  change Lp.restrictionCLMOfLE (Measure.restrict_mono (subset_univ ℝ^n₊) le_rfl)
    (weightedExtendLp n k p (a.multiplicity (PDE.Common.lastIndex (n := n))) (U.val a)) =
      U.val a
  exact restrict_weightedExtendLp n k p _ _

/-- Weighted reflection is injective because upper-half-space restriction recovers its input. -/
theorem weightedReflection_injective : Function.Injective (weightedReflection n k p (F := F)) :=
  Function.LeftInverse.injective (restrict_weightedReflection n k p)

end SobolevSpace.VectorValued.HigherOrderReflection
