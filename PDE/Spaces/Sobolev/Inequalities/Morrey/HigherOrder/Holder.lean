/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Holder.HigherOrder.Norm
public import PDE.Spaces.Sobolev.Inequalities.Morrey.HigherOrder.Embedding

/-!
# Compatible higher Hölder representatives

The Morrey representatives of the weak derivatives form one classical higher-order
Hölder function. Ordinary coordinate multiindices are identified with the symmetric
Sobolev indices using Mathlib's equivalence with multiplicities.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology Sobolev

namespace HolderSpace.MultiIndex

variable {n k : ℕ}

/-- The symmetric Sobolev index with these coordinate multiplicities. -/
def derivIndex (a : MultiIndex n k) : SobolevSpace.GraphSpace.DerivIndex n k :=
  ⟨⟨a.order, Nat.lt_succ_of_le a.order_le⟩,
    (Sym.equivNatSumOfFintype (Fin n) a.order).symm ⟨a.1, rfl⟩⟩

/-- The derivative word has the original multiindex order. -/
theorem derivIndex_length (a : MultiIndex n k) :
    a.derivIndex.toList.length = a.order :=
  SobolevSpace.GraphSpace.DerivIndex.toList_length _

/-- Coordinate multiplicities are preserved by the symmetric-index conversion. -/
theorem derivIndex_count (a : MultiIndex n k) (i : Fin n) :
    a.derivIndex.toList.count i = a.1 i := by
  rw [SobolevSpace.GraphSpace.DerivIndex.toList_count]
  change ((Sym.equivNatSumOfFintype (Fin n) a.order)
    ((Sym.equivNatSumOfFintype (Fin n) a.order).symm ⟨a.1, rfl⟩)).1 i = a.1 i
  simp

/-- The empty multiindex corresponds to the base function. -/
@[simp] theorem derivIndex_zero :
    (0 : MultiIndex n k).derivIndex = SobolevSpace.GraphSpace.baseIndex n k := by
  apply SobolevSpace.GraphSpace.DerivIndex.eq_baseIndex
  apply List.length_eq_zero_iff.mp
  rw [derivIndex_length, order_zero]

/-- Differentiation appends one coordinate, independently of the chosen word ordering. -/
theorem derivIndex_succ_perm (a : MultiIndex n k) (ha : a.order < k) (i : Fin n) :
    (a.succ ha i).derivIndex.toList.Perm (a.derivIndex.toList ++ [i]) := by
  apply List.perm_iff_count.mpr
  intro j
  rw [derivIndex_count, List.count_append, derivIndex_count]
  by_cases hij : i = j <;> simp [succ, List.count_nil, hij, eq_comm]

end HolderSpace.MultiIndex

namespace SobolevSpace.GraphSpace

open HolderSpace

variable {n k : ℕ} {Ω : Set (ℝ^n)} {p q : ℝ}
  [Fact (0 < n)] [Fact (1 ≤ ENNReal.ofReal p)] [Boundary.C1ExtensionAtlas n Ω]

/-- Permuting a derivative word leaves its Morrey representative unchanged. -/
theorem finiteMorreyDerivativeRepresentativeOn_perm
    (hp : (n : ℝ) < p) (hpq : p.HolderConjugate q)
    {m : ℕ} {α β : List (Fin n)} (hα : α.length + 1 ≤ m)
    (hβ : β.length + 1 ≤ m) (hperm : α.Perm β)
    (U : W^{m,ENNReal.ofReal p}(Ω)) :
    finiteMorreyDerivativeRepresentativeOn hp hpq α hα U =
      finiteMorreyDerivativeRepresentativeOn hp hpq β hβ U := by
  have hs : derivativeWordCLM (r := 1) α hα U =
      derivativeWordCLM (r := 1) β hβ U := by
    apply Subtype.ext
    apply PiLp.ext
    intro a
    simp only [derivativeWordCLM_apply]
    exact congrArg (fun b : DerivIndex n m ↦ (U : WkpAmbientOn n m (ENNReal.ofReal p) Ω) b)
      (derivativeWordIndex_eq_of_perm α hα a β hβ a (hperm.append_right _))
  unfold finiteMorreyDerivativeRepresentativeOn
  rw [hs]

/-- The global Hölder field representing one of the retained weak derivatives. -/
def higherMorreyField (hp : (n : ℝ) < p) (hpq : p.HolderConjugate q)
    (U : W^{k + 1,ENNReal.ofReal p}(Ω)) (a : MultiIndex n k) :
    C0GammaOn (ℝ^n) (finiteMorreyHolderExponent n p Fact.out hp) :=
  finiteMorreyEmbedding Fact.out hp hpq
    (Extension.C1.extensionCLM
      (derivativeWordCLM (r := 1) a.derivIndex.toList
        (by rw [MultiIndex.derivIndex_length]; exact Nat.add_le_add_right a.order_le 1) U))

/-- The global Hölder fields are exactly the higher-order Morrey representatives. -/
theorem higherMorreyField_apply (hp : (n : ℝ) < p) (hpq : p.HolderConjugate q)
    (U : W^{k + 1,ENNReal.ofReal p}(Ω)) (a : MultiIndex n k) (x : ℝ^n) :
    higherMorreyField hp hpq U a x =
      finiteMorreyDerivativeRepresentativeOn hp hpq a.derivIndex.toList
        (by rw [MultiIndex.derivIndex_length]; exact Nat.add_le_add_right a.order_le 1) U x :=
  rfl

/-- The derivative fields satisfy the classical compatibility relations in the open domain. -/
theorem higherMorreyField_hasFDerivAt
    (hp : (n : ℝ) < p) (hpq : p.HolderConjugate q)
    (U : W^{k + 1,ENNReal.ofReal p}(Ω))
    (a : MultiIndex n k) (ha : a.order < k) {x : ℝ^n} (hx : x ∈ Ω) :
    HasFDerivAt (higherMorreyField hp hpq U a)
      (∑ i : Fin n, higherMorreyField hp hpq U (a.succ ha i) x •
        (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ)) x := by
  have h := finiteMorreyDerivativeRepresentativeOn_hasFDerivAt
    hp hpq a.derivIndex.toList (by rw [MultiIndex.derivIndex_length]; omega) U hx
  have heq :
      (∑ i : Fin n, higherMorreyField hp hpq U (a.succ ha i) x •
        (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ)) =
      innerSL ℝ (WithLp.toLp 2 fun i ↦
        finiteMorreyDerivativeRepresentativeOn hp hpq (a.derivIndex.toList ++ [i])
          (by simp only [List.length_append, List.length_singleton,
            MultiIndex.derivIndex_length]; omega) U x) := by
    ext v
    simp only [sum_apply, smul_apply, smul_eq_mul, innerSL_apply_apply, PiLp.inner_apply,
      RCLike.inner_apply, conj_trivial]
    apply Finset.sum_congr rfl
    intro i _
    rw [higherMorreyField_apply, finiteMorreyDerivativeRepresentativeOn_perm
      (hperm := a.derivIndex_succ_perm ha i)]
    exact mul_comm _ _
  rw [heq]
  exact h

/-- The higher-order Morrey embedding as a single compatible classical Hölder function. -/
def finiteHigherHolderRepresentative
    (hp : (n : ℝ) < p) (hpq : p.HolderConjugate q)
    (U : W^{k + 1,ENNReal.ofReal p}(Ω)) :
    CKGammaOn n k Ω (finiteMorreyHolderExponent n p Fact.out hp) := by
  let F (a : MultiIndex n k) := C0GammaOn.restrict (closure Ω) (higherMorreyField hp hpq U a)
  refine ⟨(fun a ↦ (F a).toBoundedContinuousFunction, fun a ↦ F a.1), ?_, ?_⟩
  · intro a
    rfl
  · intro a ha x hx
    have h := higherMorreyField_hasFDerivAt hp hpq U a ha hx
    have heq : Function.extend Subtype.val (F a).toBoundedContinuousFunction 0
        =ᶠ[𝓝 x] higherMorreyField hp hpq U a := by
      filter_upwards [Boundary.C1ExtensionAtlas.isOpen.mem_nhds hx] with y hy
      exact BoundedContinuousFunction.extend_zero_apply _ (subset_closure hy)
    rw [JetData.gradientCLM_apply]
    exact h.congr_of_eventuallyEq heq

/-- The classical representative is the original Sobolev function almost everywhere. -/
theorem finiteHigherHolderRepresentative_ae
    (hp : (n : ℝ) < p) (hpq : p.HolderConjugate q)
    (U : W^{k + 1,ENNReal.ofReal p}(Ω)) :
    (finiteHigherHolderRepresentative hp hpq U).interiorDerivative 0
      =ᵐ[domainMeasure n Ω] baseRepresentative U := by
  have h := finiteMorreyDerivativeRepresentativeOn_ae hp hpq [] (by simp) U
  filter_upwards [h, ae_restrict_mem Boundary.C1ExtensionAtlas.isOpen.measurableSet] with x hx hΩ
  rw [CKGammaOn.interiorDerivative_apply _ _ (subset_closure hΩ)]
  simpa [CKGammaOn.derivative, finiteHigherHolderRepresentative, higherMorreyField,
    finiteMorreyDerivativeRepresentativeOn, baseRepresentative] using hx

end SobolevSpace.GraphSpace
