/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Derivatives
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.OrderRestriction

/-!
# Assembling one additional Banach-valued Sobolev order

If a Sobolev function and each of its first weak derivatives belong to `W^{m,p}`,
their derivative coordinates form an element of `W^{m+1,p}`. The construction
uses the `Lp` rows, including at `p = ∞`. Continuous duality proves the
weak identities for these already Bochner locally integrable representatives;
it does not infer Bochner integrability from scalar tests.

The resulting graph retains every lower-order coordinate, and each extracted
first derivative is the entire prescribed Sobolev graph. Thus mixed and repeated
derivatives agree without additional compatibility assumptions.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens ℝ^n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Append derivatives of a Sobolev graph to an already established weak derivative.
The new derivative is an `Lp` coordinate, so its Bochner local
integrability is available before testing with continuous linear functionals. -/
theorem HasWeakDerivativeOn.append_from_wkp {f : ℝ^n → F}
    (V : W^{m,p}(Ω; F)) (α β : List (Fin n)) (hβ : β.length ≤ m)
    (hbase : HasWeakDerivativeOn Ω α f (V.val (baseIndex n m))) :
    HasWeakDerivativeOn Ω (α ++ β) f (V.val (derivIndexOfList β hβ)) := by
  have hloc : LocallyIntegrableOn (V.val (derivIndexOfList β hβ)) Ω volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((Lp.memLp (V.val (derivIndexOfList β hβ))).locallyIntegrable Fact.out)
  apply (hasWeakDerivativeOn_iff_forall_dual hbase.locallyIntegrable_f hloc).mpr
  intro L
  have hfirst := hasWeakDerivativeOn_real_iff.mp (hbase.map L)
  have hfirst' : SobolevSpace.HasWeakDerivativeOn (Ω : Set ℝ^n) α (L ∘ f)
      ((scalarEquiv (mapCLM L V)).val (baseIndex n m)) :=
    (SobolevSpace.hasWeakDerivativeOn_congr_ae Filter.EventuallyEq.rfl
      (mapCLM_apply_ae L V (baseIndex n m)).symm).mp hfirst
  have hscalar := GraphSpace.HasWeakDerivativeOn.append_from_wkp
    (scalarEquiv (mapCLM L V)) α β hβ hfirst'
  exact (SobolevSpace.hasWeakDerivativeOn_congr_ae Filter.EventuallyEq.rfl
    (mapCLM_apply_ae L V (derivIndexOfList β hβ))).mp hscalar

private def succOrderRow (U : W^{m,p}(Ω; F)) (V : Fin n → W^{m,p}(Ω; F))
    (a : DerivIndex n (m + 1)) : Lp F p (domainMeasure n Ω) :=
  if ha : a.toList.length ≤ m then
    U.val (derivIndexOfList a.toList ha)
  else
    let hne : a.toList ≠ [] := by
      intro hnil
      exact ha (by simp [hnil])
    (V (a.toList.head hne)).val (derivIndexOfList a.toList.tail (by
      have htotal := a.toList_length_le
      have hpos := List.length_pos_iff.mpr hne
      simp only [List.length_tail]
      omega))

omit [Fact (1 ≤ p)] in
private theorem succOrderRow_base (U : W^{m,p}(Ω; F))
    (V : Fin n → W^{m,p}(Ω; F)) :
    succOrderRow U V (baseIndex n (m + 1)) = U.val (baseIndex n m) := by
  unfold succOrderRow
  rw [dite_eq_left (by simp only [baseIndex_toList, List.length_nil]; exact Nat.zero_le _)]
  simp only [baseIndex_toList]
  rfl

/-- Assemble a Sobolev graph from its lower-order graph and first weak derivatives.
The lower-order restriction and every first derivative agree as entire Sobolev
elements. This includes order zero, dimension zero, and both exponent endpoints. -/
theorem exists_succOrder_of_weakDerivatives (U : W^{m,p}(Ω; F))
    (V : Fin n → W^{m,p}(Ω; F))
    (hV : ∀ i, HasWeakDerivativeOn Ω [i]
      (U.val (baseIndex n m)) ((V i).val (baseIndex n m))) :
    ∃ W : W^{m + 1,p}(Ω; F),
      lowerOrderCLM (Nat.le_succ m) W = U ∧
      ∀ i, (∂[i] W : W^{m,p}(Ω; F)) = V i := by
  classical
  have hweak (a : DerivIndex n (m + 1)) :
      HasWeakDerivativeOn Ω a.toList
        (U.val (baseIndex n m)) (succOrderRow U V a) := by
    by_cases ha : a.toList.length ≤ m
    · simpa only [succOrderRow, dite_eq_left ha] using
        U.property.hasWeakDerivativeOn_list a.toList ha
    · cases hlist : a.toList with
      | nil => exact (ha (by simp [hlist])).elim
      | cons i rest =>
        have hrest : rest.length ≤ m := by
          have htotal := a.toList_length_le
          simp only [hlist, List.length_cons] at htotal
          omega
        have hnot : ¬(i :: rest).length ≤ m := by simpa only [hlist] using ha
        simpa only [succOrderRow, hlist, dite_eq_right hnot, List.head_cons, List.tail_cons,
          List.singleton_append] using
          HasWeakDerivativeOn.append_from_wkp (V i) [i] rest hrest (hV i)
  let W : W^{m + 1,p}(Ω; F) :=
    ⟨WithLp.toLp p (succOrderRow U V), fun a ↦ by
      change HasWeakDerivativeOn Ω a.toList
        (succOrderRow U V (baseIndex n (m + 1))) (succOrderRow U V a)
      rw [succOrderRow_base]
      exact hweak a⟩
  have hbase : W.val (baseIndex n (m + 1)) = U.val (baseIndex n m) :=
    succOrderRow_base U V
  refine ⟨W, ?_, fun i ↦ ?_⟩
  · apply WkpSpaceOn.ext_of_base_ae
    simp only [lowerOrderCLM_apply, DerivIndex.castOrder_baseIndex, hbase]
    exact Filter.EventuallyEq.rfl
  · apply WkpSpaceOn.ext_of_base_ae
    have hfirst := W.property.hasWeakDerivativeOn_list [i] (by simp)
    rw [hbase] at hfirst
    simpa only [partialDerivative_eq, partialDerivCLM, derivativeWordCLM_apply,
      derivativeWordIndex_baseIndex] using
      hfirst.ae_eq (hV i)

/-- A positive-order graph gains one order when each first derivative has the
same Sobolev regularity. This is the coordinate-equality form used in chart
pullback induction. -/
theorem exists_succOrder_of_firstDerivatives (hm : 0 < m) (U : W^{m,p}(Ω; F))
    (V : Fin n → W^{m,p}(Ω; F))
    (hV : ∀ i, (V i).val (baseIndex n m) =
      U.val (firstDerivIndex n m hm i)) :
    ∃ W : W^{m + 1,p}(Ω; F),
      (W.val (baseIndex n (m + 1)) : ℝ^n → F) =ᵐ[domainMeasure n Ω]
        (U.val (baseIndex n m) : ℝ^n → F) := by
  have hfirst (i : Fin n) : HasWeakDerivativeOn Ω [i]
      (U.val (baseIndex n m)) ((V i).val (baseIndex n m)) := by
    rw [hV i]
    simpa only [firstDerivIndex] using
      U.property.hasWeakDerivativeOn_list [i] (by simp only [List.length_singleton]; omega)
  obtain ⟨W, hW, _⟩ := exists_succOrder_of_weakDerivatives U V hfirst
  refine ⟨W, ?_⟩
  have hbase := congrArg (fun T : W^{m,p}(Ω; F) ↦ T.val (baseIndex n m)) hW
  simp only [lowerOrderCLM_apply, DerivIndex.castOrder_baseIndex] at hbase
  exact Filter.EventuallyEq.of_eq (congrArg (fun f : Lp F p (domainMeasure n Ω) ↦
    (f : ℝ^n → F)) hbase)

end SobolevSpace.VectorValued
