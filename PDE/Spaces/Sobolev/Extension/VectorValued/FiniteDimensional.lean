/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.VectorValued.Geometric.RightInverse

/-!
# Sobolev extension with finite-dimensional real values

A scalar extension acts on the coordinates of a finite basis. Reassembling the
extended coordinates gives a bounded operator on the Banach-valued Sobolev graph,
with its original norm. The bound records the norms of the basis vectors and
coordinate functionals; no Euclidean norm on the target is substituted.

The transfer works in every dimension and derivative order and for `1 ≤ p ≤ ∞`.
The imported geometric entry `exists_extension` supplies an extension on bounded
open domains with Cᵏ graph boundary for arbitrary real Banach targets.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.Extension.VectorValued

open SobolevSpace.VectorValued

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens ℝ^n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ F] {ι : Type*} [Fintype ι]

/-- Extend the scalar coordinates of a finite basis and reassemble the vector.
Both scalar identifications are isometries of the full Sobolev graph. -/
def ofScalar (b : Module.Basis ι ℝ F)
    (E : W^{k,p}(Ω) →L[ℝ] W^{k,p}((Set.univ : Set ℝ^n))) :
    W^{k,p}(Ω; F) →L[ℝ] W^{k,p}(ℝ^n; F) :=
  ∑ i, (mapCLM (ContinuousLinearMap.toSpanSingleton ℝ (b i))).comp
    (scalarEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (E.comp (scalarEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (mapCLM (b.coord i).toContinuousLinearMap))))

/-- The coordinate construction obeys the finite-basis bound in the original
Sobolev graph norm, including the maximum norm at `p = ∞`. -/
theorem norm_ofScalar_apply_le (b : Module.Basis ι ℝ F)
    (E : W^{k,p}(Ω) →L[ℝ] W^{k,p}((Set.univ : Set ℝ^n)))
    (U : W^{k,p}(Ω; F)) :
    ‖ofScalar b E U‖ ≤
      (∑ i, ‖b i‖ * ‖(b.coord i).toContinuousLinearMap‖) * ‖E‖ * ‖U‖ := by
  let V (i : ι) : W^{k,p}(Ω; ℝ) := mapCLM (b.coord i).toContinuousLinearMap U
  let T (i : ι) : W^{k,p}(ℝ^n; ℝ) := scalarEquiv.symm (E (scalarEquiv (V i)))
  have hsum : ofScalar b E U =
      ∑ i, mapCLM (ContinuousLinearMap.toSpanSingleton ℝ (b i)) (T i) := by
    simp only [ofScalar, sum_apply, ContinuousLinearMap.comp_apply]
    rfl
  calc
    ‖ofScalar b E U‖ ≤
        ∑ i, ‖mapCLM (ContinuousLinearMap.toSpanSingleton ℝ (b i)) (T i)‖ := by
      rw [hsum]
      exact norm_sum_le _ _
    _ ≤ ∑ i, ‖b i‖ * (‖E‖ * (‖(b.coord i).toContinuousLinearMap‖ * ‖U‖)) := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ‖ContinuousLinearMap.toSpanSingleton ℝ (b i)‖ *
            ‖T i‖ :=
          norm_mapCLM_apply_le _ _
        _ = ‖b i‖ * ‖E (scalarEquiv (V i))‖ := by
          rw [ContinuousLinearMap.norm_toSpanSingleton]
          exact congrArg (‖b i‖ * ·) (scalarEquiv.symm.norm_map _)
        _ ≤ ‖b i‖ * (‖E‖ * ‖scalarEquiv (V i)‖) :=
          mul_le_mul_of_nonneg_left (E.le_opNorm _) (norm_nonneg _)
        _ ≤ _ := by
          rw [LinearIsometryEquiv.norm_map]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (norm_mapCLM_apply_le (b.coord i).toContinuousLinearMap U) (norm_nonneg E))
            (norm_nonneg _)
    _ = _ := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The operator norm grows by at most the sum of the basis projection bounds. -/
theorem norm_ofScalar_le (b : Module.Basis ι ℝ F)
    (E : W^{k,p}(Ω) →L[ℝ] W^{k,p}((Set.univ : Set ℝ^n))) :
    ‖ofScalar b E‖ ≤ (∑ i, ‖b i‖ * ‖(b.coord i).toContinuousLinearMap‖) * ‖E‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (norm_ofScalar_apply_le b E)

/-- Every derivative coordinate of the extension is the finite sum of the
extended scalar coordinates, almost everywhere in the whole space. -/
theorem ofScalar_apply_ae (b : Module.Basis ι ℝ F)
    (E : W^{k,p}(Ω) →L[ℝ] W^{k,p}((Set.univ : Set ℝ^n)))
    (U : W^{k,p}(Ω; F)) (a : GraphSpace.DerivIndex n k) :
    ((ofScalar b E U).val a : ℝ^n → F) =ᵐ[domainMeasure n Set.univ]
      fun x ↦ ∑ i, (E (scalarEquiv
        (mapCLM (b.coord i).toContinuousLinearMap U))).val a x • b i := by
  let V (i : ι) : W^{k,p}(Ω; ℝ) := mapCLM (b.coord i).toContinuousLinearMap U
  let T (i : ι) : W^{k,p}(ℝ^n; ℝ) := scalarEquiv.symm (E (scalarEquiv (V i)))
  let A (i : ι) : W^{k,p}(ℝ^n; F) :=
    mapCLM (ContinuousLinearMap.toSpanSingleton ℝ (b i)) (T i)
  have hsum : (ofScalar b E U).val a = ∑ i, (A i).val a := by
    change coordinateCLM a (ofScalar b E U) = _
    simp only [ofScalar, sum_apply, ContinuousLinearMap.comp_apply, map_sum]
    rfl
  have hA : ∀ᵐ x ∂domainMeasure n Set.univ, ∀ i,
      (A i).val a x = (T i).val a x • b i :=
    ae_all_iff.mpr fun i ↦
      mapCLM_apply_ae (ContinuousLinearMap.toSpanSingleton ℝ (b i)) (T i) a
  rw [hsum]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i ↦ (A i).val a),
    hA] with x hs h
  rw [hs]
  exact Finset.sum_congr rfl fun i _ ↦ h i

/-- If the scalar map is an extension, every weak derivative of the vector
extension agrees with the original on the open domain. -/
theorem ofScalar_agree_ae (b : Module.Basis ι ℝ F)
    (E : W^{k,p}(Ω) →L[ℝ] W^{k,p}((Set.univ : Set ℝ^n)))
    (hE : (GraphSpace.restrictCLM Ω.isOpen.measurableSet (Set.subset_univ (Ω : Set ℝ^n))).comp E =
      ContinuousLinearMap.id ℝ W^{k,p}((Ω : Set ℝ^n)))
    (U : W^{k,p}(Ω; F)) (a : GraphSpace.DerivIndex n k) :
    ((ofScalar b E U).val a : ℝ^n → F) =ᵐ[domainMeasure n Ω] U.val a := by
  let V (i : ι) : W^{k,p}(Ω; ℝ) := mapCLM (b.coord i).toContinuousLinearMap U
  have hscalar (i : ι) :
      ((E (scalarEquiv (V i))).val a : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦ b.coord i (U.val a x) := by
    have hrestrict := GraphSpace.restrictCLM_apply_ae Ω.isOpen.measurableSet
      (Set.subset_univ (Ω : Set ℝ^n)) (E (scalarEquiv (V i))) a
    have hi := DFunLike.congr_fun hE (scalarEquiv (V i))
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hi
    rw [hi] at hrestrict
    exact hrestrict.symm.trans (mapCLM_apply_ae (b.coord i).toContinuousLinearMap U a)
  have hsum := ae_mono (Measure.restrict_mono (Set.subset_univ (Ω : Set ℝ^n)) le_rfl)
    (ofScalar_apply_ae b E U a)
  filter_upwards [hsum, ae_all_iff.mpr hscalar] with x hs hx
  rw [hs]
  calc
    _ = ∑ i, b.coord i (U.val a x) • b i := Finset.sum_congr rfl fun i _ ↦ by
      rw [show (E (scalarEquiv (mapCLM (b.coord i).toContinuousLinearMap U))).val a x =
        b.coord i (U.val a x) from hx i]
    _ = U.val a x := b.sum_repr _

/-- Coordinate extension is a bounded right inverse of vector Sobolev restriction. -/
theorem restrict_ofScalar (b : Module.Basis ι ℝ F)
    (E : W^{k,p}(Ω) →L[ℝ] W^{k,p}((Set.univ : Set ℝ^n)))
    (hE : (GraphSpace.restrictCLM Ω.isOpen.measurableSet (Set.subset_univ (Ω : Set ℝ^n))).comp E =
      ContinuousLinearMap.id ℝ W^{k,p}((Ω : Set ℝ^n))) :
    (restrictCLM (show Ω ≤ ⊤ from le_top)).comp (ofScalar b E) =
      ContinuousLinearMap.id ℝ W^{k,p}(Ω; F) := by
  ext U : 1
  apply SobolevSpace.VectorValued.WkpSpaceOn.ext_of_base_ae
  exact (restrictCLM_apply_ae le_top (ofScalar b E U) (GraphSpace.baseIndex n k)).trans
    (ofScalar_agree_ae b E hE U (GraphSpace.baseIndex n k))

end SobolevSpace.Extension.VectorValued
