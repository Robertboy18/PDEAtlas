/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Pullback.VectorValued.FirstOrder
public import PDE.Spaces.Sobolev.Extension.VectorValued.Multiplier
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.SuccOrder
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.ZeroOrder
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Topology
import PDE.Analysis.Normed.Operator.InjectiveLift

/-!
# Higher-order chart pullback for Banach-valued Sobolev functions

A bounded `C^k` chart with a `C¹` inverse preserves the Banach-valued
Sobolev graph. The induction multiplies pulled-back first derivatives by `C^(k-1)`
chart coefficients, then assembles the successor graph. No embedding theorem or
additional coefficient derivative is needed. An injective closed-graph lift of
the `Lp` pullback gives the bounded operator in the original graph norm.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued.WeakChangeOfVariables

open GraphSpace

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {E : OpenPartialHomeomorph ℝ^n ℝ^n}

private theorem base_partial_weak {k : ℕ} {Ω : Opens ℝ^n}
    (U : W^{k + 1,p}(Ω; F)) (i : Fin n) :
    HasWeakDerivativeOn Ω [i] (U.val (baseIndex n (k + 1)))
      ((∂[i] U : W^{k,p}(Ω; F)).val (baseIndex n k)) := by
  simpa only [partialDerivative_eq, partialDerivCLM, derivativeWordCLM_apply,
    derivativeWordIndex_baseIndex] using
    U.property.hasWeakDerivativeOn_list [i] (by simp)

private theorem base_finsetSum {k : ℕ} {Ω : Opens ℝ^n} {ι : Type*}
    (S : Finset ι) (U : ι → W^{k,p}(Ω; F)) :
    ((∑ i ∈ S, U i).val (baseIndex n k) : ℝ^n → F) =ᵐ[domainMeasure n Ω]
      fun x ↦ ∑ i ∈ S, (U i).val (baseIndex n k) x := by
  change (coordinateCLM (baseIndex n k) (∑ i ∈ S, U i) : ℝ^n → F) =ᵐ[_] _
  rw [map_sum]
  exact Lp.coeFn_fun_finsetSum S (fun i ↦ coordinateCLM (baseIndex n k) (U i))

omit [Fact (1 ≤ p)] [CompleteSpace F] [NormedAddCommGroup F] [NormedSpace ℝ F] in
private theorem contDiff_chart_coefficient {k : ℕ}
    (hE : ContDiff ℝ (k + 1) E) (i j : Fin n) :
    ContDiff ℝ k (fun x ↦ (fderiv ℝ E x (EuclideanSpace.single i 1)) j) := by
  have hfd : ContDiff ℝ k (fderiv ℝ E) := hE.fderiv_right (by simp)
  exact (EuclideanSpace.proj j).contDiff.comp (hfd.clm_apply contDiff_const)

/-- Pullback by a bounded chart preserves every finite Sobolev order, for arbitrary
Banach codomains and `1 ≤ p ≤ ∞`. At order zero only the `C¹` chart assumptions
needed by the `Lp` pullback are used. -/
theorem exists_pullback (k : ℕ)
    (hE : ContDiff ℝ (max k 1 : ℕ) E) (hSymm : ContDiff ℝ 1 E.symm)
    (hTarget : Bornology.IsBounded E.target)
    (U : W^{k,p}(⟨E.target, E.open_target⟩; F)) :
    ∃ P : W^{k,p}(⟨E.source, E.open_source⟩; F),
      (P.val (baseIndex n k) : ℝ^n → F) =ᵐ[domainMeasure n E.source]
        fun x ↦ U.val (baseIndex n k) (E x) := by
  classical
  induction k with
  | zero =>
      refine ⟨lpToZeroOrder
        (SobolevSpace.WeakChangeOfVariables.boundedPullbackCLM hE hSymm hTarget
          (U.val (baseIndex n 0))), ?_⟩
      exact SobolevSpace.WeakChangeOfVariables.boundedPullbackLp_apply_ae
        hE hSymm hTarget _
  | succ k ih =>
      have hEk : ContDiff ℝ (k + 1) E := by simpa using hE
      have hE1 : ContDiff ℝ 1 E := hEk.of_le (by simp)
      have hElower : ContDiff ℝ (max k 1 : ℕ) E :=
        hEk.of_le (by
          have hk : max k 1 ≤ k + 1 := Nat.max_le.mpr ⟨Nat.le_succ k, by omega⟩
          exact_mod_cast hk)
      have hSource := SobolevSpace.WeakChangeOfVariables.isBounded_source_of_isBounded_target
        hSymm.continuous hTarget
      obtain ⟨P, hP⟩ := ih hElower (lowerOrderCLM (Nat.le_succ k) U)
      choose Q hQ using fun j : Fin n ↦ ih hElower (∂[j] U :
        W^{k,p}(⟨E.target, E.open_target⟩; F))
      let c (i j : Fin n) (x : ℝ^n) : ℝ :=
        (fderiv ℝ E x (EuclideanSpace.single i 1)) j
      choose T hT using fun i j : Fin n ↦ exists_smul_contDiff_on_bounded hSource
        (c i j) (contDiff_chart_coefficient hEk i j) (Q j)
      have hTbase (i j : Fin n) :
          ((T i j).val (baseIndex n k) : ℝ^n → F) =ᵐ[domainMeasure n E.source]
            fun x ↦ c i j x • (∂[j] U : W^{k,p}(⟨E.target, E.open_target⟩; F)).val
              (baseIndex n k) (E x) := by
        filter_upwards [hT i j, hQ j] with x ht hq
        exact ht.trans (congrArg (fun v ↦ c i j x • v) hq)
      let D (i : Fin n) : W^{k,p}(⟨E.source, E.open_source⟩; F) := ∑ j, T i j
      have hDbase (i : Fin n) :
          ((D i).val (baseIndex n k) : ℝ^n → F) =ᵐ[domainMeasure n E.source]
            fun x ↦ ∑ j, c i j x •
              (∂[j] U : W^{k,p}(⟨E.target, E.open_target⟩; F)).val
                (baseIndex n k) (E x) := by
        filter_upwards [base_finsetSum Finset.univ (T i), ae_all_iff.mpr (hTbase i)]
          with x hx hterms
        exact hx.trans (Finset.sum_congr rfl fun j _ ↦ hterms j)
      have hPbase : (P.val (baseIndex n k) : ℝ^n → F) =ᵐ[domainMeasure n E.source]
          fun x ↦ U.val (baseIndex n (k + 1)) (E x) := by
        simpa only [lowerOrderCLM_apply, DerivIndex.castOrder_baseIndex] using hP
      have hDweak (i : Fin n) : HasWeakDerivativeOn ⟨E.source, E.open_source⟩ [i]
          (P.val (baseIndex n k)) ((D i).val (baseIndex n k)) := by
        have hchain := hasWeakDerivativeOn_comp_partialHomeomorph hE1 hSymm hTarget
          (Lp.memLp (U.val (baseIndex n (k + 1))))
          (fun j ↦ Lp.memLp ((∂[j] U :
            W^{k,p}(⟨E.target, E.open_target⟩; F)).val (baseIndex n k)))
          (base_partial_weak U) i
        exact hchain.congr_ae hPbase.symm (hDbase i).symm
      obtain ⟨V, hV, _⟩ := exists_succOrder_of_weakDerivatives P D hDweak
      refine ⟨V, ?_⟩
      have hbase := congrArg (fun A ↦ A.val (baseIndex n k)) hV
      simp only [lowerOrderCLM_apply, DerivIndex.castOrder_baseIndex] at hbase
      rw [hbase]
      exact hPbase

variable {k : ℕ}

/-- The Sobolev pullback is a bounded lift of the same `Lp` pullback. -/
theorem exists_pullbackCLM
    (hE : ContDiff ℝ (max k 1 : ℕ) E) (hSymm : ContDiff ℝ 1 E.symm)
    (hTarget : Bornology.IsBounded E.target) :
    ∃ T : W^{k,p}(⟨E.target, E.open_target⟩; F) →L[ℝ]
        W^{k,p}(⟨E.source, E.open_source⟩; F),
      (coordinateCLM (baseIndex n k)).comp T =
        (SobolevSpace.WeakChangeOfVariables.boundedPullbackCLM
          (hE.of_le (by exact_mod_cast Nat.le_max_right k 1)) hSymm hTarget).comp
            (coordinateCLM (baseIndex n k)) := by
  let A : W^{k,p}(⟨E.source, E.open_source⟩; F) →L[ℝ]
      Lp F p (domainMeasure n E.source) := coordinateCLM (baseIndex n k)
  let B : W^{k,p}(⟨E.target, E.open_target⟩; F) →L[ℝ]
      Lp F p (domainMeasure n E.source) :=
    (SobolevSpace.WeakChangeOfVariables.boundedPullbackCLM
      (hE.of_le (by exact_mod_cast Nat.le_max_right k 1)) hSymm hTarget).comp
        (coordinateCLM (baseIndex n k))
  have hA : Function.Injective A := baseCoordinateCLM_injective
  have hB (U : W^{k,p}(⟨E.target, E.open_target⟩; F)) : ∃ P, A P = B U := by
    obtain ⟨P, hP⟩ := exists_pullback k hE hSymm hTarget U
    refine ⟨P, Lp.ext (hP.trans ?_)⟩
    exact (SobolevSpace.WeakChangeOfVariables.boundedPullbackLp_apply_ae
      (hE.of_le (by exact_mod_cast Nat.le_max_right k 1)) hSymm hTarget _).symm
  exact ContinuousLinearMap.exists_lift_of_injective A B hA hB

/-- Composition with a bounded `C^k` chart on the Banach-valued Sobolev graph.
The closed graph theorem supplies continuity in the graph norm. -/
def pullbackCLM
    (hE : ContDiff ℝ (max k 1 : ℕ) E) (hSymm : ContDiff ℝ 1 E.symm)
    (hTarget : Bornology.IsBounded E.target) :
    W^{k,p}(⟨E.target, E.open_target⟩; F) →L[ℝ]
      W^{k,p}(⟨E.source, E.open_source⟩; F) :=
  (exists_pullbackCLM hE hSymm hTarget).choose

/-- Reading the base coordinate gives exactly the canonical bounded `Lp` pullback. -/
theorem coordinateCLM_comp_pullbackCLM
    (hE : ContDiff ℝ (max k 1 : ℕ) E) (hSymm : ContDiff ℝ 1 E.symm)
    (hTarget : Bornology.IsBounded E.target) :
    (coordinateCLM (baseIndex n k)).comp (pullbackCLM (F := F) (p := p) hE hSymm hTarget) =
      (SobolevSpace.WeakChangeOfVariables.boundedPullbackCLM
        (hE.of_le (by exact_mod_cast Nat.le_max_right k 1)) hSymm hTarget).comp
          (coordinateCLM (baseIndex n k)) :=
  (exists_pullbackCLM hE hSymm hTarget).choose_spec

/-- The physical `Lp` coordinate of the Sobolev pullback is the canonical `Lp` pullback. -/
@[simp] theorem pullbackCLM_base
    (hE : ContDiff ℝ (max k 1 : ℕ) E) (hSymm : ContDiff ℝ 1 E.symm)
    (hTarget : Bornology.IsBounded E.target)
    (U : W^{k,p}(⟨E.target, E.open_target⟩; F)) :
    (pullbackCLM hE hSymm hTarget U).val (baseIndex n k) =
      SobolevSpace.WeakChangeOfVariables.boundedPullbackCLM
        (hE.of_le (by exact_mod_cast Nat.le_max_right k 1)) hSymm hTarget
          (U.val (baseIndex n k)) :=
  congrArg (fun T ↦ T U) (coordinateCLM_comp_pullbackCLM hE hSymm hTarget)

/-- The Sobolev pullback represents composition with the chart almost everywhere. -/
theorem pullbackCLM_base_ae
    (hE : ContDiff ℝ (max k 1 : ℕ) E) (hSymm : ContDiff ℝ 1 E.symm)
    (hTarget : Bornology.IsBounded E.target)
    (U : W^{k,p}(⟨E.target, E.open_target⟩; F)) :
    ((pullbackCLM hE hSymm hTarget U).val (baseIndex n k) : ℝ^n → F)
      =ᵐ[domainMeasure n E.source] fun x ↦ U.val (baseIndex n k) (E x) := by
  rw [pullbackCLM_base]
  exact SobolevSpace.WeakChangeOfVariables.boundedPullbackLp_apply_ae
    (hE.of_le (by exact_mod_cast Nat.le_max_right k 1)) hSymm hTarget _

/-- The first derivative of the higher-order pullback is the physical chain-rule
sum of chart coefficients and pulled-back weak derivatives. -/
theorem pullbackCLM_partialDeriv_ae
    (hE : ContDiff ℝ (max (k + 1) 1 : ℕ) E) (hSymm : ContDiff ℝ 1 E.symm)
    (hTarget : Bornology.IsBounded E.target)
    (U : W^{k + 1,p}(⟨E.target, E.open_target⟩; F)) (i : Fin n) :
    ((∂[i] (pullbackCLM hE hSymm hTarget U) :
        W^{k,p}(⟨E.source, E.open_source⟩; F)).val (baseIndex n k) : ℝ^n → F)
      =ᵐ[domainMeasure n E.source] fun x ↦ ∑ j : Fin n,
        (∂[i] (E : ℝ^n → ℝ^n)) x j •
          (∂[j] U : W^{k,p}(⟨E.target, E.open_target⟩; F)).val (baseIndex n k) (E x) := by
  have hchain := hasWeakDerivativeOn_comp_partialHomeomorph
    (hE.of_le (by exact_mod_cast Nat.le_max_right (k + 1) 1)) hSymm hTarget
    (Lp.memLp (U.val (baseIndex n (k + 1))))
    (fun j ↦ Lp.memLp ((∂[j] U :
      W^{k,p}(⟨E.target, E.open_target⟩; F)).val (baseIndex n k)))
    (base_partial_weak U) i
  exact (base_partial_weak (pullbackCLM hE hSymm hTarget U) i).ae_eq
    (hchain.congr_ae (pullbackCLM_base_ae hE hSymm hTarget U).symm Filter.EventuallyEq.rfl)

/-- Pullback commutes with every continuous linear map of Banach codomains. -/
theorem pullbackCLM_mapCLM
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (hE : ContDiff ℝ (max k 1 : ℕ) E) (hSymm : ContDiff ℝ 1 E.symm)
    (hTarget : Bornology.IsBounded E.target) (L : F →L[ℝ] G)
    (U : W^{k,p}(⟨E.target, E.open_target⟩; F)) :
    pullbackCLM hE hSymm hTarget (mapCLM L U) =
      mapCLM L (pullbackCLM hE hSymm hTarget U) := by
  apply baseCoordinateCLM_injective
  simp only [coordinateCLM_apply, pullbackCLM_base, mapCLM_apply]
  exact SobolevSpace.WeakChangeOfVariables.boundedPullbackCLM_compLpL
    (hE.of_le (by exact_mod_cast Nat.le_max_right k 1)) hSymm hTarget L _

end SobolevSpace.VectorValued.WeakChangeOfVariables
