/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.SmoothMultiplier
public import PDE.Spaces.Sobolev.Extension.HigherOrder.Multiplier
import PDE.DistributionTheory.TestFunction.CompactCutoff

/-!
# Finite regularity scalar multipliers on Banach-valued Sobolev spaces

A compactly supported `C^k` scalar coefficient multiplies the full `W^{k,p}` weak jet.
Continuous duality transfers the scalar finite regularity theorem to any Banach codomain,
with the same finite Leibniz rows. On bounded domains a smooth cutoff supplies compact
support without changing the coefficient on the domain.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev Distributions

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens ℝ^n}
  {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- A continuous linear map commutes almost everywhere with every finite Leibniz row. -/
theorem smoothLeibnizRepresentative_mapCLM_ae (L : F →L[ℝ] G)
    (a : ℝ^n → ℝ) (U : W^{k,p}(Ω; F)) (α : List (Fin n)) :
    smoothLeibnizRepresentative a (mapCLM L U) α =ᵐ[domainMeasure n Ω]
      fun x ↦ L (smoothLeibnizRepresentative a U α x) := by
  filter_upwards [ae_all_iff.mpr (fun b ↦ mapCLM_apply_ae L U b)] with x hx
  simp only [smoothLeibnizRepresentative, map_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro q _
  simp only [Function.comp_apply, map_smul]
  by_cases hq : q.2.length ≤ k
  · simp only [wordRepresentative, dite_eq_left hq, hx]
  · simp only [wordRepresentative, dite_eq_right hq, Pi.zero_apply, map_zero]

/-- A compactly supported `C^k` coefficient multiplies every Banach-valued Sobolev jet,
including the endpoint exponents, with the exact finite Leibniz coordinates. -/
theorem exists_smul_contDiff_compact (a : ℝ^n → ℝ) (ha : ContDiff ℝ k a)
    (hac : HasCompactSupport a) (U : W^{k,p}(Ω; F)) :
    ∃ W : W^{k,p}(Ω; F),
      (W.val (baseIndex n k) : ℝ^n → F) =ᵐ[domainMeasure n Ω]
        (fun x ↦ a x • U.val (baseIndex n k) x) ∧
      ∀ α : DerivIndex n k, (W.val α : ℝ^n → F) =ᵐ[domainMeasure n Ω]
        smoothLeibnizRepresentative a U α.toList := by
  have hbound β (hβ : β.length ≤ k) :
      MemLp (iteratedPartialDeriv β a) ∞ (domainMeasure n Ω) :=
    (PDE.contDiff_iteratedPartialDeriv_of_le ha β hβ).continuous.memLp_top_of_hasCompactSupport
      (hasCompactSupport_iteratedPartialDeriv hac β) _
  let d := fun α : DerivIndex n k ↦ smoothLeibnizRepresentative a U α.toList
  have hmem α : MemLp (d α) p (domainMeasure n Ω) :=
    memLp_smoothLeibnizRepresentative a hbound U α.toList α.toList_length_le
  have hweak α : HasWeakDerivativeOn Ω α.toList (d (baseIndex n k)) (d α) := by
    apply (hasWeakDerivativeOn_iff_forall_dual
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((hmem (baseIndex n k)).locallyIntegrable Fact.out))
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((hmem α).locallyIntegrable Fact.out))).mpr
    intro L
    obtain ⟨S, hbase, hrows⟩ := Extension.HigherOrder.exists_mul_contDiff_compact
      a ha hac (scalarEquiv (mapCLM L U))
    have hscalar := (S.property α).congr_ae hbase (hrows α)
    have hrow : weakLeibnizExpansion a
        (wkpWordRepresentative (scalarEquiv (mapCLM L U))) α.toList.reverse =
        smoothLeibnizRepresentative a (mapCLM L U) α.toList := rfl
    rw [hrow] at hscalar
    apply (SobolevSpace.hasWeakDerivativeOn_congr_ae
      (α := α.toList) _ (smoothLeibnizRepresentative_mapCLM_ae L a U α.toList)).mp
      hscalar
    filter_upwards [mapCLM_apply_ae L U (baseIndex n k)] with x hx
    simp only [d, baseIndex_toList, smoothLeibnizRepresentative_nil,
      Function.comp_apply, map_smul]
    change a x * (mapCLM L U).val (baseIndex n k) x = a x * L (U.val (baseIndex n k) x)
    rw [hx]
  refine ⟨ofWeakDerivatives d hmem hweak, ?_, fun α ↦
    ofWeakDerivatives_apply_ae d hmem hweak α⟩
  simpa only [d, baseIndex_toList, smoothLeibnizRepresentative_nil] using
    ofWeakDerivatives_apply_ae d hmem hweak (baseIndex n k)

/-- A global `C^k` scalar coefficient multiplies Banach-valued `W^{k,p}` on a bounded
open domain. Compactification supplies the required coefficient bounds. -/
theorem exists_smul_contDiff_on_bounded (hbounded : Bornology.IsBounded (Ω : Set ℝ^n))
    (a : ℝ^n → ℝ) (ha : ContDiff ℝ k a) (U : W^{k,p}(Ω; F)) :
    ∃ W : W^{k,p}(Ω; F),
      (W.val (baseIndex n k) : ℝ^n → F) =ᵐ[domainMeasure n Ω]
        fun x ↦ a x • U.val (baseIndex n k) x := by
  obtain ⟨ψ, _, hψ, _, _⟩ := TestFunction.exists_eq_one_on_compact
    isOpen_univ hbounded.isCompact_closure (Set.subset_univ _)
  obtain ⟨W, hW, _⟩ := exists_smul_contDiff_compact
    (fun x ↦ ψ.toFun x * a x) ((ψ.contDiff.of_le (by simp)).mul ha)
    ψ.hasCompactSupport.mul_right U
  refine ⟨W, ?_⟩
  filter_upwards [hW, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
  simpa only [hψ x (subset_closure hxΩ), one_mul] using hx

end SobolevSpace.VectorValued
