/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.IndicatorExtension
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Restriction
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.ZeroOrder

/-!
# Zero extension of Banach-valued order-zero Sobolev functions

The order-zero graph is its base `Lp` class, so extension by the indicator of
the open domain preserves its norm. The physical representative vanishes
almost everywhere outside the domain, and restriction recovers the input.
The construction includes `p = ∞` and dimension zero.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens ℝ^n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private theorem measurePreserving_id_top :
    MeasurePreserving (id : ℝ^n → ℝ^n) (domainMeasure n (⊤ : Opens ℝ^n)) volume := by
  simpa only [domainMeasure, Opens.coe_top, Measure.restrict_univ] using
    (MeasurePreserving.id (volume : Measure ℝ^n))

/-- Extension by zero is a linear isometry on order-zero Banach-valued Sobolev graphs. -/
def zeroExtendₗᵢ : W^{0,p}(Ω; F) →ₗᵢ[ℝ] W^{0,p}(ℝ^n; F) :=
  (lpEquivZeroOrder (Ω := ⊤)).toLinearIsometry.comp
    ((Lp.compMeasurePreservingₗᵢ ℝ id (by exact measurePreserving_id_top)).comp
      ((Lp.extendByZeroₗᵢ (𝕜 := ℝ) Ω.isOpen.measurableSet).comp
        lpEquivZeroOrder.symm.toLinearIsometry))

/-- The base coordinate of zero extension is represented by the domain indicator. -/
theorem zeroExtendₗᵢ_apply_ae (U : W^{0,p}(Ω; F)) :
    ((zeroExtendₗᵢ U).val (baseIndex n 0) : ℝ^n → F) =ᵐ[volume]
      (Ω : Set ℝ^n).indicator (fun x ↦ U.val (baseIndex n 0) x) := by
  have htransport := Lp.coeFn_compMeasurePreserving
    (Lp.extendByZeroₗᵢ (𝕜 := ℝ) Ω.isOpen.measurableSet (U.val (baseIndex n 0)))
    (measurePreserving_id_top (n := n))
  have hzero := Lp.extendByZeroₗᵢ_apply_ae (𝕜 := ℝ)
    Ω.isOpen.measurableSet (U.val (baseIndex n 0))
  have htransport' :
      ((zeroExtendₗᵢ U).val (baseIndex n 0) : ℝ^n → F)
        =ᵐ[domainMeasure n (⊤ : Opens ℝ^n)]
        (Lp.extendByZeroₗᵢ (𝕜 := ℝ) Ω.isOpen.measurableSet
          (U.val (baseIndex n 0)) : ℝ^n → F) :=
    htransport
  have hvolume : volume ≤ domainMeasure n (⊤ : Opens ℝ^n) := by
    simp only [domainMeasure, Opens.coe_top, Measure.restrict_univ, le_refl]
  filter_upwards [ae_mono hvolume htransport', hzero] with x hx hxzero
  exact hx.trans hxzero

/-- Any representative on the original domain gives the same indicator representative. -/
theorem zeroExtendₗᵢ_base_ae (U : W^{0,p}(Ω; F)) {f : ℝ^n → F}
    (hU : (U.val (baseIndex n 0) : ℝ^n → F) =ᵐ[domainMeasure n Ω] f) :
    ((zeroExtendₗᵢ U).val (baseIndex n 0) : ℝ^n → F) =ᵐ[volume]
      (Ω : Set ℝ^n).indicator f :=
  (zeroExtendₗᵢ_apply_ae U).trans
    ((ae_eq_restrict_iff_indicator_ae_eq Ω.isOpen.measurableSet).mp hU)

/-- Zero extension agrees almost everywhere with the original function on its domain. -/
theorem zeroExtendₗᵢ_agree_ae (U : W^{0,p}(Ω; F)) :
    ((zeroExtendₗᵢ U).val (baseIndex n 0) : ℝ^n → F) =ᵐ[domainMeasure n Ω]
      U.val (baseIndex n 0) := by
  filter_upwards [ae_mono Measure.restrict_le_self (zeroExtendₗᵢ_apply_ae U),
    ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
  exact hx.trans (Set.indicator_of_mem hxΩ _)

/-- The physical base representative vanishes almost everywhere off the original domain. -/
theorem zeroExtendₗᵢ_eq_zero_ae (U : W^{0,p}(Ω; F)) :
    ((zeroExtendₗᵢ U).val (baseIndex n 0) : ℝ^n → F)
      =ᵐ[volume.restrict (Ω : Set ℝ^n)ᶜ] 0 := by
  filter_upwards [ae_mono Measure.restrict_le_self (zeroExtendₗᵢ_apply_ae U),
    ae_restrict_mem Ω.isOpen.measurableSet.compl] with x hx hxΩ
  exact hx.trans (Set.indicator_of_notMem hxΩ _)

/-- Zero extension preserves the complete order-zero graph norm. -/
theorem norm_zeroExtendₗᵢ (U : W^{0,p}(Ω; F)) :
    ‖zeroExtendₗᵢ U‖ = ‖U‖ :=
  zeroExtendₗᵢ.norm_map U

/-- Restricting the zero extension to the original open domain recovers the input. -/
@[simp] theorem restrictCLM_zeroExtendₗᵢ (U : W^{0,p}(Ω; F)) :
    restrictCLM (show Ω ≤ ⊤ from le_top) (zeroExtendₗᵢ U) = U := by
  apply WkpSpaceOn.ext_of_base_ae
  exact (restrictCLM_apply_ae le_top (zeroExtendₗᵢ U) (baseIndex n 0)).trans
    (zeroExtendₗᵢ_agree_ae U)

/-- Zero extension is a right inverse of restriction as an identity of continuous linear maps. -/
@[simp] theorem restrictCLM_comp_zeroExtendₗᵢ :
    (restrictCLM (F := F) (k := 0) (p := p) (show Ω ≤ ⊤ from le_top)).comp
      zeroExtendₗᵢ.toContinuousLinearMap =
        ContinuousLinearMap.id ℝ W^{0,p}(Ω; F) := by
  ext U : 1
  exact restrictCLM_zeroExtendₗᵢ U

end SobolevSpace.VectorValued
