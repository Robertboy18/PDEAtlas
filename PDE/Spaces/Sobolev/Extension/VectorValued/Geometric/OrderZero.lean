/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.VectorValued.ZeroOrder

/-!
# Order-zero extension from an open domain

The order-zero isometric extension has an `Lp` companion, given by the
same physical indicator. Their base-coordinate equality supplies the order-zero
case of geometric extension without imposing boundary regularity. This bridge
works in dimension zero and at both exponent endpoints.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace Set
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued.GeometricExtension

open GraphSpace

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens ℝ^n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The physical order-zero extension is the indicator extension of an `Lp` class. -/
def zeroOrderExtensionLp :
    Lp F p (domainMeasure n Ω) →L[ℝ] Lp F p (domainMeasure n univ) :=
  (Lp.restrictionCLMOfLE
    (show domainMeasure n univ ≤ volume from Measure.restrict_le_self)).comp
    (Lp.extendByZeroₗᵢ (𝕜 := ℝ) Ω.isOpen.measurableSet).toContinuousLinearMap

/-- The extension is represented by the original function on the domain and zero outside. -/
theorem zeroOrderExtensionLp_apply_ae (u : Lp F p (domainMeasure n Ω)) :
    (zeroOrderExtensionLp u : ℝ^n → F) =ᵐ[domainMeasure n univ]
      (Ω : Set ℝ^n).indicator (u : ℝ^n → F) :=
  (Lp.restrictionCLMOfLE_apply_ae _ _).trans
    (ae_mono Measure.restrict_le_self
      (Lp.extendByZeroₗᵢ_apply_ae (𝕜 := ℝ) Ω.isOpen.measurableSet u))

/-- Restricting the indicator extension recovers the initial `Lp` class. -/
theorem restrict_zeroOrderExtensionLp (u : Lp F p (domainMeasure n Ω)) :
    Lp.restrictionCLMOfLE
      (Measure.restrict_mono (subset_univ (Ω : Set ℝ^n)) le_rfl)
      (zeroOrderExtensionLp u) = u := by
  apply Lp.ext
  refine (Lp.restrictionCLMOfLE_apply_ae _ _).trans ?_
  have h := ae_mono (Measure.restrict_mono (subset_univ (Ω : Set ℝ^n)) le_rfl)
    (zeroOrderExtensionLp_apply_ae u)
  filter_upwards [h, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
  simpa only [indicator_of_mem hxΩ] using hx

/-- Indicator extension does not increase the physical `Lp` norm. -/
theorem norm_zeroOrderExtensionLp_le (u : Lp F p (domainMeasure n Ω)) :
    ‖zeroOrderExtensionLp u‖ ≤ ‖u‖ := by
  exact (Lp.norm_restrictionCLMOfLE_apply_le _ _).trans_eq
    (LinearIsometry.norm_map _ u)

/-- A continuous linear map commutes with zero extension almost everywhere. -/
theorem zeroOrderExtensionLp_compLpL_ae
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (u : Lp F p (domainMeasure n Ω)) :
    (zeroOrderExtensionLp (L.compLpL p (domainMeasure n Ω) u) : ℝ^n → G)
      =ᵐ[volume] L ∘ (zeroOrderExtensionLp u : ℝ^n → F) := by
  have hu := (ae_restrict_iff' Ω.isOpen.measurableSet).mp (L.coeFn_compLpL u)
  have hv := zeroOrderExtensionLp_apply_ae u
  have hw := zeroOrderExtensionLp_apply_ae (L.compLpL p (domainMeasure n Ω) u)
  simp only [domainMeasure, Measure.restrict_univ] at hv hw
  filter_upwards [hu, hv, hw] with x hx hvx hwx
  rw [Function.comp_apply, hvx, hwx]
  by_cases hxΩ : x ∈ Ω
  · simpa only [indicator_of_mem hxΩ] using hx hxΩ
  · simp only [indicator_of_notMem hxΩ, map_zero]

variable [CompleteSpace F]

/-- The order-zero isometry has the indicator extension as its base action. -/
theorem zeroExtendₗᵢ_base_eq_zeroOrderExtensionLp (U : W^{0,p}(Ω; F)) :
    coordinateCLM (baseIndex n 0) (zeroExtendₗᵢ U) =
      zeroOrderExtensionLp (coordinateCLM (baseIndex n 0) U) := by
  apply Lp.ext
  have h :
      ((zeroExtendₗᵢ U).val (baseIndex n 0) : ℝ^n → F) =ᵐ[domainMeasure n univ]
        (Ω : Set ℝ^n).indicator (fun x ↦ U.val (baseIndex n 0) x) :=
    ae_mono Measure.restrict_le_self (zeroExtendₗᵢ_apply_ae U)
  exact h.trans (zeroOrderExtensionLp_apply_ae (U.val (baseIndex n 0))).symm

end SobolevSpace.VectorValued.GeometricExtension
