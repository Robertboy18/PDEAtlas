/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Localization.Cutoff.BoundedOperator
import PDE.Analysis.Normed.PiLp.CompareExp

/-!
# Quantitative bounds for relative cutoff extension

A smooth cutoff supported in an open set `V` extends `W^{k,p}(V ∩ Ω)` to
`W^{k,p}(Ω)` for open `Ω`. Its support may meet the boundary of `Ω`.

The operator `relativeCutoffCLM` has the same finite-jet bound as interior
cutoff extension, with the row norms computed on `V ∩ Ω`. Each Leibniz row
vanishes outside `V`, so restricting the target measure to `V` preserves its
norm. The bound then follows from the finite Leibniz estimate.
-/

@[expose] public noncomputable section

open scoped Sobolev

open TopologicalSpace
open scoped Distributions ENNReal

namespace SobolevSpace.CompactSupportLocalization.HigherOrderLocalizedCutoff

open MeasureTheory Set GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Each relative cutoff coordinate satisfies the finite Leibniz estimate
on `V ∩ Ω`, even when the cutoff support meets the boundary of `Ω`. -/
theorem norm_interCutoff_coordinate_le
    {V Ω : Set (ℝ^n)} (hV : IsOpen V) (hΩ : IsOpen Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψ : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}((V ∩ Ω))) (a : DerivIndex n k) :
    ‖(interCutoff hV hΩ ψ hψ U).val a‖ ≤
      (cutoffLeibnizENormBound U ψ a.toList.reverse).toReal := by
  rw [Lp.norm_def]
  have hα : a.toList.reverse.length ≤ k := by simpa using a.toList_length_le
  have hrow := interCutoff_coordinate_ae hV hΩ ψ hψ U a
  have hrestrict := eLpNorm_restrict_eq_of_support_subset (p := p)
    ((Lp.aestronglyMeasurable ((interCutoff hV hΩ ψ hψ U).val a)).congr hrow)
    ((weakLeibnizExpansion_support U ψ a.toList.reverse).trans hψ)
  have hmeasure : (domainMeasure n Ω).restrict V = domainMeasure n (V ∩ Ω) := by
    rw [domainMeasure, Measure.restrict_restrict hV.measurableSet]
  rw [hmeasure] at hrestrict
  rw [eLpNorm_congr_ae hrow, ← hrestrict]
  exact ENNReal.toReal_mono (cutoffLeibnizENormBound_ne_top U ψ a.toList.reverse hα)
    (eLpNorm_weakLeibnizExpansion_le U ψ a.toList.reverse hα)

/-- Relative cutoff extension has the same finite-jet graph bound as interior
extension, computed on the Sobolev source `V ∩ Ω`. -/
theorem norm_interCutoff_le_cutoffExtensionNormBound
    {V Ω : Set (ℝ^n)} (hV : IsOpen V) (hΩ : IsOpen Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψ : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}((V ∩ Ω))) :
    ‖interCutoff hV hΩ ψ hψ U‖ ≤
      cutoffExtensionNormBound k p (V ∩ Ω) ψ * ‖U‖ := by
  let _ : MeasurableSpace (DerivIndex n k) := ⊤
  let A : PiLp p (fun _ : DerivIndex n k ↦ ℝ) :=
    WithLp.toLp p fun a ↦ cutoffLeibnizRowBound (V ∩ Ω) ψ a.toList.reverse
  have hrow (a : DerivIndex n k) :
      ‖(interCutoff hV hΩ ψ hψ U).val a‖ ≤ ‖U‖ * ‖A a‖ := by
    have hα : a.toList.reverse.length ≤ k := by simpa using a.toList_length_le
    change ‖(interCutoff hV hΩ ψ hψ U).val a‖ ≤
      ‖U‖ * ‖cutoffLeibnizRowBound (V ∩ Ω) ψ a.toList.reverse‖
    rw [Real.norm_of_nonneg (cutoffLeibnizRowBound_nonneg (V ∩ Ω) ψ a.toList.reverse),
      mul_comm]
    exact (norm_interCutoff_coordinate_le hV hΩ ψ hψ U a).trans
      (cutoffLeibnizENormBound_toReal_le U ψ a.toList.reverse hα)
  have h := PiLp.norm_le_card_rpow_mul_of_coordinate_norm_le
    le_rfl ‖U‖ (norm_nonneg U) A (interCutoff hV hΩ ψ hψ U).val hrow
  change ‖(interCutoff hV hΩ ψ hψ U).val‖ ≤ ‖A‖ * ‖U‖
  simpa only [sub_self, ENNReal.rpow_zero, ENNReal.toReal_one, one_mul,
    mul_comm] using h

end SobolevSpace.CompactSupportLocalization.HigherOrderLocalizedCutoff

namespace SobolevSpace.Extension.HigherOrder

open MeasureTheory Set GraphSpace
open CompactSupportLocalization.HigherOrderLocalizedCutoff

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The relative bounded operator evaluates to the canonical relative extension. -/
@[simp]
theorem relativeCutoffCLM_apply
    {V Ω : Set (ℝ^n)} (hV : IsOpen V) (hΩ : IsOpen Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψ : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}((V ∩ Ω))) :
    relativeCutoffCLM hV hΩ ψ hψ U = interCutoff hV hΩ ψ hψ U :=
  rfl

/-- Relative cutoff extension has an explicit finite-jet operator bound at every
order and exponent, including `k = 0`, `p = 1`, and `p = ∞`. -/
theorem norm_relativeCutoffCLM_le
    {V Ω : Set (ℝ^n)} (hV : IsOpen V) (hΩ : IsOpen Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψ : tsupport ψ.toFun ⊆ V) :
    ‖relativeCutoffCLM (k := k) (p := p) hV hΩ ψ hψ‖ ≤
      cutoffExtensionNormBound k p (V ∩ Ω) ψ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (cutoffExtensionNormBound_nonneg (k := k) (p := p) (V ∩ Ω) ψ)
  exact norm_interCutoff_le_cutoffExtensionNormBound hV hΩ ψ hψ

/-- The base representative of relative extension is the cutoff product
almost everywhere on the target. -/
theorem relativeCutoffCLM_base_ae
    {V Ω : Set (ℝ^n)} (hV : IsOpen V) (hΩ : IsOpen Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψ : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}((V ∩ Ω))) :
    baseRepresentative (relativeCutoffCLM hV hΩ ψ hψ U)
      =ᵐ[domainMeasure n Ω] fun x ↦ ψ.toFun x * baseRepresentative U x :=
  interCutoff_base_ae hV hΩ ψ hψ U

/-- Every derivative coordinate of relative extension is its finite weak Leibniz
expansion, including the base row at order zero. -/
theorem relativeCutoffCLM_coordinate_ae
    {V Ω : Set (ℝ^n)} (hV : IsOpen V) (hΩ : IsOpen Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψ : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}((V ∩ Ω))) (a : DerivIndex n k) :
    ⇑((relativeCutoffCLM hV hΩ ψ hψ U).val a)
      =ᵐ[domainMeasure n Ω]
        weakLeibnizExpansion ψ.toFun (wkpWordRepresentative U) a.toList.reverse :=
  interCutoff_coordinate_ae hV hΩ ψ hψ U a

/-- The relative operator preserves the finer input-dependent estimate on each
Leibniz row. -/
theorem norm_relativeCutoffCLM_coordinate_le
    {V Ω : Set (ℝ^n)} (hV : IsOpen V) (hΩ : IsOpen Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψ : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}((V ∩ Ω))) (a : DerivIndex n k) :
    ‖(relativeCutoffCLM hV hΩ ψ hψ U).val a‖ ≤
      (cutoffLeibnizENormBound U ψ a.toList.reverse).toReal :=
  norm_interCutoff_coordinate_le hV hΩ ψ hψ U a

/-- At exponent two and positive order, the general relative operator agrees
with the Hilbert-space operator `interCutoffCLM`. -/
theorem relativeCutoffCLM_eq_interCutoffCLM
    {V Ω : Set (ℝ^n)} (hk : 0 < k) (hV : IsOpen V) (hΩ : IsOpen Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψ : tsupport ψ.toFun ⊆ V) :
    relativeCutoffCLM (k := k) (p := 2) hV hΩ ψ hψ =
      interCutoffCLM hk hV hΩ ψ hψ := by
  ext U
  rfl

end SobolevSpace.Extension.HigherOrder
