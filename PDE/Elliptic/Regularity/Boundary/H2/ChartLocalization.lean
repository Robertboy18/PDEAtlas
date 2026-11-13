/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.H2.ReflectedPullback
public import PDE.Spaces.Sobolev.Boundary.Atlas.Definitions
public import PDE.Spaces.Sobolev.Extension.Pullback.HigherOrderOperator

/-!
# Returning a localized half-space representative to the physical domain

Odd reflection extends an `H² ∩ H¹₀` field across the flat boundary.
A bounded C² pullback then gives the physical cutoff piece. The target
cutoff need only equal one on the image of the physical cutoff support.
No differential equation enters this geometric step.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped Distributions Sobolev

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set SobolevSpace.WeakChangeOfVariables
open scoped ENNReal

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- A half-space `H² ∩ H¹₀` representative of a target localization yields
an `H²(Ω)` representative of the corresponding physical cutoff. -/
theorem exists_H2_chartLocalization
    (hΩ : SobolevSpace.Boundary.C1ExtensionAtlas n Ω) (a : Fin hΩ.N)
    (hE : ContDiff ℝ 2 (fun x ↦ hΩ.chart a x))
    (ψ η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hψ : tsupport ψ.toFun ⊆ (hΩ.chart a).source)
    (hη : ∀ y ∈ (hΩ.chart a) '' tsupport ψ.toFun, η.toFun y = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ^n → ℝ)
    (U : W^{2,2}(HalfSpace.upper n)),
    lowerOrderCLM (k := 1) (m := 2) (by omega) U ∈
      (h10SubmoduleOn (n := n) (Ω := HalfSpace.upper n)).toSubmodule →
    (U.val (baseIndex n 2) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (HalfSpace.upper n)]
        (fun y ↦ η.toFun y * u ((hΩ.chart a).symm y)) →
    ∃ W : W^{2,2}(Ω),
      (baseRepresentative W =ᵐ[domainMeasure n Ω] fun x ↦ ψ.toFun x * u x) ∧
      ‖W‖ ≤ C * ‖U‖ := by
  let E := hΩ.chart a
  have hSource : Bornology.IsBounded E.source :=
    ((hΩ.chart_target_bounded a).isCompact_closure.image
      (hΩ.chart_symm_contDiff a).continuous).isBounded.subset
        fun x hx ↦ ⟨E x, subset_closure (E.map_source hx), E.left_inv hx⟩
  let T := restrictCLM (k := 2) (p := 2) E.open_target.measurableSet
    (subset_univ E.target)
  let P := higherOrderPullbackCLM (by norm_num : 0 < 2) hE
    (hΩ.chart_symm_contDiff a) hSource (hΩ.chart_target_bounded a)
  let X := CompactSupportLocalization.HigherOrderLocalizedCutoff.extendByCutoffCLM
    (by norm_num : 0 < 2) E.open_source isOpen_univ (subset_univ E.source) ψ hψ
  let S := restrictCLM (k := 2) (p := 2) hΩ.isOpen.measurableSet (subset_univ Ω)
  let B := S.comp (X.comp (P.comp T))
  refine ⟨‖B‖ * Real.sqrt 2, by positivity, fun u U htrace hbase ↦ ?_⟩
  let R := HigherOrderReflection.oddReflectionH2 (n := n) ⟨U, htrace⟩
  have hR : (R.val (baseIndex n 2) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (HalfSpace.upper n)]
        fun y ↦ η.toFun y * u (E.symm y) := by
    have hr := restrictCLM_apply_ae (k := 2) (p := 2)
      (HalfSpace.measurableSet_upper n) (subset_univ (HalfSpace.upper n))
      R (baseIndex n 2)
    rw [HigherOrderReflection.restrict_oddReflectionH2] at hr
    exact hr.symm.trans hbase
  let G := X (P (T R))
  have hP : (wkpBaseCoordinateCLM (P (T R)) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n E.source] fun x ↦ R.val (baseIndex n 2) (E x) := by
    have hT := restrictCLM_apply_ae (k := 2) (p := 2) E.open_target.measurableSet
      (subset_univ E.target) R (baseIndex n 2)
    exact (higherOrderPullbackCLM_base_ae (by norm_num : 0 < 2) hE
      (hΩ.chart_symm_contDiff a) hSource (hΩ.chart_target_bounded a) (T R)).trans
      ((quasiMeasurePreserving_partialHomeomorph
        (hΩ.chart_contDiff a) (hΩ.chart_symm_contDiff a)).ae_eq_comp hT)
  have hG : (G.val (baseIndex n 2) : ℝ^n → ℝ) =ᵐ[domainMeasure n univ]
      fun x ↦ ψ.toFun x * R.val (baseIndex n 2) (E x) := by
    have hX := CompactSupportLocalization.HigherOrderLocalizedCutoff.extendByCutoff_base_ae
      (p := 2) E.open_source (subset_univ E.source) ψ hψ (P (T R))
    filter_upwards [hX, ae_restrict_of_ae ((ae_restrict_iff' E.open_source.measurableSet).mp hP)]
      with x hx hp
    change G.val (baseIndex n 2) x =
      ψ.toFun x * wkpBaseCoordinateCLM (P (T R)) x at hx
    change G.val (baseIndex n 2) x = _
    rw [hx]
    by_cases hzero : ψ.toFun x = 0
    · simp only [hzero, zero_mul]
    · rw [hp (hψ (subset_tsupport ψ.toFun hzero))]
  let W := restrictCLM (k := 2) (p := 2) hΩ.isOpen.measurableSet (subset_univ Ω) G
  have hW := restrictCLM_apply_ae (k := 2) (p := 2)
    hΩ.isOpen.measurableSet (subset_univ Ω) G (baseIndex n 2)
  let EΩ := SobolevSpace.Boundary.C1ExtensionAtlas.Charts.chartOnΩ (Ω := Ω) a
  have hupper : EΩ.target ⊆ HalfSpace.upper n :=
    SobolevSpace.Boundary.C1ExtensionAtlas.Charts.chartOnΩ_target_subset_upper a
  have hcomp := (quasiMeasurePreserving_partialHomeomorph (E := EΩ)
    (hΩ.chart_contDiff a) (hΩ.chart_symm_contDiff a)).ae_eq_comp
      (ae_restrict_of_ae_restrict_of_subset hupper hR)
  have hsource : ∀ᵐ x ∂domainMeasure n EΩ.source,
      R.val (baseIndex n 2) (E x) = η.toFun (E x) * u x := by
    filter_upwards [hcomp, ae_restrict_mem EΩ.open_source.measurableSet] with x hx hxS
    change R.val (baseIndex n 2) (E x) = η.toFun (E x) * u (E.symm (E x)) at hx
    exact hx.trans (congrArg (η.toFun (E x) * ·) (congrArg u (E.left_inv hxS.1)))
  have hnorm : ‖W‖ ≤ (‖B‖ * Real.sqrt 2) * ‖U‖ := (B.le_opNorm R).trans_eq
    (by rw [HigherOrderReflection.norm_oddReflectionH2, mul_assoc]; rfl)
  refine ⟨W, ?_, hnorm⟩
  filter_upwards [hW, ae_restrict_of_ae_restrict_of_subset (subset_univ Ω) hG,
    ae_restrict_of_ae ((ae_restrict_iff' EΩ.open_source.measurableSet).mp hsource),
    ae_restrict_mem hΩ.isOpen.measurableSet] with x hxW hxG hxS hxΩ
  change W.val (baseIndex n 2) x = ψ.toFun x * u x
  rw [hxW, hxG]
  by_cases hxψ : ψ.toFun x = 0
  · simp only [hxψ, zero_mul]
  · have hxSupport := subset_tsupport ψ.toFun hxψ
    rw [hxS ⟨hψ hxSupport, hxΩ⟩, hη (E x) ⟨x, hxSupport, rfl⟩, one_mul]

end SobolevSpace.GraphSpace.BoundaryRegularity
