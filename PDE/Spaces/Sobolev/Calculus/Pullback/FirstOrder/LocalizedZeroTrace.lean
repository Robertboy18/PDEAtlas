/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.GraphOperator
public import PDE.Spaces.Sobolev.Boundary.Geometry.HalfSpace
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.ExtensionByZero
public import PDE.Spaces.Sobolev.Localization.Cutoff.ExtensionCoordinates
import PDE.Spaces.Sobolev.Approximation.ZeroTrace.HalfSpace

/-!
# Localized zero-trace pullback to a half-space

Extend a zero-trace Sobolev function by zero, pull it back through the full
chart, and multiply by a cutoff supported inside the chart target. This
produces a global `H¹` function. For a boundary-flattening chart it vanishes
below the flat boundary, so its restriction belongs to `H¹₀` on the
upper half-space.

The cutoff may be chosen independently of a partition of unity. This is useful
when a local equation needs a larger solution cutoff than its test functions.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped Distributions Sobolev

namespace SobolevSpace.WeakChangeOfVariables

open MeasureTheory Set GraphSpace
open CompactSupportLocalization.HigherOrderLocalizedCutoff
open scoped ENNReal

variable {n : ℕ} {Ω : Set (ℝ^n)} {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}

/-- Pull back the global zero extension of an `H¹₀` function to the full chart target. -/
def zeroExtendedPullbackCLM (hΩ : MeasurableSet Ω)
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hTarget : Bornology.IsBounded E.target) :
    H¹₀(Ω) →L[ℝ] H¹(E.target) :=
  (boundedW1pPullbackCLM (E := E.symm) hSymm hE
    (isBounded_source_of_isBounded_target hSymm.continuous hTarget)).comp
      ((restrictCLM E.open_source.measurableSet (subset_univ E.source)).comp
        (ZeroTrace.zeroExtendH10 hΩ))

/-- The pullback represents composition of the literal zero extension with the inverse chart. -/
theorem zeroExtendedPullbackCLM_base_ae (hΩ : MeasurableSet Ω)
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hTarget : Bornology.IsBounded E.target) (u : H¹₀(Ω)) :
    baseRepresentative (zeroExtendedPullbackCLM hΩ hE hSymm hTarget u)
      =ᵐ[domainMeasure n E.target]
        fun y ↦ Ω.indicator (baseCoordCLM u : ℝ^n → ℝ) (E.symm y) := by
  let U := ZeroTrace.zeroExtendH10 hΩ u
  let V := restrictCLM E.open_source.measurableSet (subset_univ E.source) U
  have hV := restrictCLM_apply_ae E.open_source.measurableSet
    (subset_univ E.source) U (baseIndex n 1)
  have hU := (ZeroTrace.zeroExtendH10_coordinate_apply_ae hΩ u (baseIndex n 1)).filter_mono
    (ae_mono (Measure.restrict_le_self : domainMeasure n E.source ≤ volume))
  have hinput : baseRepresentative V =ᵐ[domainMeasure n E.source]
      Ω.indicator (baseCoordCLM u : ℝ^n → ℝ) := hV.trans hU
  have hq := quasiMeasurePreserving_partialHomeomorph (E := E.symm) hSymm hE
  exact (boundedW1pPullbackCLM_base_ae (E := E.symm) hSymm hE
    (isBounded_source_of_isBounded_target hSymm.continuous hTarget) V).trans
      (hq.ae_eq_comp hinput)

/-- The full-chart pullback differentiates the literal zero extension by the
inverse-chart chain rule. -/
theorem zeroExtendedPullbackCLM_derivative_ae (hΩ : MeasurableSet Ω)
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hTarget : Bornology.IsBounded E.target) (u : H¹₀(Ω)) (i : Fin n) :
    ⇑((zeroExtendedPullbackCLM hΩ hE hSymm hTarget u).val (singleDerivIndex n i))
      =ᵐ[domainMeasure n E.target] fun y ↦ ∑ j : Fin n,
        Ω.indicator (derivCoordCLM j u : ℝ^n → ℝ) (E.symm y) *
          (∂[i] (fun z ↦ E.symm z)) y j := by
  let U := ZeroTrace.zeroExtendH10 hΩ u
  let V := restrictCLM E.open_source.measurableSet (subset_univ E.source) U
  have hinput (j : Fin n) : ⇑(V.val (singleDerivIndex n j))
      =ᵐ[domainMeasure n E.source] Ω.indicator (derivCoordCLM j u : ℝ^n → ℝ) :=
    (restrictCLM_apply_ae E.open_source.measurableSet
      (subset_univ E.source) U (singleDerivIndex n j)).trans
      ((ZeroTrace.zeroExtendH10_coordinate_apply_ae hΩ u (singleDerivIndex n j)).filter_mono
        (ae_mono (Measure.restrict_le_self : domainMeasure n E.source ≤ volume)))
  have hq := quasiMeasurePreserving_partialHomeomorph (E := E.symm) hSymm hE
  filter_upwards [boundedW1pPullbackCLM_derivative_ae (E := E.symm) hSymm hE
    (isBounded_source_of_isBounded_target hSymm.continuous hTarget) V i,
    ae_all_iff.mpr (fun j ↦ hq.ae_eq_comp (hinput j))] with y hy hc
  exact hy.trans (Finset.sum_congr rfl fun j _ ↦
    congrArg (fun t : ℝ ↦
      t * (fderiv ℝ (fun z ↦ E.symm z) y (EuclideanSpace.single i 1)) j) (hc j))

/-- Localizing the chart pullback extends it to a global `H¹` function. -/
def localizedZeroExtendedPullbackCLM (hΩ : MeasurableSet Ω)
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hTarget : Bornology.IsBounded E.target)
    (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hκ : tsupport κ.toFun ⊆ E.target) :
    H¹₀(Ω) →L[ℝ] H¹(ℝ^n) :=
  (extendByCutoffCLM (by norm_num) E.open_target isOpen_univ
    (subset_univ E.target) κ hκ).comp
      (zeroExtendedPullbackCLM hΩ hE hSymm hTarget)

/-- The localized pullback has its literal cutoff-composition representative on the whole space. -/
theorem localizedZeroExtendedPullbackCLM_base_ae (hΩ : MeasurableSet Ω)
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hTarget : Bornology.IsBounded E.target)
    (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hκ : tsupport κ.toFun ⊆ E.target)
    (u : H¹₀(Ω)) :
    baseRepresentative (localizedZeroExtendedPullbackCLM hΩ hE hSymm hTarget κ hκ u)
      =ᵐ[volume] fun y ↦ κ.toFun y *
        Ω.indicator (baseCoordCLM u : ℝ^n → ℝ) (E.symm y) := by
  let V := zeroExtendedPullbackCLM hΩ hE hSymm hTarget u
  have hext := extendByCutoff_base_ae E.open_target (subset_univ E.target) κ hκ V
  have hcomp := (ae_restrict_iff' E.open_target.measurableSet).mp
    (zeroExtendedPullbackCLM_base_ae hΩ hE hSymm hTarget u)
  simp only [domainMeasure, Measure.restrict_univ] at hext
  filter_upwards [hext, hcomp] with y hy hc
  change baseRepresentative (extendByCutoff E.open_target (subset_univ E.target) κ hκ V) y = _
  rw [hy]
  by_cases hzero : κ.toFun y = 0
  · simp only [hzero, zero_mul]
  · rw [hc (hκ (subset_tsupport κ.toFun hzero))]

/-- On the core of the solution cutoff, the localized global field retains
the full inverse-chart derivative formula. -/
theorem localizedZeroExtendedPullbackCLM_derivative_ae_on_core (hΩ : MeasurableSet Ω)
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hTarget : Bornology.IsBounded E.target)
    (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hκ : tsupport κ.toFun ⊆ E.target)
    (u : H¹₀(Ω)) (i : Fin n) {K : Set (ℝ^n)}
    (hcore : ∀ y ∈ K, κ.toFun =ᶠ[nhds y] 1) :
    ∀ᵐ y ∂volume, y ∈ K →
      (localizedZeroExtendedPullbackCLM hΩ hE hSymm hTarget κ hκ u).val
        (singleDerivIndex n i) y =
      ∑ j : Fin n, Ω.indicator (derivCoordCLM j u : ℝ^n → ℝ) (E.symm y) *
        (∂[i] (fun z ↦ E.symm z)) y j := by
  let V := zeroExtendedPullbackCLM hΩ hE hSymm hTarget u
  have hext := extendByCutoff_derivative_ae_on_core E.open_target
    (subset_univ E.target) κ hκ V i hcore
  have hcomp := (ae_restrict_iff' E.open_target.measurableSet).mp
    (zeroExtendedPullbackCLM_derivative_ae hΩ hE hSymm hTarget u i)
  simp only [domainMeasure, Measure.restrict_univ] at hext
  filter_upwards [hext, hcomp] with y hy hc hyK
  have hyt : y ∈ E.target := hκ (subset_tsupport κ.toFun (by
    change κ.toFun y ≠ 0
    rw [(hcore y hyK).eq_of_nhds]; norm_num))
  exact (hy hyK).trans (hc hyt)

variable [Fact (0 < n)]

/-- The localized full-chart pullback vanishes below the flat boundary. -/
theorem localizedZeroExtendedPullbackCLM_zero_below (hΩ : MeasurableSet Ω)
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hTarget : Bornology.IsBounded E.target)
    (hflat : ∀ x ∈ E.source, x ∈ Ω ↔ E x ∈ HalfSpace.upper n)
    (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hκ : tsupport κ.toFun ⊆ E.target)
    (u : H¹₀(Ω)) :
    ∀ᵐ y ∂volume, y (PDE.Common.lastIndex (n := n)) ≤ 0 →
      baseRepresentative (localizedZeroExtendedPullbackCLM hΩ hE hSymm hTarget κ hκ u) y =
        0 := by
  filter_upwards [localizedZeroExtendedPullbackCLM_base_ae hΩ hE hSymm hTarget κ hκ u]
    with y hy hlast
  rw [hy]
  by_cases hzero : κ.toFun y = 0
  · simp only [hzero, zero_mul]
  have hyt : y ∈ E.target := hκ (subset_tsupport κ.toFun hzero)
  have hout : E.symm y ∉ Ω := by
    intro hin
    have hupper := (hflat (E.symm y) (E.map_target hyt)).mp hin
    rw [E.right_inv hyt] at hupper
    exact (not_lt_of_ge hlast) hupper
  rw [indicator_of_notMem hout, mul_zero]

/-- Restriction of the localized pullback belongs to the half-space zero-trace closure. -/
theorem localizedZeroExtendedPullbackCLM_mem_H10 (hΩ : MeasurableSet Ω)
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hTarget : Bornology.IsBounded E.target)
    (hflat : ∀ x ∈ E.source, x ∈ Ω ↔ E x ∈ HalfSpace.upper n)
    (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hκ : tsupport κ.toFun ⊆ E.target)
    (u : H¹₀(Ω)) :
    restrictCLM (HalfSpace.measurableSet_upper n) (subset_univ (HalfSpace.upper n))
        (localizedZeroExtendedPullbackCLM hΩ hE hSymm hTarget κ hκ u) ∈
      (h10SubmoduleOn (n := n) (Ω := HalfSpace.upper n)).toSubmodule :=
  HalfSpace.restrict_mem_Wkp0_of_zero_below (by norm_num) _
    (localizedZeroExtendedPullbackCLM_zero_below hΩ hE hSymm hTarget hflat κ hκ u)

/-- A boundary-flattening chart and an arbitrary compact target cutoff induce a
continuous linear map from `H¹₀(Ω)` to half-space `H¹₀`. -/
def localizedHalfSpacePullbackCLM (hΩ : MeasurableSet Ω)
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hTarget : Bornology.IsBounded E.target)
    (hflat : ∀ x ∈ E.source, x ∈ Ω ↔ E x ∈ HalfSpace.upper n)
    (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hκ : tsupport κ.toFun ⊆ E.target) :
    H¹₀(Ω) →L[ℝ] H¹₀(HalfSpace.upper n) :=
  ((restrictCLM (HalfSpace.measurableSet_upper n) (subset_univ (HalfSpace.upper n))).comp
    (localizedZeroExtendedPullbackCLM hΩ hE hSymm hTarget κ hκ)).codRestrict
      (h10SubmoduleOn (n := n) (Ω := HalfSpace.upper n)).toSubmodule
      (localizedZeroExtendedPullbackCLM_mem_H10 hΩ hE hSymm hTarget hflat κ hκ)

/-- The half-space map represents the expected cutoff and inverse-chart composition. -/
theorem localizedHalfSpacePullbackCLM_base_ae (hΩ : MeasurableSet Ω)
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hTarget : Bornology.IsBounded E.target)
    (hflat : ∀ x ∈ E.source, x ∈ Ω ↔ E x ∈ HalfSpace.upper n)
    (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hκ : tsupport κ.toFun ⊆ E.target)
    (u : H¹₀(Ω)) :
    ⇑(baseCoordCLM (localizedHalfSpacePullbackCLM hΩ hE hSymm hTarget hflat κ hκ u))
      =ᵐ[domainMeasure n (HalfSpace.upper n)] fun y ↦
        κ.toFun y * Ω.indicator (baseCoordCLM u : ℝ^n → ℝ) (E.symm y) := by
  have hr := restrictCLM_apply_ae (HalfSpace.measurableSet_upper n)
    (subset_univ (HalfSpace.upper n))
    (localizedZeroExtendedPullbackCLM hΩ hE hSymm hTarget κ hκ u) (baseIndex n 1)
  exact hr.trans
    ((localizedZeroExtendedPullbackCLM_base_ae hΩ hE hSymm hTarget κ hκ u).filter_mono
      (ae_mono Measure.restrict_le_self))

/-- On the solution-cutoff core in the upper half-space, the zero-extension
indicator disappears and the derivative is the inverse-chart gradient. -/
theorem localizedHalfSpacePullbackCLM_derivative_ae_on_core (hΩ : MeasurableSet Ω)
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hTarget : Bornology.IsBounded E.target)
    (hflat : ∀ x ∈ E.source, x ∈ Ω ↔ E x ∈ HalfSpace.upper n)
    (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hκ : tsupport κ.toFun ⊆ E.target)
    (u : H¹₀(Ω)) (i : Fin n) {K : Set (ℝ^n)}
    (hcore : ∀ y ∈ K, κ.toFun =ᶠ[nhds y] 1) :
    ∀ᵐ y ∂domainMeasure n (HalfSpace.upper n), y ∈ K →
      derivCoordCLM i (localizedHalfSpacePullbackCLM hΩ hE hSymm hTarget hflat κ hκ u) y =
      ∑ j : Fin n, derivCoordCLM j u (E.symm y) *
        (∂[i] (fun z ↦ E.symm z)) y j := by
  have hr := restrictCLM_apply_ae (HalfSpace.measurableSet_upper n)
    (subset_univ (HalfSpace.upper n))
    (localizedZeroExtendedPullbackCLM hΩ hE hSymm hTarget κ hκ u) (singleDerivIndex n i)
  have hc := (localizedZeroExtendedPullbackCLM_derivative_ae_on_core
    hΩ hE hSymm hTarget κ hκ u i hcore).filter_mono
      (ae_mono (Measure.restrict_le_self : domainMeasure n (HalfSpace.upper n) ≤ volume))
  filter_upwards [hr, hc, ae_restrict_mem (HalfSpace.measurableSet_upper n)]
    with y hy hc hyupper hyK
  have hyt : y ∈ E.target := hκ (subset_tsupport κ.toFun (by
    change κ.toFun y ≠ 0
    rw [(hcore y hyK).eq_of_nhds]; norm_num))
  have hyΩ : E.symm y ∈ Ω := (hflat _ (E.map_target hyt)).mpr (by
    rw [E.right_inv hyt]; exact hyupper)
  exact hy.trans ((hc hyK).trans (by simp only [indicator_of_mem hyΩ]))

end SobolevSpace.WeakChangeOfVariables
