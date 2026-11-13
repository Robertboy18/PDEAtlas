/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.C1.LocalPieces.ChartPullback
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Cutoff
import PDE.Spaces.Sobolev.Localization.Cutoff.CompactSupport

/-!
# Banach chart operator for C¹ extension

The last step of the boundary construction in the extension theorem (Evans §5.4,
Theorem 1) pulls the reflected function on the flattened picture back through
the chart `Φᵢ` to a function on `ℝ^n`. We build that step as a bounded
operator

  `preparedChartCLM i : W^{1,p}(Φᵢ.target) → W^{1,p}(ℝ^n)`

on graph-space elements.  The input is first multiplied by the target cutoff
`η`, equal to one on the flattened support and compactly supported in the chart
target, so that the pullback `x ↦ (η v)(Φᵢ x)` vanishes outside the compact set
`pullbackSupport i ⊆ Φᵢ.source` and extends by zero to `ℝ^n`.  Its derivative
coordinates are the chain-rule sums `∑ⱼ (∂ⱼ(ηv))(Φᵢ x) · ∂ₖ(Φᵢ)ⱼ(x)` built from
the coordinate maps of `LocalPieces.ChartPullback`.  The weak-derivative
identities on `ℝ^n` follow from the weak chain rule on the chart source and a
cutoff argument on the compact support.

## Main definitions and results

* `targetCutoffCLM i`: multiplication by `η` on `W^{1,p}(Φᵢ.target)`.
* `localizedChartAmbient i`, `preparedChartAmbient i`: the coordinatewise
  pullback on the ambient bundle, before and after the cutoff, with their
  `_apply` lemmas.
* `preparedChartBaseRepresentative`, `preparedChartAmbient_base_apply_ae`: the
  pointwise representative `𝟙_L · (𝟙_K (ηv)) ∘ Φᵢ` of the base coordinate.
* `preparedChartAmbient_mapsIsWkpOn`: the output satisfies all first-order
  weak-derivative constraints on `ℝ^n`.
* `preparedChartCLM i`: the resulting bounded operator, with
  `preparedChartCLM_apply_coe`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.4, Theorem 1, pp. 268-271; the return to the original
  variables is in step 5, p. 270.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv)

open scoped Sobolev

noncomputable section

namespace SobolevSpace

open Set
open scoped ENNReal Topology

namespace Extension

namespace C1

variable {n : ℕ} {p : ℝ≥0∞} {Ω : Set (ℝ^n)}

open MeasureTheory
open CompactSupportLocalization

namespace BoundaryPiece

variable [Fact (0 < n)] [Fact (1 ≤ p)] [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- Extract all canonical first-derivative coordinates from a Banach
`W^{1,p}` ambient bundle. -/
noncomputable def chartFirstDerivativesLp (i : Fin hΩ.N) :
    SobolevSpace.GraphSpace.WkpAmbientOn n 1 p (hΩ.chart i).target →L[ℝ]
      (Fin n → SobolevSpace.GraphSpace.DerivLp n p (hΩ.chart i).target) := by
  classical
  exact ContinuousLinearMap.pi fun j ↦
    PiLp.proj (𝕜 := ℝ) (p := p)
      (β := fun _ : SobolevSpace.GraphSpace.DerivIndex n 1 ↦
        SobolevSpace.GraphSpace.DerivLp n p (hΩ.chart i).target)
      (SobolevSpace.GraphSpace.singleDerivIndex n j)

/-- One output coordinate of the localized chart map. -/
noncomputable def localizedChartLpAt
    (i : Fin hΩ.N) (a : SobolevSpace.GraphSpace.DerivIndex n 1) :
    SobolevSpace.GraphSpace.WkpAmbientOn n 1 p (hΩ.chart i).target →L[ℝ]
      SobolevSpace.GraphSpace.DerivLp n p (Set.univ : Set (ℝ^n)) :=
  SobolevSpace.GraphSpace.firstOrderRows
    ((localizedChartPullbackLp (n := n) (p := p) (Ω := Ω) i).comp
      (PiLp.proj (𝕜 := ℝ) (p := p)
        (β := fun _ : SobolevSpace.GraphSpace.DerivIndex n 1 ↦
          SobolevSpace.GraphSpace.DerivLp n p (hΩ.chart i).target)
        (SobolevSpace.GraphSpace.baseIndex n 1)))
    (fun k ↦
      (localizedChartDerivativeLp (n := n) (p := p) (Ω := Ω) i k).comp
        (chartFirstDerivativesLp (n := n) (p := p) (Ω := Ω) i))
    a

/-- Localized chart pullback on the complete Banach `W^{1,p}` ambient
derivative bundle. -/
noncomputable def localizedChartAmbient (i : Fin hΩ.N) :
    SobolevSpace.GraphSpace.WkpAmbientOn n 1 p (hΩ.chart i).target →L[ℝ]
      SobolevSpace.GraphSpace.WkpAmbientOn n 1 p (Set.univ : Set (ℝ^n)) := by
  classical
  let eUniv := PiLp.continuousLinearEquiv (𝕜 := ℝ) (p := p)
    (β := fun _ : SobolevSpace.GraphSpace.DerivIndex n 1 ↦
      SobolevSpace.GraphSpace.DerivLp n p (Set.univ : Set (ℝ^n)))
  exact eUniv.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun a ↦
      localizedChartLpAt (n := n) (p := p) (Ω := Ω) i a)

/-- Each coordinate of `localizedChartAmbient i U` is the corresponding
localized chart coordinate map applied to `U`. -/
@[simp] theorem localizedChartAmbient_apply
    (i : Fin hΩ.N)
    (U : SobolevSpace.GraphSpace.WkpAmbientOn n 1 p (hΩ.chart i).target)
    (a : SobolevSpace.GraphSpace.DerivIndex n 1) :
    localizedChartAmbient (n := n) (p := p) (Ω := Ω) i U a =
      localizedChartLpAt (n := n) (p := p) (Ω := Ω) i a U := by
  classical
  simp [localizedChartAmbient]

/-- The target cutoff used before chart pullback, as a bounded endomorphism
of Sobolev graph-space `W^{1,p}`. -/
noncomputable def targetCutoffCLM (i : Fin hΩ.N) :
    W^{1,p}((hΩ.chart i).target) →L[ℝ]
      W^{1,p}((hΩ.chart i).target) :=
  SobolevSpace.GraphSpace.cutoffCLM
    (n := n) (p := p) (Ω := (hΩ.chart i).target)
    (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff (n := n) (Ω := Ω) i)

/-- Prepare a chart Sobolev field with the smooth target cutoff and apply all
localized base/derivative coordinate maps.  The next theorem proves that this
ambient result lies in global `W^{1,p}`. -/
noncomputable def preparedChartAmbient (i : Fin hΩ.N) :
    W^{1,p}((hΩ.chart i).target) →L[ℝ]
      SobolevSpace.GraphSpace.WkpAmbientOn n 1 p (Set.univ : Set (ℝ^n)) :=
  (localizedChartAmbient (n := n) (p := p) (Ω := Ω) i).comp
    ((Submodule.subtypeL
      (SobolevSpace.GraphSpace.wkpSubmoduleOn n 1 p (hΩ.chart i).target)).comp
      (targetCutoffCLM (n := n) (p := p) (Ω := Ω) i))

/-- Each coordinate of `preparedChartAmbient i U` is the localized chart
coordinate map applied to the cutoff field `η U`. -/
@[simp] theorem preparedChartAmbient_apply
    (i : Fin hΩ.N)
    (U : W^{1,p}((hΩ.chart i).target))
    (a : SobolevSpace.GraphSpace.DerivIndex n 1) :
    preparedChartAmbient (n := n) (p := p) (Ω := Ω) i U a =
      localizedChartLpAt (n := n) (p := p) (Ω := Ω) i a
        ((targetCutoffCLM (n := n) (p := p) (Ω := Ω) i U :
          W^{1,p}((hΩ.chart i).target)) :
          SobolevSpace.GraphSpace.WkpAmbientOn n 1 p (hΩ.chart i).target) := by
  rfl

/-- Pointwise representative of the prepared global chart base coordinate. -/
def preparedChartBaseRepresentative
    (i : Fin hΩ.N)
    (U : W^{1,p}((hΩ.chart i).target)) : ℝ^n → ℝ :=
  let V := targetCutoffCLM (n := n) (p := p) (Ω := Ω) i U
  let K := Boundary.C1ExtensionAtlas.DerivedCutoffs.targetCutoffSupport (n := n) (Ω := Ω) i
  let L := Boundary.C1ExtensionAtlas.DerivedCutoffs.pullbackSupport (n := n) (Ω := Ω) i
  L.indicator fun x ↦
    K.indicator (SobolevSpace.GraphSpace.baseRepresentative V) (hΩ.chart i x)

/-- Pointwise representative of the prepared global chart derivative
coordinate. -/
private def preparedChartDerivativeRepresentative
    (i : Fin hΩ.N)
    (U : W^{1,p}((hΩ.chart i).target))
    (k : Fin n) : ℝ^n → ℝ :=
  let V := targetCutoffCLM (n := n) (p := p) (Ω := Ω) i U
  let K := Boundary.C1ExtensionAtlas.DerivedCutoffs.targetCutoffSupport (n := n) (Ω := Ω) i
  let L := Boundary.C1ExtensionAtlas.DerivedCutoffs.pullbackSupport (n := n) (Ω := Ω) i
  L.indicator fun x ↦ ∑ j : Fin n,
    chartJacobianCoefficient (n := n) (Ω := Ω) i k j x *
      K.indicator
        (fun y ↦
          ((V : SobolevSpace.GraphSpace.WkpAmbientOn n 1 p (hΩ.chart i).target)
            (SobolevSpace.GraphSpace.singleDerivIndex n j) y))
        (hΩ.chart i x)

private theorem support_preparedChartBaseRepresentative_subset
    (i : Fin hΩ.N)
    (U : W^{1,p}((hΩ.chart i).target)) :
    Function.support
        (preparedChartBaseRepresentative (n := n) (p := p) (Ω := Ω) i U) ⊆
      Boundary.C1ExtensionAtlas.DerivedCutoffs.pullbackSupport (n := n) (Ω := Ω) i := by
  intro x hx
  by_contra hxL
  exact hx (by simp [preparedChartBaseRepresentative, hxL])

private theorem support_preparedChartDerivativeRepresentative_subset
    (i : Fin hΩ.N)
    (U : W^{1,p}((hΩ.chart i).target))
    (k : Fin n) :
    Function.support
        (preparedChartDerivativeRepresentative
          (n := n) (p := p) (Ω := Ω) i U k) ⊆
      Boundary.C1ExtensionAtlas.DerivedCutoffs.pullbackSupport (n := n) (Ω := Ω) i := by
  intro x hx
  by_contra hxL
  exact hx (by simp [preparedChartDerivativeRepresentative, hxL])

private theorem preparedChart_hasWeakDerivative
    (i : Fin hΩ.N)
    (U : W^{1,p}((hΩ.chart i).target))
    (k : Fin n) :
    HasWeakDerivativeOn (n := n) (Set.univ : Set (ℝ^n)) [k]
      (preparedChartBaseRepresentative (n := n) (p := p) (Ω := Ω) i U)
      (preparedChartDerivativeRepresentative
        (n := n) (p := p) (Ω := Ω) i U k) := by
  classical
  let E := hΩ.chart i
  let K := Boundary.C1ExtensionAtlas.DerivedCutoffs.targetCutoffSupport (n := n) (Ω := Ω) i
  let L := Boundary.C1ExtensionAtlas.DerivedCutoffs.pullbackSupport (n := n) (Ω := Ω) i
  let V := targetCutoffCLM (n := n) (p := p) (Ω := Ω) i U
  let base : ℝ^n → ℝ :=
    SobolevSpace.GraphSpace.baseRepresentative V
  let deriv : Fin n → ℝ^n → ℝ := fun j ↦
    (V : SobolevSpace.GraphSpace.WkpAmbientOn n 1 p E.target)
      (SobolevSpace.GraphSpace.singleDerivIndex n j)
  have hbaseLp : MeasureTheory.MemLp base p (domainMeasure n E.target) := Lp.memLp _
  have hderivLp (j : Fin n) : MeasureTheory.MemLp (deriv j) p (domainMeasure n E.target) :=
    Lp.memLp _
  have hweakTarget (j : Fin n) : HasWeakDerivativeOn (n := n) E.target [j] base (deriv j) := by
    simpa [E, V, base, deriv, SobolevSpace.GraphSpace.baseRepresentative,
      SobolevSpace.GraphSpace.singleDerivIndex_toList] using
      V.property (SobolevSpace.GraphSpace.singleDerivIndex n j)
  -- the weak chain rule through the chart
  have hchain :=
    SobolevSpace.WeakChangeOfVariables.hasWeakDerivativeOn_comp_partialHomeomorph_W1_of_memLp
      (n := n) (p := p) (SobolevSpace.Approximation.standardMollifier n)
      (E := E) (by simpa [E] using hΩ.chart_contDiff i)
      (by simpa [E] using hΩ.chart_symm_contDiff i)
      (hΩ.chart_target_bounded i).measure_lt_top.ne hbaseLp hderivLp hweakTarget k
  let rawBase : ℝ^n → ℝ := fun x ↦ base (E x)
  let rawDerivative : ℝ^n → ℝ := fun x ↦ ∑ j : Fin n,
    deriv j (E x) * chartJacobianCoefficient (n := n) (Ω := Ω) i k j x
  have hchain' : HasWeakDerivativeOn (n := n) E.source [k]
      rawBase rawDerivative := by
    simpa [E, rawBase, rawDerivative, chartJacobianCoefficient, partialDeriv] using hchain
  have hqmp :
      MeasureTheory.QuasiMeasurePreserving (fun x ↦ E x)
        (domainMeasure n E.source) (domainMeasure n E.target) :=
    SobolevSpace.WeakChangeOfVariables.quasiMeasurePreserving_partialHomeomorph
      (n := n) (E := E) (by simpa [E] using hΩ.chart_contDiff i)
      (by simpa [E] using hΩ.chart_symm_contDiff i)
  have hbaseIndicator : K.indicator base =ᵐ[domainMeasure n E.target] base := by
    simpa [E, K, V, base, SobolevSpace.GraphSpace.baseRepresentative,
      targetCutoffCLM,
      Boundary.C1ExtensionAtlas.DerivedCutoffs.targetCutoffSupport] using
      SobolevSpace.GraphSpace.cutoffCLM_base_tsupport_indicator_ae
        (n := n) (p := p) (Ω := (hΩ.chart i).target)
        (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff (n := n) (Ω := Ω) i) U
  have hderivIndicator (j : Fin n) :
      K.indicator (deriv j) =ᵐ[domainMeasure n E.target] deriv j := by
    simpa [E, K, V, deriv, targetCutoffCLM,
      Boundary.C1ExtensionAtlas.DerivedCutoffs.targetCutoffSupport] using
      SobolevSpace.GraphSpace.cutoffCLM_singleDeriv_tsupport_indicator_ae
        (n := n) (p := p) (Ω := (hΩ.chart i).target)
        (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff (n := n) (Ω := Ω) i) U j
  have hbaseComp := hqmp.ae_eq_comp hbaseIndicator
  have hderivComp : ∀ᵐ x ∂ domainMeasure n E.source, ∀ j : Fin n,
      K.indicator (deriv j) (E x) = deriv j (E x) :=
    MeasureTheory.ae_all_iff.2 fun j ↦ hqmp.ae_eq_comp (hderivIndicator j)
  -- on the chart source, `L = E⁻¹ K`
  have hLK {x : ℝ^n} (hx : x ∈ E.source) : x ∈ L ↔ E x ∈ K := by
    refine ⟨?_, fun hxK ↦ ⟨E x, hxK, E.left_inv hx⟩⟩
    rintro ⟨y, hyK, rfl⟩
    change E (E.symm y) ∈ K
    rwa [E.right_inv (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetCutoffSupport_subset_target
      (n := n) (Ω := Ω) i hyK)]
  have hbaseEq : rawBase =ᵐ[domainMeasure n E.source]
      preparedChartBaseRepresentative (n := n) (p := p) (Ω := Ω) i U := by
    filter_upwards [hbaseComp,
      MeasureTheory.ae_restrict_mem E.open_source.measurableSet] with x hxbase hxSource
    have hxLK := hLK hxSource
    by_cases hxK : E x ∈ K
    · have hxL : x ∈ L := hxLK.2 hxK
      simp [rawBase, preparedChartBaseRepresentative, E, K, L, V, base, hxK, hxL]
    · have hxL : x ∉ L := fun hx ↦ hxK (hxLK.1 hx)
      have hxzero : base (E x) = 0 := by
        simpa [hxK] using hxbase.symm
      simp [rawBase, preparedChartBaseRepresentative, E, L, V, base, hxL, hxzero]
  have hderivEq : rawDerivative =ᵐ[domainMeasure n E.source]
      preparedChartDerivativeRepresentative
        (n := n) (p := p) (Ω := Ω) i U k := by
    filter_upwards [hderivComp,
      MeasureTheory.ae_restrict_mem E.open_source.measurableSet] with x hxderiv hxSource
    have hxLK := hLK hxSource
    by_cases hxK : E x ∈ K
    · have hxL : x ∈ L := hxLK.2 hxK
      simp [rawDerivative, preparedChartDerivativeRepresentative, E, K, L, V, deriv,
        hxK, hxL, mul_comm]
    · have hxL : x ∉ L := fun hx ↦ hxK (hxLK.1 hx)
      have hxzero (j : Fin n) : deriv j (E x) = 0 := by simpa [hxK] using (hxderiv j).symm
      simp [rawDerivative, preparedChartDerivativeRepresentative,
        E, L, V, deriv, hxL, hxzero]
  have hweakSource : HasWeakDerivativeOn (n := n) E.source [k]
      (preparedChartBaseRepresentative (n := n) (p := p) (Ω := Ω) i U)
      (preparedChartDerivativeRepresentative
        (n := n) (p := p) (Ω := Ω) i U k) :=
    ((SobolevSpace.hasWeakDerivativeOn_congr_ae
      (n := n) (hfg := hbaseEq) (hf'g' := hderivEq)).1 hchain')
  exact hasWeakDerivativeOn_univ_of_support_subset_of_cutoff_one_nhds
    (n := n) (U := E.source) (K := L) E.open_source
    (by simpa [E, L] using
      Boundary.C1ExtensionAtlas.DerivedCutoffs.pullbackSupport_subset_source (n := n) (Ω := Ω) i)
    (support_preparedChartBaseRepresentative_subset
      (n := n) (p := p) (Ω := Ω) i U)
    (support_preparedChartDerivativeRepresentative_subset
      (n := n) (p := p) (Ω := Ω) i U k)
    (Boundary.C1ExtensionAtlas.DerivedCutoffs.pullbackSupportCutoff (n := n) (Ω := Ω) i)
    (by
      simpa [E] using
        (Boundary.C1ExtensionAtlas.DerivedCutoffs.tsupport_pullbackSupportCutoff_subset_source
          (n := n) (Ω := Ω) i))
    (Boundary.C1ExtensionAtlas.DerivedCutoffs.pullbackSupportCutoff_eq_one_nhds_on_pullbackSupport
      (n := n) (Ω := Ω) i) hweakSource

/-- The base coordinate of the prepared chart bundle has its explicit
representative almost everywhere. -/
theorem preparedChartAmbient_base_apply_ae
    (i : Fin hΩ.N)
    (U : W^{1,p}((hΩ.chart i).target)) :
    ((preparedChartAmbient (n := n) (p := p) (Ω := Ω) i U
        (SobolevSpace.GraphSpace.baseIndex n 1) :
        SobolevSpace.GraphSpace.DerivLp n p (Set.univ : Set (ℝ^n))) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (Set.univ : Set (ℝ^n))]
        preparedChartBaseRepresentative (n := n) (p := p) (Ω := Ω) i U := by
  let V := targetCutoffCLM (n := n) (p := p) (Ω := Ω) i U
  simpa [preparedChartAmbient_apply, localizedChartLpAt,
    preparedChartBaseRepresentative,
    SobolevSpace.GraphSpace.baseRepresentative, V] using
    localizedChartPullbackLp_apply_ae (n := n) (p := p) (Ω := Ω) i
      ((V : SobolevSpace.GraphSpace.WkpAmbientOn n 1 p (hΩ.chart i).target)
        (SobolevSpace.GraphSpace.baseIndex n 1))

private theorem preparedChartAmbient_derivative_apply_ae
    (i : Fin hΩ.N)
    (U : W^{1,p}((hΩ.chart i).target))
    (k : Fin n) :
    ((preparedChartAmbient (n := n) (p := p) (Ω := Ω) i U
        (SobolevSpace.GraphSpace.singleDerivIndex n k) :
        SobolevSpace.GraphSpace.DerivLp n p (Set.univ : Set (ℝ^n))) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (Set.univ : Set (ℝ^n))]
        preparedChartDerivativeRepresentative
          (n := n) (p := p) (Ω := Ω) i U k := by
  let V := targetCutoffCLM (n := n) (p := p) (Ω := Ω) i U
  simpa [preparedChartAmbient_apply, localizedChartLpAt, chartFirstDerivativesLp,
      preparedChartDerivativeRepresentative, V] using
    localizedChartDerivativeLp_apply_ae (n := n) (p := p) (Ω := Ω) i k
      (fun j ↦
        (V : SobolevSpace.GraphSpace.WkpAmbientOn n 1 p (hΩ.chart i).target)
          (SobolevSpace.GraphSpace.singleDerivIndex n j))

/-- The prepared chart bundle satisfies all global `W^{1,p}` weak-derivative
constraints. -/
theorem preparedChartAmbient_mapsIsWkpOn
    (i : Fin hΩ.N)
    (U : W^{1,p}((hΩ.chart i).target)) :
    SobolevSpace.GraphSpace.IsWkpOn (n := n) (k := 1) (p := p)
      (Ω := (Set.univ : Set (ℝ^n)))
      (preparedChartAmbient (n := n) (p := p) (Ω := Ω) i U) := by
  classical
  intro a
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨k, ha⟩
  · subst a
    have hloc := memLp_locallyIntegrableOn_domain
      (MeasureTheory.Lp.memLp
        (preparedChartAmbient (n := n) (p := p) (Ω := Ω) i U
          (SobolevSpace.GraphSpace.baseIndex n 1)))
      (Fact.out : (1 : ℝ≥0∞) ≤ p)
    simpa only [SobolevSpace.GraphSpace.baseIndex_toList] using hasWeakDerivativeOn_nil hloc
  · subst a
    simpa using (SobolevSpace.hasWeakDerivativeOn_congr_ae
      (n := n) (Ω := (Set.univ : Set (ℝ^n))) (α := [k])
      (preparedChartAmbient_base_apply_ae
        (n := n) (p := p) (Ω := Ω) i U)
      (preparedChartAmbient_derivative_apply_ae
        (n := n) (p := p) (Ω := Ω) i U k)).2
      (preparedChart_hasWeakDerivative (n := n) (p := p) (Ω := Ω) i U k)

/-- The localized chart pullback, preceded by its target cutoff, as a bounded
linear map into global `W^{1,p}(ℝ^n)`. -/
noncomputable def preparedChartCLM (i : Fin hΩ.N) :
    W^{1,p}((hΩ.chart i).target) →L[ℝ]
      W^{1,p}((Set.univ : Set (ℝ^n))) :=
  ContinuousLinearMap.codRestrict
    (preparedChartAmbient (n := n) (p := p) (Ω := Ω) i)
    (SobolevSpace.GraphSpace.wkpSubmoduleOn n 1 p (Set.univ : Set (ℝ^n)))
    (preparedChartAmbient_mapsIsWkpOn (n := n) (p := p) (Ω := Ω) i)

/-- The underlying ambient bundle of `preparedChartCLM i U` is
`preparedChartAmbient i U`. -/
@[simp] theorem preparedChartCLM_apply_coe
    (i : Fin hΩ.N)
    (U : W^{1,p}((hΩ.chart i).target)) :
    ((preparedChartCLM (n := n) (p := p) (Ω := Ω) i U :
        W^{1,p}((Set.univ : Set (ℝ^n)))) :
        SobolevSpace.GraphSpace.WkpAmbientOn n 1 p (Set.univ : Set (ℝ^n))) =
      preparedChartAmbient (n := n) (p := p) (Ω := Ω) i U :=
  rfl

end BoundaryPiece

end C1

end Extension

end SobolevSpace
