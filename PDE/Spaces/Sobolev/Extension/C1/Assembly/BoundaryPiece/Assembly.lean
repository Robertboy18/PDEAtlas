/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.C1.Assembly.Flattening.Assembly
public import PDE.Spaces.Sobolev.Extension.C1.LocalPieces.BoundaryOperator
import PDE.Spaces.Sobolev.Extension.C1.Assembly.BoundaryPiece.Agreement

/-!
# Assembly of a C1 boundary contribution

We compose flattening, half-space reflection, target localization,
and chart pullback into the bounded contribution of one boundary chart. Its
main theorem identifies that contribution with the corresponding partition
term on the original domain.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.4, Theorem 1, pp. 268-271; the proof flattens the boundary
  near each boundary point (step 5, p. 270), extends across the flat boundary, and glues the pieces
  with a partition of unity (step 6, (9), p. 270).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

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
open Boundary.C1ExtensionAtlas.DerivedCutoffs

namespace BoundaryPiece

variable [Fact (0 < n)] [Fact (1 ≤ p)] [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- Complete bounded `i`-th boundary contribution, following the proof of Evans §5.4,
Theorem 1: localize, flatten, reflect, relocalize, and pull back. -/
noncomputable def boundaryCLM (i : Fin hΩ.N) :
    W^{1,p}(Ω) →L[ℝ]
      W^{1,p}((Set.univ : Set (ℝ^n))) :=
  (boundaryFromUpperCLM (n := n) (p := p) (Ω := Ω) i).comp
    (flattenCLM (n := n) (p := p) (Ω := Ω) i)

/-- The complete bounded boundary contribution agrees with the partition term
`ψᵢu` on the original domain. -/
theorem boundaryCLM_agree_ae
    (i : Fin hΩ.N)
    (U : W^{1,p}(Ω)) :
    ∀ᵐ x ∂ domainMeasure n Ω,
      GraphSpace.baseRepresentative (n := n) (p := p)
          (boundaryCLM (n := n) (p := p) (Ω := Ω) i U) x =
        (hΩ.boundaryCutoff i).toFun x *
          GraphSpace.baseRepresentative (n := n) (p := p) U x := by
  classical
  let E := Boundary.C1ExtensionAtlas.Charts.chartOnΩ i
  let F := flattenCLM i U
  let W := reflectedChartTargetCLM i F
  let V := GraphSpace.cutoffCLM (hΩ.boundaryCutoff i) U
  let K := boundarySupport i
  have hsourceSub : E.source ⊆ (hΩ.chart i).source := fun x hx ↦ by
    simpa [E, Boundary.C1ExtensionAtlas.Charts.chartOnΩ_source] using hx.1
  have hsourceSubΩ : E.source ⊆ Ω := fun x hx ↦ by
    simpa [E, Boundary.C1ExtensionAtlas.Charts.chartOnΩ_source] using hx.2
  -- on the chart target, `W` is `ψᵢ u` pushed forward by the chart
  have htarget : GraphSpace.baseRepresentative W =ᵐ[domainMeasure n E.target]
      fun y ↦ GraphSpace.baseRepresentative V ((hΩ.chart i).symm y) := by
    have hreflect := reflectedChartTargetCLM_base_agree_ae i F
    have hflat := flattenCLM_base_agree_ae i U
    filter_upwards [hreflect, hflat] with y hyReflect hyFlat
    exact hyReflect.trans hyFlat
  have hqmp : QuasiMeasurePreserving (fun x ↦ E x)
      (domainMeasure n E.source) (domainMeasure n E.target) :=
    WeakChangeOfVariables.quasiMeasurePreserving_partialHomeomorph (E := E)
      (by simpa [E, Boundary.C1ExtensionAtlas.Charts.chartOnΩ] using hΩ.chart_contDiff i)
      (by simpa [E, Boundary.C1ExtensionAtlas.Charts.chartOnΩ] using hΩ.chart_symm_contDiff i)
  have hpullback : ∀ᵐ x ∂ domainMeasure n E.source,
      GraphSpace.baseRepresentative (boundaryCLM i U) x =
        (targetSupportCutoff i).toFun (hΩ.chart i x) *
          GraphSpace.baseRepresentative W (hΩ.chart i x) := by
    simpa [boundaryCLM, boundaryFromUpperCLM, W, F] using ae_restrict_of_ae_restrict_of_subset
      hsourceSub (preparedChartCLM_base_agree_ae i W)
  have hsupport : K.indicator (GraphSpace.baseRepresentative V)
      =ᵐ[domainMeasure n Ω] GraphSpace.baseRepresentative V := by
    simpa [K, V, GraphSpace.baseRepresentative, boundarySupport] using
      GraphSpace.cutoffCLM_base_tsupport_indicator_ae
        (hΩ.boundaryCutoff i) U
  have hcutoff : GraphSpace.baseRepresentative V =ᵐ[domainMeasure n Ω]
      fun x ↦ (hΩ.boundaryCutoff i).toFun x * GraphSpace.baseRepresentative U x := by
    simpa [V, GraphSpace.baseRepresentative] using
      GraphSpace.cutoffCLM_base_apply_ae (hΩ.boundaryCutoff i) U
  -- inside the chart source, `ηᵢ = 1` on the image of `supp ψᵢ`
  have hinside : ∀ᵐ x ∂ domainMeasure n E.source,
      GraphSpace.baseRepresentative (boundaryCLM i U) x =
        (hΩ.boundaryCutoff i).toFun x * GraphSpace.baseRepresentative U x := by
    filter_upwards [hpullback, hqmp.ae_eq_comp htarget,
      ae_restrict_of_ae_restrict_of_subset hsourceSubΩ hsupport,
      ae_restrict_of_ae_restrict_of_subset hsourceSubΩ hcutoff,
      ae_restrict_mem E.open_source.measurableSet] with x hxpull hxtarget hxsupport hxcutoff hx
    have htargetAt : GraphSpace.baseRepresentative W (hΩ.chart i x) =
        GraphSpace.baseRepresentative V x := by
      simpa [E, Boundary.C1ExtensionAtlas.Charts.chartOnΩ, (hΩ.chart i).left_inv (hsourceSub hx)]
        using hxtarget
    rw [hxpull, htargetAt]
    by_cases hxK : x ∈ K
    · rw [targetSupportCutoff_eq_one_on_boundarySupportInTarget i _
        ⟨x, hxK, rfl⟩, one_mul]
      exact hxcutoff
    · have hVzero : GraphSpace.baseRepresentative V x = 0 := by
        simpa [hxK] using hxsupport.symm
      rw [hVzero, mul_zero]
      exact hVzero.symm.trans hxcutoff
  have hmeasureInside : (domainMeasure n Ω).restrict (hΩ.chart i).source =
      domainMeasure n E.source := by
    rw [domainMeasure, Measure.restrict_restrict (hΩ.chart i).open_source.measurableSet]
    simp [E, inter_comm]
  -- outside the chart source both sides vanish
  have hactual : ∀ᵐ x ∂ domainMeasure n Ω,
      GraphSpace.baseRepresentative (boundaryCLM i U) x =
        preparedChartBaseRepresentative i W x := by
    simpa [GraphSpace.baseRepresentative, boundaryCLM, boundaryFromUpperCLM, W, F,
      domainMeasure, Measure.restrict_restrict, inter_univ] using
      ae_restrict_of_ae (s := Ω) (preparedChartAmbient_base_apply_ae i W)
  refine ae_of_ae_restrict_of_ae_restrict_compl (hΩ.chart i).source (hmeasureInside ▸ hinside) ?_
  filter_upwards [ae_restrict_of_ae hactual,
    ae_restrict_mem (hΩ.chart i).open_source.measurableSet.compl] with x hxactual hxOutside
  have hψzero : (hΩ.boundaryCutoff i).toFun x = 0 := by
    by_contra hne
    exact hxOutside (hΩ.boundaryCutoff_support i (subset_tsupport _ hne))
  have hxL : x ∉ pullbackSupport (n := n) (Ω := Ω) i :=
    fun hxL ↦ hxOutside (pullbackSupport_subset_source i hxL)
  rw [hxactual]
  simp [preparedChartBaseRepresentative, hxL, hψzero]

end BoundaryPiece

end C1

end Extension

end SobolevSpace
