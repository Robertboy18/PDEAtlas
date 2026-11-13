/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.C1.LocalPieces.BoundaryOperator
public import PDE.Spaces.Sobolev.Extension.C1.Assembly.Flattening.Assembly

/-!
# Agreement lemmas for a C¹ boundary piece

The `C¹` extension theorem (Evans §5.4, Theorem 1) extends a Sobolev function on a domain `Ω` to all
of `ℝ^n` by localizing near the boundary with a partition of unity, flattening each boundary patch
with a `C¹` chart onto the upper half-space, reflecting across the flat boundary, and pulling the
result back through the chart. Each of these steps is a bounded operator on graph-space Sobolev
elements, defined in `Assembly.Flattening.Assembly`, `LocalPieces.BoundaryOperator` and
`LocalPieces.ChartOperator`, and each is determined only up to null sets. We record, for a single
boundary chart `i`, what the resulting `L^p` coordinates are almost everywhere on the relevant chart
region:

* `flattenCLM_base_agree_ae`, `flattenCLM_deriv_agree_ae`: on the flattened
  image of `Ω ∩ chart source`, the flattened field is `(ψᵢ u) ∘ chartᵢ⁻¹` and
  its first derivatives are given by the chain rule
  `∂ₖ((ψᵢu) ∘ chartᵢ⁻¹) = ∑ⱼ (∂ⱼ(ψᵢu)) ∘ chartᵢ⁻¹ · ∂ₖ(chartᵢ⁻¹)ⱼ`, with the
  Sobolev derivatives of `ψᵢu` on the right.
* `reflectedChartTargetCLM_base_agree_ae`: the reflected field, restricted to
  the chart target, agrees with the input on the part of the chart target
  lying in the upper half-space.
* `preparedChartCLM_base_agree_ae`: on the chart source, the pullback of the
  target-cutoff field is `η(chartᵢ x) · u(chartᵢ x)`.

These identities are the compatibility input used in
`BoundaryPiece.ClassicalRepresentative` to identify the boundary contribution
with the original function on `Ω`.

## Implementation notes

Everything is stated for an arbitrary graph-space input; no classical
differentiability of the input is assumed.  Restrictions of the domain measure
to chart regions are rewritten as domain measures of those regions, and the
supports of the cutoffs are transported through the chart by the
quasi-measure-preserving property of `C¹` diffeomorphisms.

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

/-- The inverse of the chart on `Ω` maps the flattened image back into `Ω`. -/
private theorem chartOnΩ_symm_target_subset (i : Fin hΩ.N) :
    (Boundary.C1ExtensionAtlas.Charts.chartOnΩ (n := n) (Ω := Ω) i).symm.target ⊆ Ω :=
  fun x hx ↦ by
    have hx' : x ∈ (Boundary.C1ExtensionAtlas.Charts.chartOnΩ (n := n) (Ω := Ω) i).source := by
      simpa using hx
    simpa [Boundary.C1ExtensionAtlas.Charts.chartOnΩ_source] using hx'.2

/-- The inverse chart on `Ω` is quasi-measure-preserving between its source and target. -/
private theorem quasiMeasurePreserving_chartOnΩ_symm (i : Fin hΩ.N) :
    QuasiMeasurePreserving
      (fun y ↦ (Boundary.C1ExtensionAtlas.Charts.chartOnΩ (n := n) (Ω := Ω) i).symm y)
      (domainMeasure n (Boundary.C1ExtensionAtlas.Charts.chartOnΩ (n := n) (Ω := Ω) i).symm.source)
      (domainMeasure n
        (Boundary.C1ExtensionAtlas.Charts.chartOnΩ (n := n) (Ω := Ω) i).symm.target) :=
  SobolevSpace.WeakChangeOfVariables.quasiMeasurePreserving_partialHomeomorph
    (by simpa [Boundary.C1ExtensionAtlas.Charts.chartOnΩ] using hΩ.chart_symm_contDiff i)
    (by simpa [Boundary.C1ExtensionAtlas.Charts.chartOnΩ] using hΩ.chart_contDiff i)

/-- On the flattened image, the inverse chart lands in the boundary support exactly at the
points of its chart image. -/
private theorem chartOnΩ_symm_mem_boundarySupport_iff (i : Fin hΩ.N) {y : ℝ^n}
    (hy : y ∈ (Boundary.C1ExtensionAtlas.Charts.chartOnΩ (n := n) (Ω := Ω) i).symm.source) :
    (Boundary.C1ExtensionAtlas.Charts.chartOnΩ (n := n) (Ω := Ω) i).symm y ∈
        boundarySupport (n := n) (Ω := Ω) i ↔
      y ∈ boundarySupportInTarget (n := n) (Ω := Ω) i := by
  have hy' : y ∈ (Boundary.C1ExtensionAtlas.Charts.chartOnΩ (n := n) (Ω := Ω) i).target := by
    simpa using hy
  have hyChartTarget : y ∈ (hΩ.chart i).target := by
    simpa [Boundary.C1ExtensionAtlas.Charts.chartOnΩ_target_eq_target_inter_upper] using hy'.1
  constructor
  · intro hxK
    exact ⟨_, hxK, by
      simpa [Boundary.C1ExtensionAtlas.Charts.chartOnΩ] using (hΩ.chart i).right_inv hyChartTarget⟩
  · rintro ⟨x, hxK, rfl⟩
    simpa [Boundary.C1ExtensionAtlas.Charts.chartOnΩ,
      (hΩ.chart i).left_inv (boundarySupport_subset_source (n := n) (Ω := Ω) i hxK)] using hxK

/-- On the flattened chart portion of the upper half-space, the bounded
flattening operator represents `(ψᵢu) ∘ chart.symm`. -/
theorem flattenCLM_base_agree_ae
    (i : Fin hΩ.N)
    (U : W^{1,p}(Ω)) :
    ∀ᵐ y ∂ domainMeasure n
        (Boundary.C1ExtensionAtlas.Charts.chartOnΩ (n := n) (Ω := Ω) i).target,
      GraphSpace.baseRepresentative (n := n) (p := p)
          (flattenCLM (n := n) (p := p) (Ω := Ω) i U) y =
        GraphSpace.baseRepresentative (n := n) (p := p)
          (SobolevSpace.GraphSpace.cutoffCLM
            (n := n) (p := p) (Ω := Ω) (hΩ.boundaryCutoff i) U)
          ((hΩ.chart i).symm y) := by
  classical
  let E := (Boundary.C1ExtensionAtlas.Charts.chartOnΩ (n := n) (Ω := Ω) i).symm
  let K := boundarySupport (n := n) (Ω := Ω) i
  let base : ℝ^n → ℝ :=
    (SobolevSpace.GraphSpace.cutoffCLM (n := n) (p := p) (Ω := Ω) (hΩ.boundaryCutoff i) U :
      SobolevSpace.GraphSpace.WkpAmbientOn n 1 p Ω) (SobolevSpace.GraphSpace.baseIndex n 1)
  have hsupportΩ : K.indicator base =ᵐ[domainMeasure n Ω] base := by
    simpa [K, base, boundarySupport] using
      SobolevSpace.GraphSpace.cutoffCLM_base_tsupport_indicator_ae
        (n := n) (p := p) (Ω := Ω) (hΩ.boundaryCutoff i) U
  have hsupport : K.indicator base =ᵐ[domainMeasure n E.target] base :=
    ae_restrict_of_ae_restrict_of_subset (chartOnΩ_symm_target_subset i) hsupportΩ
  have hactual : ∀ᵐ y ∂ domainMeasure n
        (Boundary.C1ExtensionAtlas.Charts.chartOnΩ (n := n) (Ω := Ω) i).target,
      GraphSpace.baseRepresentative (n := n) (p := p)
          (flattenCLM (n := n) (p := p) (Ω := Ω) i U) y =
        preparedFlattenBaseRepresentative (n := n) (p := p) (Ω := Ω) i U y := by
    simpa [GraphSpace.baseRepresentative, flattenCLM_apply_coe] using
      ae_restrict_of_ae_restrict_of_subset
        (Boundary.C1ExtensionAtlas.Charts.chartOnΩ_target_subset_upper (n := n) (Ω := Ω) i)
        (preparedFlattenAmbient_base_apply_ae (n := n) (p := p) (Ω := Ω) i U)
  filter_upwards [hactual, (quasiMeasurePreserving_chartOnΩ_symm i).ae_eq_comp hsupport,
    ae_restrict_mem E.open_source.measurableSet] with y hyactual hysupport hySource
  rw [hyactual]
  have hyK := chartOnΩ_symm_mem_boundarySupport_iff i hySource
  change (boundarySupportInTarget (n := n) (Ω := Ω) i).indicator
    (fun z ↦ K.indicator (Ω.indicator base) ((hΩ.chart i).symm z)) y = base ((hΩ.chart i).symm y)
  have hEy : (hΩ.chart i).symm y = E y := rfl
  by_cases hxK : E y ∈ K
  · rw [indicator_of_mem (hyK.1 hxK), hEy, indicator_of_mem hxK,
      indicator_of_mem (chartOnΩ_symm_target_subset i (E.map_source hySource))]
  · rw [indicator_of_notMem (mt hyK.2 hxK), hEy]
    exact (hysupport.symm.trans (indicator_of_notMem hxK base)).symm

/-- On the flattened chart target, every first derivative coordinate of `flattenCLM` has the
Sobolev chain-rule representative.  This is the derivative-level companion to
`flattenCLM_base_agree_ae`; it is stated for an arbitrary Sobolev input and therefore introduces
no classical differentiability assumption on that input. -/
theorem flattenCLM_deriv_agree_ae
    (i : Fin hΩ.N)
    (U : W^{1,p}(Ω))
    (k : Fin n) :
    ∀ᵐ y ∂ domainMeasure n
        (Boundary.C1ExtensionAtlas.Charts.chartOnΩ (n := n) (Ω := Ω) i).target,
      (((flattenCLM (n := n) (p := p) (Ω := Ω) i U :
          SobolevSpace.GraphSpace.WkpAmbientOn n 1 p
            (SobolevSpace.HalfSpace.upper n))
          (SobolevSpace.GraphSpace.singleDerivIndex n k) :
          SobolevSpace.GraphSpace.DerivLp n p (SobolevSpace.HalfSpace.upper n)) :
          ℝ^n → ℝ) y =
        ∑ j : Fin n,
          ((((SobolevSpace.GraphSpace.cutoffCLM
              (n := n) (p := p) (Ω := Ω) (hΩ.boundaryCutoff i) U :
                SobolevSpace.GraphSpace.WkpAmbientOn n 1 p Ω)
              (SobolevSpace.GraphSpace.singleDerivIndex n j) :
              SobolevSpace.GraphSpace.DerivLp n p Ω) : ℝ^n → ℝ)
                ((hΩ.chart i).symm y)) *
            ((fderiv ℝ (fun z ↦ (hΩ.chart i).symm z) y)
              (EuclideanSpace.single k (1 : ℝ))) j := by
  classical
  let E := (Boundary.C1ExtensionAtlas.Charts.chartOnΩ (n := n) (Ω := Ω) i).symm
  let K := boundarySupport (n := n) (Ω := Ω) i
  let d : Fin n → ℝ^n → ℝ := fun j ↦
    ((SobolevSpace.GraphSpace.cutoffCLM (n := n) (p := p) (Ω := Ω) (hΩ.boundaryCutoff i) U :
      SobolevSpace.GraphSpace.WkpAmbientOn n 1 p Ω)
        (SobolevSpace.GraphSpace.singleDerivIndex n j) : ℝ^n → ℝ)
  have hsupport : ∀ᵐ x ∂ domainMeasure n E.target, ∀ j : Fin n,
      K.indicator (d j) x = d j x :=
    ae_all_iff.2 fun j ↦ by
      have hj : K.indicator (d j) =ᵐ[domainMeasure n Ω] d j := by
        simpa [K, d, boundarySupport] using
          SobolevSpace.GraphSpace.cutoffCLM_singleDeriv_tsupport_indicator_ae
            (n := n) (p := p) (Ω := Ω) (hΩ.boundaryCutoff i) U j
      exact ae_restrict_of_ae_restrict_of_subset (chartOnΩ_symm_target_subset i) hj
  have hactual :
      ((((flattenCLM (n := n) (p := p) (Ω := Ω) i U :
          SobolevSpace.GraphSpace.WkpAmbientOn n 1 p
            (SobolevSpace.HalfSpace.upper n))
          (SobolevSpace.GraphSpace.singleDerivIndex n k) :
          SobolevSpace.GraphSpace.DerivLp n p (SobolevSpace.HalfSpace.upper n)) :
          ℝ^n → ℝ)) =ᵐ[domainMeasure n
            (Boundary.C1ExtensionAtlas.Charts.chartOnΩ (n := n) (Ω := Ω) i).target]
        preparedFlattenDerivativeRepresentative (n := n) (p := p) (Ω := Ω) i U k :=
    ae_restrict_of_ae_restrict_of_subset
      (Boundary.C1ExtensionAtlas.Charts.chartOnΩ_target_subset_upper (n := n) (Ω := Ω) i)
      (preparedFlattenAmbient_derivative_apply_ae (n := n) (p := p) (Ω := Ω) i U k)
  filter_upwards [hactual, (quasiMeasurePreserving_chartOnΩ_symm i).ae hsupport,
    ae_restrict_mem E.open_source.measurableSet] with y hyactual hysupport hySource
  rw [hyactual]
  have hyK := chartOnΩ_symm_mem_boundarySupport_iff i hySource
  have hEy : (hΩ.chart i).symm y = E y := rfl
  simp only [preparedFlattenDerivativeRepresentative]
  by_cases hxK : E y ∈ K
  · rw [indicator_of_mem (hyK.1 hxK)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    change flattenJacobianCoefficient (n := n) (Ω := Ω) i k j y *
        K.indicator (Ω.indicator (d j)) ((hΩ.chart i).symm y) =
      d j ((hΩ.chart i).symm y) *
        ((fderiv ℝ (fun z ↦ (hΩ.chart i).symm z) y) (EuclideanSpace.single k (1 : ℝ))) j
    rw [hEy, indicator_of_mem hxK,
      indicator_of_mem (chartOnΩ_symm_target_subset i (E.map_source hySource))]
    simp [flattenJacobianCoefficient, mul_comm]
  · rw [indicator_of_notMem (mt hyK.2 hxK)]
    refine (Finset.sum_eq_zero fun j _ ↦ ?_).symm
    change d j (E y) *
        ((fderiv ℝ (fun z ↦ (hΩ.chart i).symm z) y) (EuclideanSpace.single k (1 : ℝ))) j = 0
    rw [show d j (E y) = 0 from (hysupport j).symm.trans (indicator_of_notMem hxK (d j)),
      zero_mul]

/-- On the part of the chart target lying in the upper half-space, the
reflected field agrees with the input: the half-space extension operator
reproduces `U` on the upper half-space, and restricting to the chart target
does not change representatives there. -/
theorem reflectedChartTargetCLM_base_agree_ae
    (i : Fin hΩ.N)
    (U : W^{1,p}((SobolevSpace.HalfSpace.upper n))) :
    ∀ᵐ y ∂ domainMeasure n
        (Boundary.C1ExtensionAtlas.Charts.chartOnΩ (n := n) (Ω := Ω) i).target,
      GraphSpace.baseRepresentative (n := n) (p := p)
          (reflectedChartTargetCLM (n := n) (p := p) (Ω := Ω) i U) y =
        GraphSpace.baseRepresentative (n := n) (p := p) U y := by
  let chartΩ := Boundary.C1ExtensionAtlas.Charts.chartOnΩ (n := n) (Ω := Ω) i
  let R := (SobolevSpace.Extension.GraphSpace.HalfSpace.operator
    (n := n) (p := p)).toContinuousLinearMap U
  have hchartSub : chartΩ.target ⊆ (hΩ.chart i).target := fun y hy ↦ by
    simpa [chartΩ,
      Boundary.C1ExtensionAtlas.Charts.chartOnΩ_target_eq_target_inter_upper] using hy.1
  -- restricting to the chart target does not change the representative
  have hrestrict : ∀ᵐ y ∂ domainMeasure n chartΩ.target,
      GraphSpace.baseRepresentative (n := n) (p := p)
          (reflectedChartTargetCLM (n := n) (p := p) (Ω := Ω) i U) y =
        GraphSpace.baseRepresentative (n := n) (p := p) R y := by
    simpa [GraphSpace.baseRepresentative, reflectedChartTargetCLM] using
      ae_restrict_of_ae_restrict_of_subset hchartSub
        (SobolevSpace.GraphSpace.restrictCLM_apply_ae (n := n) (k := 1) (p := p)
          (Ω := (hΩ.chart i).target) (Ωbig := (Set.univ : Set (ℝ^n)))
          (hΩ.chart i).open_target.measurableSet (subset_univ _) R
          (SobolevSpace.GraphSpace.baseIndex n 1))
  -- the extension operator reproduces `U` on the upper half-space
  have hreflect : ∀ᵐ y ∂ domainMeasure n chartΩ.target,
      GraphSpace.baseRepresentative (n := n) (p := p) R y =
        GraphSpace.baseRepresentative (n := n) (p := p) U y :=
    ae_restrict_of_ae_restrict_of_subset
      (Boundary.C1ExtensionAtlas.Charts.chartOnΩ_target_subset_upper (n := n) (Ω := Ω) i)
      ((SobolevSpace.Extension.GraphSpace.HalfSpace.operator (n := n) (p := p)).agree_ae U)
  filter_upwards [hrestrict, hreflect] with y hyRestrict hyReflect using hyRestrict.trans hyReflect

/-- On the chart source, the prepared pullback is the target-cutoff field
composed with the chart. -/
theorem preparedChartCLM_base_agree_ae
    (i : Fin hΩ.N)
    (U : W^{1,p}((hΩ.chart i).target)) :
    ∀ᵐ x ∂ domainMeasure n (hΩ.chart i).source,
      GraphSpace.baseRepresentative (n := n) (p := p)
          (preparedChartCLM (n := n) (p := p) (Ω := Ω) i U) x =
        (targetSupportCutoff
          (n := n) (Ω := Ω) i).toFun (hΩ.chart i x) *
          GraphSpace.baseRepresentative (n := n) (p := p) U (hΩ.chart i x) := by
  classical
  let E := hΩ.chart i
  let η := targetSupportCutoff (n := n) (Ω := Ω) i
  let K := targetCutoffSupport (n := n) (Ω := Ω) i
  let base : ℝ^n → ℝ :=
    (targetCutoffCLM (n := n) (p := p) (Ω := Ω) i U :
      SobolevSpace.GraphSpace.WkpAmbientOn n 1 p E.target) (SobolevSpace.GraphSpace.baseIndex n 1)
  have hactual : ∀ᵐ x ∂ domainMeasure n E.source,
      GraphSpace.baseRepresentative (n := n) (p := p)
          (preparedChartCLM (n := n) (p := p) (Ω := Ω) i U) x =
        preparedChartBaseRepresentative (n := n) (p := p) (Ω := Ω) i U x := by
    simpa [GraphSpace.baseRepresentative, preparedChartCLM_apply_coe, domainMeasure,
      Measure.restrict_restrict, inter_univ] using
      ae_restrict_of_ae (s := E.source)
        (preparedChartAmbient_base_apply_ae (n := n) (p := p) (Ω := Ω) i U)
  have hsupport : K.indicator base =ᵐ[domainMeasure n E.target] base := by
    simpa [E, η, K, base, targetCutoffCLM, targetCutoffSupport] using
      SobolevSpace.GraphSpace.cutoffCLM_base_tsupport_indicator_ae
        (n := n) (p := p) (Ω := E.target) η U
  have hcutoff : base =ᵐ[domainMeasure n E.target]
      fun y ↦ η.toFun y * GraphSpace.baseRepresentative (n := n) (p := p) U y := by
    simpa [E, η, base, targetCutoffCLM, GraphSpace.baseRepresentative] using
      SobolevSpace.GraphSpace.cutoffCLM_base_apply_ae
        (n := n) (p := p) (Ω := E.target) η U
  have hqmp : QuasiMeasurePreserving (fun x ↦ E x)
      (domainMeasure n E.source) (domainMeasure n E.target) :=
    SobolevSpace.WeakChangeOfVariables.quasiMeasurePreserving_partialHomeomorph
      (by simpa [E] using hΩ.chart_contDiff i) (by simpa [E] using hΩ.chart_symm_contDiff i)
  filter_upwards [hactual, hqmp.ae_eq_comp hsupport, hqmp.ae_eq_comp hcutoff,
    ae_restrict_mem E.open_source.measurableSet] with x hxactual hxsupport hxcutoff hxSource
  have hxLK : x ∈ pullbackSupport (n := n) (Ω := Ω) i ↔ E x ∈ K := by
    refine ⟨?_, fun hxK ↦ ⟨E x, hxK, E.left_inv hxSource⟩⟩
    rintro ⟨y, hyK, rfl⟩
    change E (E.symm y) ∈ K
    rwa [E.right_inv (targetCutoffSupport_subset_target (n := n) (Ω := Ω) i hyK)]
  have hprepared :
      preparedChartBaseRepresentative (n := n) (p := p) (Ω := Ω) i U x = base (E x) := by
    change (pullbackSupport (n := n) (Ω := Ω) i).indicator (fun z ↦ K.indicator base (E z)) x =
      base (E x)
    by_cases hxK : E x ∈ K
    · rw [indicator_of_mem (hxLK.2 hxK), indicator_of_mem hxK]
    · rw [indicator_of_notMem (mt hxLK.1 hxK), (by simpa [hxK] using hxsupport.symm :
        base (E x) = 0)]
  rw [hxactual, hprepared]
  simpa [E, η, GraphSpace.baseRepresentative] using hxcutoff

end BoundaryPiece

end C1

end Extension

end SobolevSpace
