/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.C1.Assembly.Flattening.Jacobian
public import PDE.Spaces.Sobolev.Extension.C1.Assembly.Flattening.ZeroExtension
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Cutoff
import PDE.Spaces.Sobolev.Localization.Cutoff.CompactSupport

/-!
# Assembly of the C¹ boundary-flattening operator

In the proof of the extension theorem for `C¹` domains (Evans §5.4, Theorem 1), a Sobolev function
`u` on `Ω` is localized near a boundary point by a cutoff `ψᵢ` and then straightened:
`v := (ψᵢ u) ∘ Φᵢ⁻¹`, where `Φᵢ` is a `C¹` chart sending `Ω ∩ source` onto a piece of the upper
half-space. We build that step as a bounded linear operator

  `flattenCLM i : W^{1,p}(Ω) → W^{1,p}(ℝ^n₊)`

on graph-space Sobolev elements.  The base coordinate of the output is
`(ψᵢ u) ∘ Φᵢ⁻¹`, extended by zero outside the compact flattened support
`boundarySupportInTarget i`; the derivative coordinates are the chain-rule
expressions `∑ⱼ (∂ⱼ(ψᵢu)) ∘ Φᵢ⁻¹ · ∂ₖ(Φᵢ⁻¹)ⱼ` assembled in
`Flattening.Jacobian`, zero-extended in the same way.  That these coordinates
satisfy the weak-derivative identities on the upper half-space is proved from
the weak chain rule for `W^{1,p}` under `C¹` diffeomorphisms, applied on the
chart target, together with a cutoff argument that transfers the identity from
`Φᵢ(Ω ∩ source)` to all of `ℝ^n₊` using that the representatives vanish outside
a compact subset of the chart target.

## Main definitions and results

* `preparedFlattenAmbient i`: the ambient bundle map `W^{1,p}(Ω) → PiLp` over
  the upper half-space, obtained by applying `cutoffCLM ψᵢ` and then the
  coordinatewise flattening maps.
* `preparedFlattenBaseRepresentative`,
  `preparedFlattenDerivativeRepresentative`: explicit pointwise representatives
  of the output coordinates, with their support bounds and the
  almost-everywhere identifications `preparedFlattenAmbient_base_apply_ae`,
  `preparedFlattenAmbient_derivative_apply_ae`.
* `preparedFlattenAmbient_mapsIsWkpOn`: the output satisfies every first-order
  weak-derivative constraint on `ℝ^n₊`.
* `flattenCLM i`: the resulting bounded operator into `W^{1,p}(ℝ^n₊)`, with
  `flattenCLM_apply_coe`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.4, Theorem 1, pp. 268-271; the proof flattens the boundary
  near each boundary point (step 5, p. 270), extends across the flat boundary, and glues the pieces
  with a partition of unity (step 6, (9), p. 270).
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
open Boundary.C1ExtensionAtlas.DerivedCutoffs

namespace BoundaryPiece

variable [Fact (0 < n)] [Fact (1 ≤ p)] [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- The transformed derivative coordinate, zero-extended and restricted to
the upper half-space. -/
noncomputable def flattenDerivativeUpperLp
    (i : Fin hΩ.N) (k : Fin n) :
    (Fin n → SobolevSpace.GraphSpace.DerivLp n p Ω) →L[ℝ]
      SobolevSpace.GraphSpace.DerivLp n p (SobolevSpace.HalfSpace.upper n) :=
  (compactToUpperLp (n := n) (p := p) (Ω := Ω) i).comp
    (flattenDerivativeCompactLp (n := n) (p := p) (Ω := Ω) i k)

/-- Almost-everywhere formula for a transformed derivative on the upper
half-space. -/
private theorem flattenDerivativeUpperLp_apply_ae
    (i : Fin hΩ.N) (k : Fin n)
    (du : Fin n → SobolevSpace.GraphSpace.DerivLp n p Ω) :
    ((flattenDerivativeUpperLp (n := n) (p := p) (Ω := Ω) i k du :
        SobolevSpace.GraphSpace.DerivLp n p (SobolevSpace.HalfSpace.upper n)) :
        ℝ^n → ℝ)
      =ᵐ[domainMeasure n (SobolevSpace.HalfSpace.upper n)]
        (boundarySupportInTarget (n := n) (Ω := Ω) i).indicator
          (fun y ↦ ∑ j : Fin n,
            flattenJacobianCoefficient (n := n) (Ω := Ω) i k j y *
              (boundarySupport (n := n) (Ω := Ω) i).indicator
                (Ω.indicator fun x ↦ du j x) ((hΩ.chart i).symm y)) := by
  filter_upwards [compactToUpperLp_apply_ae i (flattenDerivativeCompactLp i k du),
    ae_restrict_of_ae ((ae_restrict_iff' (isCompact_boundarySupportInTarget i).measurableSet).1
      (flattenDerivativeCompactLp_apply_ae i k du))] with y hy hc
  refine hy.trans ?_
  by_cases hyKT : y ∈ boundarySupportInTarget (n := n) (Ω := Ω) i
  · simp [hyKT, hc hyKT]
  · simp [hyKT]

/-- Extract the first derivative coordinates of a Banach `W^{1,p}(Ω)`
bundle. -/
noncomputable def flattenFirstDerivativesLp :
    SobolevSpace.GraphSpace.WkpAmbientOn n 1 p Ω →L[ℝ]
      (Fin n → SobolevSpace.GraphSpace.DerivLp n p Ω) := by
  classical
  exact ContinuousLinearMap.pi fun j ↦
    PiLp.proj (𝕜 := ℝ) (p := p)
      (β := fun _ : SobolevSpace.GraphSpace.DerivIndex n 1 ↦
        SobolevSpace.GraphSpace.DerivLp n p Ω)
      (SobolevSpace.GraphSpace.singleDerivIndex n j)

/-- One output coordinate of the flattening map. -/
noncomputable def flattenLpAt
    (i : Fin hΩ.N) (a : SobolevSpace.GraphSpace.DerivIndex n 1) :
    SobolevSpace.GraphSpace.WkpAmbientOn n 1 p Ω →L[ℝ]
      SobolevSpace.GraphSpace.DerivLp n p (SobolevSpace.HalfSpace.upper n) :=
  SobolevSpace.GraphSpace.firstOrderRows
    ((flattenUpperLp (n := n) (p := p) (Ω := Ω) i).comp
      (PiLp.proj (𝕜 := ℝ) (p := p)
        (β := fun _ : SobolevSpace.GraphSpace.DerivIndex n 1 ↦
          SobolevSpace.GraphSpace.DerivLp n p Ω)
        (SobolevSpace.GraphSpace.baseIndex n 1)))
    (fun k ↦
      (flattenDerivativeUpperLp (n := n) (p := p) (Ω := Ω) i k).comp
        (flattenFirstDerivativesLp (n := n) (p := p) (Ω := Ω)))
    a

/-- Flattening on the complete ambient derivative bundle. -/
noncomputable def flattenAmbient (i : Fin hΩ.N) :
    SobolevSpace.GraphSpace.WkpAmbientOn n 1 p Ω →L[ℝ]
      SobolevSpace.GraphSpace.WkpAmbientOn n 1 p (SobolevSpace.HalfSpace.upper n) := by
  classical
  let e := PiLp.continuousLinearEquiv (𝕜 := ℝ) (p := p)
    (β := fun _ : SobolevSpace.GraphSpace.DerivIndex n 1 ↦
      SobolevSpace.GraphSpace.DerivLp n p (SobolevSpace.HalfSpace.upper n))
  exact e.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun a ↦
      flattenLpAt (n := n) (p := p) (Ω := Ω) i a)

/-- Localize by `ψᵢ` and apply all flattening coordinates. -/
noncomputable def preparedFlattenAmbient (i : Fin hΩ.N) :
    W^{1,p}(Ω) →L[ℝ]
      SobolevSpace.GraphSpace.WkpAmbientOn n 1 p (SobolevSpace.HalfSpace.upper n) :=
  (flattenAmbient (n := n) (p := p) (Ω := Ω) i).comp
    ((Submodule.subtypeL (SobolevSpace.GraphSpace.wkpSubmoduleOn n 1 p Ω)).comp
      (SobolevSpace.GraphSpace.cutoffCLM
        (n := n) (p := p) (Ω := Ω) (hΩ.boundaryCutoff i)))

private theorem preparedFlattenAmbient_apply
    (i : Fin hΩ.N)
    (U : W^{1,p}(Ω))
    (a : SobolevSpace.GraphSpace.DerivIndex n 1) :
    preparedFlattenAmbient (n := n) (p := p) (Ω := Ω) i U a =
      flattenLpAt (n := n) (p := p) (Ω := Ω) i a
        (((SobolevSpace.GraphSpace.cutoffCLM
          (n := n) (p := p) (Ω := Ω) (hΩ.boundaryCutoff i)) U :
          W^{1,p}(Ω)) :
          SobolevSpace.GraphSpace.WkpAmbientOn n 1 p Ω) := by
  rfl

/-- Pointwise base representative used to certify the flattening bundle. -/
def preparedFlattenBaseRepresentative
    (i : Fin hΩ.N)
    (U : W^{1,p}(Ω)) : ℝ^n → ℝ :=
  let V := SobolevSpace.GraphSpace.cutoffCLM
    (n := n) (p := p) (Ω := Ω) (hΩ.boundaryCutoff i) U
  let K := boundarySupport (n := n) (Ω := Ω) i
  let KT := boundarySupportInTarget (n := n) (Ω := Ω) i
  KT.indicator fun y ↦
    K.indicator (Ω.indicator (SobolevSpace.GraphSpace.baseRepresentative V))
      ((hΩ.chart i).symm y)

/-- Pointwise first-derivative representative used to certify the flattening
bundle. -/
def preparedFlattenDerivativeRepresentative
    (i : Fin hΩ.N)
    (U : W^{1,p}(Ω))
    (k : Fin n) : ℝ^n → ℝ :=
  let V := SobolevSpace.GraphSpace.cutoffCLM
    (n := n) (p := p) (Ω := Ω) (hΩ.boundaryCutoff i) U
  let K := boundarySupport (n := n) (Ω := Ω) i
  let KT := boundarySupportInTarget (n := n) (Ω := Ω) i
  KT.indicator fun y ↦ ∑ j : Fin n,
    flattenJacobianCoefficient (n := n) (Ω := Ω) i k j y *
      K.indicator
        (Ω.indicator fun x ↦
          ((V : SobolevSpace.GraphSpace.WkpAmbientOn n 1 p Ω)
            (SobolevSpace.GraphSpace.singleDerivIndex n j) x)) ((hΩ.chart i).symm y)

/-- The prepared flattening base representative is supported in the compact chart target. -/
theorem support_preparedFlattenBaseRepresentative_subset
    (i : Fin hΩ.N)
    (U : W^{1,p}(Ω)) :
    Function.support
        (preparedFlattenBaseRepresentative (n := n) (p := p) (Ω := Ω) i U) ⊆
      boundarySupportInTarget (n := n) (Ω := Ω) i := by
  intro y hy
  by_contra hyKT
  exact hy (by simp [preparedFlattenBaseRepresentative, hyKT])

/-- Each prepared flattening derivative is supported in the compact chart target. -/
theorem support_preparedFlattenDerivativeRepresentative_subset
    (i : Fin hΩ.N)
    (U : W^{1,p}(Ω))
    (k : Fin n) :
    Function.support
        (preparedFlattenDerivativeRepresentative
          (n := n) (p := p) (Ω := Ω) i U k) ⊆
      boundarySupportInTarget (n := n) (Ω := Ω) i := by
  intro y hy
  by_contra hyKT
  exact hy (by simp [preparedFlattenDerivativeRepresentative, hyKT])

/-- The base coordinate of the prepared flattening bundle has its explicit
representative almost everywhere. -/
theorem preparedFlattenAmbient_base_apply_ae
    (i : Fin hΩ.N)
    (U : W^{1,p}(Ω)) :
    ((preparedFlattenAmbient (n := n) (p := p) (Ω := Ω) i U
        (SobolevSpace.GraphSpace.baseIndex n 1) :
        SobolevSpace.GraphSpace.DerivLp n p (SobolevSpace.HalfSpace.upper n)) :
        ℝ^n → ℝ)
      =ᵐ[domainMeasure n (SobolevSpace.HalfSpace.upper n)]
        preparedFlattenBaseRepresentative (n := n) (p := p) (Ω := Ω) i U := by
  simpa [preparedFlattenAmbient_apply, flattenLpAt, preparedFlattenBaseRepresentative,
    SobolevSpace.GraphSpace.baseRepresentative] using flattenUpperLp_apply_ae i
      ((SobolevSpace.GraphSpace.cutoffCLM (hΩ.boundaryCutoff i) U :
        SobolevSpace.GraphSpace.WkpAmbientOn n 1 p Ω) (SobolevSpace.GraphSpace.baseIndex n 1))

/-- Each first-derivative coordinate of the prepared flattening bundle has its
explicit representative almost everywhere. -/
theorem preparedFlattenAmbient_derivative_apply_ae
    (i : Fin hΩ.N)
    (U : W^{1,p}(Ω))
    (k : Fin n) :
    ((preparedFlattenAmbient (n := n) (p := p) (Ω := Ω) i U
        (SobolevSpace.GraphSpace.singleDerivIndex n k) :
        SobolevSpace.GraphSpace.DerivLp n p (SobolevSpace.HalfSpace.upper n)) :
        ℝ^n → ℝ)
      =ᵐ[domainMeasure n (SobolevSpace.HalfSpace.upper n)]
        preparedFlattenDerivativeRepresentative
          (n := n) (p := p) (Ω := Ω) i U k := by
  simpa [preparedFlattenAmbient_apply, flattenLpAt, flattenFirstDerivativesLp,
    preparedFlattenDerivativeRepresentative] using flattenDerivativeUpperLp_apply_ae i k fun j ↦
      (SobolevSpace.GraphSpace.cutoffCLM (hΩ.boundaryCutoff i) U :
        SobolevSpace.GraphSpace.WkpAmbientOn n 1 p Ω) (SobolevSpace.GraphSpace.singleDerivIndex n j)

private theorem preparedFlatten_hasWeakDerivative
    (i : Fin hΩ.N)
    (U : W^{1,p}(Ω))
    (k : Fin n) :
    HasWeakDerivativeOn (n := n) (SobolevSpace.HalfSpace.upper n) [k]
      (preparedFlattenBaseRepresentative (n := n) (p := p) (Ω := Ω) i U)
      (preparedFlattenDerivativeRepresentative
        (n := n) (p := p) (Ω := Ω) i U k) := by
  classical
  let chartΩ := Boundary.C1ExtensionAtlas.Charts.chartOnΩ i
  let E := chartΩ.symm
  let K := boundarySupport i
  let KT := boundarySupportInTarget i
  let V := SobolevSpace.GraphSpace.cutoffCLM (hΩ.boundaryCutoff i) U
  let base : ℝ^n → ℝ := SobolevSpace.GraphSpace.baseRepresentative V
  let deriv : Fin n → ℝ^n → ℝ := fun j ↦
    (V : SobolevSpace.GraphSpace.WkpAmbientOn n 1 p Ω)
      (SobolevSpace.GraphSpace.singleDerivIndex n j)
  have htargetSub : E.target ⊆ Ω := fun x hx ↦ hx.2
  have hmeasureTarget : (domainMeasure n Ω).restrict E.target = domainMeasure n E.target := by
    simpa [domainMeasure] using
      Measure.restrict_restrict_of_subset (μ := (volume : Measure (ℝ^n))) htargetSub
  have hmemLp (v : SobolevSpace.GraphSpace.DerivLp n p Ω) :
      MemLp v p (domainMeasure n E.target) :=
    hmeasureTarget ▸ (Lp.memLp v).restrict E.target
  have hweakTarget (j : Fin n) : HasWeakDerivativeOn (n := n) E.target [j] base (deriv j) :=
    HasWeakDerivativeOn.mono (n := n) E.open_target.measurableSet htargetSub (by
      simpa [base, deriv, V, SobolevSpace.GraphSpace.baseRepresentative,
        SobolevSpace.GraphSpace.singleDerivIndex_toList] using
        V.property (SobolevSpace.GraphSpace.singleDerivIndex n j))
  have hchain : HasWeakDerivativeOn (n := n) E.source [k] (fun y ↦ base (E y))
      (fun y ↦ ∑ j : Fin n, deriv j (E y) * flattenJacobianCoefficient i k j y) := by
    simpa [flattenJacobianCoefficient, E, chartΩ, Boundary.C1ExtensionAtlas.Charts.chartOnΩ,
      partialDeriv] using
      WeakChangeOfVariables.hasWeakDerivativeOn_comp_partialHomeomorph_W1_of_memLp
        (Approximation.standardMollifier n) (E := E) (u := base) (du := deriv)
        (hΩ.chart_symm_contDiff i) (hΩ.chart_contDiff i)
        (hΩ.bounded.subset htargetSub).measure_lt_top.ne (hmemLp _) (fun _ ↦ hmemLp _)
        hweakTarget k
  have hcomp {f : ℝ^n → ℝ} (h : K.indicator f =ᵐ[domainMeasure n Ω] f) :
      K.indicator f ∘ E =ᵐ[domainMeasure n E.source] f ∘ E :=
    (WeakChangeOfVariables.quasiMeasurePreserving_partialHomeomorph (E := E)
      (hΩ.chart_symm_contDiff i) (hΩ.chart_contDiff i)).ae_eq_comp
      (hmeasureTarget ▸ ae_restrict_of_ae h)
  have hyK : ∀ y ∈ E.source, (E y ∈ K ↔ y ∈ KT) := fun y hy ↦
    ⟨fun hxK ↦ ⟨E y, hxK, (hΩ.chart i).right_inv hy.1⟩, by
      rintro ⟨x, hxK, rfl⟩
      simpa [E, chartΩ, Boundary.C1ExtensionAtlas.Charts.chartOnΩ,
        (hΩ.chart i).left_inv (boundarySupport_subset_source i hxK)] using hxK⟩
  have hbaseEq :
      (fun y ↦ base (E y)) =ᵐ[domainMeasure n E.source] preparedFlattenBaseRepresentative i U := by
    filter_upwards [hcomp (f := base) (by
        simpa [K, V, base, boundarySupport, SobolevSpace.GraphSpace.baseRepresentative] using
          SobolevSpace.GraphSpace.cutoffCLM_base_tsupport_indicator_ae (hΩ.boundaryCutoff i) U),
      ae_restrict_mem E.open_source.measurableSet] with y hybase hy
    change base (E y) = KT.indicator (fun z ↦ K.indicator (Ω.indicator base) (E z)) y
    by_cases hxK : E y ∈ K
    · rw [indicator_of_mem ((hyK y hy).1 hxK), indicator_of_mem hxK,
        indicator_of_mem (show E y ∈ Ω from hy.2)]
    · rw [indicator_of_notMem (mt (hyK y hy).2 hxK)]
      simpa [hxK] using hybase.symm
  have hderivEq : (fun y ↦ ∑ j : Fin n, deriv j (E y) * flattenJacobianCoefficient i k j y)
      =ᵐ[domainMeasure n E.source] preparedFlattenDerivativeRepresentative i U k := by
    filter_upwards [ae_all_iff.2 fun j ↦ hcomp (f := deriv j) (by
        simpa [K, V, deriv, boundarySupport] using
          SobolevSpace.GraphSpace.cutoffCLM_singleDeriv_tsupport_indicator_ae
            (hΩ.boundaryCutoff i) U j),
      ae_restrict_mem E.open_source.measurableSet] with y hyderiv hy
    change _ = KT.indicator (fun z ↦ ∑ j : Fin n,
      flattenJacobianCoefficient i k j z * K.indicator (Ω.indicator (deriv j)) (E z)) y
    by_cases hxK : E y ∈ K
    · rw [indicator_of_mem ((hyK y hy).1 hxK)]
      exact Finset.sum_congr rfl fun j _ ↦ by
        rw [indicator_of_mem hxK, indicator_of_mem (show E y ∈ Ω from hy.2), mul_comm]
    · have hxzero (j : Fin n) : deriv j (E y) = 0 := by simpa [hxK] using (hyderiv j).symm
      simp [indicator_of_notMem (mt (hyK y hy).2 hxK), hxzero]
  have hsource : E.source = (hΩ.chart i).target ∩ SobolevSpace.HalfSpace.upper n :=
    Boundary.C1ExtensionAtlas.Charts.chartOnΩ_target_eq_target_inter_upper i
  apply hasWeakDerivativeOn_of_inter_of_cutoff_one_nhds (n := n) (p := p)
    (V := (hΩ.chart i).target) (Ωbig := SobolevSpace.HalfSpace.upper n) (K := KT)
    (hΩ.chart i).open_target (SobolevSpace.HalfSpace.isOpen_upper (n := n))
    (support_preparedFlattenBaseRepresentative_subset i U)
    (support_preparedFlattenDerivativeRepresentative_subset i U k) (targetSupportCutoff i)
    (tsupport_targetSupportCutoff_subset_target i)
    (targetSupportCutoff_eq_one_nhds_on_boundarySupportInTarget i)
    ((memLp_congr_ae (preparedFlattenAmbient_base_apply_ae i U)).1 (Lp.memLp _))
    ((memLp_congr_ae (preparedFlattenAmbient_derivative_apply_ae i U k)).1 (Lp.memLp _))
  rw [← hsource]
  exact (hasWeakDerivativeOn_congr_ae (n := n) (hfg := hbaseEq) (hf'g' := hderivEq)).1 hchain

/-- The prepared flattening bundle satisfies all upper-half-space `W^{1,p}`
weak-derivative constraints. -/
theorem preparedFlattenAmbient_mapsIsWkpOn
    (i : Fin hΩ.N)
    (U : W^{1,p}(Ω)) :
    SobolevSpace.GraphSpace.IsWkpOn (n := n) (k := 1) (p := p)
      (Ω := SobolevSpace.HalfSpace.upper n)
      (preparedFlattenAmbient (n := n) (p := p) (Ω := Ω) i U) := by
  classical
  intro a
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨k, rfl⟩
  · simpa only [SobolevSpace.GraphSpace.baseIndex_toList] using
      hasWeakDerivativeOn_nil (memLp_locallyIntegrableOn_domain (Lp.memLp
        (preparedFlattenAmbient i U (SobolevSpace.GraphSpace.baseIndex n 1))) Fact.out)
  · simpa using (SobolevSpace.hasWeakDerivativeOn_congr_ae
      (preparedFlattenAmbient_base_apply_ae i U)
      (preparedFlattenAmbient_derivative_apply_ae i U k)).2
      (preparedFlatten_hasWeakDerivative i U k)

/-- Bounded flattening of the `i`-th localized boundary partition term into
the upper half-space. -/
noncomputable def flattenCLM (i : Fin hΩ.N) :
    W^{1,p}(Ω) →L[ℝ]
      W^{1,p}((SobolevSpace.HalfSpace.upper n)) :=
  ContinuousLinearMap.codRestrict
    (preparedFlattenAmbient (n := n) (p := p) (Ω := Ω) i)
    (SobolevSpace.GraphSpace.wkpSubmoduleOn n 1 p
      (SobolevSpace.HalfSpace.upper n))
    (preparedFlattenAmbient_mapsIsWkpOn (n := n) (p := p) (Ω := Ω) i)

/-- The underlying ambient bundle of `flattenCLM i U` is
`preparedFlattenAmbient i U`. -/
@[simp] theorem flattenCLM_apply_coe
    (i : Fin hΩ.N)
    (U : W^{1,p}(Ω)) :
    ((flattenCLM (n := n) (p := p) (Ω := Ω) i U :
        W^{1,p}((SobolevSpace.HalfSpace.upper n))) :
        SobolevSpace.GraphSpace.WkpAmbientOn n 1 p (SobolevSpace.HalfSpace.upper n)) =
      preparedFlattenAmbient (n := n) (p := p) (Ω := Ω) i U :=
  rfl

end BoundaryPiece

end C1

end Extension

end SobolevSpace
