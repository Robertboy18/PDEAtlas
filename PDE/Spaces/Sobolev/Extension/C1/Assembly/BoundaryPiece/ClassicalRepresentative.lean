/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.C1.Assembly.Flattening.Assembly
public import PDE.Spaces.Sobolev.Extension.C1.LocalPieces.BoundaryFlattening
import PDE.Spaces.Sobolev.Extension.C1.Assembly.BoundaryPiece.Agreement

/-!
# Classical representatives for a C¹ boundary piece

The boundary contribution of the `C¹` extension operator (Evans §5.4, Theorem 1) is built in two
parallel forms: as a bounded operator on graph-space elements (`BoundaryPiece.boundaryCLM`, which
`Assembly.Operator` sums with the interior piece), and as a construction on representative-level
Sobolev functions `SobolevSpaceOn n 1 p Ω`, which carry a chosen pointwise function together with
`L^p` weak derivatives. We give the second form for a single boundary chart `i`, and identify the
base coordinate of `flattenCLM` with its explicit representative.

Given `u` on `Ω` with representative `f`, the flattened base coordinate is
identified as the function `η · (ψᵢ f) ∘ Φᵢ⁻¹` on the whole upper half-space,
where `ψᵢ` is the partition function and `η` the target cutoff equal to one on
the flattened support.  The representative-level boundary piece is then the
reflected field of `LocalPieces.BoundaryFlattening`, relocalized by `η` and
pulled back through the chart, extended by zero outside the chart source.  Its
weak derivatives are the chain-rule expressions, and on `Ω` it agrees with
`ψᵢ u` almost everywhere.

## Main results

* `flattenCLM_base_eq_classical_ae`: the explicit representative of the
  flattened base coordinate on `ℝ^n₊`.
* `extension i u`: the global `W^{1,p}(ℝ^n)` element contributed by chart `i`,
  at the level of representatives.
* `extension_agree_ae`: on `Ω`, `extension i u = ψᵢ u` almost everywhere.

## Implementation notes

The weak-derivative identities for the pulled-back field are established
first on the chart source by the weak chain rule and then extended to `ℝ^n`
using a cutoff equal to one near the compact support of the field; this is why
the pulled-back function is defined as an indicator over the chart source.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.4, Theorem 1, pp. 268-271; the proof flattens the boundary
  near each boundary point (step 5, p. 270), extends across the flat boundary, and glues the pieces
  with a partition of unity (step 6, (9), p. 270).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

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

/-- For an input with classical representative `f`, the flattened base
coordinate is the compactly supported chart expression
`χᵢ · (ψᵢ f) ∘ chartᵢ⁻¹` on the whole upper half-space. -/
theorem flattenCLM_base_eq_classical_ae
    (i : Fin hΩ.N)
    (U : W^{1,p}(Ω))
    (f : ℝ^n → ℝ)
    (hU :
      ((((U : SobolevSpace.GraphSpace.WkpAmbientOn n 1 p Ω)
          (SobolevSpace.GraphSpace.baseIndex n 1) :
          SobolevSpace.GraphSpace.DerivLp n p Ω) : ℝ^n → ℝ)) =ᵐ[domainMeasure n Ω] f) :
    GraphSpace.baseRepresentative (n := n) (p := p)
        (flattenCLM (n := n) (p := p) (Ω := Ω) i U) =ᵐ[
      domainMeasure n (SobolevSpace.HalfSpace.upper n)]
      fun y ↦
        (targetSupportCutoff
          (n := n) (Ω := Ω) i).toFun y *
          (hΩ.boundaryCutoff i).toFun ((hΩ.chart i).symm y) *
          f ((hΩ.chart i).symm y) := by
  classical
  let upper := SobolevSpace.HalfSpace.upper n
  let chartΩ := Boundary.C1ExtensionAtlas.Charts.chartOnΩ (n := n) (Ω := Ω) i
  let A := chartΩ.target
  let E := chartΩ.symm
  let V := GraphSpace.cutoffCLM (n := n) (p := p) (Ω := Ω) (hΩ.boundaryCutoff i) U
  let baseV : ℝ^n → ℝ := (V : GraphSpace.WkpAmbientOn n 1 p Ω) (GraphSpace.baseIndex n 1)
  let flat : ℝ^n → ℝ := GraphSpace.baseRepresentative (flattenCLM (n := n) (p := p) (Ω := Ω) i U)
  let q : ℝ^n → ℝ := fun y ↦ (targetSupportCutoff (n := n) (Ω := Ω) i).toFun y *
    (hΩ.boundaryCutoff i).toFun ((hΩ.chart i).symm y) * f ((hΩ.chart i).symm y)
  have hAmeas : MeasurableSet A := chartΩ.open_target.measurableSet
  have hupper : ∀ᵐ y ∂domainMeasure n upper, y ∈ upper :=
    ae_restrict_mem (SobolevSpace.HalfSpace.isOpen_upper (n := n)).measurableSet
  have hA : ∀ y ∈ upper, y ∈ (hΩ.chart i).target → y ∈ A := fun y hyU hyT ↦ by
    simpa [A, chartΩ, Boundary.C1ExtensionAtlas.Charts.chartOnΩ_target_eq_target_inter_upper]
      using ⟨hyT, hyU⟩
  have htargetSub : E.target ⊆ Ω := fun x hx ↦ by
    have hx' : x ∈ chartΩ.source := by simpa [E] using hx
    simpa [chartΩ, Boundary.C1ExtensionAtlas.Charts.chartOnΩ_source] using hx'.2
  have hcut : baseV =ᵐ[domainMeasure n Ω] fun x ↦ (hΩ.boundaryCutoff i).toFun x * f x := by
    filter_upwards [GraphSpace.cutoffCLM_base_apply_ae (n := n) (p := p) (Ω := Ω)
      (hΩ.boundaryCutoff i) U, hU] with x hcx hux
    exact hcx.trans (congrArg _ hux)
  have hqmp : QuasiMeasurePreserving (fun y ↦ E y)
      (domainMeasure n E.source) (domainMeasure n E.target) :=
    WeakChangeOfVariables.quasiMeasurePreserving_partialHomeomorph (E := E)
      (by simpa [E, chartΩ, Boundary.C1ExtensionAtlas.Charts.chartOnΩ] using
        hΩ.chart_symm_contDiff i)
      (by simpa [E, chartΩ, Boundary.C1ExtensionAtlas.Charts.chartOnΩ] using
        hΩ.chart_contDiff i)
  -- on the chart target, `flat = baseV ∘ chart⁻¹ = ψᵢ f ∘ chart⁻¹`, and `η = 1` on `supp ψᵢ`
  have hlocal : flat =ᵐ[domainMeasure n A] q := by
    filter_upwards [flattenCLM_base_agree_ae (n := n) (p := p) (Ω := Ω) i U,
      hqmp.ae_eq_comp (ae_restrict_of_ae_restrict_of_subset htargetSub hcut),
      ae_restrict_mem E.open_source.measurableSet] with y hyflat hycut hySource
    have hyTarget : y ∈ (hΩ.chart i).target := by
      have hy' : y ∈ chartΩ.target := by simpa [E] using hySource
      simpa [chartΩ, Boundary.C1ExtensionAtlas.Charts.chartOnΩ_target_eq_target_inter_upper]
        using hy'.1
    change flat y = baseV (E y) at hyflat
    change baseV (E y) = (hΩ.boundaryCutoff i).toFun (E y) * f (E y) at hycut
    rw [hyflat, hycut, show E y = (hΩ.chart i).symm y from rfl]
    by_cases hψ : (hΩ.boundaryCutoff i).toFun ((hΩ.chart i).symm y) = 0
    · simp only [q, hψ, mul_zero, zero_mul]
    · simp only [q]
      rw [targetSupportCutoff_eq_one_on_boundarySupportInTarget (n := n) (Ω := Ω) i y
        ⟨_, subset_tsupport _ hψ, (hΩ.chart i).right_inv hyTarget⟩, one_mul]
  have hactual : flat =ᵐ[domainMeasure n upper]
      preparedFlattenBaseRepresentative (n := n) (p := p) (Ω := Ω) i U := by
    simpa [flat, GraphSpace.baseRepresentative, flattenCLM_apply_coe] using
      preparedFlattenAmbient_base_apply_ae (n := n) (p := p) (Ω := Ω) i U
  -- outside `A`, both `flat` and `q` vanish on the upper half-space
  have hflatSupport : A.indicator flat =ᵐ[domainMeasure n upper] flat := by
    filter_upwards [hactual, hupper] with y hyactual hyUpper
    by_cases hyA : y ∈ A
    · exact indicator_of_mem hyA _
    · have hyKT : y ∉ boundarySupportInTarget (n := n) (Ω := Ω) i := fun hy ↦
        hyA (hA y hyUpper (boundarySupportInTarget_subset_target (n := n) (Ω := Ω) i hy))
      rw [indicator_of_notMem hyA, hyactual]
      simp [preparedFlattenBaseRepresentative, hyKT]
  have hqSupport : A.indicator q =ᵐ[domainMeasure n upper] q := by
    filter_upwards [hupper] with y hyUpper
    by_cases hyA : y ∈ A
    · exact indicator_of_mem hyA _
    · have hηzero : (targetSupportCutoff (n := n) (Ω := Ω) i).toFun y = 0 := by
        by_contra hne
        exact hyA (hA y hyUpper (tsupport_targetSupportCutoff_subset_target (n := n) (Ω := Ω) i
          (subset_tsupport _ hne)))
      rw [indicator_of_notMem hyA]
      simp only [q, hηzero, zero_mul]
  have hind : A.indicator flat =ᵐ[domainMeasure n upper] A.indicator q :=
    (ae_eq_restrict_iff_indicator_ae_eq hAmeas).mp <| by
      rwa [Measure.restrict_restrict_of_subset
        (Boundary.C1ExtensionAtlas.Charts.chartOnΩ_target_subset_upper (n := n) (Ω := Ω) i)]
  exact hflatSupport.symm.trans (hind.trans hqSupport)

/-- The relocalized reflected boundary field pulled back through the chart and
extended by zero outside the chart source; this is the pointwise function of
the boundary piece `extension i u`. -/
def pulledFn (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) : ℝ^n → ℝ :=
  (hΩ.chart i).source.indicator fun x ↦
    (relocalizedReflectedBoundaryField
      (n := n) (p := p) (Ω := Ω) i u).toFun (hΩ.chart i x)

private theorem support_pulledFn_subset_pullbackSupport
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) :
    Function.support (pulledFn (n := n) (p := p) (Ω := Ω) i u) ⊆
      pullbackSupport (n := n) (Ω := Ω) i := by
  intro x hx
  by_cases hxS : x ∈ (hΩ.chart i).source
  · have htarget :
        (relocalizedReflectedBoundaryField
          (n := n) (p := p) (Ω := Ω) i u).toFun (hΩ.chart i x) ≠ 0 := by
      simpa [pulledFn, hxS] using hx
    have hK := support_relocalizedReflectedBoundaryField_subset_targetCutoffSupport
      (n := n) (p := p) (Ω := Ω) i u htarget
    exact ⟨hΩ.chart i x, hK, (hΩ.chart i).left_inv hxS⟩
  · exact False.elim (hx (by simp [pulledFn, hxS]))

/-- The pulled-back relocalized reflection lies in `Lp` on all of `ℝ^n`. -/
theorem pulledFn_memLp
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) :
    MeasureTheory.MemLp (pulledFn (n := n) (p := p) (Ω := Ω) i u) p
      (domainMeasure n (Set.univ : Set (ℝ^n))) := by
  have htargetLp : MemLp (relocalizedReflectedBoundaryField (n := n) (p := p) (Ω := Ω) i u).toFun
      p (domainMeasure n (hΩ.chart i).target) := by
    simpa [domainMeasure] using
      (relocalizedReflectedBoundaryField (n := n) (p := p) (Ω := Ω) i u).memLp.restrict
        (hΩ.chart i).target
  have hcomp := WeakChangeOfVariables.memLp_comp_partialHomeomorph_of_compact_support
    (E := hΩ.chart i) (hΩ.chart_contDiff i) (hΩ.chart_symm_contDiff i)
    (isCompact_targetCutoffSupport (n := n) (Ω := Ω) i)
    (targetCutoffSupport_subset_target (n := n) (Ω := Ω) i)
    (support_relocalizedReflectedBoundaryField_subset_targetCutoffSupport
      (n := n) (p := p) (Ω := Ω) i u) htargetLp
  rw [pulledFn, memLp_indicator_iff_restrict
    (hΩ.chart i).open_source.measurableSet.nullMeasurableSet]
  simpa [domainMeasure] using hcomp

/-- The chain-rule candidate for the `k`th weak derivative of the pulled-back relocalized
reflection, built from the derivative representatives `dR` on the chart target. -/
def pulledDerivativeFn
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) (dR : Fin n → ℝ^n → ℝ)
    (k : Fin n) : ℝ^n → ℝ :=
  (hΩ.chart i).source.indicator fun x ↦ ∑ j : Fin n,
    relocalizedReflectedBoundaryDerivativeRepresentative
        (n := n) (p := p) (Ω := Ω) i u j (dR j) (hΩ.chart i x) *
      ((fderiv ℝ (fun z ↦ hΩ.chart i z) x)
        (EuclideanSpace.single k (1 : ℝ))) j

private theorem support_pulledDerivativeFn_subset_pullbackSupport
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) (dR : Fin n → ℝ^n → ℝ)
    (k : Fin n) :
    Function.support (pulledDerivativeFn (n := n) (p := p) (Ω := Ω) i u dR k) ⊆
      pullbackSupport (n := n) (Ω := Ω) i := by
  intro x hx
  by_cases hxS : x ∈ (hΩ.chart i).source
  · by_contra hxK
    have htargetNotK : hΩ.chart i x ∉
        targetCutoffSupport (n := n) (Ω := Ω) i := by
      intro htargetK
      exact hxK ⟨hΩ.chart i x, htargetK, (hΩ.chart i).left_inv hxS⟩
    have hzero : ∀ j : Fin n,
        relocalizedReflectedBoundaryDerivativeRepresentative
          (n := n) (p := p) (Ω := Ω) i u j (dR j) (hΩ.chart i x) = 0 := by
      intro j
      by_contra hne
      exact htargetNotK
        (support_relocalizedReflectedBoundaryDerivativeRepresentative_subset
          (n := n) (p := p) (Ω := Ω) i u j (dR j) hne)
    apply hx
    simp [pulledDerivativeFn, hxS, hzero]
  · exact False.elim (hx (by simp [pulledDerivativeFn, hxS]))

/-- The pulled-back derivative candidate lies in `Lp` on all of `ℝ^n`. -/
theorem pulledDerivativeFn_memLp
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) (dR : Fin n → ℝ^n → ℝ)
    (hdRLp : ∀ j, MeasureTheory.MemLp (dR j) p
      (domainMeasure n (Set.univ : Set (ℝ^n)))) (k : Fin n) :
    MeasureTheory.MemLp
      (pulledDerivativeFn (n := n) (p := p) (Ω := Ω) i u dR k) p
      (domainMeasure n (Set.univ : Set (ℝ^n))) := by
  let q : Fin n → ℝ^n → ℝ := fun j ↦
    relocalizedReflectedBoundaryDerivativeRepresentative (n := n) (p := p) (Ω := Ω) i u j (dR j)
  have hterm (j : Fin n) : MemLp ((hΩ.chart i).source.indicator fun x ↦ q j (hΩ.chart i x) *
      ((fderiv ℝ (fun z ↦ hΩ.chart i z) x) (EuclideanSpace.single k (1 : ℝ))) j) p
      (domainMeasure n (Set.univ : Set (ℝ^n))) := by
    have hqTarget : MemLp (q j) p (domainMeasure n (hΩ.chart i).target) := by
      simpa [q, domainMeasure] using (relocalizedReflectedBoundaryDerivativeRepresentative_memLp
        (n := n) (p := p) (Ω := Ω) i u j (hdRLp j)).restrict (hΩ.chart i).target
    refine memLp_indicator_mul_continuous_of_support_within
      (hΩ.chart i).open_source.measurableSet (isCompact_pullbackSupport (n := n) (Ω := Ω) i)
      (WeakChangeOfVariables.memLp_comp_partialHomeomorph_of_compact_support
        (E := hΩ.chart i) (hΩ.chart_contDiff i) (hΩ.chart_symm_contDiff i)
        (isCompact_targetCutoffSupport (n := n) (Ω := Ω) i)
        (targetCutoffSupport_subset_target (n := n) (Ω := Ω) i)
        (support_relocalizedReflectedBoundaryDerivativeRepresentative_subset
          (n := n) (p := p) (Ω := Ω) i u j (dR j)) hqTarget)
      (fun x hxS hne ↦ ⟨hΩ.chart i x,
        support_relocalizedReflectedBoundaryDerivativeRepresentative_subset
          (n := n) (p := p) (Ω := Ω) i u j (dR j) hne, (hΩ.chart i).left_inv hxS⟩) ?_
    exact (EuclideanSpace.proj j).continuous.comp
      (((hΩ.chart_contDiff i).continuous_fderiv one_ne_zero).clm_apply continuous_const)
  convert memLp_finsetSum' Finset.univ fun j _ ↦ hterm j using 1
  ext x
  by_cases hxS : x ∈ (hΩ.chart i).source <;> simp [pulledDerivativeFn, q, hxS]

/-- The pulled-back derivative candidate is the `k`th weak derivative of the pulled-back
relocalized reflection on all of `ℝ^n`. -/
theorem pulled_hasWeakDerivative
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) (dR : Fin n → ℝ^n → ℝ)
    (hdRLp : ∀ j, MeasureTheory.MemLp (dR j) p
      (domainMeasure n (Set.univ : Set (ℝ^n))))
    (hdRWeak : ∀ j, HasWeakDerivativeOn (n := n) (Set.univ : Set (ℝ^n)) [j]
      (reflectedBoundaryField (n := n) (p := p) (Ω := Ω) i u).toFun (dR j))
    (k : Fin n) :
    HasWeakDerivativeOn (n := n) (Set.univ : Set (ℝ^n)) [k]
      (pulledFn (n := n) (p := p) (Ω := Ω) i u)
      (pulledDerivativeFn (n := n) (p := p) (Ω := Ω) i u dR k) := by
  let q : Fin n → ℝ^n → ℝ := fun j ↦
    relocalizedReflectedBoundaryDerivativeRepresentative (n := n) (p := p) (Ω := Ω) i u j (dR j)
  -- the relocalized field and its derivatives on the chart target
  have hqTargetLp (j : Fin n) : MemLp (q j) p (domainMeasure n (hΩ.chart i).target) := by
    simpa [domainMeasure] using (relocalizedReflectedBoundaryDerivativeRepresentative_memLp
      (n := n) (p := p) (Ω := Ω) i u j (hdRLp j)).restrict (hΩ.chart i).target
  have hqTargetWeak (j : Fin n) : HasWeakDerivativeOn (n := n) (hΩ.chart i).target [j]
      (relocalizedReflectedBoundaryField (n := n) (p := p) (Ω := Ω) i u).toFun (q j) :=
    (hasWeakDerivativeOn_mul_testFunction_first (Ω := (Set.univ : Set (ℝ^n)))
      (reflectedBoundaryField (n := n) (p := p) (Ω := Ω) i u).memLp (hdRLp j) (hdRWeak j)
      (targetSupportCutoff (n := n) (Ω := Ω) i)).mono (hΩ.chart i).open_target.measurableSet
      (subset_univ _)
  have htargetLp : MemLp (relocalizedReflectedBoundaryField (n := n) (p := p) (Ω := Ω) i u).toFun
      p (domainMeasure n (hΩ.chart i).target) := by
    simpa [domainMeasure] using
      (relocalizedReflectedBoundaryField (n := n) (p := p) (Ω := Ω) i u).memLp.restrict
        (hΩ.chart i).target
  -- the weak chain rule on the chart source
  have hchain : HasWeakDerivativeOn (n := n) (hΩ.chart i).source [k]
      (fun x ↦ (relocalizedReflectedBoundaryField (n := n) (p := p) (Ω := Ω) i u).toFun
        (hΩ.chart i x))
      (fun x ↦ ∑ j : Fin n, q j (hΩ.chart i x) *
        ((fderiv ℝ (fun z ↦ hΩ.chart i z) x) (EuclideanSpace.single k (1 : ℝ))) j) := by
    simpa [partialDeriv] using
      WeakChangeOfVariables.hasWeakDerivativeOn_comp_partialHomeomorph_W1_of_memLp
        (Approximation.standardMollifier n) (E := hΩ.chart i) (hΩ.chart_contDiff i)
        (hΩ.chart_symm_contDiff i) (hΩ.chart_target_bounded i).measure_lt_top.ne htargetLp
        hqTargetLp hqTargetWeak k
  have hweakSource : HasWeakDerivativeOn (n := n) (hΩ.chart i).source [k]
      (pulledFn (n := n) (p := p) (Ω := Ω) i u)
      (pulledDerivativeFn (n := n) (p := p) (Ω := Ω) i u dR k) :=
    (hasWeakDerivativeOn_congr_ae
      (ae_restrict_of_forall_mem (hΩ.chart i).open_source.measurableSet fun x hx ↦ by
        simp [pulledFn, hx])
      (ae_restrict_of_forall_mem (hΩ.chart i).open_source.measurableSet fun x hx ↦ by
        simp [pulledDerivativeFn, q, hx])).1 hchain
  exact hasWeakDerivativeOn_univ_of_support_subset_of_cutoff_one_nhds
    (hΩ.chart i).open_source (pullbackSupport_subset_source (n := n) (Ω := Ω) i)
    (support_pulledFn_subset_pullbackSupport (n := n) (p := p) (Ω := Ω) i u)
    (support_pulledDerivativeFn_subset_pullbackSupport (n := n) (p := p) (Ω := Ω) i u dR k)
    (pullbackSupportCutoff (n := n) (Ω := Ω) i)
    (tsupport_pullbackSupportCutoff_subset_source (n := n) (Ω := Ω) i)
    (pullbackSupportCutoff_eq_one_nhds_on_pullbackSupport (n := n) (Ω := Ω) i) hweakSource

/-- The `i`-th boundary chart contributes a global `W^{1,p}(ℝ^n)` extension piece. -/
noncomputable def extension (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) :
    _root_.SobolevSpace.GlobalSobolevSpace n 1 p := by
  classical
  choose dR hdRLp hdRWeak using fun j : Fin n ↦
    (reflectedBoundaryField
      (n := n) (p := p) (Ω := Ω) i u).weak_derivs_inLp [j] (by simp)
  refine
    { toFun := pulledFn (n := n) (p := p) (Ω := Ω) i u
      memLp := pulledFn_memLp (n := n) (p := p) (Ω := Ω) i u
      weak_derivs_inLp := ?_ }
  intro α hα
  have hshape : α = [] ∨ ∃ k : Fin n, α = [k] := by
    cases α with
    | nil => exact Or.inl rfl
    | cons k rest =>
        cases rest with
        | nil => exact Or.inr ⟨k, rfl⟩
        | cons l tail => simp at hα
  rcases hshape with rfl | ⟨k, rfl⟩
  · have hLp := pulledFn_memLp (n := n) (p := p) (Ω := Ω) i u
    refine ⟨pulledFn (n := n) (p := p) (Ω := Ω) i u, hLp, ?_⟩
    have hloc := memLp_locallyIntegrableOn_domain hLp (Fact.out : (1 : ℝ≥0∞) ≤ p)
    exact hasWeakDerivativeOn_nil hloc
  · refine ⟨pulledDerivativeFn (n := n) (p := p) (Ω := Ω) i u dR k, ?_, ?_⟩
    · exact pulledDerivativeFn_memLp (n := n) (p := p) (Ω := Ω) i u dR hdRLp k
    · exact pulled_hasWeakDerivative
        (n := n) (p := p) (Ω := Ω) i u dR hdRLp hdRWeak k

/-- On the original domain, the global boundary-chart extension agrees almost everywhere with
the partition term `ψᵢu`. -/
theorem extension_agree_ae
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) :
    ∀ᵐ x ∂ domainMeasure n Ω,
      (extension (n := n) (p := p) (Ω := Ω) i u).toFun x =
        (hΩ.boundaryCutoff i).toFun x * u.toFun x := by
  let E := Boundary.C1ExtensionAtlas.Charts.chartOnΩ (n := n) (Ω := Ω) i
  -- on the flattened target, the reflected field is the upper-half-space field
  have hRTarget : (reflectedBoundaryField (n := n) (p := p) (Ω := Ω) i u).toFun
      =ᵐ[domainMeasure n E.target]
        (upperHalfSpaceBoundaryField (n := n) (p := p) (Ω := Ω) i u).toFun := by
    have h := ae_restrict_of_ae (s := (hΩ.chart i).target)
      (reflectedBoundaryField_agree_ae_upperHalfSpace (n := n) (p := p) (Ω := Ω) i u)
    rwa [Measure.restrict_restrict (hΩ.chart i).open_target.measurableSet,
      ← Boundary.C1ExtensionAtlas.Charts.chartOnΩ_target_eq_target_inter_upper] at h
  have hqmp : QuasiMeasurePreserving (fun x ↦ E x)
      (domainMeasure n E.source) (domainMeasure n E.target) :=
    WeakChangeOfVariables.quasiMeasurePreserving_partialHomeomorph (E := E)
      (by simpa [E, Boundary.C1ExtensionAtlas.Charts.chartOnΩ] using hΩ.chart_contDiff i)
      (by simpa [E, Boundary.C1ExtensionAtlas.Charts.chartOnΩ] using hΩ.chart_symm_contDiff i)
  have hinside : ∀ᵐ x ∂ domainMeasure n E.source,
      (pulledFn (n := n) (p := p) (Ω := Ω) i u) x =
        (hΩ.boundaryCutoff i).toFun x * u.toFun x := by
    filter_upwards [hqmp.ae_eq_comp hRTarget, ae_restrict_mem E.open_source.measurableSet] with
      x hxR hxSource
    have hxS : x ∈ (hΩ.chart i).source := by
      simpa [E, Boundary.C1ExtensionAtlas.Charts.chartOnΩ_source] using hxSource.1
    have hxR' : (reflectedBoundaryField (n := n) (p := p) (Ω := Ω) i u).toFun (hΩ.chart i x) =
        (hΩ.boundaryCutoff i).toFun x * u.toFun x := by
      refine hxR.trans ?_
      change upperHalfSpaceBoundaryRepresentative (n := n) (p := p) (Ω := Ω) i u
        (hΩ.chart i x) = _
      simp [upperHalfSpaceBoundaryRepresentative, flattenedBoundaryRepresentative,
        localizedBoundaryRepresentative, (hΩ.chart i).map_source hxS, (hΩ.chart i).left_inv hxS]
    rw [pulledFn, indicator_of_mem hxS, relocalizedReflectedBoundaryField_apply, hxR']
    by_cases hψ : (hΩ.boundaryCutoff i).toFun x = 0
    · simp only [hψ, zero_mul, mul_zero]
    · rw [targetSupportCutoff_eq_one_on_boundarySupportInTarget (n := n) (Ω := Ω) i _
        ⟨x, subset_tsupport _ hψ, rfl⟩, one_mul]
  have hmeasureInside : (domainMeasure n Ω).restrict (hΩ.chart i).source =
      domainMeasure n E.source := by
    rw [domainMeasure, Measure.restrict_restrict (hΩ.chart i).open_source.measurableSet]
    simp [E, inter_comm]
  have houtside : ∀ᵐ x ∂ (domainMeasure n Ω).restrict (hΩ.chart i).sourceᶜ,
      (pulledFn (n := n) (p := p) (Ω := Ω) i u) x =
        (hΩ.boundaryCutoff i).toFun x * u.toFun x := by
    refine ae_restrict_of_forall_mem (hΩ.chart i).open_source.measurableSet.compl fun x hx ↦ ?_
    have hψzero : (hΩ.boundaryCutoff i).toFun x = 0 := by
      by_contra hne
      exact hx (hΩ.boundaryCutoff_support i (subset_tsupport _ hne))
    simp [pulledFn, show x ∉ (hΩ.chart i).source from hx, hψzero]
  simpa [extension] using
    ae_of_ae_restrict_of_ae_restrict_compl _ (hmeasureInside ▸ hinside) houtside

omit [Fact (1 ≤ p)] in
/-- The flattened representative is the cutoff-weighted function in chart coordinates. -/
@[simp] theorem flattenedBoundaryRepresentative_apply
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) (y : ℝ^n) :
    flattenedBoundaryRepresentative (n := n) (p := p) (Ω := Ω) i u y =
      (hΩ.boundaryCutoff i).toFun ((hΩ.chart i).symm y) * u.toFun ((hΩ.chart i).symm y) :=
  rfl

end BoundaryPiece

end C1

end Extension

end SobolevSpace
