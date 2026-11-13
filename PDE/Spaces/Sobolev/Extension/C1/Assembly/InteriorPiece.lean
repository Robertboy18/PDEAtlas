/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.Lp.ZeroExtension
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Cutoff
public import PDE.Spaces.Sobolev.Boundary.Atlas.Definitions
import PDE.Spaces.Sobolev.Boundary.Atlas.Cutoffs
import PDE.Spaces.Sobolev.Localization.Cutoff.CompactSupport

/-!
# Interior contribution for C¹ extension

In the partition-of-unity proof of the extension theorem (Evans §5.4, Theorem 1), the term `ψ₀ u`
carried by the interior partition function needs no straightening: `ψ₀` has compact support inside
`Ω`, so `ψ₀ u` extended by zero is already a Sobolev function on `ℝ^n`, with weak derivatives the
zero extensions of the weak derivatives of `ψ₀ u`. We prove that statement for graph-space elements
and bundle it as a bounded operator `InteriorAssembly.extensionCLM : W^{1,p}(Ω) → W^{1,p}(ℝ^n)`.

The weak-derivative identity on `ℝ^n` is obtained from the identity on `Ω` by a
cutoff argument: a smooth function equal to one on a neighbourhood of the
compact set `interiorSupport = supp ψ₀` and supported in `Ω` lets test functions
on `ℝ^n` be replaced by test functions on `Ω`.

## Main definitions and results

* `zeroAmbient`: coordinatewise zero extension `L^p(Ω) → L^p(ℝ^n)` on the
  ambient derivative bundle, with `zeroAmbient_apply`.
* `preparedAmbient`: multiply by `ψ₀` and zero-extend every coordinate, with
  `preparedAmbient_apply`.
* `extensionCLM`: the bounded interior contribution into `W^{1,p}(ℝ^n)`, with
  `extensionCLM_apply_coe`.
* `extensionCLM_agree_ae`: on `Ω`, the base coordinate of the interior
  contribution is `ψ₀ u` almost everywhere.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.4, Theorem 1, pp. 268-271; in step 6, p. 270, the interior
  term is `ζ₀ ū₀` with `ū₀ = u` and `W₀ ⊂⊂ U`.
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

namespace InteriorAssembly

variable [Fact (0 < n)] [Fact (1 ≤ p)] [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- Coordinatewise zero extension on the ambient derivative bundle. -/
noncomputable def zeroAmbient :
    SobolevSpace.GraphSpace.WkpAmbientOn n 1 p Ω →L[ℝ]
      SobolevSpace.GraphSpace.WkpAmbientOn n 1 p (Set.univ : Set (ℝ^n)) := by
  classical
  let e := PiLp.continuousLinearEquiv (𝕜 := ℝ) (p := p)
    (β := fun _ : SobolevSpace.GraphSpace.DerivIndex n 1 ↦
      SobolevSpace.GraphSpace.DerivLp n p (Set.univ : Set (ℝ^n)))
  exact e.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun a ↦
      (SobolevSpace.Extension.Lp.zeroExtendLp
        (n := n) (p := p) (Ω := Ω) hΩ.isOpen.measurableSet).comp
        (PiLp.proj (𝕜 := ℝ) (p := p)
          (β := fun _ : SobolevSpace.GraphSpace.DerivIndex n 1 ↦
            SobolevSpace.GraphSpace.DerivLp n p Ω) a))

/-- Each coordinate of `zeroAmbient U` is the zero extension of the
corresponding coordinate of `U`. -/
@[simp] theorem zeroAmbient_apply
    (U : SobolevSpace.GraphSpace.WkpAmbientOn n 1 p Ω)
    (a : SobolevSpace.GraphSpace.DerivIndex n 1) :
    zeroAmbient (n := n) (p := p) (Ω := Ω) U a =
      SobolevSpace.Extension.Lp.zeroExtendLp
        (n := n) (p := p) (Ω := Ω) hΩ.isOpen.measurableSet (U a) := by
  classical
  simp [zeroAmbient]

/-- Cut off by the interior partition function and zero-extend all derivative
coordinates. -/
noncomputable def preparedAmbient :
    W^{1,p}(Ω) →L[ℝ]
      SobolevSpace.GraphSpace.WkpAmbientOn n 1 p (Set.univ : Set (ℝ^n)) :=
  (zeroAmbient (n := n) (p := p) (Ω := Ω)).comp
    ((Submodule.subtypeL (SobolevSpace.GraphSpace.wkpSubmoduleOn n 1 p Ω)).comp
      (SobolevSpace.GraphSpace.cutoffCLM
        (n := n) (p := p) (Ω := Ω) hΩ.interiorCutoff))

/-- Each coordinate of `preparedAmbient U` is the zero extension of the
corresponding coordinate of the cutoff field `ψ₀ U`. -/
@[simp] theorem preparedAmbient_apply
    (U : W^{1,p}(Ω))
    (a : SobolevSpace.GraphSpace.DerivIndex n 1) :
    preparedAmbient (n := n) (p := p) (Ω := Ω) U a =
      SobolevSpace.Extension.Lp.zeroExtendLp
        (n := n) (p := p) (Ω := Ω) hΩ.isOpen.measurableSet
        ((((SobolevSpace.GraphSpace.cutoffCLM
          (n := n) (p := p) (Ω := Ω) hΩ.interiorCutoff) U :
          W^{1,p}(Ω)) :
          SobolevSpace.GraphSpace.WkpAmbientOn n 1 p Ω) a) := by
  rfl

private def preparedInteriorBaseFn
    (U : W^{1,p}(Ω)) : ℝ^n → ℝ :=
  let V := SobolevSpace.GraphSpace.cutoffCLM
    (n := n) (p := p) (Ω := Ω) hΩ.interiorCutoff U
  (interiorSupport (n := n) (Ω := Ω)).indicator
    (SobolevSpace.GraphSpace.baseRepresentative V)

private def preparedInteriorDerivativeFn
    (U : W^{1,p}(Ω))
    (i : Fin n) : ℝ^n → ℝ :=
  let V := SobolevSpace.GraphSpace.cutoffCLM
    (n := n) (p := p) (Ω := Ω) hΩ.interiorCutoff U
  (interiorSupport (n := n) (Ω := Ω)).indicator
    (fun x ↦
      ((V : SobolevSpace.GraphSpace.WkpAmbientOn n 1 p Ω)
        (SobolevSpace.GraphSpace.singleDerivIndex n i) x))

private theorem support_preparedInteriorBaseFn_subset
    (U : W^{1,p}(Ω)) :
    Function.support
        (preparedInteriorBaseFn (n := n) (p := p) (Ω := Ω) U) ⊆
      interiorSupport (n := n) (Ω := Ω) := by
  intro x hx
  by_contra hxK
  exact hx (by simp [preparedInteriorBaseFn, hxK])

private theorem support_preparedInteriorDerivativeFn_subset
    (U : W^{1,p}(Ω)) (i : Fin n) :
    Function.support
        (preparedInteriorDerivativeFn (n := n) (p := p) (Ω := Ω) U i) ⊆
      interiorSupport (n := n) (Ω := Ω) := by
  intro x hx
  by_contra hxK
  exact hx (by simp [preparedInteriorDerivativeFn, hxK])

private theorem preparedAmbient_base_coeFn
    (U : W^{1,p}(Ω)) :
    ((preparedAmbient (n := n) (p := p) (Ω := Ω) U
        (SobolevSpace.GraphSpace.baseIndex n 1) :
        SobolevSpace.GraphSpace.DerivLp n p (Set.univ : Set (ℝ^n))) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (Set.univ : Set (ℝ^n))]
        preparedInteriorBaseFn (n := n) (p := p) (Ω := Ω) U := by
  let V := SobolevSpace.GraphSpace.cutoffCLM
    (n := n) (p := p) (Ω := Ω) hΩ.interiorCutoff U
  let K0 := interiorSupport (n := n) (Ω := Ω)
  let v : SobolevSpace.GraphSpace.DerivLp n p Ω :=
    (V : SobolevSpace.GraphSpace.WkpAmbientOn n 1 p Ω)
      (SobolevSpace.GraphSpace.baseIndex n 1)
  have hzero := SobolevSpace.Extension.Lp.zeroExtendLp_apply_ae
    (n := n) (p := p) (Ω := Ω) hΩ.isOpen.measurableSet v
  have hsupport : K0.indicator (fun x ↦ v x) =ᵐ[domainMeasure n Ω]
      fun x ↦ v x := by
    simpa [K0, V, v, interiorSupport] using
      SobolevSpace.GraphSpace.cutoffCLM_base_tsupport_indicator_ae
        (n := n) (p := p) (Ω := Ω) hΩ.interiorCutoff U
  have hindicator : Ω.indicator (K0.indicator fun x ↦ v x)
      =ᵐ[(MeasureTheory.volume : Measure (ℝ^n))]
        Ω.indicator (fun x ↦ v x) :=
    (ae_eq_restrict_iff_indicator_ae_eq
      hΩ.isOpen.measurableSet).1 (by simpa [domainMeasure] using hsupport)
  have hKsub := interiorSupport_subset_domain (n := n) (Ω := Ω)
  have hglobal : Ω.indicator (fun x ↦ v x)
      =ᵐ[(MeasureTheory.volume : Measure (ℝ^n))]
        K0.indicator (fun x ↦ v x) := by
    have hleft : Ω.indicator (K0.indicator fun x ↦ v x) =
        K0.indicator (fun x ↦ v x) := by
      funext x
      by_cases hxK : x ∈ K0
      · have hxΩ := hKsub hxK
        simp [hxK, hxΩ]
      · simp [hxK]
    simpa [hleft] using hindicator.symm
  have hzero' :
      ((SobolevSpace.Extension.Lp.zeroExtendLp
        (n := n) (p := p) (Ω := Ω) hΩ.isOpen.measurableSet v :
        SobolevSpace.GraphSpace.DerivLp n p (Set.univ : Set (ℝ^n))) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n (Set.univ : Set (ℝ^n))]
          Ω.indicator (fun x ↦ v x) := by
    simpa [SobolevSpace.Extension.Lp.extensionByZero] using hzero
  have hglobal' : Ω.indicator (fun x ↦ v x)
      =ᵐ[domainMeasure n (Set.univ : Set (ℝ^n))]
        K0.indicator (fun x ↦ v x) := by
    simpa [domainMeasure] using hglobal
  simpa [preparedAmbient_apply, preparedInteriorBaseFn,
    SobolevSpace.GraphSpace.baseRepresentative, V, v, K0, domainMeasure] using
    hzero'.trans hglobal'

private theorem preparedAmbient_derivative_coeFn
    (U : W^{1,p}(Ω)) (i : Fin n) :
    ((preparedAmbient (n := n) (p := p) (Ω := Ω) U
        (SobolevSpace.GraphSpace.singleDerivIndex n i) :
        SobolevSpace.GraphSpace.DerivLp n p (Set.univ : Set (ℝ^n))) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (Set.univ : Set (ℝ^n))]
        preparedInteriorDerivativeFn (n := n) (p := p) (Ω := Ω) U i := by
  let V := SobolevSpace.GraphSpace.cutoffCLM
    (n := n) (p := p) (Ω := Ω) hΩ.interiorCutoff U
  let K0 := interiorSupport (n := n) (Ω := Ω)
  let v : SobolevSpace.GraphSpace.DerivLp n p Ω :=
    (V : SobolevSpace.GraphSpace.WkpAmbientOn n 1 p Ω)
      (SobolevSpace.GraphSpace.singleDerivIndex n i)
  have hzero := SobolevSpace.Extension.Lp.zeroExtendLp_apply_ae
    (n := n) (p := p) (Ω := Ω) hΩ.isOpen.measurableSet v
  have hsupport : K0.indicator (fun x ↦ v x) =ᵐ[domainMeasure n Ω]
      fun x ↦ v x := by
    simpa [K0, V, v, interiorSupport] using
      SobolevSpace.GraphSpace.cutoffCLM_singleDeriv_tsupport_indicator_ae
        (n := n) (p := p) (Ω := Ω) hΩ.interiorCutoff U i
  have hindicator : Ω.indicator (K0.indicator fun x ↦ v x)
      =ᵐ[(MeasureTheory.volume : Measure (ℝ^n))]
        Ω.indicator (fun x ↦ v x) :=
    (ae_eq_restrict_iff_indicator_ae_eq
      hΩ.isOpen.measurableSet).1 (by simpa [domainMeasure] using hsupport)
  have hKsub := interiorSupport_subset_domain (n := n) (Ω := Ω)
  have hglobal : Ω.indicator (fun x ↦ v x)
      =ᵐ[(MeasureTheory.volume : Measure (ℝ^n))]
        K0.indicator (fun x ↦ v x) := by
    have hleft : Ω.indicator (K0.indicator fun x ↦ v x) =
        K0.indicator (fun x ↦ v x) := by
      funext x
      by_cases hxK : x ∈ K0
      · have hxΩ := hKsub hxK
        simp [hxK, hxΩ]
      · simp [hxK]
    simpa [hleft] using hindicator.symm
  have hzero' :
      ((SobolevSpace.Extension.Lp.zeroExtendLp
        (n := n) (p := p) (Ω := Ω) hΩ.isOpen.measurableSet v :
        SobolevSpace.GraphSpace.DerivLp n p (Set.univ : Set (ℝ^n))) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n (Set.univ : Set (ℝ^n))]
          Ω.indicator (fun x ↦ v x) := by
    simpa [SobolevSpace.Extension.Lp.extensionByZero] using hzero
  have hglobal' : Ω.indicator (fun x ↦ v x)
      =ᵐ[domainMeasure n (Set.univ : Set (ℝ^n))]
        K0.indicator (fun x ↦ v x) := by
    simpa [domainMeasure] using hglobal
  simpa [preparedAmbient_apply, preparedInteriorDerivativeFn,
    V, v, K0, domainMeasure] using
    hzero'.trans hglobal'

private theorem prepared_hasWeakDerivative
    (U : W^{1,p}(Ω)) (i : Fin n) :
    HasWeakDerivativeOn (n := n) (Set.univ : Set (ℝ^n)) [i]
      (preparedInteriorBaseFn (n := n) (p := p) (Ω := Ω) U)
      (preparedInteriorDerivativeFn (n := n) (p := p) (Ω := Ω) U i) := by
  let V := SobolevSpace.GraphSpace.cutoffCLM
    (n := n) (p := p) (Ω := Ω) hΩ.interiorCutoff U
  let K0 := interiorSupport (n := n) (Ω := Ω)
  let base : ℝ^n → ℝ :=
    SobolevSpace.GraphSpace.baseRepresentative V
  let deriv : ℝ^n → ℝ :=
    (V : SobolevSpace.GraphSpace.WkpAmbientOn n 1 p Ω)
      (SobolevSpace.GraphSpace.singleDerivIndex n i)
  have hweak : HasWeakDerivativeOn (n := n) Ω [i] base deriv := by
    simpa [base, deriv, V, SobolevSpace.GraphSpace.baseRepresentative,
      SobolevSpace.GraphSpace.singleDerivIndex_toList] using
      V.property (SobolevSpace.GraphSpace.singleDerivIndex n i)
  have hbaseSupport : K0.indicator base =ᵐ[domainMeasure n Ω] base := by
    simpa [K0, base, V, interiorSupport,
      SobolevSpace.GraphSpace.baseRepresentative] using
      SobolevSpace.GraphSpace.cutoffCLM_base_tsupport_indicator_ae
        (n := n) (p := p) (Ω := Ω) hΩ.interiorCutoff U
  have hderivSupport : K0.indicator deriv =ᵐ[domainMeasure n Ω] deriv := by
    simpa [K0, deriv, V, interiorSupport] using
      SobolevSpace.GraphSpace.cutoffCLM_singleDeriv_tsupport_indicator_ae
        (n := n) (p := p) (Ω := Ω) hΩ.interiorCutoff U i
  have hweakK : HasWeakDerivativeOn (n := n) Ω [i]
      (K0.indicator base) (K0.indicator deriv) :=
    ((SobolevSpace.hasWeakDerivativeOn_congr_ae
      (n := n) (hfg := hbaseSupport) (hf'g' := hderivSupport)).2 hweak)
  exact hasWeakDerivativeOn_univ_of_support_subset_of_cutoff_one_nhds
    (n := n) (U := Ω) (K := K0) hΩ.isOpen
    (interiorSupport_subset_domain (n := n) (Ω := Ω))
    (support_preparedInteriorBaseFn_subset
      (n := n) (p := p) (Ω := Ω) U)
    (support_preparedInteriorDerivativeFn_subset
      (n := n) (p := p) (Ω := Ω) U i)
    (interiorSupportCutoff (n := n) (Ω := Ω))
    (tsupport_interiorSupportCutoff_subset_domain
      (n := n) (Ω := Ω))
    (interiorSupportCutoff_eq_one_nhds_on_interiorSupport
      (n := n) (Ω := Ω))
    (by simpa [preparedInteriorBaseFn, preparedInteriorDerivativeFn,
      SobolevSpace.GraphSpace.baseRepresentative, V, base, deriv, K0] using
        hweakK)

/-- The prepared interior contribution lands in the ambient `W^{1,p}` graph
space. -/
theorem preparedAmbient_mapsIsWkpOn
    (U : W^{1,p}(Ω)) :
    SobolevSpace.GraphSpace.IsWkpOn (n := n) (k := 1) (p := p)
      (Ω := (Set.univ : Set (ℝ^n)))
      (preparedAmbient (n := n) (p := p) (Ω := Ω) U) := by
  classical
  intro a
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨i, ha⟩
  · subst a
    have hloc := memLp_locallyIntegrableOn_domain
      (MeasureTheory.Lp.memLp
        (preparedAmbient (n := n) (p := p) (Ω := Ω) U
          (SobolevSpace.GraphSpace.baseIndex n 1)))
      (Fact.out : (1 : ℝ≥0∞) ≤ p)
    simpa only [SobolevSpace.GraphSpace.baseIndex_toList] using hasWeakDerivativeOn_nil hloc
  · subst a
    simpa using (SobolevSpace.hasWeakDerivativeOn_congr_ae
      (n := n) (Ω := (Set.univ : Set (ℝ^n))) (α := [i])
      (preparedAmbient_base_coeFn (n := n) (p := p) (Ω := Ω) U)
      (preparedAmbient_derivative_coeFn
        (n := n) (p := p) (Ω := Ω) U i)).2
      (prepared_hasWeakDerivative (n := n) (p := p) (Ω := Ω) U i)

/-- Bounded global interior partition contribution. -/
noncomputable def extensionCLM :
    W^{1,p}(Ω) →L[ℝ]
      W^{1,p}((Set.univ : Set (ℝ^n))) :=
  ContinuousLinearMap.codRestrict
    (preparedAmbient (n := n) (p := p) (Ω := Ω))
    (SobolevSpace.GraphSpace.wkpSubmoduleOn n 1 p (Set.univ : Set (ℝ^n)))
    (preparedAmbient_mapsIsWkpOn (n := n) (p := p) (Ω := Ω))

/-- The underlying ambient bundle of the interior contribution is
`preparedAmbient U`. -/
@[simp] theorem extensionCLM_apply_coe
    (U : W^{1,p}(Ω)) :
    ((extensionCLM (n := n) (p := p) (Ω := Ω) U :
        W^{1,p}((Set.univ : Set (ℝ^n)))) :
        SobolevSpace.GraphSpace.WkpAmbientOn n 1 p (Set.univ : Set (ℝ^n))) =
      preparedAmbient (n := n) (p := p) (Ω := Ω) U :=
  rfl

/-- On the original domain, the bounded interior contribution is exactly
`ψ₀u` almost everywhere. -/
theorem extensionCLM_agree_ae
    (U : W^{1,p}(Ω)) :
    ∀ᵐ x ∂ domainMeasure n Ω,
      SobolevSpace.GraphSpace.baseRepresentative
          (extensionCLM (n := n) (p := p) (Ω := Ω) U) x =
        hΩ.interiorCutoff.toFun x *
          SobolevSpace.GraphSpace.baseRepresentative U x := by
  let V := SobolevSpace.GraphSpace.cutoffCLM
    (n := n) (p := p) (Ω := Ω) hΩ.interiorCutoff U
  let K0 := interiorSupport (n := n) (Ω := Ω)
  have hprepared := preparedAmbient_base_coeFn
    (n := n) (p := p) (Ω := Ω) U
  have hpreparedΩ' := MeasureTheory.ae_restrict_of_ae (s := Ω) hprepared
  have hpreparedΩ : ∀ᵐ x ∂ domainMeasure n Ω,
      SobolevSpace.GraphSpace.baseRepresentative
          (extensionCLM (n := n) (p := p) (Ω := Ω) U) x =
        preparedInteriorBaseFn (n := n) (p := p) (Ω := Ω) U x := by
    simpa [SobolevSpace.GraphSpace.baseRepresentative,
      extensionCLM_apply_coe, domainMeasure,
      Measure.restrict_restrict, inter_univ] using hpreparedΩ'
  have hsupport :
      K0.indicator (SobolevSpace.GraphSpace.baseRepresentative V)
        =ᵐ[domainMeasure n Ω]
          SobolevSpace.GraphSpace.baseRepresentative V := by
    simpa [K0, V, interiorSupport,
      SobolevSpace.GraphSpace.baseRepresentative] using
      SobolevSpace.GraphSpace.cutoffCLM_base_tsupport_indicator_ae
        (n := n) (p := p) (Ω := Ω) hΩ.interiorCutoff U
  have hcutoff :
      SobolevSpace.GraphSpace.baseRepresentative V
        =ᵐ[domainMeasure n Ω]
          fun x ↦ hΩ.interiorCutoff.toFun x *
            SobolevSpace.GraphSpace.baseRepresentative U x := by
    simpa [V, SobolevSpace.GraphSpace.baseRepresentative] using
      SobolevSpace.GraphSpace.cutoffCLM_base_apply_ae
        (n := n) (p := p) (Ω := Ω) hΩ.interiorCutoff U
  filter_upwards [hpreparedΩ, hsupport, hcutoff] with x hxprepared hxsupport hxcutoff
  calc
    SobolevSpace.GraphSpace.baseRepresentative
        (extensionCLM (n := n) (p := p) (Ω := Ω) U) x =
        preparedInteriorBaseFn (n := n) (p := p) (Ω := Ω) U x := hxprepared
    _ = SobolevSpace.GraphSpace.baseRepresentative V x := by
      simpa [preparedInteriorBaseFn, V, K0] using hxsupport
    _ = hΩ.interiorCutoff.toFun x *
        SobolevSpace.GraphSpace.baseRepresentative U x := hxcutoff

end InteriorAssembly

end C1

end Extension

end SobolevSpace
