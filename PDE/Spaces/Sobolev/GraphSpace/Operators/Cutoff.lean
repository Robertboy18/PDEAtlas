/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Model.Notation
import PDE.Spaces.Sobolev.Foundations.Representatives.Algebra

/-!
# Bounded cutoff multiplication on Sobolev graph spaces

For a smooth compactly supported `ψ : C_c^∞(ℝ^n)` and `u ∈ W^{1,p}(Ω)`, the product
`ψu` lies again in `W^{1,p}(Ω)`, with weak derivatives given by the product rule
`∂ᵢ(ψu) = ψ ∂ᵢu + (∂ᵢψ) u`.  We realise `u ↦ ψu` as a continuous linear
endomorphism `cutoffCLM ψ` of the first-order graph space `WkpSpaceOn n 1 p Ω`.
Evans, PDE, §5.2.3, Theorem 1(iv), states the product rule for `ζ ∈ C_c^∞(U)`; here `ψ` is
the restriction of a function in `C_c^∞(ℝ^n)`, so its support may meet the boundary of `Ω`.

The construction is coordinatewise on the ambient product `WkpAmbientOn n 1 p Ω`:
the base coordinate is multiplied by `ψ` (`mulLpLeft` with the `L^∞` class of `ψ`),
and the `i`-th derivative coordinate is sent to `ψ ∂ᵢu + (∂ᵢψ) u`
(`cutoffDerivativeLp`). Each row is one of the bounded coefficient operators of
`GraphSpace.Model.Definitions`.  The weak product rule
`hasWeakDerivativeOn_mul_testFunction_first` then shows that the graph submodule
`wkpSubmoduleOn` is mapped into itself, so the ambient operator restricts. Every
coordinate of `ψu` vanishes a.e. outside `tsupport ψ`, as cutoff arguments on
unbounded domains need.

## Main results

* `SobolevSpace.GraphSpace.cutoffAmbient`: coordinatewise cutoff multiplication on
  the ambient product.
* `SobolevSpace.GraphSpace.cutoffCLM`: the induced continuous linear map on
  `WkpSpaceOn n 1 p Ω`.
* `SobolevSpace.GraphSpace.cutoffCLM_base_apply_ae`,
  `SobolevSpace.GraphSpace.cutoffCLM_singleDeriv_apply_ae`: a.e. formulas for the
  base and derivative coordinates.
* `SobolevSpace.GraphSpace.cutoffCLM_base_tsupport_indicator_ae`,
  `SobolevSpace.GraphSpace.cutoffCLM_singleDeriv_tsupport_indicator_ae`: the
  result is supported in `tsupport ψ`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.3, Theorem 1(iv), (7), pp. 261-262, and step 3 of its
  proof, which treats `|α| = 1` by testing against `ζφ`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open TopologicalSpace
open scoped Distributions Sobolev

namespace SobolevSpace

open MeasureTheory Set Function ENNReal

namespace GraphSpace

section Cutoff

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

/-- One output coordinate of cutoff multiplication on the ambient derivative
bundle. -/
noncomputable def cutoffLpAt (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (a : DerivIndex n 1) :
    WkpAmbientOn n 1 p Ω →L[ℝ] DerivLp n p Ω :=
  firstOrderRows
    ((mulLpLeft (n := n) (p := p) (Ω := Ω)
      (testFunctionLpTop (n := n) (Ω := Ω) ψ)).comp
      (PiLp.proj (𝕜 := ℝ) (p := p)
        (β := fun _ : DerivIndex n 1 ↦ DerivLp n p Ω) (baseIndex n 1)))
    (fun i ↦
      (cutoffDerivativeLp (n := n) (p := p) (Ω := Ω) ψ i).comp
        ((PiLp.proj (𝕜 := ℝ) (p := p)
          (β := fun _ : DerivIndex n 1 ↦ DerivLp n p Ω) (baseIndex n 1)).prod
            (PiLp.proj (𝕜 := ℝ) (p := p)
              (β := fun _ : DerivIndex n 1 ↦ DerivLp n p Ω)
              (singleDerivIndex n i))))
    a

/-- Ambient bounded linear cutoff multiplication on the `PiLp` derivative
bundle. -/
noncomputable def cutoffAmbient (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    WkpAmbientOn n 1 p Ω →L[ℝ] WkpAmbientOn n 1 p Ω := by
  classical
  let e := PiLp.continuousLinearEquiv (𝕜 := ℝ) (p := p)
    (β := fun _ : DerivIndex n 1 ↦ DerivLp n p Ω)
  exact e.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun a ↦
      cutoffLpAt (n := n) (p := p) (Ω := Ω) ψ a)

/-- The `a`-th coordinate of `cutoffAmbient ψ U` is the row operator `cutoffLpAt ψ a` applied
to `U`. -/
@[simp] theorem cutoffAmbient_apply (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (U : WkpAmbientOn n 1 p Ω) (a : DerivIndex n 1) :
    cutoffAmbient (n := n) (p := p) (Ω := Ω) ψ U a =
      cutoffLpAt (n := n) (p := p) (Ω := Ω) ψ a U := by
  classical
  simp [cutoffAmbient]

private theorem cutoffAmbient_base_apply_ae
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (U : WkpAmbientOn n 1 p Ω) :
    ((cutoffAmbient (n := n) (p := p) (Ω := Ω) ψ U (baseIndex n 1) :
        DerivLp n p Ω) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω]
        fun x ↦ ψ.toFun x * (U (baseIndex n 1)) x := by
  rw [cutoffAmbient_apply]
  simp only [cutoffLpAt]
  have hmul := mulLpLeft_apply_ae (n := n) (p := p) (Ω := Ω)
    (testFunctionLpTop (n := n) (Ω := Ω) ψ) (U (baseIndex n 1))
  filter_upwards [hmul, testFunctionLpTop_apply_ae (n := n) (Ω := Ω) ψ] with x hx hψ
  simpa [hψ] using hx

/-- Multiplication by a smooth compactly supported cutoff preserves the
weak-derivative graph relations of the ambient bundle. -/
theorem cutoffAmbient_mapsIsWkpOn
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (U : WkpAmbientOn n 1 p Ω)
    (hU : IsWkpOn (n := n) (k := 1) (p := p) (Ω := Ω) U) :
    IsWkpOn (n := n) (k := 1) (p := p) (Ω := Ω)
      (cutoffAmbient (n := n) (p := p) (Ω := Ω) ψ U) := by
  classical
  intro a
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨i, ha⟩
  · subst a
    have hloc := memLp_locallyIntegrableOn_domain
      (MeasureTheory.Lp.memLp
        ((cutoffAmbient (n := n) (p := p) (Ω := Ω) ψ U) (baseIndex n 1)))
      (Fact.out : (1 : ℝ≥0∞) ≤ p)
    simpa only [baseIndex_toList] using hasWeakDerivativeOn_nil hloc
  · subst a
    have hweak : HasWeakDerivativeOn (n := n) Ω [i]
        (U (baseIndex n 1) : ℝ^n → ℝ)
        (U (singleDerivIndex n i) : ℝ^n → ℝ) := by
      simpa only [firstDerivIndex_one] using
        hU.hasWeakDerivativeOn_first (by norm_num) i
    have hproduct := hasWeakDerivativeOn_mul_testFunction_first
      (n := n) (p := p) (Ω := Ω) (i := i)
      (MeasureTheory.Lp.memLp (U (baseIndex n 1)))
      (MeasureTheory.Lp.memLp (U (singleDerivIndex n i))) hweak ψ
    have hbase := cutoffAmbient_base_apply_ae
      (n := n) (p := p) (Ω := Ω) ψ U
    have hderiv :
        ((cutoffAmbient (n := n) (p := p) (Ω := Ω) ψ U
            (singleDerivIndex n i) : DerivLp n p Ω) : ℝ^n → ℝ)
          =ᵐ[domainMeasure n Ω]
            fun x ↦ ψ.toFun x * (U (singleDerivIndex n i)) x +
              iteratedPartialDeriv (n := n) [i] ψ.toFun x *
                (U (baseIndex n 1)) x := by
      rw [cutoffAmbient_apply]
      simpa [cutoffLpAt] using
        cutoffDerivativeLp_apply_ae (n := n) (p := p) (Ω := Ω) ψ i
          (U (baseIndex n 1)) (U (singleDerivIndex n i))
    simpa using (hasWeakDerivativeOn_congr_ae
      (n := n) (Ω := Ω) (α := [i]) hbase hderiv).2 hproduct

/-- Multiplication by a smooth compactly supported cutoff as a continuous
linear endomorphism of Sobolev graph-space `W^{1,p}(Ω)`. -/
noncomputable def cutoffCLM (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    W^{1,p}(Ω) →L[ℝ] W^{1,p}(Ω) :=
  ContinuousLinearMap.codRestrict
    ((cutoffAmbient (n := n) (p := p) (Ω := Ω) ψ).comp
      (Submodule.subtypeL (wkpSubmoduleOn n 1 p Ω)))
    (wkpSubmoduleOn n 1 p Ω)
    (fun U ↦ cutoffAmbient_mapsIsWkpOn
      (n := n) (p := p) (Ω := Ω) ψ U U.property)

/-- On the underlying ambient tuple, `cutoffCLM ψ` is `cutoffAmbient ψ`. -/
@[simp] theorem cutoffCLM_apply_coe
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (U : W^{1,p}(Ω)) :
    ((cutoffCLM (n := n) (p := p) (Ω := Ω) ψ U : WkpAmbientOn n 1 p Ω)) =
      cutoffAmbient (n := n) (p := p) (Ω := Ω) ψ U :=
  rfl

/-- The base function represented by `cutoffCLM ψ U` is `ψu` almost
everywhere. -/
theorem cutoffCLM_base_apply_ae
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (U : W^{1,p}(Ω)) :
    ((((cutoffCLM (n := n) (p := p) (Ω := Ω) ψ U :
        W^{1,p}(Ω)) : WkpAmbientOn n 1 p Ω) (baseIndex n 1) :
        DerivLp n p Ω) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω]
        fun x ↦ ψ.toFun x * ((U : WkpAmbientOn n 1 p Ω) (baseIndex n 1)) x := by
  simpa using cutoffAmbient_base_apply_ae
    (n := n) (p := p) (Ω := Ω) ψ (U : WkpAmbientOn n 1 p Ω)

/-- A first-derivative coordinate of `cutoffCLM ψ U` realizes the weak
product rule almost everywhere. -/
theorem cutoffCLM_singleDeriv_apply_ae
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (U : W^{1,p}(Ω))
    (i : Fin n) :
    ((((cutoffCLM (n := n) (p := p) (Ω := Ω) ψ U :
        W^{1,p}(Ω)) : WkpAmbientOn n 1 p Ω)
        (singleDerivIndex n i) : DerivLp n p Ω) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω]
        fun x ↦ ψ.toFun x *
            ((U : WkpAmbientOn n 1 p Ω) (singleDerivIndex n i)) x +
          iteratedPartialDeriv (n := n) [i] ψ.toFun x *
            ((U : WkpAmbientOn n 1 p Ω) (baseIndex n 1)) x := by
  change
    ((cutoffAmbient (n := n) (p := p) (Ω := Ω) ψ
        (U : WkpAmbientOn n 1 p Ω) (singleDerivIndex n i) :
        DerivLp n p Ω) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] _
  rw [cutoffAmbient_apply]
  simpa [cutoffLpAt, singleDerivIndex_toList] using
    cutoffDerivativeLp_apply_ae (n := n) (p := p) (Ω := Ω) ψ i
      ((U : WkpAmbientOn n 1 p Ω) (baseIndex n 1))
      ((U : WkpAmbientOn n 1 p Ω) (singleDerivIndex n i))

/-- The base coordinate after cutoff multiplication is supported, up to null
sets, in `tsupport ψ`. -/
theorem cutoffCLM_base_tsupport_indicator_ae
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (U : W^{1,p}(Ω)) :
    (tsupport ψ.toFun).indicator
        (fun x ↦
          ((((cutoffCLM (n := n) (p := p) (Ω := Ω) ψ U :
            W^{1,p}(Ω)) : WkpAmbientOn n 1 p Ω)
            (baseIndex n 1) : DerivLp n p Ω) : ℝ^n → ℝ) x)
      =ᵐ[domainMeasure n Ω]
        fun x ↦
          ((((cutoffCLM (n := n) (p := p) (Ω := Ω) ψ U :
            W^{1,p}(Ω)) : WkpAmbientOn n 1 p Ω)
            (baseIndex n 1) : DerivLp n p Ω) : ℝ^n → ℝ) x := by
  have hV := cutoffCLM_base_apply_ae (n := n) (p := p) (Ω := Ω) ψ U
  filter_upwards [hV] with x hx
  by_cases hxK : x ∈ tsupport ψ.toFun
  · exact Set.indicator_of_mem hxK _
  · have hψzero : ψ.toFun x = 0 := by
      by_contra hne
      exact hxK (subset_tsupport ψ.toFun hne)
    have hVzero :
        ((((cutoffCLM (n := n) (p := p) (Ω := Ω) ψ U :
          W^{1,p}(Ω)) : WkpAmbientOn n 1 p Ω)
          (baseIndex n 1) : DerivLp n p Ω) : ℝ^n → ℝ) x = 0 := by
      calc
        _ = ψ.toFun x *
            ((U : WkpAmbientOn n 1 p Ω) (baseIndex n 1)) x := hx
        _ = 0 := by rw [hψzero]; simp
    calc
      _ = 0 := Set.indicator_of_notMem hxK _
      _ = _ := hVzero.symm

/-- Every first-derivative coordinate after cutoff multiplication is
supported, up to null sets, in `tsupport ψ`. -/
theorem cutoffCLM_singleDeriv_tsupport_indicator_ae
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (U : W^{1,p}(Ω))
    (i : Fin n) :
    (tsupport ψ.toFun).indicator
        (fun x ↦
          ((((cutoffCLM (n := n) (p := p) (Ω := Ω) ψ U :
            W^{1,p}(Ω)) : WkpAmbientOn n 1 p Ω)
            (singleDerivIndex n i) : DerivLp n p Ω) : ℝ^n → ℝ) x)
      =ᵐ[domainMeasure n Ω]
        fun x ↦
          ((((cutoffCLM (n := n) (p := p) (Ω := Ω) ψ U :
            W^{1,p}(Ω)) : WkpAmbientOn n 1 p Ω)
            (singleDerivIndex n i) : DerivLp n p Ω) : ℝ^n → ℝ) x := by
  have hV := cutoffCLM_singleDeriv_apply_ae
    (n := n) (p := p) (Ω := Ω) ψ U i
  filter_upwards [hV] with x hx
  by_cases hxK : x ∈ tsupport ψ.toFun
  · exact Set.indicator_of_mem hxK _
  · have hψzero : ψ.toFun x = 0 := by
      by_contra hne
      exact hxK (subset_tsupport ψ.toFun hne)
    have hdψzero : iteratedPartialDeriv (n := n) [i] ψ.toFun x = 0 := by
      by_contra hne
      exact hxK
        (tsupport_iteratedPartialDeriv_subset_tsupport
          (n := n) ([i] : List (Fin n)) ψ.toFun (subset_tsupport _ hne))
    have hVzero :
        ((((cutoffCLM (n := n) (p := p) (Ω := Ω) ψ U :
          W^{1,p}(Ω)) : WkpAmbientOn n 1 p Ω)
          (singleDerivIndex n i) : DerivLp n p Ω) : ℝ^n → ℝ) x = 0 := by
      calc
        _ = ψ.toFun x *
              ((U : WkpAmbientOn n 1 p Ω) (singleDerivIndex n i)) x +
            iteratedPartialDeriv (n := n) [i] ψ.toFun x *
              ((U : WkpAmbientOn n 1 p Ω) (baseIndex n 1)) x := hx
        _ = 0 := by rw [hψzero, hdψzero]; ring
    calc
      _ = 0 := Set.indicator_of_notMem hxK _
      _ = _ := hVzero.symm

end Cutoff

end GraphSpace

end SobolevSpace
