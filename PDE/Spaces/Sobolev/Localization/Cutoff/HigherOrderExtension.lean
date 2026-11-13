/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Localization.Cutoff.HigherOrder
public import PDE.Spaces.Sobolev.Localization.Cutoff.HigherOrderBounds
import PDE.Spaces.Sobolev.Approximation.Density.Global

/-!
# Canonical higher-order compact-support localization

Let `V ⊆ Ω` be open sets and `ψ` a smooth cutoff with compact support in `V`. For `U ∈ W^{k,p}(V)`
the product `ψ U`, extended by zero, is an element of `W^{k,p}(Ω)` whose derivative rows are given
by the Leibniz formula (Evans §5.2.3, Theorem 1(iv), (7)). The membership theorems in
`Cutoff.HigherOrder` prove existence of such an extension; `extendByCutoff` fixes one, which is
linear in `U` when `Ω` is open and bounded for `p = 2` and `0 < k`.

A boundary-relative variant handles data on `V ∩ Ω` for a cutoff supported in `V`, the situation
that arises when an open neighbourhood `V` of a boundary point is cut down to the domain `Ω`.
Regularity arguments use these operators rather than choosing fresh witnesses from the existence
theorems.

## Main results

* `extendByCutoff`: the extension of `ψ U` from `W^{k,p}(V)` to `W^{k,p}(Ω)`, with
  `extendByCutoff_base_ae` and `extendByCutoff_coordinate_ae` identifying its rows.
* `extendByCutoffLinearMap`, `extendByCutoffCLM`: the linear map and, for `p = 2` and `0 < k`,
  the bounded operator, with `norm_extendByCutoffCLM_le`.
* `interCutoff`, `interCutoffLinearMap`, `interCutoffCLM`: the boundary-relative versions from
  `W^{k,p}(V ∩ Ω)` to `W^{k,p}(Ω)`, with `norm_interCutoffCLM_le` (again for `p = 2`, `0 < k`).
* `extendByCutoff_self_eq_higherOrderCutoffCLM`: for `V = Ω`, `p = 2`, and `0 < k` the
  extension is the canonical higher-order cutoff endomorphism.

## How it works

The Leibniz rows of `ψ U` (`weakLeibnizExpansion`) vanish outside `tsupport ψ`, so they extend by
zero without creating boundary terms, and `exists_wkpSpaceOn_mul_testFunction_with_rows` gives an
extension with these rows. We fix one by choice and identify its rows almost everywhere
(`extendByCutoff_base_ae`, `extendByCutoff_coordinate_ae`). On an open target domain an element is
determined by its base row (`WkpSpaceOn.ext_of_base_ae`), since weak derivatives are unique; this
makes the extension additive and homogeneous. For `p = 2` the rows on `Ω` are the rows on `V`
extended by zero, so the extension has the norm of the cutoff multiplication on `V`
(`norm_extendByCutoff_eq_norm_self`), and the `W^{k,∞}` multiplier bound
`norm_higherOrderCutoffCLM_apply_le` bounds it.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.3, Theorem 1(iv), (7), pp. 261-262.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open TopologicalSpace
open scoped Distributions ENNReal

namespace SobolevSpace.CompactSupportLocalization.HigherOrderLocalizedCutoff

open MeasureTheory Set
open SobolevSpace.GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Multiplication by a cutoff supported in `V` transports almost-everywhere
equality from the local source measure to a larger target measure. -/
private theorem cutoff_mul_congr_ae
    {S V Ω : Set (ℝ^n)} (hVmeasurable : MeasurableSet V)
    (hmeasure :
      (domainMeasure n Ω).restrict V = domainMeasure n S)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψV : tsupport ψ.toFun ⊆ V)
    {f g : ℝ^n → ℝ} (hfg : f =ᵐ[domainMeasure n S] g) :
    (fun x ↦ ψ.toFun x * f x) =ᵐ[domainMeasure n Ω]
      fun x ↦ ψ.toFun x * g x := by
  apply MeasureTheory.ae_of_ae_restrict_of_ae_restrict_compl V
  · rw [hmeasure]
    filter_upwards [hfg] with x hx
    rw [hx]
  · filter_upwards
      [MeasureTheory.ae_restrict_mem hVmeasurable.compl] with x hx
    have hψ : ψ.toFun x = 0 :=
      image_eq_zero_of_notMem_tsupport fun hxt ↦ hx (hψV hxt)
    simp [hψ]

/-- Two `W^{k,2}` bundles assembled from the same compactly supported rows
have equal graph norms before and after extending the row measure. -/
private theorem norm_eq_of_coordinate_ae_restrict
    {S R Ω : Set (ℝ^n)}
    (hmeasure : (domainMeasure n Ω).restrict R = domainMeasure n S)
    (d : DerivIndex n k → ℝ^n → ℝ)
    (hdR : ∀ a, Function.support (d a) ⊆ R)
    (UΩ : W^{k,2}(Ω)) (US : W^{k,2}(S))
    (hUΩ : ∀ a,
      ((((UΩ : WkpAmbientOn n k 2 Ω) a : DerivLp n 2 Ω) : ℝ^n → ℝ))
        =ᵐ[domainMeasure n Ω] d a)
    (hUS : ∀ a,
      ((((US : WkpAmbientOn n k 2 S) a : DerivLp n 2 S) : ℝ^n → ℝ))
        =ᵐ[domainMeasure n S] d a) :
    ‖UΩ‖ = ‖US‖ := by
  have hcoord (a : DerivIndex n k) :
      ‖((UΩ : WkpAmbientOn n k 2 Ω) a : DerivLp n 2 Ω)‖ =
        ‖((US : WkpAmbientOn n k 2 S) a : DerivLp n 2 S)‖ := by
    rw [MeasureTheory.Lp.norm_def, MeasureTheory.Lp.norm_def]
    congr 1
    calc
      eLpNorm
            (((UΩ : WkpAmbientOn n k 2 Ω) a :
              DerivLp n 2 Ω) : ℝ^n → ℝ)
            2 (domainMeasure n Ω)
          =
          eLpNorm (d a) 2 (domainMeasure n Ω) :=
        eLpNorm_congr_ae (hUΩ a)
      _ = eLpNorm (d a) 2 (domainMeasure n S) := by
        have hrestrict :=
          eLpNorm_restrict_eq_of_support_subset
            (μ := domainMeasure n Ω) (p := (2 : ℝ≥0∞))
            ((Lp.aestronglyMeasurable
              ((UΩ : WkpAmbientOn n k 2 Ω) a)).congr (hUΩ a)) (hdR a)
        rw [hmeasure] at hrestrict
        exact hrestrict.symm
      _ =
          eLpNorm
            (((US : WkpAmbientOn n k 2 S) a :
              DerivLp n 2 S) : ℝ^n → ℝ)
            2 (domainMeasure n S) :=
        (eLpNorm_congr_ae (hUS a)).symm
  change
    ‖(UΩ : WkpAmbientOn n k 2 Ω)‖ =
      ‖(US : WkpAmbientOn n k 2 S)‖
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  congr 1
  exact Finset.sum_congr rfl fun a _ ↦ congrArg (fun r : ℝ ↦ r ^ 2) (hcoord a)

/-- The canonical extension to `Ω` of `ψU`, where `U ∈ W^{k,p}(V)` and the
smooth cutoff `ψ` is compactly supported in the open set `V ⊆ Ω`. -/
noncomputable def extendByCutoff
    {V Ω : Set (ℝ^n)} (hVopen : IsOpen V) (hVΩ : V ⊆ Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψV : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}(V)) :
    W^{k,p}(Ω) :=
  Classical.choose
    (exists_wkpSpaceOn_mul_testFunction_with_rows
      (n := n) (k := k) (p := p) hVopen hVΩ ψ hψV U)

/-- The base representative of `extendByCutoff` is the pointwise product
of the cutoff and the local input representative. -/
theorem extendByCutoff_base_ae
    {V Ω : Set (ℝ^n)} (hVopen : IsOpen V) (hVΩ : V ⊆ Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψV : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}(V)) :
    baseRepresentative
        (extendByCutoff
          (n := n) (k := k) (p := p) hVopen hVΩ ψ hψV U)
      =ᵐ[domainMeasure n Ω]
        fun x ↦ ψ.toFun x * baseRepresentative U x := by
  simpa only [extendByCutoff, baseRepresentative] using
    (Classical.choose_spec
      (exists_wkpSpaceOn_mul_testFunction_with_rows
        (n := n) (k := k) (p := p) hVopen hVΩ ψ hψV U)).1

/-- Every derivative coordinate of `extendByCutoff` is represented by the
finite weak Leibniz expansion. -/
theorem extendByCutoff_coordinate_ae
    {V Ω : Set (ℝ^n)} (hVopen : IsOpen V) (hVΩ : V ⊆ Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψV : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}(V)) (a : DerivIndex n k) :
    ((((extendByCutoff
          (n := n) (k := k) (p := p) hVopen hVΩ ψ hψV U :
        W^{k,p}(Ω)) : WkpAmbientOn n k p Ω) a :
      DerivLp n p Ω) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω]
        weakLeibnizExpansion ψ.toFun (wkpWordRepresentative U)
          a.toList.reverse := by
  simpa only [extendByCutoff] using
    (Classical.choose_spec
      (exists_wkpSpaceOn_mul_testFunction_with_rows
        (n := n) (k := k) (p := p) hVopen hVΩ ψ hψV U)).2 a

/-- Each derivative row `a` of `extendByCutoff ψ U` has `Lᵖ(Ω)` norm at most
`cutoffLeibnizENormBound U ψ a.toList.reverse`, the bound from the finite Leibniz expansion. -/
theorem norm_extendByCutoff_coordinate_le
    {V Ω : Set (ℝ^n)} (hVopen : IsOpen V) (hVΩ : V ⊆ Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψV : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}(V)) (a : DerivIndex n k) :
    ‖((extendByCutoff
        (n := n) (k := k) (p := p) hVopen hVΩ ψ hψV U :
      WkpAmbientOn n k p Ω) a : DerivLp n p Ω)‖ ≤
        (cutoffLeibnizENormBound U ψ a.toList.reverse).toReal := by
  rw [MeasureTheory.Lp.norm_def]
  let alpha := a.toList.reverse
  have halpha : alpha.length ≤ k := by
    simpa [alpha] using a.toList_length_le
  have hsupp :
      Function.support
          (weakLeibnizExpansion ψ.toFun (wkpWordRepresentative U) alpha) ⊆ V :=
    (weakLeibnizExpansion_support U ψ alpha).trans hψV
  have hmeasure :
      (domainMeasure n Ω).restrict V = domainMeasure n V := by
    simpa [domainMeasure] using
      (Measure.restrict_restrict_of_subset
        (μ := (volume : Measure (ℝ^n))) hVΩ)
  have hrow := extendByCutoff_coordinate_ae
    (n := n) (k := k) (p := p) hVopen hVΩ ψ hψV U a
  have hnormRestr :=
    eLpNorm_restrict_eq_of_support_subset
      (μ := domainMeasure n Ω) (p := p)
      ((Lp.aestronglyMeasurable
        ((extendByCutoff hVopen hVΩ ψ hψV U :
          WkpAmbientOn n k p Ω) a)).congr hrow) hsupp
  rw [hmeasure] at hnormRestr
  rw [eLpNorm_congr_ae hrow]
  rw [← hnormRestr]
  exact ENNReal.toReal_mono
    (cutoffLeibnizENormBound_ne_top U ψ alpha halpha)
    (eLpNorm_weakLeibnizExpansion_le U ψ alpha halpha)

/-- Compact-support extension is additive in the local Sobolev field when
the target domain is open. -/
theorem extendByCutoff_add
    {V Ω : Set (ℝ^n)} (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (hVΩ : V ⊆ Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψV : tsupport ψ.toFun ⊆ V)
    (U W : W^{k,p}(V)) :
    extendByCutoff
        (n := n) (k := k) (p := p) hVopen hVΩ ψ hψV (U + W) =
      extendByCutoff
          (n := n) (k := k) (p := p) hVopen hVΩ ψ hψV U +
        extendByCutoff
          (n := n) (k := k) (p := p) hVopen hVΩ ψ hψV W := by
  apply WkpSpaceOn.ext_of_base_ae hΩopen
  change
    baseRepresentative
        (extendByCutoff
          (n := n) (k := k) (p := p) hVopen hVΩ ψ hψV (U + W))
      =ᵐ[domainMeasure n Ω]
    baseRepresentative
      (extendByCutoff
          (n := n) (k := k) (p := p) hVopen hVΩ ψ hψV U +
        extendByCutoff
          (n := n) (k := k) (p := p) hVopen hVΩ ψ hψV W)
  have hmeasure :
      (domainMeasure n Ω).restrict V = domainMeasure n V := by
    simpa [domainMeasure] using
      (Measure.restrict_restrict_of_subset
        (μ := (volume : Measure (ℝ^n))) hVΩ)
  have hinput :=
    cutoff_mul_congr_ae
      (n := n) hVopen.measurableSet hmeasure ψ hψV
      (baseRepresentative_add_ae U W)
  filter_upwards
    [extendByCutoff_base_ae
      (n := n) (k := k) (p := p) hVopen hVΩ ψ hψV (U + W),
    extendByCutoff_base_ae
      (n := n) (k := k) (p := p) hVopen hVΩ ψ hψV U,
    extendByCutoff_base_ae
      (n := n) (k := k) (p := p) hVopen hVΩ ψ hψV W,
    hinput,
    baseRepresentative_add_ae
      (extendByCutoff
        (n := n) (k := k) (p := p) hVopen hVΩ ψ hψV U)
      (extendByCutoff
        (n := n) (k := k) (p := p) hVopen hVΩ ψ hψV W)] with
      x hleft hU hW hinput houtput
  rw [hleft, hinput, houtput, hU, hW]
  ring

/-- Compact-support extension is homogeneous in the local Sobolev field
when the target domain is open. -/
theorem extendByCutoff_smul
    {V Ω : Set (ℝ^n)} (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (hVΩ : V ⊆ Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψV : tsupport ψ.toFun ⊆ V)
    (c : ℝ) (U : W^{k,p}(V)) :
    extendByCutoff
        (n := n) (k := k) (p := p) hVopen hVΩ ψ hψV (c • U) =
      c • extendByCutoff
        (n := n) (k := k) (p := p) hVopen hVΩ ψ hψV U := by
  apply WkpSpaceOn.ext_of_base_ae hΩopen
  change
    baseRepresentative
        (extendByCutoff
          (n := n) (k := k) (p := p) hVopen hVΩ ψ hψV (c • U))
      =ᵐ[domainMeasure n Ω]
    baseRepresentative
      (c • extendByCutoff
        (n := n) (k := k) (p := p) hVopen hVΩ ψ hψV U)
  have hmeasure :
      (domainMeasure n Ω).restrict V = domainMeasure n V := by
    simpa [domainMeasure] using
      (Measure.restrict_restrict_of_subset
        (μ := (volume : Measure (ℝ^n))) hVΩ)
  have hinput :=
    cutoff_mul_congr_ae
      (n := n) hVopen.measurableSet hmeasure ψ hψV
      (baseRepresentative_smul_ae c U)
  filter_upwards
    [extendByCutoff_base_ae
      (n := n) (k := k) (p := p) hVopen hVΩ ψ hψV (c • U),
    extendByCutoff_base_ae
      (n := n) (k := k) (p := p) hVopen hVΩ ψ hψV U,
    hinput,
    baseRepresentative_smul_ae c
      (extendByCutoff
        (n := n) (k := k) (p := p) hVopen hVΩ ψ hψV U)] with
      x hleft hU hinput houtput
  rw [hleft, hinput, houtput, hU]
  simp only [smul_eq_mul]
  ring

/-- Extension by a fixed compactly supported cutoff as a linear map between
higher-order Sobolev graph spaces. -/
noncomputable def extendByCutoffLinearMap
    {V Ω : Set (ℝ^n)} (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (hVΩ : V ⊆ Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψV : tsupport ψ.toFun ⊆ V) :
    W^{k,p}(V) →ₗ[ℝ] W^{k,p}(Ω) where
  toFun := extendByCutoff
    (n := n) (k := k) (p := p) hVopen hVΩ ψ hψV
  map_add' := extendByCutoff_add
    (n := n) (k := k) (p := p) hVopen hΩopen hVΩ ψ hψV
  map_smul' := extendByCutoff_smul
    (n := n) (k := k) (p := p) hVopen hΩopen hVΩ ψ hψV

/-- The linear map `extendByCutoffLinearMap` is `extendByCutoff` on elements. -/
@[simp]
theorem extendByCutoffLinearMap_apply
    {V Ω : Set (ℝ^n)} (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (hVΩ : V ⊆ Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψV : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}(V)) :
    extendByCutoffLinearMap
        (n := n) (k := k) (p := p) hVopen hΩopen hVΩ ψ hψV U =
      extendByCutoff
        (n := n) (k := k) (p := p) hVopen hVΩ ψ hψV U :=
  rfl

/-- The canonical boundary-relative extension of `ψU` from `V ∩ Ω` to
the open target domain `Ω`. -/
noncomputable def interCutoff
    {V Ω : Set (ℝ^n)} (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψV : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}((V ∩ Ω))) :
    W^{k,p}(Ω) :=
  Classical.choose
    (exists_wkpSpaceOn_mul_testFunction_inter_with_rows
      (n := n) (k := k) (p := p) hVopen hΩopen ψ hψV U)

/-- The base representative of `interCutoff` is the boundary-relative
pointwise product `ψU`. -/
theorem interCutoff_base_ae
    {V Ω : Set (ℝ^n)} (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψV : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}((V ∩ Ω))) :
    baseRepresentative
        (interCutoff
          (n := n) (k := k) (p := p) hVopen hΩopen ψ hψV U)
      =ᵐ[domainMeasure n Ω]
        fun x ↦ ψ.toFun x * baseRepresentative U x := by
  simpa only [interCutoff, baseRepresentative] using
    (Classical.choose_spec
      (exists_wkpSpaceOn_mul_testFunction_inter_with_rows
        (n := n) (k := k) (p := p) hVopen hΩopen ψ hψV U)).1

/-- Every derivative coordinate of `interCutoff` is represented by the
finite weak Leibniz expansion. -/
theorem interCutoff_coordinate_ae
    {V Ω : Set (ℝ^n)} (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψV : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}((V ∩ Ω))) (a : DerivIndex n k) :
    ((((interCutoff
          (n := n) (k := k) (p := p) hVopen hΩopen ψ hψV U :
        W^{k,p}(Ω)) : WkpAmbientOn n k p Ω) a :
      DerivLp n p Ω) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω]
        weakLeibnizExpansion ψ.toFun (wkpWordRepresentative U)
          a.toList.reverse := by
  simpa only [interCutoff] using
    (Classical.choose_spec
      (exists_wkpSpaceOn_mul_testFunction_inter_with_rows
        (n := n) (k := k) (p := p) hVopen hΩopen ψ hψV U)).2 a

/-- Boundary-relative cutoff extension is additive in its local input. -/
theorem interCutoff_add
    {V Ω : Set (ℝ^n)} (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψV : tsupport ψ.toFun ⊆ V)
    (U W : W^{k,p}((V ∩ Ω))) :
    interCutoff
        (n := n) (k := k) (p := p) hVopen hΩopen ψ hψV (U + W) =
      interCutoff
          (n := n) (k := k) (p := p) hVopen hΩopen ψ hψV U +
        interCutoff
          (n := n) (k := k) (p := p) hVopen hΩopen ψ hψV W := by
  apply WkpSpaceOn.ext_of_base_ae hΩopen
  change
    baseRepresentative
        (interCutoff
          (n := n) (k := k) (p := p) hVopen hΩopen ψ hψV (U + W))
      =ᵐ[domainMeasure n Ω]
    baseRepresentative
      (interCutoff
          (n := n) (k := k) (p := p) hVopen hΩopen ψ hψV U +
        interCutoff
          (n := n) (k := k) (p := p) hVopen hΩopen ψ hψV W)
  have hmeasure :
      (domainMeasure n Ω).restrict V =
        domainMeasure n (V ∩ Ω) := by
    rw [domainMeasure, Measure.restrict_restrict hVopen.measurableSet]
  have hinput :=
    cutoff_mul_congr_ae
      (n := n) hVopen.measurableSet hmeasure ψ hψV
      (baseRepresentative_add_ae U W)
  filter_upwards
    [interCutoff_base_ae
      (n := n) (k := k) (p := p) hVopen hΩopen ψ hψV (U + W),
    interCutoff_base_ae
      (n := n) (k := k) (p := p) hVopen hΩopen ψ hψV U,
    interCutoff_base_ae
      (n := n) (k := k) (p := p) hVopen hΩopen ψ hψV W,
    hinput,
    baseRepresentative_add_ae
      (interCutoff
        (n := n) (k := k) (p := p) hVopen hΩopen ψ hψV U)
      (interCutoff
        (n := n) (k := k) (p := p) hVopen hΩopen ψ hψV W)] with
      x hleft hU hW hinput houtput
  rw [hleft, hinput, houtput, hU, hW]
  ring

/-- Boundary-relative cutoff extension is homogeneous in its local input. -/
theorem interCutoff_smul
    {V Ω : Set (ℝ^n)} (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψV : tsupport ψ.toFun ⊆ V)
    (c : ℝ) (U : W^{k,p}((V ∩ Ω))) :
    interCutoff
        (n := n) (k := k) (p := p) hVopen hΩopen ψ hψV (c • U) =
      c • interCutoff
        (n := n) (k := k) (p := p) hVopen hΩopen ψ hψV U := by
  apply WkpSpaceOn.ext_of_base_ae hΩopen
  change
    baseRepresentative
        (interCutoff
          (n := n) (k := k) (p := p) hVopen hΩopen ψ hψV (c • U))
      =ᵐ[domainMeasure n Ω]
    baseRepresentative
      (c • interCutoff
        (n := n) (k := k) (p := p) hVopen hΩopen ψ hψV U)
  have hmeasure :
      (domainMeasure n Ω).restrict V =
        domainMeasure n (V ∩ Ω) := by
    rw [domainMeasure, Measure.restrict_restrict hVopen.measurableSet]
  have hinput :=
    cutoff_mul_congr_ae
      (n := n) hVopen.measurableSet hmeasure ψ hψV
      (baseRepresentative_smul_ae c U)
  filter_upwards
    [interCutoff_base_ae
      (n := n) (k := k) (p := p) hVopen hΩopen ψ hψV (c • U),
    interCutoff_base_ae
      (n := n) (k := k) (p := p) hVopen hΩopen ψ hψV U,
    hinput,
    baseRepresentative_smul_ae c
      (interCutoff
        (n := n) (k := k) (p := p) hVopen hΩopen ψ hψV U)] with
      x hleft hU hinput houtput
  rw [hleft, hinput, houtput, hU]
  simp only [smul_eq_mul]
  ring

/-- Boundary-relative multiplication by a fixed cutoff as a linear map from
`W^{k,p}(V ∩ Ω)` to `W^{k,p}(Ω)`. -/
noncomputable def interCutoffLinearMap
    {V Ω : Set (ℝ^n)} (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψV : tsupport ψ.toFun ⊆ V) :
    W^{k,p}((V ∩ Ω)) →ₗ[ℝ] W^{k,p}(Ω) where
  toFun := interCutoff
    (n := n) (k := k) (p := p) hVopen hΩopen ψ hψV
  map_add' := interCutoff_add
    (n := n) (k := k) (p := p) hVopen hΩopen ψ hψV
  map_smul' := interCutoff_smul
    (n := n) (k := k) (p := p) hVopen hΩopen ψ hψV

/-- The linear map `interCutoffLinearMap` is `interCutoff` on elements. -/
@[simp]
theorem interCutoffLinearMap_apply
    {V Ω : Set (ℝ^n)} (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψV : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}((V ∩ Ω))) :
    interCutoffLinearMap
        (n := n) (k := k) (p := p) hVopen hΩopen ψ hψV U =
      interCutoff
        (n := n) (k := k) (p := p) hVopen hΩopen ψ hψV U :=
  rfl

/-- On a single open domain and for `p = 2`, compact-support extension
agrees with the canonical higher-order cutoff endomorphism. -/
theorem extendByCutoff_self_eq_higherOrderCutoffCLM
    {V : Set (ℝ^n)} (hk : 0 < k) (hVopen : IsOpen V)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψV : tsupport ψ.toFun ⊆ V)
    (U : W^{k,2}(V)) :
    extendByCutoff
        (n := n) (k := k) (p := 2) hVopen Subset.rfl ψ hψV U =
      higherOrderCutoffCLM
        (n := n) (Ω := V) hk hVopen ψ U := by
  apply WkpSpaceOn.ext_of_base_ae hVopen
  exact
    (extendByCutoff_base_ae
      (n := n) (k := k) (p := (2 : ℝ≥0∞))
      hVopen Subset.rfl ψ hψV U).trans
      (higherOrderCutoffCLM_base_ae
        (n := n) (k := k) (Ω := V) hk hVopen ψ U).symm

/-! ## Continuous operators in the Hilbert case -/

/-- Extending compactly supported cutoff rows from `V` to `Ω` preserves
their `W^{k,2}` graph norm. -/
theorem norm_extendByCutoff_eq_norm_self
    {V Ω : Set (ℝ^n)} (hVopen : IsOpen V) (hVΩ : V ⊆ Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψV : tsupport ψ.toFun ⊆ V)
    (U : W^{k,2}(V)) :
    ‖extendByCutoff
        (n := n) (k := k) (p := 2) hVopen hVΩ ψ hψV U‖ =
      ‖extendByCutoff
        (n := n) (k := k) (p := 2) hVopen Subset.rfl ψ hψV U‖ := by
  let d : DerivIndex n k → ℝ^n → ℝ := fun a ↦
    weakLeibnizExpansion ψ.toFun (wkpWordRepresentative U)
      a.toList.reverse
  apply norm_eq_of_coordinate_ae_restrict
    (S := V) (R := V) (Ω := Ω) (d := d)
  · simpa [domainMeasure] using
      (Measure.restrict_restrict_of_subset
        (μ := (volume : Measure (ℝ^n))) hVΩ)
  · intro a
    have hsupp :
        Function.support (d a) ⊆ tsupport ψ.toFun := by
      simpa [d] using
        weakLeibnizExpansion_support U ψ a.toList.reverse
    exact hsupp.trans hψV
  · exact extendByCutoff_coordinate_ae
      (n := n) (k := k) (p := (2 : ℝ≥0∞))
      hVopen hVΩ ψ hψV U
  · exact extendByCutoff_coordinate_ae
      (n := n) (k := k) (p := (2 : ℝ≥0∞))
      hVopen Subset.rfl ψ hψV U

/-- If `0 < k`, `V` is open, `V ⊆ Ω` and `tsupport ψ ⊆ V`, then for `U ∈ W^{k,2}(V)` the extension
`extendByCutoff ψ U` has norm at most
`wkTopMultiplierNormBound n k * ‖globalTestFunctionToWkTopOn ψ‖ * ‖U‖`, the `W^{k,∞}` norm of
`ψ` being taken on `V`. -/
theorem norm_extendByCutoff_le
    {V Ω : Set (ℝ^n)} (hk : 0 < k)
    (hVopen : IsOpen V) (hVΩ : V ⊆ Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψV : tsupport ψ.toFun ⊆ V)
    (U : W^{k,2}(V)) :
    ‖extendByCutoff
        (n := n) (k := k) (p := 2) hVopen hVΩ ψ hψV U‖ ≤
      wkTopMultiplierNormBound n k *
        ‖globalTestFunctionToWkTopOn
          (n := n) (k := k) (Ω := V) ψ‖ * ‖U‖ := by
  rw [norm_extendByCutoff_eq_norm_self
    (n := n) (k := k) hVopen hVΩ ψ hψV U]
  rw [extendByCutoff_self_eq_higherOrderCutoffCLM
    (n := n) (k := k) hk hVopen ψ hψV U]
  exact norm_higherOrderCutoffCLM_apply_le
    (n := n) (k := k) (Ω := V) hk hVopen ψ U

/-- Compact-support extension as a bounded linear map
`W^{k,2}(V) → W^{k,2}(Ω)`. -/
noncomputable def extendByCutoffCLM
    {V Ω : Set (ℝ^n)} (hk : 0 < k)
    (hVopen : IsOpen V) (hΩopen : IsOpen Ω) (hVΩ : V ⊆ Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψV : tsupport ψ.toFun ⊆ V) :
    W^{k,2}(V) →L[ℝ] W^{k,2}(Ω) :=
  LinearMap.mkContinuous
    (extendByCutoffLinearMap
      (n := n) (k := k) (p := 2) hVopen hΩopen hVΩ ψ hψV)
    (wkTopMultiplierNormBound n k *
      ‖globalTestFunctionToWkTopOn
        (n := n) (k := k) (Ω := V) ψ‖)
    fun U ↦ by
      simpa [mul_assoc] using
        norm_extendByCutoff_le
          (n := n) (k := k) hk hVopen hVΩ ψ hψV U

/-- The bounded operator `extendByCutoffCLM` is `extendByCutoff` (at `p = 2`) on elements. -/
@[simp]
theorem extendByCutoffCLM_apply
    {V Ω : Set (ℝ^n)} (hk : 0 < k)
    (hVopen : IsOpen V) (hΩopen : IsOpen Ω) (hVΩ : V ⊆ Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψV : tsupport ψ.toFun ⊆ V)
    (U : W^{k,2}(V)) :
    extendByCutoffCLM
        (n := n) (k := k) hk hVopen hΩopen hVΩ ψ hψV U =
      extendByCutoff
        (n := n) (k := k) (p := 2) hVopen hVΩ ψ hψV U :=
  rfl

/-- The operator norm of `extendByCutoffCLM` is at most
`wkTopMultiplierNormBound n k * ‖globalTestFunctionToWkTopOn ψ‖`, the `W^{k,∞}` norm of `ψ`
being taken on `V`. -/
theorem norm_extendByCutoffCLM_le
    {V Ω : Set (ℝ^n)} (hk : 0 < k)
    (hVopen : IsOpen V) (hΩopen : IsOpen Ω) (hVΩ : V ⊆ Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψV : tsupport ψ.toFun ⊆ V) :
    ‖extendByCutoffCLM
        (n := n) (k := k) hk hVopen hΩopen hVΩ ψ hψV‖ ≤
      wkTopMultiplierNormBound n k *
        ‖globalTestFunctionToWkTopOn
          (n := n) (k := k) (Ω := V) ψ‖ :=
  LinearMap.mkContinuous_norm_le _
    (mul_nonneg (wkTopMultiplierNormBound_nonneg n k) (norm_nonneg _)) _

/-- Boundary-relative cutoff extension has the same graph norm as the
canonical multiplier on `V ∩ Ω`. -/
theorem norm_interCutoff_eq_norm_higherOrderCutoffCLM
    {V Ω : Set (ℝ^n)} (hk : 0 < k)
    (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψV : tsupport ψ.toFun ⊆ V)
    (U : W^{k,2}((V ∩ Ω))) :
    ‖interCutoff
        (n := n) (k := k) (p := 2) hVopen hΩopen ψ hψV U‖ =
      ‖higherOrderCutoffCLM
        (n := n) (k := k) (Ω := V ∩ Ω)
        hk (hVopen.inter hΩopen) ψ U‖ := by
  let hlocal :=
    exists_wkpSpaceOn_mul_testFunction_sameDomain_with_rows
      (n := n) (k := k) (p := (2 : ℝ≥0∞)) ψ U
  let Wlocal : W^{k,2}((V ∩ Ω)) := Classical.choose hlocal
  have hWlocalBase :
      baseRepresentative Wlocal =ᵐ[domainMeasure n (V ∩ Ω)]
        fun x ↦ ψ.toFun x * baseRepresentative U x := by
    simpa only [Wlocal, baseRepresentative] using
      (Classical.choose_spec hlocal).1
  have hWlocalRows (a : DerivIndex n k) :
      ((((Wlocal : WkpAmbientOn n k 2 (V ∩ Ω)) a :
          DerivLp n 2 (V ∩ Ω)) : ℝ^n → ℝ))
        =ᵐ[domainMeasure n (V ∩ Ω)]
          weakLeibnizExpansion ψ.toFun (wkpWordRepresentative U)
            a.toList.reverse := by
    simpa only [Wlocal] using (Classical.choose_spec hlocal).2 a
  have hnorm :
      ‖interCutoff
          (n := n) (k := k) (p := 2) hVopen hΩopen ψ hψV U‖ =
        ‖Wlocal‖ := by
    let d : DerivIndex n k → ℝ^n → ℝ := fun a ↦
      weakLeibnizExpansion ψ.toFun (wkpWordRepresentative U)
        a.toList.reverse
    apply norm_eq_of_coordinate_ae_restrict
      (S := V ∩ Ω) (R := V) (Ω := Ω) (d := d)
    · rw [domainMeasure, Measure.restrict_restrict hVopen.measurableSet]
    · intro a
      have hsupp :
          Function.support (d a) ⊆ tsupport ψ.toFun := by
        simpa [d] using
          weakLeibnizExpansion_support U ψ a.toList.reverse
      exact hsupp.trans hψV
    · exact interCutoff_coordinate_ae
        (n := n) (k := k) (p := (2 : ℝ≥0∞))
        hVopen hΩopen ψ hψV U
    · simpa only [d] using hWlocalRows
  have hWlocal :
      Wlocal =
        higherOrderCutoffCLM
          (n := n) (k := k) (Ω := V ∩ Ω)
          hk (hVopen.inter hΩopen) ψ U := by
    apply WkpSpaceOn.ext_of_base_ae (hVopen.inter hΩopen)
    exact hWlocalBase.trans
      (higherOrderCutoffCLM_base_ae
        (n := n) (k := k) (Ω := V ∩ Ω)
        hk (hVopen.inter hΩopen) ψ U).symm
  exact hnorm.trans (congrArg norm hWlocal)

/-- If `0 < k`, `V` and `Ω` are open and `tsupport ψ ⊆ V`, then for `U ∈ W^{k,2}(V ∩ Ω)` the
extension `interCutoff ψ U` has norm at most
`wkTopMultiplierNormBound n k * ‖globalTestFunctionToWkTopOn ψ‖ * ‖U‖`, the `W^{k,∞}` norm of
`ψ` being taken on `V ∩ Ω`. -/
theorem norm_interCutoff_le
    {V Ω : Set (ℝ^n)} (hk : 0 < k)
    (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψV : tsupport ψ.toFun ⊆ V)
    (U : W^{k,2}((V ∩ Ω))) :
    ‖interCutoff
        (n := n) (k := k) (p := 2) hVopen hΩopen ψ hψV U‖ ≤
      wkTopMultiplierNormBound n k *
        ‖globalTestFunctionToWkTopOn
          (n := n) (k := k) (Ω := V ∩ Ω) ψ‖ * ‖U‖ := by
  rw [norm_interCutoff_eq_norm_higherOrderCutoffCLM
    (n := n) (k := k) hk hVopen hΩopen ψ hψV U]
  exact norm_higherOrderCutoffCLM_apply_le
    (n := n) (k := k) (Ω := V ∩ Ω)
    hk (hVopen.inter hΩopen) ψ U

/-- Boundary-relative cutoff extension as a bounded linear map
`W^{k,2}(V ∩ Ω) → W^{k,2}(Ω)`. -/
noncomputable def interCutoffCLM
    {V Ω : Set (ℝ^n)} (hk : 0 < k)
    (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψV : tsupport ψ.toFun ⊆ V) :
    W^{k,2}((V ∩ Ω)) →L[ℝ] W^{k,2}(Ω) :=
  LinearMap.mkContinuous
    (interCutoffLinearMap
      (n := n) (k := k) (p := 2) hVopen hΩopen ψ hψV)
    (wkTopMultiplierNormBound n k *
      ‖globalTestFunctionToWkTopOn
        (n := n) (k := k) (Ω := V ∩ Ω) ψ‖)
    fun U ↦ by
      simpa [mul_assoc] using
        norm_interCutoff_le
          (n := n) (k := k) hk hVopen hΩopen ψ hψV U

/-- The bounded operator `interCutoffCLM` is `interCutoff` (at `p = 2`) on elements. -/
@[simp]
theorem interCutoffCLM_apply
    {V Ω : Set (ℝ^n)} (hk : 0 < k)
    (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψV : tsupport ψ.toFun ⊆ V)
    (U : W^{k,2}((V ∩ Ω))) :
    interCutoffCLM
        (n := n) (k := k) hk hVopen hΩopen ψ hψV U =
      interCutoff
        (n := n) (k := k) (p := 2) hVopen hΩopen ψ hψV U :=
  rfl

/-- The operator norm of `interCutoffCLM` is at most
`wkTopMultiplierNormBound n k * ‖globalTestFunctionToWkTopOn ψ‖`, the `W^{k,∞}` norm of `ψ`
being taken on `V ∩ Ω`. -/
theorem norm_interCutoffCLM_le
    {V Ω : Set (ℝ^n)} (hk : 0 < k)
    (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψV : tsupport ψ.toFun ⊆ V) :
    ‖interCutoffCLM
        (n := n) (k := k) hk hVopen hΩopen ψ hψV‖ ≤
      wkTopMultiplierNormBound n k *
        ‖globalTestFunctionToWkTopOn
          (n := n) (k := k) (Ω := V ∩ Ω) ψ‖ :=
  LinearMap.mkContinuous_norm_le _
    (mul_nonneg (wkTopMultiplierNormBound_nonneg n k) (norm_nonneg _)) _

end SobolevSpace.CompactSupportLocalization.HigherOrderLocalizedCutoff
