/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.Core
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions
import Mathlib.MeasureTheory.Function.Jacobian
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.FiniteExponent
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.PullbackBounds

/-!
# Localized weak pullbacks

For a `C¹` partial homeomorphism `E` with `C¹` inverse, null sets on the target pull back to
null sets on the source (`E` is quasi-measure-preserving). This permits weak first derivatives
to be transported through the chart without choosing globally measurable representatives:
measurable representatives are picked with `AEMeasurable.mk`, the chain rule of
`FiniteExponent` is applied to them, and the resulting identity is transported back.

On a compact patch `K` of the target, localizing to `K` and then composing with `E` defines a
bounded linear map `L^p(E.target) → L^p(E.symm '' K)`, for every `1 ≤ p ≤ ∞`. For `p < ∞`
the bound is the Jacobian estimate of `PullbackBounds`; for `p = ∞` it is simply that
essential bounds pull back along a null-set-preserving map, with constant `1`.

## Main results

* `quasiMeasurePreserving_partialHomeomorph`: `E` pulls null sets of `E.target` back to null
  sets of `E.source`; the proof uses the Jacobian inequality for `C¹` images of null sets.
* `hasWeakDerivativeOn_comp_partialHomeomorph_W1`,
  `hasWeakDerivativeOn_comp_partialHomeomorph_W1_of_memLp`: the first-order chain rule for
  every exponent `1 ≤ p ≤ ∞` on a finite-volume target, first for measurable representatives
  and then for arbitrary ones.
* `hasWeakDerivativeOn_comp_partialHomeomorph_W1p_of_memLp`: the finite-exponent chain rule
  for arbitrary representatives, with no volume hypothesis.
* `memLp_comp_partialHomeomorph_of_bounded_target`,
  `memLp_comp_partialHomeomorph_of_compact_support`: `L^p` membership is preserved by pullback.
* `localizedPullbackCLM`: the localized pullback `u ↦ (1_K u) ∘ E` as a continuous linear map
  on `L^p`, with the bound `exists_norm_localizedPullbackLp_le`.

## Implementation notes

The `p = ∞` case of the chain rule is reduced to `p = 2` on the finite-measure target: the
statement `HasWeakDerivativeOn` is a distributional identity and does not mention `p`, and
`L^∞` data on a finite-measure set are in `L²`. The compact source patch is
`compactPullbackSource E K = E.symm '' K`, kept as a named set so that the graph-space
elements built on it in `Pullback.SecondOrder` have a fixed domain.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace

open MeasureTheory Set Function ENNReal Approximation
open scoped Topology

namespace WeakChangeOfVariables

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

local notation "qₚ" => ENNReal.conjExponent p

/-!
## Finite and infinite exponents

`HasWeakDerivativeOn` is a *distributional* identity and does not depend on `p`. For `p = ∞`,
we reduce to a finite exponent on finite-measure domains.
-/

/-- The first-order weak chain rule for every exponent `1 ≤ p ≤ ∞` on a target of finite
volume, for measurable representatives. For `p < ∞` this is
`hasWeakDerivativeOn_comp_partialHomeomorph_W1p`; for `p = ∞`, the data lie in `L²(E.target)`
because the target has finite measure, and since `HasWeakDerivativeOn` does not depend on the
exponent the finite-exponent theorem applies with `p = 2`. -/
theorem hasWeakDerivativeOn_comp_partialHomeomorph_W1
    (μ : SobolevSpace.Approximation.Mollifier n)
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 1 (fun x ↦ E x)) (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    (hvol_target : (MeasureTheory.volume : Measure (ℝ^n)) E.target ≠ ∞)
    {u : ℝ^n → ℝ} (hu_meas : Measurable u)
    (huLp : MeasureTheory.MemLp u p (domainMeasure n E.target))
    {du : Fin n → ℝ^n → ℝ}
    (hdu_meas : ∀ j, Measurable (du j))
    (hduLp : ∀ j, MeasureTheory.MemLp (du j) p (domainMeasure n E.target))
    (hweak : ∀ j, HasWeakDerivativeOn (n := n) E.target [j] u (du j)) :
    ∀ i,
      HasWeakDerivativeOn (n := n) E.source [i] (fun x ↦ u (E x))
        (fun x ↦ ∑ j : Fin n, du j (E x) *
          (∂[i] (fun z ↦ E z)) x j) := by
  classical
  by_cases hp : p = ∞
  · subst hp
    -- Reduce to a finite exponent on the finite-measure set `E.target`.
    have hvol_target' : volume E.target ≠ ∞ := by
      simpa using hvol_target
    have : MeasureTheory.IsFiniteMeasure (domainMeasure n E.target) := by
      simpa [domainMeasure, MeasureTheory.isFiniteMeasure_restrict] using hvol_target'
    -- Any fixed `p₀ ∈ [1, ∞)` works; take `p₀ = 2`.
    let p₀ : ℝ≥0∞ := (2 : ℝ≥0∞)
    have : Fact (1 ≤ p₀) := ⟨by norm_num⟩
    have hp₀ : p₀ ≠ ∞ := by simp [p₀]
    have huLp₀ : MeasureTheory.MemLp u p₀ (domainMeasure n E.target) :=
      huLp.mono_exponent (p := p₀) (hpq := by simp [p₀])
    have hduLp₀ : ∀ j, MeasureTheory.MemLp (du j) p₀ (domainMeasure n E.target) := fun j ↦
      (hduLp j).mono_exponent (p := p₀) (hpq := by simp [p₀])
    exact
      hasWeakDerivativeOn_comp_partialHomeomorph_W1p (n := n) (p := p₀) (μ := μ) hp₀
        (E := E) hE hEsymm (u := u) hu_meas huLp₀ (du := du) hdu_meas hduLp₀ hweak
  · exact
      hasWeakDerivativeOn_comp_partialHomeomorph_W1p (n := n) (p := p) (μ := μ) hp
        (E := E) hE hEsymm (u := u) hu_meas huLp (du := du) hdu_meas hduLp hweak

/-!
## Measurable representatives

The main chain rule assumes globally measurable representatives. Sobolev functions are defined
only up to a.e. equality, so measurable representatives are chosen with `AEMeasurable.mk` and
the resulting weak derivative identity is transported back to the original functions.

The only additional ingredient needed is that the chart map is quasi-measure-preserving, so a.e.
equalities on `E.target` pull back to a.e. equalities on `E.source`.
-/

private theorem volume_image_eq_zero_of_contDiff {f : ℝ^n → ℝ^n} (hf : ContDiff ℝ 1 f)
    {s : Set (ℝ^n)} (hs : MeasurableSet s) (hμs : (volume : Measure (ℝ^n)) s = 0) :
    (volume : Measure (ℝ^n)) (f '' s) = 0 := by
  -- Jacobian inequality: `μ (f '' s) ≤ ∫ |det f'|`.
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have hf' :
      ∀ x ∈ s, HasFDerivWithinAt f (fderiv ℝ f x) s x := by
    intro x hx
    exact (hdiff.differentiableAt.hasFDerivAt).hasFDerivWithinAt
  have hle :=
    MeasureTheory.addHaar_image_le_lintegral_abs_det_fderiv
      (μ := (volume : Measure (ℝ^n))) (s := s) (f := f)
      (f' := fun x : ℝ^n ↦ fderiv ℝ f x) hs hf'
  -- if `μ s = 0`, the RHS is `0`, hence so is `μ (f '' s)`.
  have hRHS0 :
      (∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ f x).det| ∂ (volume : Measure (ℝ^n))) = 0 := by
    have : (volume : Measure (ℝ^n)).restrict s = 0 := Measure.restrict_zero_set hμs
    -- Restricting to a null set gives the zero measure.
    simp [this]
  have hle0 : (volume : Measure (ℝ^n)) (f '' s) ≤ 0 := by
    simpa [hRHS0] using hle
  exact (nonpos_iff_eq_zero.1 hle0)

private theorem preimage_inter_source_eq_symm_image_inter_target
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)} {s : Set (ℝ^n)} :
    (E ⁻¹' s) ∩ E.source = (E.symm '' (s ∩ E.target)) := by
  ext x
  constructor
  · rintro ⟨hxpre, hxsrc⟩
    have hxT : E x ∈ E.target := E.map_source hxsrc
    refine ⟨E x, ⟨hxpre, hxT⟩, ?_⟩
    simp [E.left_inv hxsrc]
  · rintro ⟨y, ⟨hy, hyT⟩, rfl⟩
    have hxsrc : E.symm y ∈ E.source := E.map_target hyT
    refine ⟨?_, hxsrc⟩
    simpa [E.right_inv hyT] using hy

/-- A `C¹` partial homeomorphism whose inverse is also `C¹` preserves measure-zero sets in the
direction needed for Sobolev pullback.  This is the common measure-theoretic foundation for all
boundary-chart chain rules. -/
theorem quasiMeasurePreserving_partialHomeomorph
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 1 (fun x ↦ E x)) (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x)) :
    MeasureTheory.QuasiMeasurePreserving (fun x ↦ E x)
      (domainMeasure n E.source) (domainMeasure n E.target) := by
  refine ⟨hE.continuous.measurable, ?_⟩
  intro s hs
  -- Reduce to the measurable hull of `s` for the map measure.
  have hs_meas : MeasurableSet (toMeasurable (domainMeasure n E.target) s) :=
    measurableSet_toMeasurable _ _
  have hs0 :
      (domainMeasure n E.target) (toMeasurable (domainMeasure n E.target) s) = 0 := by
    calc
      (domainMeasure n E.target) (toMeasurable (domainMeasure n E.target) s)
          = (domainMeasure n E.target) s := by
              simp
      _ = 0 := hs
  have hmap :
      (domainMeasure n E.source).map (fun x ↦ E x)
          (toMeasurable (domainMeasure n E.target) s)
        =
        (domainMeasure n E.source) ((fun x ↦ E x) ⁻¹'
          (toMeasurable (domainMeasure n E.target) s)) := by
    simpa using
      (Measure.map_apply (μ := domainMeasure n E.source) (f := fun x ↦ E x)
        (hf := hE.continuous.measurable) (hs := hs_meas))
  have hs0_vol :
      (volume : Measure (ℝ^n)) (toMeasurable (domainMeasure n E.target) s ∩ E.target) = 0 := by
    -- The domain measure is Lebesgue measure restricted to the chart target.
    have hs0' :
        (volume : Measure (ℝ^n)).restrict E.target
            (toMeasurable ((volume : Measure (ℝ^n)).restrict E.target) s) = 0 := by
      simpa [domainMeasure] using hs0
    have hs_meas' :
        MeasurableSet
          (toMeasurable ((volume : Measure (ℝ^n)).restrict E.target) s) := by
      exact hs_meas
    have hs0'' := hs0'
    -- `((volume).restrict E.target) t = (volume) (t ∩ E.target)`.
    rw [Measure.restrict_apply hs_meas'] at hs0''
    simpa [domainMeasure, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using hs0''
  have htarget_meas :
      MeasurableSet (toMeasurable (domainMeasure n E.target) s ∩ E.target) :=
    hs_meas.inter E.open_target.measurableSet
  have himg0 :
      (volume : Measure (ℝ^n))
          (E.symm '' (toMeasurable (domainMeasure n E.target) s ∩ E.target)) = 0 :=
    volume_image_eq_zero_of_contDiff (n := n) (f := fun x ↦ E.symm x) hEsymm htarget_meas hs0_vol
  have hpre :
      ((fun x ↦ E x) ⁻¹' (toMeasurable (domainMeasure n E.target) s)) ∩ E.source
        =
        E.symm '' (toMeasurable (domainMeasure n E.target) s ∩ E.target) := by
    simpa [Set.preimage, Set.mem_preimage] using
      (preimage_inter_source_eq_symm_image_inter_target (n := n) (E := E)
        (s := toMeasurable (domainMeasure n E.target) s))
  have hpre_meas :
      MeasurableSet ((fun x ↦ E x) ⁻¹' (toMeasurable (domainMeasure n E.target) s)) :=
    hs_meas.preimage (hE.continuous.measurable)
  have hpre0 :
      (domainMeasure n E.source)
          ((fun x ↦ E x) ⁻¹' (toMeasurable (domainMeasure n E.target) s)) = 0 := by
    -- Restricting to `E.source` amounts to intersecting with `E.source`.
    have :
        (domainMeasure n E.source) ((fun x ↦ E x) ⁻¹' (toMeasurable (domainMeasure n E.target) s))
          =
          (volume : Measure (ℝ^n))
            (((fun x ↦ E x) ⁻¹' (toMeasurable (domainMeasure n E.target) s)) ∩ E.source) := by
      rw [domainMeasure, Measure.restrict_apply hpre_meas]
    rw [this, hpre, himg0]
  have hmap0 :
      (domainMeasure n E.source).map (fun x ↦ E x)
          (toMeasurable (domainMeasure n E.target) s) = 0 := by
    simpa [hmap] using hpre0
  -- Use monotonicity along `s ⊆ toMeasurable s`.
  have hle :
      (domainMeasure n E.source).map (fun x ↦ E x) s
        ≤ (domainMeasure n E.source).map (fun x ↦ E x)
            (toMeasurable (domainMeasure n E.target) s) :=
    measure_mono (subset_toMeasurable (domainMeasure n E.target) s)
  exact le_antisymm (hle.trans_eq hmap0) zero_le

/-- A finite-exponent `L^p` function remains in `L^p` after pullback through
the full source of a smooth partial homeomorphism with bounded target. -/
theorem memLp_comp_partialHomeomorph_of_bounded_target
    (hp : p ≠ ∞)
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (_hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    (hTarget : Bornology.IsBounded E.target)
    {f : ℝ^n → ℝ}
    (hfLp : MeasureTheory.MemLp f p (domainMeasure n E.target)) :
    MeasureTheory.MemLp (fun x ↦ f (E x)) p
      (domainMeasure n E.source) := by
  rcases eLpNorm_comp_partialHomeomorph_le_of_bounded_target
      (n := n) (p := p) hp (E := E) hEsymm hTarget with
    ⟨C, hC, hbound⟩
  exact lt_of_le_of_lt (hbound f)
    (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hC) hfLp.eLpNorm_lt_top)

/-- A compactly supported `Lᵖ` function remains in `Lᵖ` after pullback by a `C¹` partial
homeomorphism with `C¹` inverse.  The statement includes `p = ∞`: finite exponents use the
Jacobian bound on the compact inverse image of the support, while the essential-supremum case
uses only preservation of null sets. -/
theorem memLp_comp_partialHomeomorph_of_compact_support
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 1 (fun x ↦ E x)) (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    {f : ℝ^n → ℝ} (hsupp : Function.support f ⊆ K)
    (hfLp : MeasureTheory.MemLp f p (domainMeasure n E.target)) :
    MeasureTheory.MemLp (fun x ↦ f (E x)) p (domainMeasure n E.source) := by
  classical
  let L : Set (ℝ^n) := E.symm '' K
  have hLcompact : IsCompact L :=
    hK.image hEsymm.continuous
  have hLsub : L ⊆ E.source := by
    rintro x ⟨y, hyK, rfl⟩
    exact E.map_target (hKsub hyK)
  have hEL : E '' L = K := by
    ext y
    constructor
    · rintro ⟨x, ⟨z, hzK, rfl⟩, rfl⟩
      simpa [E.right_inv (hKsub hzK)] using hzK
    · intro hyK
      exact ⟨E.symm y, ⟨y, hyK, rfl⟩, E.right_inv (hKsub hyK)⟩
  have hqmp :
      MeasureTheory.QuasiMeasurePreserving (fun x ↦ E x)
        (domainMeasure n E.source) (domainMeasure n E.target) :=
    quasiMeasurePreserving_partialHomeomorph (n := n) (E := E) hE hEsymm
  have hcompMeas : MeasureTheory.AEStronglyMeasurable (fun x ↦ f (E x))
      (domainMeasure n E.source) := by
    simpa [Function.comp_def] using hfLp.aestronglyMeasurable.comp_quasiMeasurePreserving hqmp
  by_cases hpTop : p = ∞
  · -- Essential bounds pull back along every quasi-measure-preserving map.
    have hfBound : ∀ᵐ y ∂ domainMeasure n E.target,
        ‖f y‖ₑ ≤ MeasureTheory.eLpNormEssSup f (domainMeasure n E.target) :=
      MeasureTheory.enorm_ae_le_eLpNormEssSup f (domainMeasure n E.target)
    have hcompBound : ∀ᵐ x ∂ domainMeasure n E.source,
        ‖f (E x)‖ₑ ≤ MeasureTheory.eLpNormEssSup f (domainMeasure n E.target) :=
      hqmp.ae hfBound
    have hfEssTop : MeasureTheory.eLpNormEssSup f (domainMeasure n E.target) < ∞ := by
      simpa only [hpTop, MeasureTheory.eLpNorm_exponent_top hfLp.aestronglyMeasurable]
        using hfLp.eLpNorm_lt_top
    have hle := MeasureTheory.eLpNormEssSup_le_of_ae_enorm_bound hcompBound
    simpa only [MeasureTheory.memLp_iff, hpTop,
      MeasureTheory.eLpNorm_exponent_top hcompMeas] using hle.trans_lt hfEssTop
  · -- For finite `p`, use a measurable representative and the compact Jacobian estimate.
    let f' : ℝ^n → ℝ := hfLp.aemeasurable.mk f
    have hff' : f =ᵐ[domainMeasure n E.target] f' :=
      hfLp.aemeasurable.ae_eq_mk
    have hf'Lp : MeasureTheory.MemLp f' p (domainMeasure n E.target) :=
      (MeasureTheory.memLp_congr_ae hff').1 hfLp
    have hf'Meas : Measurable f' := hfLp.aemeasurable.measurable_mk
    have hlocal' : MeasureTheory.MemLp (fun x ↦ f' (E x)) p (domainMeasure n L) :=
      memLp_comp_partialHomeomorph_of_compact
        (n := n) (p := p) hpTop (E := E) hE hEsymm hLcompact hLsub hf'Meas hf'Lp
    have hcompAEsource :
        (fun x ↦ f' (E x)) =ᵐ[domainMeasure n E.source] (fun x ↦ f (E x)) :=
      (hqmp.ae_eq_comp hff').symm
    have hμL : (domainMeasure n E.source).restrict L = domainMeasure n L := by
      simpa [domainMeasure] using
        (Measure.restrict_restrict_of_subset
          (μ := (volume : Measure (ℝ^n))) (s := L) (t := E.source) hLsub)
    have hcompAEL :
        (fun x ↦ f' (E x)) =ᵐ[domainMeasure n L] (fun x ↦ f (E x)) := by
      rw [← hμL]
      exact MeasureTheory.ae_restrict_of_ae hcompAEsource
    have hlocal : MeasureTheory.MemLp (fun x ↦ f (E x)) p (domainMeasure n L) :=
      (MeasureTheory.memLp_congr_ae hcompAEL).1 hlocal'
    have hindicator : MeasureTheory.MemLp
        (L.indicator fun x ↦ f (E x)) p (domainMeasure n E.source) := by
      rw [MeasureTheory.memLp_indicator_iff_restrict hLcompact.measurableSet.nullMeasurableSet, hμL]
      exact hlocal
    have hindicatorEq :
        (L.indicator fun x ↦ f (E x)) =ᵐ[domainMeasure n E.source]
          (fun x ↦ f (E x)) := by
      refine MeasureTheory.ae_restrict_of_forall_mem E.open_source.measurableSet ?_
      intro x hxsource
      by_cases hxL : x ∈ L
      · simp [Set.indicator_of_mem hxL]
      · have hExNotK : E x ∉ K := by
          intro hExK
          apply hxL
          exact ⟨E x, hExK, E.left_inv hxsource⟩
        have hfzero : f (E x) = 0 := by
          by_contra hne
          exact hExNotK (hsupp hne)
        simp [hxL, hfzero]
    exact (MeasureTheory.memLp_congr_ae hindicatorEq).1 hindicator

/-!
## Bounded localized pullback on `L^p`

The chart construction first localizes a function to a compact subset `K` of
the chart target and then composes with the inverse chart.  Keeping the compact
localization inside the definition makes this operation canonical on `Lp`
equivalence classes and exposes the compact Jacobian estimate above as a
continuous-linear-map bound.
-/

/-- Compact source set corresponding to a compact set in a partial
homeomorphism's target. -/
noncomputable def compactPullbackSource
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)) (K : Set (ℝ^n)) : Set (ℝ^n) :=
  E.symm '' K

/-- The inverse image of a compact target patch under a continuous inverse
chart is compact. -/
theorem isCompact_compactPullbackSource
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)} {K : Set (ℝ^n)}
    (hEsymm : Continuous (fun x ↦ E.symm x)) (hK : IsCompact K) :
    IsCompact (compactPullbackSource (n := n) E K) := by
  exact hK.image hEsymm

/-- Localize an `Lp` representative to `K` and pull it back through `E`. -/
noncomputable def localizedPullbackFun
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)) (K : Set (ℝ^n))
    (u : MeasureTheory.Lp ℝ p (domainMeasure n E.target)) : ℝ^n → ℝ :=
  fun x ↦ K.indicator (fun y ↦ u y) (E x)

/-- The localized pullback `x ↦ (1_K u)(E x)` lies in `L^p` on the compact source patch
`E.symm '' K`, for every `1 ≤ p ≤ ∞`. -/
theorem memLp_localizedPullbackFun
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (u : MeasureTheory.Lp ℝ p (domainMeasure n E.target)) :
    MeasureTheory.MemLp
      (localizedPullbackFun (n := n) (p := p) E K u) p
      (domainMeasure n (compactPullbackSource (n := n) E K)) := by
  have hKindicator : MeasureTheory.MemLp
      (K.indicator fun y ↦ u y) p (domainMeasure n E.target) :=
    (MeasureTheory.Lp.memLp u).indicator hK.measurableSet.nullMeasurableSet
  have hsupp : Function.support (K.indicator fun y ↦ u y) ⊆ K := by
    intro y hy
    by_contra hyK
    exact hy (Set.indicator_of_notMem hyK (fun y ↦ u y))
  have hcomp := memLp_comp_partialHomeomorph_of_compact_support
    (n := n) (p := p) (E := E) hE hEsymm hK hKsub hsupp hKindicator
  have hrestricted := hcomp.restrict (compactPullbackSource (n := n) E K)
  have hsourceSubset : compactPullbackSource (n := n) E K ⊆ E.source := by
    rintro x ⟨y, hyK, rfl⟩
    exact E.map_target (hKsub hyK)
  have hmeasure :
      (domainMeasure n E.source).restrict (compactPullbackSource (n := n) E K) =
        domainMeasure n (compactPullbackSource (n := n) E K) := by
    simpa [domainMeasure] using
      (Measure.restrict_restrict_of_subset
        (μ := (MeasureTheory.volume : Measure (ℝ^n))) hsourceSubset)
  change MeasureTheory.MemLp
    (fun x ↦ K.indicator (fun y ↦ u y) (E x)) p
      (domainMeasure n (compactPullbackSource (n := n) E K))
  rw [← hmeasure]
  exact hrestricted

/-- The localized chart pullback as an `Lp` value on the corresponding compact
source set. -/
noncomputable def localizedPullbackLp
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (u : MeasureTheory.Lp ℝ p (domainMeasure n E.target)) :
    MeasureTheory.Lp ℝ p
      (domainMeasure n (compactPullbackSource (n := n) E K)) :=
  (memLp_localizedPullbackFun (n := n) (p := p) hE hEsymm hK hKsub u).toLp
    (localizedPullbackFun (n := n) (p := p) E K u)

/-- Almost-everywhere semantics of the localized pullback. -/
theorem localizedPullbackLp_apply_ae
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (u : MeasureTheory.Lp ℝ p (domainMeasure n E.target)) :
    ((localizedPullbackLp (n := n) (p := p) hE hEsymm hK hKsub u :
        MeasureTheory.Lp ℝ p
          (domainMeasure n (compactPullbackSource (n := n) E K))) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (compactPullbackSource (n := n) E K)]
        localizedPullbackFun (n := n) (p := p) E K u :=
  (memLp_localizedPullbackFun (n := n) (p := p) hE hEsymm hK hKsub u).coeFn_toLp

/-- The localized pullback is additive on `L^p`. -/
theorem localizedPullbackLp_add
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (u v : MeasureTheory.Lp ℝ p (domainMeasure n E.target)) :
    localizedPullbackLp (n := n) (p := p) hE hEsymm hK hKsub (u + v) =
      localizedPullbackLp (n := n) (p := p) hE hEsymm hK hKsub u +
        localizedPullbackLp (n := n) (p := p) hE hEsymm hK hKsub v := by
  apply MeasureTheory.Lp.ext
  let μt := domainMeasure n E.target
  let μs := domainMeasure n (compactPullbackSource (n := n) E K)
  have hqmp : MeasureTheory.QuasiMeasurePreserving (fun x ↦ E x)
      (domainMeasure n E.source) μt :=
    quasiMeasurePreserving_partialHomeomorph (n := n) (E := E) hE hEsymm
  have haddTarget : ((u + v : MeasureTheory.Lp ℝ p μt) : ℝ^n → ℝ)
      =ᵐ[μt] fun y ↦ u y + v y := MeasureTheory.Lp.coeFn_add u v
  have haddSource := hqmp.ae_eq_comp haddTarget
  have hsourceSubset : compactPullbackSource (n := n) E K ⊆ E.source := by
    rintro x ⟨y, hyK, rfl⟩
    exact E.map_target (hKsub hyK)
  have hmeasure :
      (domainMeasure n E.source).restrict (compactPullbackSource (n := n) E K) = μs := by
    simpa [μs, domainMeasure] using
      (Measure.restrict_restrict_of_subset
        (μ := (MeasureTheory.volume : Measure (ℝ^n))) hsourceSubset)
  have haddSource' : ∀ᵐ x ∂ μs, (u + v : MeasureTheory.Lp ℝ p μt) (E x) =
      u (E x) + v (E x) := by
    simpa [← hmeasure] using MeasureTheory.ae_restrict_of_ae haddSource
  filter_upwards [
    localizedPullbackLp_apply_ae (n := n) (p := p) hE hEsymm hK hKsub (u + v),
    localizedPullbackLp_apply_ae (n := n) (p := p) hE hEsymm hK hKsub u,
    localizedPullbackLp_apply_ae (n := n) (p := p) hE hEsymm hK hKsub v,
    MeasureTheory.Lp.coeFn_add
      (localizedPullbackLp (n := n) (p := p) hE hEsymm hK hKsub u)
      (localizedPullbackLp (n := n) (p := p) hE hEsymm hK hKsub v),
    haddSource'] with x huv hu hv hout hadd
  have hout' :
      ((localizedPullbackLp (n := n) (p := p) hE hEsymm hK hKsub u +
          localizedPullbackLp (n := n) (p := p) hE hEsymm hK hKsub v :
          MeasureTheory.Lp ℝ p μs) : ℝ^n → ℝ) x =
        (localizedPullbackLp (n := n) (p := p) hE hEsymm hK hKsub u) x +
          (localizedPullbackLp (n := n) (p := p) hE hEsymm hK hKsub v) x := by
    simpa using hout
  rw [huv, hout', hu, hv]
  by_cases hx : E x ∈ K
  · simpa only [localizedPullbackFun, Set.indicator_of_mem hx] using hadd
  · simp [localizedPullbackFun, hx]

/-- The localized pullback commutes with real scalar multiplication. -/
theorem localizedPullbackLp_smul
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (c : ℝ) (u : MeasureTheory.Lp ℝ p (domainMeasure n E.target)) :
    localizedPullbackLp (n := n) (p := p) hE hEsymm hK hKsub (c • u) =
      c • localizedPullbackLp (n := n) (p := p) hE hEsymm hK hKsub u := by
  apply MeasureTheory.Lp.ext
  let μt := domainMeasure n E.target
  let μs := domainMeasure n (compactPullbackSource (n := n) E K)
  have hqmp : MeasureTheory.QuasiMeasurePreserving (fun x ↦ E x)
      (domainMeasure n E.source) μt :=
    quasiMeasurePreserving_partialHomeomorph (n := n) (E := E) hE hEsymm
  have hsmulTarget : ((c • u : MeasureTheory.Lp ℝ p μt) : ℝ^n → ℝ)
      =ᵐ[μt] fun y ↦ c • u y := MeasureTheory.Lp.coeFn_smul c u
  have hsmulSource := hqmp.ae_eq_comp hsmulTarget
  have hsourceSubset : compactPullbackSource (n := n) E K ⊆ E.source := by
    rintro x ⟨y, hyK, rfl⟩
    exact E.map_target (hKsub hyK)
  have hmeasure :
      (domainMeasure n E.source).restrict (compactPullbackSource (n := n) E K) = μs := by
    simpa [μs, domainMeasure] using
      (Measure.restrict_restrict_of_subset
        (μ := (MeasureTheory.volume : Measure (ℝ^n))) hsourceSubset)
  have hsmulSource' : ∀ᵐ x ∂ μs,
      (c • u : MeasureTheory.Lp ℝ p μt) (E x) = c • u (E x) := by
    simpa [← hmeasure] using MeasureTheory.ae_restrict_of_ae hsmulSource
  filter_upwards [
    localizedPullbackLp_apply_ae (n := n) (p := p) hE hEsymm hK hKsub (c • u),
    localizedPullbackLp_apply_ae (n := n) (p := p) hE hEsymm hK hKsub u,
    MeasureTheory.Lp.coeFn_smul c
      (localizedPullbackLp (n := n) (p := p) hE hEsymm hK hKsub u),
    hsmulSource'] with x hcu hu hout hsmul
  have hout' :
      ((c • localizedPullbackLp (n := n) (p := p) hE hEsymm hK hKsub u :
          MeasureTheory.Lp ℝ p μs) : ℝ^n → ℝ) x =
        c * (localizedPullbackLp (n := n) (p := p) hE hEsymm hK hKsub u) x := by
    simpa [smul_eq_mul] using hout
  rw [hcu, hout', hu]
  by_cases hx : E x ∈ K
  · simpa only [localizedPullbackFun, Set.indicator_of_mem hx, smul_eq_mul] using hsmul
  · simp [localizedPullbackFun, hx]

private theorem exists_norm_localizedPullbackLp_le_of_ne_top
    (hp : p ≠ ∞)
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : MeasureTheory.Lp ℝ p (domainMeasure n E.target),
        ‖localizedPullbackLp (n := n) (p := p) hE hEsymm hK hKsub u‖ ≤
          C * ‖u‖ := by
  let L := compactPullbackSource (n := n) E K
  have hLcompact : IsCompact L := by
    exact hK.image hEsymm.continuous
  have hLsub : L ⊆ E.source := by
    rintro x ⟨y, hyK, rfl⟩
    exact E.map_target (hKsub hyK)
  have hEL : E '' L = K := by
    ext y
    constructor
    · rintro ⟨x, ⟨z, hzK, rfl⟩, rfl⟩
      simpa [E.right_inv (hKsub hzK)] using hzK
    · intro hyK
      exact ⟨E.symm y, ⟨y, hyK, rfl⟩, E.right_inv (hKsub hyK)⟩
  rcases eLpNorm_comp_partialHomeomorph_le_of_compact
      (n := n) (p := p) hp (E := E) hEsymm hLcompact hLsub with
    ⟨C, hCtop, hbound⟩
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro u
  let f : ℝ^n → ℝ := K.indicator fun y ↦ u y
  have hfTarget : MeasureTheory.MemLp f p (domainMeasure n E.target) := by
    exact (MeasureTheory.Lp.memLp u).indicator hK.measurableSet.nullMeasurableSet
  have hμKle : domainMeasure n K ≤ domainMeasure n E.target := by
    simpa [domainMeasure] using
      MeasureTheory.Measure.restrict_mono_set
        (MeasureTheory.volume : Measure (ℝ^n)) hKsub
  have hfEq : f =ᵐ[domainMeasure n K] fun y ↦ u y := by
    refine MeasureTheory.ae_restrict_of_forall_mem hK.measurableSet ?_
    intro y hy
    simp [f, hy]
  have hfK : MeasureTheory.MemLp f p (domainMeasure n K) :=
    hfTarget.mono_measure hμKle
  have hnormK : MeasureTheory.eLpNorm f p (domainMeasure n K) ≤
      MeasureTheory.eLpNorm (fun y ↦ u y) p (domainMeasure n E.target) := by
    calc
      MeasureTheory.eLpNorm f p (domainMeasure n K) =
          MeasureTheory.eLpNorm (fun y ↦ u y) p (domainMeasure n K) :=
        MeasureTheory.eLpNorm_congr_ae hfEq
      _ ≤ MeasureTheory.eLpNorm (fun y ↦ u y) p
          (domainMeasure n E.target) :=
        MeasureTheory.eLpNorm_mono_measure _ hμKle
  have hbound' :
      MeasureTheory.eLpNorm (fun x ↦ f (E x)) p (domainMeasure n L) ≤
        C * MeasureTheory.eLpNorm f p (domainMeasure n K) := by
    simpa [hEL] using hbound f
  have hproductTop :
      C * MeasureTheory.eLpNorm f p (domainMeasure n K) ≠ ∞ :=
    ENNReal.mul_ne_top hCtop hfK.eLpNorm_ne_top
  calc
    ‖localizedPullbackLp (n := n) (p := p) hE hEsymm hK hKsub u‖ =
        (MeasureTheory.eLpNorm (fun x ↦ f (E x)) p
          (domainMeasure n L)).toReal := by
      rw [localizedPullbackLp, MeasureTheory.Lp.norm_toLp]
      rfl
    _ ≤ (C * MeasureTheory.eLpNorm f p (domainMeasure n K)).toReal :=
      ENNReal.toReal_mono hproductTop hbound'
    _ = C.toReal * (MeasureTheory.eLpNorm f p (domainMeasure n K)).toReal := by
      rw [ENNReal.toReal_mul]
    _ ≤ C.toReal *
        (MeasureTheory.eLpNorm (fun y ↦ u y) p
          (domainMeasure n E.target)).toReal := by
      exact mul_le_mul_of_nonneg_left
        (ENNReal.toReal_mono (MeasureTheory.Lp.eLpNorm_ne_top u) hnormK)
        ENNReal.toReal_nonneg
    _ = C.toReal * ‖u‖ := by
      rw [MeasureTheory.Lp.norm_def]

private theorem norm_localizedPullbackLp_top_le
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (u : MeasureTheory.Lp ℝ ∞ (domainMeasure n E.target)) :
    ‖localizedPullbackLp (n := n) (p := ∞) hE hEsymm hK hKsub u‖ ≤ ‖u‖ := by
  let L := compactPullbackSource (n := n) E K
  let f : ℝ^n → ℝ := K.indicator fun y ↦ u y
  have hfMeas : MeasureTheory.AEStronglyMeasurable f (domainMeasure n E.target) :=
    (MeasureTheory.Lp.aestronglyMeasurable u).indicator hK.measurableSet
  have hcompMeas : MeasureTheory.AEStronglyMeasurable (fun x ↦ f (E x))
      (domainMeasure n L) :=
    (memLp_localizedPullbackFun (n := n) (p := ∞) hE hEsymm hK hKsub u).aestronglyMeasurable
  have hqmp : MeasureTheory.QuasiMeasurePreserving (fun x ↦ E x)
      (domainMeasure n E.source) (domainMeasure n E.target) :=
    quasiMeasurePreserving_partialHomeomorph (n := n) (E := E) hE hEsymm
  have hboundTarget : ∀ᵐ y ∂ domainMeasure n E.target,
      ‖f y‖ₑ ≤ MeasureTheory.eLpNormEssSup f (domainMeasure n E.target) :=
    MeasureTheory.enorm_ae_le_eLpNormEssSup f (domainMeasure n E.target)
  have hboundSource : ∀ᵐ x ∂ domainMeasure n E.source,
      ‖f (E x)‖ₑ ≤ MeasureTheory.eLpNormEssSup f (domainMeasure n E.target) :=
    hqmp.ae hboundTarget
  have hLsub : L ⊆ E.source := by
    rintro x ⟨y, hyK, rfl⟩
    exact E.map_target (hKsub hyK)
  have hmeasure : (domainMeasure n E.source).restrict L = domainMeasure n L := by
    simpa [domainMeasure] using
      (Measure.restrict_restrict_of_subset
        (μ := (MeasureTheory.volume : Measure (ℝ^n))) hLsub)
  have hboundL : ∀ᵐ x ∂ domainMeasure n L,
      ‖f (E x)‖ₑ ≤ MeasureTheory.eLpNormEssSup f (domainMeasure n E.target) := by
    simpa [← hmeasure] using MeasureTheory.ae_restrict_of_ae hboundSource
  have hess :
      MeasureTheory.eLpNormEssSup (fun x ↦ f (E x)) (domainMeasure n L) ≤
        MeasureTheory.eLpNormEssSup f (domainMeasure n E.target) :=
    MeasureTheory.eLpNormEssSup_le_of_ae_enorm_bound hboundL
  have hnorm :
      MeasureTheory.eLpNorm (fun x ↦ f (E x)) ∞ (domainMeasure n L) ≤
        MeasureTheory.eLpNorm (fun y ↦ u y) ∞ (domainMeasure n E.target) := by
    calc
      MeasureTheory.eLpNorm (fun x ↦ f (E x)) ∞ (domainMeasure n L) =
          MeasureTheory.eLpNormEssSup (fun x ↦ f (E x)) (domainMeasure n L) := by
        exact MeasureTheory.eLpNorm_exponent_top hcompMeas
      _ ≤ MeasureTheory.eLpNormEssSup f (domainMeasure n E.target) := hess
      _ = MeasureTheory.eLpNorm f ∞ (domainMeasure n E.target) := by
        exact (MeasureTheory.eLpNorm_exponent_top hfMeas).symm
      _ ≤ MeasureTheory.eLpNorm (fun y ↦ u y) ∞ (domainMeasure n E.target) := by
        exact MeasureTheory.eLpNorm_indicator_le (fun y ↦ u y) hK.measurableSet.nullMeasurableSet
  calc
    ‖localizedPullbackLp (n := n) (p := ∞) hE hEsymm hK hKsub u‖ =
        (MeasureTheory.eLpNorm (fun x ↦ f (E x)) ∞
          (domainMeasure n L)).toReal := by
      rw [localizedPullbackLp, MeasureTheory.Lp.norm_toLp]
      rfl
    _ ≤ (MeasureTheory.eLpNorm (fun y ↦ u y) ∞
        (domainMeasure n E.target)).toReal :=
      ENNReal.toReal_mono (MeasureTheory.Lp.eLpNorm_ne_top u) hnorm
    _ = ‖u‖ := by
      rw [MeasureTheory.Lp.norm_def]

/-- A uniform real norm bound for compactly localized pullback, including the
endpoint `p = ∞`. -/
theorem exists_norm_localizedPullbackLp_le
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : MeasureTheory.Lp ℝ p (domainMeasure n E.target),
        ‖localizedPullbackLp (n := n) (p := p) hE hEsymm hK hKsub u‖ ≤
          C * ‖u‖ := by
  by_cases hp : p = ∞
  · subst p
    refine ⟨1, zero_le_one, ?_⟩
    intro u
    simpa using norm_localizedPullbackLp_top_le
      (n := n) hE hEsymm hK hKsub u
  · exact exists_norm_localizedPullbackLp_le_of_ne_top
      (n := n) (p := p) hp hE hEsymm hK hKsub

/-- Compactly localized pullback through a `C¹` partial homeomorphism as a
continuous linear map on `L^p`. -/
noncomputable def localizedPullbackCLM
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target) :
    MeasureTheory.Lp ℝ p (domainMeasure n E.target) →L[ℝ]
      MeasureTheory.Lp ℝ p
        (domainMeasure n (compactPullbackSource (n := n) E K)) := by
  let hbound := exists_norm_localizedPullbackLp_le
    (n := n) (p := p) hE hEsymm hK hKsub
  let g :
      MeasureTheory.Lp ℝ p (domainMeasure n E.target) →ₗ[ℝ]
        MeasureTheory.Lp ℝ p
          (domainMeasure n (compactPullbackSource (n := n) E K)) :=
    { toFun := localizedPullbackLp (n := n) (p := p) hE hEsymm hK hKsub
      map_add' := localizedPullbackLp_add
        (n := n) (p := p) hE hEsymm hK hKsub
      map_smul' := localizedPullbackLp_smul
        (n := n) (p := p) hE hEsymm hK hKsub }
  exact LinearMap.mkContinuous
    g
    (Classical.choose hbound) (Classical.choose_spec hbound).2

/-- The continuous linear localized pullback evaluates to `localizedPullbackLp`. -/
@[simp] theorem localizedPullbackCLM_apply
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (u : MeasureTheory.Lp ℝ p (domainMeasure n E.target)) :
    localizedPullbackCLM (n := n) (p := p) hE hEsymm hK hKsub u =
      localizedPullbackLp (n := n) (p := p) hE hEsymm hK hKsub u :=
  rfl

/-- Finite-exponent weak chain rule without global measurability assumptions
on the chosen representatives. No finite-volume hypothesis is needed. -/
theorem hasWeakDerivativeOn_comp_partialHomeomorph_W1p_of_memLp
    (μ : SobolevSpace.Approximation.Mollifier n) (hp : p ≠ ∞)
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {u : ℝ^n → ℝ} (huLp : MeasureTheory.MemLp u p (domainMeasure n E.target))
    {du : Fin n → ℝ^n → ℝ}
    (hduLp : ∀ j, MeasureTheory.MemLp (du j) p (domainMeasure n E.target))
    (hweak : ∀ j, HasWeakDerivativeOn (n := n) E.target [j] u (du j)) :
    ∀ i,
      HasWeakDerivativeOn (n := n) E.source [i] (fun x ↦ u (E x))
        (fun x ↦ ∑ j : Fin n, du j (E x) *
          ((fderiv ℝ (fun x ↦ E x) x)
            (EuclideanSpace.single i (1 : ℝ))) j) := by
  classical
  let μt : Measure (ℝ^n) := domainMeasure n E.target
  let u' : ℝ^n → ℝ := huLp.aemeasurable.mk u
  have hu_ae : u =ᵐ[μt] u' := huLp.aemeasurable.ae_eq_mk
  have hu'_meas : Measurable u' := huLp.aemeasurable.measurable_mk
  have hu'_Lp : MeasureTheory.MemLp u' p μt :=
    (MeasureTheory.memLp_congr_ae (μ := μt) hu_ae).1 huLp
  let du' : Fin n → ℝ^n → ℝ :=
    fun j ↦ (hduLp j).aemeasurable.mk (du j)
  have hdu'_meas : ∀ j, Measurable (du' j) :=
    fun j ↦ (hduLp j).aemeasurable.measurable_mk
  have hdu'_Lp : ∀ j, MeasureTheory.MemLp (du' j) p μt := by
    intro j
    have hAE : du j =ᵐ[μt] du' j :=
      (hduLp j).aemeasurable.ae_eq_mk
    exact (MeasureTheory.memLp_congr_ae (μ := μt) hAE).1 (hduLp j)
  have hweak' : ∀ j, HasWeakDerivativeOn (n := n) E.target [j] u' (du' j) := by
    intro j
    have hAEd : du j =ᵐ[μt] du' j :=
      (hduLp j).aemeasurable.ae_eq_mk
    exact
      ((SobolevSpace.hasWeakDerivativeOn_congr_ae
        (n := n) (Ω := E.target) (α := ([j] : List (Fin n)))
        (f := u) (g := u') (f' := du j) (g' := du' j) hu_ae hAEd).1 (hweak j))
  have hmain : ∀ i,
      HasWeakDerivativeOn (n := n) E.source [i]
        (fun x ↦ u' (E x))
        (fun x ↦ ∑ j : Fin n, du' j (E x) *
          ((fderiv ℝ (fun x ↦ E x) x)
            (EuclideanSpace.single i (1 : ℝ))) j) :=
    hasWeakDerivativeOn_comp_partialHomeomorph_W1p
      (n := n) (p := p) μ hp hE hEsymm hu'_meas hu'_Lp
      hdu'_meas hdu'_Lp hweak'
  have hqmp : MeasureTheory.QuasiMeasurePreserving (fun x ↦ E x)
      (domainMeasure n E.source) (domainMeasure n E.target) :=
    quasiMeasurePreserving_partialHomeomorph (n := n) (E := E) hE hEsymm
  intro i
  have hu_comp : (fun x ↦ u' (E x)) =ᵐ[domainMeasure n E.source]
      fun x ↦ u (E x) := (hqmp.ae_eq_comp hu_ae).symm
  have hdu_comp : ∀ j,
      (fun x ↦ du' j (E x)) =ᵐ[domainMeasure n E.source]
        fun x ↦ du j (E x) := by
    intro j
    exact (hqmp.ae_eq_comp ((hduLp j).aemeasurable.ae_eq_mk)).symm
  have hsum :
      (fun x ↦ ∑ j : Fin n, du' j (E x) *
        ((fderiv ℝ (fun x ↦ E x) x)
          (EuclideanSpace.single i (1 : ℝ))) j) =ᵐ[domainMeasure n E.source]
      fun x ↦ ∑ j : Fin n, du j (E x) *
        ((fderiv ℝ (fun x ↦ E x) x)
          (EuclideanSpace.single i (1 : ℝ))) j := by
    have hall : ∀ᵐ x ∂domainMeasure n E.source,
        ∀ j : Fin n, du' j (E x) = du j (E x) :=
      (MeasureTheory.ae_all_iff.2 hdu_comp)
    filter_upwards [hall] with x hx
    simp [hx]
  exact
    ((SobolevSpace.hasWeakDerivativeOn_congr_ae
      (n := n) (Ω := E.source) (α := ([i] : List (Fin n)))
      (f := fun x ↦ u' (E x)) (g := fun x ↦ u (E x))
      (f' := fun x ↦ ∑ j : Fin n, du' j (E x) *
        ((fderiv ℝ (fun x ↦ E x) x) (EuclideanSpace.single i (1 : ℝ))) j)
      (g' := fun x ↦ ∑ j : Fin n, du j (E x) *
        ((fderiv ℝ (fun x ↦ E x) x) (EuclideanSpace.single i (1 : ℝ))) j)
      hu_comp hsum).1 (hmain i))

/-- The first-order weak chain rule for every exponent `1 ≤ p ≤ ∞` on a finite-volume target,
for arbitrary (not necessarily measurable) representatives `u` and `du j`. Measurable
representatives are chosen with `AEMeasurable.mk`, the chain rule
`hasWeakDerivativeOn_comp_partialHomeomorph_W1` is applied to them, and the identity is
transported back to `u` because `E` is quasi-measure-preserving. -/
theorem hasWeakDerivativeOn_comp_partialHomeomorph_W1_of_memLp
    (μ : SobolevSpace.Approximation.Mollifier n)
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 1 (fun x ↦ E x)) (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    (hvol_target : (MeasureTheory.volume : Measure (ℝ^n)) E.target ≠ ∞)
    {u : ℝ^n → ℝ} (huLp : MeasureTheory.MemLp u p (domainMeasure n E.target))
    {du : Fin n → ℝ^n → ℝ} (hduLp : ∀ j, MeasureTheory.MemLp (du j) p (domainMeasure n E.target))
    (hweak : ∀ j, HasWeakDerivativeOn (n := n) E.target [j] u (du j)) :
    ∀ i,
      HasWeakDerivativeOn (n := n) E.source [i] (fun x ↦ u (E x))
        (fun x ↦ ∑ j : Fin n, du j (E x) *
          (∂[i] (fun z ↦ E z)) x j) := by
  classical
  let μt : Measure (ℝ^n) := domainMeasure n E.target
  -- replace by measurable representatives on `E.target`
  let u' : ℝ^n → ℝ := huLp.aemeasurable.mk u
  have hu_ae : u =ᵐ[μt] u' := huLp.aemeasurable.ae_eq_mk
  have hu'_meas : Measurable u' := huLp.aemeasurable.measurable_mk
  have hu'_Lp : MeasureTheory.MemLp u' p μt :=
    (MeasureTheory.memLp_congr_ae (μ := μt) hu_ae).1 huLp
  let du' : Fin n → ℝ^n → ℝ := fun j ↦ (hduLp j).aemeasurable.mk (du j)
  have hdu'_meas : ∀ j, Measurable (du' j) := fun j ↦ (hduLp j).aemeasurable.measurable_mk
  have hdu'_Lp : ∀ j, MeasureTheory.MemLp (du' j) p μt := by
    intro j
    have hAE : (du j) =ᵐ[μt] (du' j) := (hduLp j).aemeasurable.ae_eq_mk
    exact (MeasureTheory.memLp_congr_ae (μ := μt) hAE).1 (hduLp j)
  have hweak' : ∀ j, HasWeakDerivativeOn (n := n) E.target [j] u' (du' j) := by
    intro j
    have hAEd : du j =ᵐ[μt] du' j := (hduLp j).aemeasurable.ae_eq_mk
    exact
      ((SobolevSpace.hasWeakDerivativeOn_congr_ae
        (n := n) (Ω := E.target) (α := ([j] : List (Fin n)))
        (f := u) (g := u') (f' := du j) (g' := du' j) hu_ae hAEd).1 (hweak j))
  -- The measurable representatives satisfy the preceding chain rule.
  have hmain :
      ∀ i,
        HasWeakDerivativeOn (n := n) E.source [i] (fun x ↦ u' (E x))
          (fun x ↦
            ∑ j : Fin n, du' j (E x) *
              ((fderiv ℝ (fun x ↦ E x) x) (EuclideanSpace.single i (1 : ℝ))) j) := by
    exact
      hasWeakDerivativeOn_comp_partialHomeomorph_W1 (n := n) (p := p) (μ := μ) (E := E)
        hE hEsymm hvol_target (u := u') hu'_meas hu'_Lp (du := du') hdu'_meas hdu'_Lp hweak'
  -- pull back the a.e. equalities through `E` and transfer the identity to `u`
  have hqmp :
      MeasureTheory.QuasiMeasurePreserving (fun x ↦ E x)
        (domainMeasure n E.source) (domainMeasure n E.target) :=
    quasiMeasurePreserving_partialHomeomorph (n := n) (E := E) hE hEsymm
  intro i
  have hu_comp : (fun x ↦ u' (E x)) =ᵐ[domainMeasure n E.source] fun x ↦ u (E x) :=
    (hqmp.ae_eq_comp hu_ae).symm
  have hdu_comp : ∀ j,
      (fun x ↦ du' j (E x)) =ᵐ[domainMeasure n E.source] fun x ↦ du j (E x) := by
    intro j
    have hAE : (du j) =ᵐ[μt] (du' j) := (hduLp j).aemeasurable.ae_eq_mk
    exact (hqmp.ae_eq_comp hAE).symm
  have hsum :
      (fun x ↦
          ∑ j : Fin n, du' j (E x) *
            ((fderiv ℝ (fun x ↦ E x) x) (EuclideanSpace.single i (1 : ℝ))) j)
        =ᵐ[domainMeasure n E.source]
        fun x ↦
          ∑ j : Fin n, du j (E x) *
            ((fderiv ℝ (fun x ↦ E x) x) (EuclideanSpace.single i (1 : ℝ))) j := by
    have hall :
        ∀ᵐ x ∂ domainMeasure n E.source, ∀ j : Fin n, du' j (E x) = du j (E x) :=
      (MeasureTheory.ae_all_iff.2 fun j ↦ hdu_comp j)
    refine hall.mono ?_
    intro x hx
    simp [hx]
  -- replace both `u' ∘ E` and the derivative term by a.e. equal functions
  exact
    ((SobolevSpace.hasWeakDerivativeOn_congr_ae
      (n := n) (Ω := E.source) (α := ([i] : List (Fin n)))
      (f := fun x ↦ u' (E x)) (g := fun x ↦ u (E x))
      (f' := fun x ↦
        ∑ j : Fin n, du' j (E x) *
          ((fderiv ℝ (fun x ↦ E x) x) (EuclideanSpace.single i (1 : ℝ))) j)
      (g' := fun x ↦
        ∑ j : Fin n, du j (E x) *
          ((fderiv ℝ (fun x ↦ E x) x) (EuclideanSpace.single i (1 : ℝ))) j)
      hu_comp hsum).1 (hmain i))

end WeakChangeOfVariables

end SobolevSpace
