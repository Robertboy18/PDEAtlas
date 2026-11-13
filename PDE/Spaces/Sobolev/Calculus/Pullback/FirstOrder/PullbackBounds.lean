/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions
import PDE.Spaces.Sobolev.Approximation.Mollification.Core -- shake: keep
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Quantitative pullback bounds for Sobolev chain rules

`L^p` estimates for composition with a `C¹` partial homeomorphism `E` of `ℝ^n` whose inverse
is also `C¹`. The change-of-variables formula for Lebesgue measure, Mathlib's
`lintegral_image_eq_lintegral_abs_det_fderiv_mul`, gives

`∫_K |f ∘ E|^p = ∫_{E(K)} |f|^p |det D(E⁻¹)|`,

so on a compact `K ⊆ E.source`, or on the whole source when the target is bounded, the
Jacobian of `E⁻¹` is bounded and `‖f ∘ E‖_{L^p(K)} ≤ C ‖f‖_{L^p(E(K))}` with
`C = (max 1 (sup |det D(E⁻¹)|))^{1/p}`. The chain rules use the coordinate expansion of
`fderiv` from `PDE.FDeriv.Calculus`.

## Main results

* `eLpNorm_comp_partialHomeomorph_le_of_compact`: the `L^p` pullback bound on a compact
  subset of the source, for `p < ∞`.
* `eLpNorm_comp_partialHomeomorph_le_of_bounded_target`: the same bound on the full source
  when the target is bounded.
* `memLp_comp_partialHomeomorph_of_compact`: `f ∈ L^p(E.target)` implies `f ∘ E ∈ L^p(K)`.
* `tendsto_eLpNorm_comp_partialHomeomorph_of_compact`: `L^p` convergence on `E '' K` pulls
  back to `L^p` convergence on `K`.

## Implementation notes

The constant is produced existentially as an `ℝ≥0∞` value with `C ≠ ∞`; the estimates are
only used to transfer convergence and membership, never with an explicit value. The exponent
is restricted to `p < ∞` because the argument goes through `∫ |·|^p`. The case `p = ∞` needs
only that `E` preserves null sets and is handled in `LocalizedPullback`.
The positive Jacobian majorant also makes the bound valid when the target norm is infinite.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley, 1999,
  for the change of variables formula for `C¹` diffeomorphisms.
  <https://www.wiley.com/en-us/Real+Analysis%3A+Modern+Techniques+and+Their+Applications%2C+2nd+Edition-p-9780471317166>
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
## Coordinate expansion of `fderiv` for scalar functions on `ℝ^n`
-/

/-!
## `L^p` control under a `C¹` diffeomorphism on compact sets

These lemmas are the analytic input needed to transfer `L^p` convergence on `E '' K` back to
`K` via composition with a `C¹` partial homeomorphism `E`.
-/

private theorem aestronglyMeasurable_comp_partialHomeomorph
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {s : Set (ℝ^n)} (hs : MeasurableSet s) (hsub : s ⊆ E.source)
    (himage : MeasurableSet (E '' s))
    {f : ℝ^n → ℝ} (hf : AEStronglyMeasurable f (domainMeasure n (E '' s))) :
    AEStronglyMeasurable (fun x ↦ f (E x)) (domainMeasure n s) := by
  -- The inverse sends the exceptional null set of a measurable representative to a null set.
  have hbad : volume ({y | f y ≠ hf.mk f y} ∩ (E '' s)) = 0 := by
    simpa only [Filter.EventuallyEq, ae_iff, domainMeasure,
      Measure.restrict_apply' himage] using hf.ae_eq_mk
  have hnull : volume (E.symm '' ({y | f y ≠ hf.mk f y} ∩ (E '' s))) = 0 :=
    MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      volume (hEsymm.differentiable (by simp)).differentiableOn hbad
  have heq : (fun x ↦ f (E x)) =ᵐ[domainMeasure n s]
      fun x ↦ hf.mk f (E x) := by
    rw [Filter.EventuallyEq, ae_iff, domainMeasure, Measure.restrict_apply' hs]
    apply measure_mono_null _ hnull
    rintro x ⟨hxne, hxs⟩
    exact ⟨E x, ⟨hxne, ⟨x, hxs, rfl⟩⟩, E.left_inv (hsub hxs)⟩
  have hEm : AEMeasurable (fun x ↦ E x) (domainMeasure n s) :=
    (E.continuousOn.mono hsub).aemeasurable hs
  exact (hf.measurable_mk.comp_aemeasurable hEm).aestronglyMeasurable.congr heq.symm

/-- The change-of-variables bound behind both pullback estimates: if `s ⊆ E.source` and `E '' s`
lies in a compact set `T`, then `‖f ∘ E‖_{L^p(s)} ≤ C ‖f‖_{L^p(E(s))}` with
`C = (max 1 (sup_T |det D(E⁻¹)|))^{1/p}`. -/
private theorem eLpNorm_comp_le_of_image_subset_compact (hp : p ≠ ∞)
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)} (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {s T : Set (ℝ^n)} (hs : MeasurableSet s) (hsub : s ⊆ E.source)
    (himage : MeasurableSet (E '' s)) (hT : IsCompact T) (hsT : E '' s ⊆ T) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : ℝ^n → ℝ,
      eLpNorm (fun x ↦ f (E x)) p (domainMeasure n s) ≤
        C * eLpNorm f p (domainMeasure n (E '' s)) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hz : 0 ≤ 1 / p.toReal := by positivity
  set J : ℝ^n → ℝ := fun y ↦ |(fderiv ℝ (fun z ↦ E.symm z) y).det|
  have hJ : Continuous J :=
    (ContinuousLinearMap.continuous_det.comp (hEsymm.continuous_fderiv one_ne_zero)).abs
  set C0 : ℝ := max 1 (sSup (J '' T))
  have hC0 : 0 < ENNReal.ofReal C0 ^ (1 / p.toReal) :=
    ENNReal.rpow_pos_of_nonneg (ENNReal.ofReal_pos.2 (zero_lt_one.trans_le (le_max_left _ _))) hz
  refine ⟨ENNReal.ofReal C0 ^ (1 / p.toReal), rpow_ne_top_of_nonneg hz ofReal_ne_top, fun f ↦ ?_⟩
  by_cases hf : AEStronglyMeasurable f (domainMeasure n (E '' s))
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hf, ENNReal.mul_top hC0.ne']
    exact le_top
  have htarget : E '' s ⊆ E.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact E.map_source (hsub hx)
  -- change of variables `x = E⁻¹ y` on `E '' s`
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume himage
    (fun y _ ↦ (hEsymm.differentiable one_ne_zero y).hasFDerivAt.hasFDerivWithinAt)
    (E.symm.injOn.mono htarget) fun x ↦ ‖f (E x)‖ₑ ^ p.toReal
  rw [show (fun y ↦ E.symm y) '' (E '' s) = s from
    E.toPartialEquiv.symm_image_image_of_subset_source hsub] at hcv
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp
      (aestronglyMeasurable_comp_partialHomeomorph hEsymm hs hsub himage hf),
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hf, ← ENNReal.mul_rpow_of_nonneg _ _ hz]
  gcongr
  calc ∫⁻ x in s, ‖f (E x)‖ₑ ^ p.toReal
      = ∫⁻ y in E '' s, ENNReal.ofReal (J y) * ‖f y‖ₑ ^ p.toReal :=
        hcv.trans <| setLIntegral_congr_fun himage fun y hy ↦ by
          simp only [E.right_inv (htarget hy), J]
    _ ≤ ∫⁻ y in E '' s, ENNReal.ofReal C0 * ‖f y‖ₑ ^ p.toReal :=
        setLIntegral_mono' himage fun y hy ↦ by
          gcongr
          exact (le_csSup (hT.image hJ).bddAbove (mem_image_of_mem J (hsT hy))).trans
            (le_max_right _ _)
    _ = _ := lintegral_const_mul' _ _ ofReal_ne_top

/-- On a compact `K ⊆ E.source`, `‖f ∘ E‖_{L^p(K)} ≤ C ‖f‖_{L^p(E(K))}` for some finite
constant `C` depending only on `E`, `K` and `p`. The statement is existential; the proof takes
`C = (max 1 (sup_{E(K)} |det D(E⁻¹)|))^{1/p}`. Only `E⁻¹ ∈ C¹` is used, through the
change-of-variables formula on `E(K)`; the hypothesis `p < ∞` keeps the `L^p` norm an
integral. -/
theorem eLpNorm_comp_partialHomeomorph_le_of_compact (hp : p ≠ ∞)
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.source) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ f : ℝ^n → ℝ,
        MeasureTheory.eLpNorm (fun x ↦ f (E x)) p (domainMeasure n K)
          ≤ C * MeasureTheory.eLpNorm f p (domainMeasure n (E '' K)) :=
  have hKE := hK.image_of_continuousOn (E.continuousOn.mono hKsub)
  eLpNorm_comp_le_of_image_subset_compact hp hEsymm hK.measurableSet hKsub hKE.measurableSet hKE
    subset_rfl

/-- Pullback on the full source of a partial homeomorphism is bounded on
`L^p` when the target is bounded and the total inverse representative is
`C^1`. Unlike the compact-patch estimate, this includes points arbitrarily
close to the boundary of the source and target. -/
theorem eLpNorm_comp_partialHomeomorph_le_of_bounded_target (hp : p ≠ ∞)
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    (hTarget : Bornology.IsBounded E.target) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ f : ℝ^n → ℝ,
        MeasureTheory.eLpNorm (fun x ↦ f (E x)) p
            (domainMeasure n E.source) ≤
          C * MeasureTheory.eLpNorm f p (domainMeasure n E.target) := by
  have h := eLpNorm_comp_le_of_image_subset_compact hp hEsymm E.open_source.measurableSet
    subset_rfl (E.image_source_eq_target ▸ E.open_target.measurableSet)
    hTarget.isCompact_closure (E.image_source_eq_target ▸ subset_closure)
  rwa [E.image_source_eq_target] at h

/-- Pulling an `Lᵖ` function back through a `C¹` partial homeomorphism preserves `Lᵖ` on every
compact subset of the source. -/
theorem memLp_comp_partialHomeomorph_of_compact (hp : p ≠ ∞)
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (_hE : ContDiff ℝ 1 (fun x ↦ E x)) (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.source)
    {f : ℝ^n → ℝ} (_hf_meas : Measurable f)
    (hfLp : MeasureTheory.MemLp f p (domainMeasure n E.target)) :
    MeasureTheory.MemLp (fun x ↦ f (E x)) p (domainMeasure n K) := by
  obtain ⟨C, hC, hbound⟩ := eLpNorm_comp_partialHomeomorph_le_of_compact hp hEsymm hK hKsub
  have hfK : MemLp f p (domainMeasure n (E '' K)) := hfLp.mono_measure <|
    Measure.restrict_mono_set volume fun _ ⟨x, hx, h⟩ ↦ h ▸ E.map_source (hKsub hx)
  exact (hbound f).trans_lt (ENNReal.mul_lt_top hC.lt_top hfK.eLpNorm_lt_top)

/-- `L^p` convergence `f_m → f` on the image `E '' K` of a compact `K ⊆ E.source` pulls back to
`L^p` convergence `f_m ∘ E → f ∘ E` on `K`, by the compact-patch pullback bound. -/
theorem tendsto_eLpNorm_comp_partialHomeomorph_of_compact (hp : p ≠ ∞)
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.source)
    {f : ℕ → ℝ^n → ℝ} {f_lim : ℝ^n → ℝ}
    (h :
      Filter.Tendsto
        (fun m ↦
          MeasureTheory.eLpNorm (fun y ↦ f m y - f_lim y) p (domainMeasure n (E '' K)))
        Filter.atTop (𝓝 0)) :
    Filter.Tendsto
      (fun m ↦
        MeasureTheory.eLpNorm (fun x ↦ f m (E x) - f_lim (E x)) p (domainMeasure n K))
      Filter.atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := eLpNorm_comp_partialHomeomorph_le_of_compact hp hEsymm hK hKsub
  have hC0 := ENNReal.Tendsto.const_mul h (Or.inr hC)
  rw [mul_zero] at hC0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hC0 (fun _ ↦ zero_le)
    fun m ↦ hbound fun y ↦ f m y - f_lim y


end WeakChangeOfVariables

end SobolevSpace
