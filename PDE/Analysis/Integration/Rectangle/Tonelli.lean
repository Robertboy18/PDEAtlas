/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.Rectangle.MixedPrimitive

/-!
# Nonnegative integrands on rectangles: integrability from the iterated integral

For a measurable function `f ≥ 0` on the closed rectangle `[a, b] × [c, d]` of `ℝ^2`,
Tonelli's theorem computes its lower integral as the iterated interval integral in coordinates as
soon as the inner integrals and the outer integral exist. In particular `f` is integrable on the
rectangle and its set integral is the iterated integral, also when `f` has a singularity, such as
a corner pole, at which the continuous form `setIntegral_coordinateRectangle` does not apply.

## Main results

* `lintegral_coordinateRectangle_eq`: `∫⁻_{[a,b] × [c,d]} f = ∫_a^b ∫_c^d f(p, q) dq dp` when the
  inner and outer integrals exist.
* `integrableOn_coordinateRectangle_of_nonneg`: a measurable `f ≥ 0` with finite iterated
  integral is integrable on the rectangle.
* `setIntegral_coordinateRectangle_of_nonneg`: the set integral of such an `f` over the rectangle
  is its iterated integral.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Analysis

/-- The rectangle `[a, b] × [c, d]` of `ℝ^2` is the preimage of `Icc a b ×ˢ Icc c d` under
`planeEquiv`. -/
private theorem coordinateRectangle_eq_preimage (a b c d : ℝ) :
    coordinateRectangle a b c d = planeEquiv ⁻¹' (Icc a b ×ˢ Icc c d) := by
  ext y
  simp only [mem_coordinateRectangle, mem_preimage, planeEquiv_apply, mem_prod]

/-- If `f ≥ 0` on `[a, b] × [c, d]` and `p ∈ [a, b]`, the inner integral `∫_c^d f(p, q) dq` is
nonnegative. -/
private theorem intervalIntegral_nonneg_of_mem {f : ℝ^2 → ℝ} {a b c d p : ℝ} (hcd : c ≤ d)
    (hp : p ∈ Icc a b) (h0 : ∀ y ∈ coordinateRectangle a b c d, 0 ≤ f y) :
    0 ≤ ∫ q in c..d, f !₂[p, q] :=
  intervalIntegral.integral_nonneg hcd fun q hq ↦ h0 _ ⟨by simpa using hp, by simpa using hq⟩

/-- **Tonelli on a rectangle.** For a measurable `f ≥ 0` on `[a, b] × [c, d]` whose inner integrals
exist for `a < p < b` and whose outer integral exists,
`∫⁻_{[a,b] × [c,d]} f = ∫_a^b ∫_c^d f(p, q) dq dp`. -/
theorem lintegral_coordinateRectangle_eq {f : ℝ^2 → ℝ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hf : Measurable f) (h0 : ∀ y ∈ coordinateRectangle a b c d, 0 ≤ f y)
    (hin : ∀ p ∈ Ioo a b, IntervalIntegrable (fun q ↦ f !₂[p, q]) volume c d)
    (hout : IntervalIntegrable (fun p ↦ ∫ q in c..d, f !₂[p, q]) volume a b) :
    ∫⁻ y in coordinateRectangle a b c d, ENNReal.ofReal (f y) =
      ENNReal.ofReal (∫ p in a..b, ∫ q in c..d, f !₂[p, q]) := by
  rw [coordinateRectangle_eq_preimage]
  have h1 := measurePreserving_planeEquiv.setLIntegral_comp_preimage_emb
    planeEquiv.measurableEmbedding (fun p ↦ ENNReal.ofReal (f (planeEquiv.symm p)))
    (Icc a b ×ˢ Icc c d)
  simp only [MeasurableEquiv.symm_apply_apply] at h1
  rw [h1, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hmeas : Measurable fun p : ℝ × ℝ ↦ ENNReal.ofReal (f (planeEquiv.symm p)) :=
    ENNReal.measurable_ofReal.comp (hf.comp planeEquiv.symm.measurable)
  rw [lintegral_prod _ hmeas.aemeasurable]
  simp only [planeEquiv_symm_apply]
  -- the inner lower integrals are the inner interval integrals for `a < p < b`
  have hinner : ∀ᵐ p ∂(volume.restrict (Icc a b)),
      ∫⁻ q in Icc c d, ENNReal.ofReal (f !₂[p, q]) =
        ENNReal.ofReal (∫ q in c..d, f !₂[p, q]) := by
    have hIoo : ∀ᵐ p ∂(volume.restrict (Icc a b)), p ∈ Ioo a b := by
      rw [ae_restrict_iff' measurableSet_Icc]
      have : ∀ᵐ p ∂volume, p ≠ a ∧ p ≠ b := by
        filter_upwards [Measure.ae_ne volume a, Measure.ae_ne volume b] with p h1 h2
        exact ⟨h1, h2⟩
      filter_upwards [this] with p hp hpI
      exact ⟨lt_of_le_of_ne hpI.1 (Ne.symm hp.1), lt_of_le_of_ne hpI.2 hp.2⟩
    filter_upwards [hIoo] with p hp
    rw [intervalIntegral.integral_of_le hcd, ← integral_Icc_eq_integral_Ioc,
      ofReal_integral_eq_lintegral_ofReal]
    · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hcd).1 (hin p hp)
    · exact (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun q hq ↦
        h0 _ ⟨by simpa using Ioo_subset_Icc_self hp, by simpa using hq⟩)
  rw [lintegral_congr_ae hinner, intervalIntegral.integral_of_le hab,
    ← integral_Icc_eq_integral_Ioc, ofReal_integral_eq_lintegral_ofReal]
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).1 hout
  · exact (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun p hp ↦
      intervalIntegral_nonneg_of_mem hcd hp h0)

/-- A measurable `f ≥ 0` with finite iterated integral is integrable on the rectangle. -/
theorem integrableOn_coordinateRectangle_of_nonneg {f : ℝ^2 → ℝ} {a b c d : ℝ} (hab : a ≤ b)
    (hcd : c ≤ d) (hf : Measurable f) (h0 : ∀ y ∈ coordinateRectangle a b c d, 0 ≤ f y)
    (hin : ∀ p ∈ Ioo a b, IntervalIntegrable (fun q ↦ f !₂[p, q]) volume c d)
    (hout : IntervalIntegrable (fun p ↦ ∫ q in c..d, f !₂[p, q]) volume a b) :
    IntegrableOn f (coordinateRectangle a b c d) := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have heq : ∫⁻ y in coordinateRectangle a b c d, ‖f y‖ₑ =
      ∫⁻ y in coordinateRectangle a b c d, ENNReal.ofReal (f y) := by
    refine setLIntegral_congr_fun (measurableSet_coordinateRectangle a b c d) fun y hy ↦ ?_
    rw [Real.enorm_eq_ofReal (h0 y hy)]
  rw [heq, lintegral_coordinateRectangle_eq hab hcd hf h0 hin hout]
  exact ENNReal.ofReal_lt_top

/-- **Fubini for nonnegative integrands with a singularity**: the set integral of a measurable
`f ≥ 0` over `[a, b] × [c, d]` is its iterated integral as soon as the latter exists. -/
theorem setIntegral_coordinateRectangle_of_nonneg {f : ℝ^2 → ℝ} {a b c d : ℝ} (hab : a ≤ b)
    (hcd : c ≤ d) (hf : Measurable f) (h0 : ∀ y ∈ coordinateRectangle a b c d, 0 ≤ f y)
    (hin : ∀ p ∈ Ioo a b, IntervalIntegrable (fun q ↦ f !₂[p, q]) volume c d)
    (hout : IntervalIntegrable (fun p ↦ ∫ q in c..d, f !₂[p, q]) volume a b) :
    ∫ y in coordinateRectangle a b c d, f y = ∫ p in a..b, ∫ q in c..d, f !₂[p, q] :=
  setIntegral_coordinateRectangle_of_integrableOn hab hcd
    (integrableOn_coordinateRectangle_of_nonneg hab hcd hf h0 hin hout)

end PDE.Analysis
