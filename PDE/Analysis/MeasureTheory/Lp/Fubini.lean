/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.LpNorm
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fubini for joint representatives of Bochner L² curves

A jointly measurable function whose spatial slices represent a Bochner L² curve is
square integrable for the product measure. The proof uses the L² norm identity
on each slice and Fubini's integrability criterion. Only the spatial measure is s-finite;
the outer measure is arbitrary. Real-valued Fubini follows from one-sided Tonelli applied
to positive and negative parts, so no finiteness assumption on the outer measure is added.

For two such representatives, the product-space integral of their pointwise inner product
equals the time integral of the inner products of their L² classes. Joint measurability
and almost-everywhere slice agreement are hypotheses. Every Bochner L² curve has such a
representative by `MemLp.exists_jointRepresentative`.
-/

@[expose] public section

noncomputable section

open Filter
open scoped ENNReal InnerProductSpace MeasureTheory

namespace MeasureTheory

section RealFubini

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [SFinite ν]

/-- Tonelli gives one-sided Fubini for a nonnegative integrable real function,
without any finiteness assumption on the outer measure. -/
private theorem integral_prod_nonneg {f : α × β → ℝ}
    (hf : Integrable f (μ.prod ν)) (hnonneg : 0 ≤ᵐ[μ.prod ν] f) :
    (∫ z, f z ∂μ.prod ν) = ∫ t, ∫ x, f (t, x) ∂ν ∂μ := by
  have hsections : ∀ᵐ t ∂μ, Integrable (fun x ↦ f (t, x)) ν :=
    ((integrable_prod_iff hf.aestronglyMeasurable).1 hf).1
  have hnonneg_sections : ∀ᵐ t ∂μ, 0 ≤ᵐ[ν] fun x ↦ f (t, x) :=
    Measure.ae_ae_of_ae_prod hnonneg
  have hnonneg_integrals : 0 ≤ᵐ[μ] fun t ↦ ∫ x, f (t, x) ∂ν :=
    hnonneg_sections.mono fun _ ht ↦ integral_nonneg_of_ae ht
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg hf.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae hnonneg_integrals
      hf.aestronglyMeasurable.integral_prod_right']
  congr 1
  rw [lintegral_prod _ hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal]
  apply lintegral_congr_ae
  filter_upwards [hsections, hnonneg_sections] with t ht htnonneg
  exact (ofReal_integral_eq_lintegral_ofReal ht htnonneg).symm

/-- An integrable real function on a product has the indicated iterated integral.
Only the inner measure is s-finite; the outer measure is arbitrary. The proof applies
Tonelli to the positive and negative parts, without interchanging the measures. -/
theorem integral_prod_real (f : α × β → ℝ) (hf : Integrable f (μ.prod ν)) :
    (∫ z, f z ∂μ.prod ν) = ∫ t, ∫ x, f (t, x) ∂ν ∂μ := by
  have hfneg : Integrable (fun z ↦ (Real.toNNReal (-f z) : ℝ)) (μ.prod ν) := by
    simpa only [Pi.neg_apply] using hf.neg.real_toNNReal
  rw [integral_eq_integral_pos_part_sub_integral_neg_part hf,
    integral_prod_nonneg hf.real_toNNReal
      (Eventually.of_forall fun _ ↦ NNReal.coe_nonneg _),
    integral_prod_nonneg hfneg
      (Eventually.of_forall fun _ ↦ NNReal.coe_nonneg _),
    ← integral_sub hf.real_toNNReal.integral_prod_left hfneg.integral_prod_left]
  apply integral_congr_ae
  filter_upwards [((integrable_prod_iff hf.aestronglyMeasurable).1 hf).1] with t ht
  exact (integral_eq_integral_pos_part_sub_integral_neg_part ht).symm

end RealFubini

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] {μ : Measure α} {ν : Measure β} [SFinite ν]

/-- A jointly measurable representative of a Bochner L² curve is L² on the product
measure. Slice agreement is required only for almost every parameter. -/
theorem memLp_prod_of_ae_eq_L2_sections
    {u : α → Lp E 2 ν} {U : α × β → E}
    (hu : MemLp u 2 μ) (hU : AEStronglyMeasurable U (μ.prod ν))
    (hsection : ∀ᵐ t ∂μ, (fun x ↦ U (t, x)) =ᵐ[ν] (u t : β → E)) :
    MemLp U 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq_norm hU).2
  apply (integrable_prod_iff (hU.norm.pow 2)).2
  constructor
  · filter_upwards [hsection] with t ht
    exact ((Lp.memLp (u t)).norm.integrable_sq).congr
      (ht.fun_comp (fun z : E ↦ ‖z‖ ^ 2)).symm
  · have hnorm :
        (fun t ↦ ∫ x, ‖‖U (t, x)‖ ^ 2‖ ∂ν) =ᵐ[μ] fun t ↦ ‖u t‖ ^ 2 := by
      filter_upwards [hsection] with t ht
      calc
        (∫ x, ‖‖U (t, x)‖ ^ 2‖ ∂ν) = ∫ x, ‖(u t) x‖ ^ 2 ∂ν := by
          apply integral_congr_ae
          filter_upwards [ht] with x hx
          rw [hx, Real.norm_of_nonneg (sq_nonneg _)]
        _ = ‖u t‖ ^ 2 := (Lp.norm_sq_eq_integral_norm_sq (u t)).symm
    exact hu.norm.integrable_sq.congr hnorm.symm

variable [InnerProductSpace ℝ E]

/-- The pointwise inner product of joint representatives of two Bochner L² curves
is integrable on the product measure. -/
theorem integrable_inner_prod_of_ae_eq_L2_sections
    {u v : α → Lp E 2 ν} {U V : α × β → E}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ)
    (hU : AEStronglyMeasurable U (μ.prod ν))
    (hV : AEStronglyMeasurable V (μ.prod ν))
    (hUsec : ∀ᵐ t ∂μ, (fun x ↦ U (t, x)) =ᵐ[ν] (u t : β → E))
    (hVsec : ∀ᵐ t ∂μ, (fun x ↦ V (t, x)) =ᵐ[ν] (v t : β → E)) :
    Integrable (fun z ↦ inner ℝ (U z) (V z)) (μ.prod ν) := by
  have hUp := memLp_prod_of_ae_eq_L2_sections hu hU hUsec
  have hVp := memLp_prod_of_ae_eq_L2_sections hv hV hVsec
  apply (L2.integrable_inner (𝕜 := ℝ) (hUp.toLp U) (hVp.toLp V)).congr
  filter_upwards [hUp.coeFn_toLp, hVp.coeFn_toLp] with z hzU hzV
  rw [hzU, hzV]

/-- Fubini converts a product-space pairing into the time pairing of the
represented L² classes. Integrability is derived from their Bochner L² hypotheses. -/
theorem integral_inner_prod_eq_integral_L2_inner
    {u v : α → Lp E 2 ν} {U V : α × β → E}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ)
    (hU : AEStronglyMeasurable U (μ.prod ν))
    (hV : AEStronglyMeasurable V (μ.prod ν))
    (hUsec : ∀ᵐ t ∂μ, (fun x ↦ U (t, x)) =ᵐ[ν] (u t : β → E))
    (hVsec : ∀ᵐ t ∂μ, (fun x ↦ V (t, x)) =ᵐ[ν] (v t : β → E)) :
    (∫ z, inner ℝ (U z) (V z) ∂μ.prod ν) =
      ∫ t, inner ℝ (u t) (v t) ∂μ := by
  rw [integral_prod_real _ (integrable_inner_prod_of_ae_eq_L2_sections
    hu hv hU hV hUsec hVsec)]
  apply integral_congr_ae
  filter_upwards [hUsec, hVsec] with t htU htV
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [htU, htV] with x hxU hxV
  rw [hxU, hxV]

end MeasureTheory

end
