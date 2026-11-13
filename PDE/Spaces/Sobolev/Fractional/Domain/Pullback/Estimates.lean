/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Pullback.Measure

/-!
# Intrinsic fractional estimates under chart pullback

A forward Lipschitz bound `L` controls the distance kernel, and an inverse volume
majorant `D` controls each integration variable. The p-th power of the difference
seminorm therefore grows by at most `D² (L^(n / p.toReal + s))^p.toReal`.
Only a nonnegative distance exponent is needed, with no upper bound on the order.
The estimates hold for normed real codomains, including in dimension zero.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace SobolevSpace.Fractional.Pullback

variable {n : ℕ} {s : ℝ} {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)} {L D : ℝ≥0}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞}

/-- The distance kernel is controlled by the forward Lipschitz constant.
No finite-exponent or completeness assumption is needed for this pointwise bound. -/
theorem norm_diffQuot_comp_le
    (hs : 0 ≤ (n : ℝ) / p.toReal + s) (hL : LipschitzOnWith L E E.source)
    (u : ℝ^n → F) {x y : ℝ^n} (hx : x ∈ E.source) (hy : y ∈ E.source) :
    ‖diffQuot n s (u ∘ E) (x, y) (p := p)‖ ≤
      (L : ℝ) ^ ((n : ℝ) / p.toReal + s) *
        ‖diffQuot n s u (E x, E y) (p := p)‖ := by
  by_cases hxy : E x = E y
  · simp [diffQuot, hxy]
  have hxyn : x ≠ y := fun h ↦ hxy (congrArg E h)
  have ha : 0 < ‖x - y‖ ^ ((n : ℝ) / p.toReal + s) :=
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxyn)) _
  have hb : 0 < ‖E x - E y‖ ^ ((n : ℝ) / p.toReal + s) :=
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) _
  have hdist : ‖E x - E y‖ ≤ L * ‖x - y‖ := by
    simpa only [dist_eq_norm] using hL.dist_le_mul x hx y hy
  have hpow := Real.rpow_le_rpow (norm_nonneg _) hdist hs
  rw [Real.mul_rpow L.coe_nonneg (norm_nonneg _)] at hpow
  simp only [diffQuot, Function.comp_apply, norm_smul, norm_inv,
    Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  simp only [← div_eq_inv_mul]
  apply (div_le_iff₀ ha).mpr
  calc
    ‖u (E x) - u (E y)‖ =
        (‖u (E x) - u (E y)‖ / ‖E x - E y‖ ^ ((n : ℝ) / p.toReal + s)) *
          ‖E x - E y‖ ^ ((n : ℝ) / p.toReal + s) := (div_mul_cancel₀ _ hb.ne').symm
    _ ≤ (‖u (E x) - u (E y)‖ / ‖E x - E y‖ ^ ((n : ℝ) / p.toReal + s)) *
        ((L : ℝ) ^ ((n : ℝ) / p.toReal + s) *
          ‖x - y‖ ^ ((n : ℝ) / p.toReal + s)) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring

/-- Change of variables for the power integral of the weighted difference.
For finite positive `p`, this is the fractional p-energy. -/
theorem lintegral_diffQuot_comp_le
    (hs : 0 ≤ (n : ℝ) / p.toReal + s) (hE : Measurable (fun x ↦ E x))
    (hL : LipschitzOnWith L E E.source)
    (hD : Measure.map E (volume.restrict E.source) ≤
      (D : ℝ≥0∞) • volume.restrict E.target)
    {u : ℝ^n → F} (hu : AEStronglyMeasurable u (volume.restrict E.target)) :
    (∫⁻ z, ‖diffQuot n s (u ∘ E) z (p := p)‖ₑ ^ p.toReal
      ∂gagliardoProductMeasure n E.source) ≤
      ENNReal.ofReal ((L : ℝ) ^ ((n : ℝ) / p.toReal + s)) ^ p.toReal *
        (D : ℝ≥0∞) ^ 2 *
          ∫⁻ z, ‖diffQuot n s u z (p := p)‖ₑ ^ p.toReal
            ∂gagliardoProductMeasure n E.target := by
  have hmeas := (aestronglyMeasurable_diffQuot (s := s) (p := p) hu).enorm
  have hmem := ae_restrict_mem (μ := volume) E.open_source.measurableSet
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal ((L : ℝ) ^ ((n : ℝ) / p.toReal + s)) ^ p.toReal *
        ‖diffQuot n s u (Prod.map E E z) (p := p)‖ₑ ^ p.toReal
          ∂gagliardoProductMeasure n E.source := by
      apply lintegral_mono_ae
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae hmem,
        Measure.quasiMeasurePreserving_snd.ae hmem] with z hx hy
      have hnorm := norm_diffQuot_comp_le hs hL u hx hy
      have h := ENNReal.ofReal_le_ofReal hnorm
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg L.coe_nonneg _)] at h
      simpa only [← ofReal_norm, Prod.map_apply', Prod.mk.eta,
        ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg]
        using ENNReal.rpow_le_rpow h ENNReal.toReal_nonneg
    _ = ENNReal.ofReal ((L : ℝ) ^ ((n : ℝ) / p.toReal + s)) ^ p.toReal *
        ∫⁻ z, ‖diffQuot n s u (Prod.map E E z) (p := p)‖ₑ ^ p.toReal
          ∂gagliardoProductMeasure n E.source :=
      lintegral_const_mul' _ _
        (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top).ne
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (lintegral_comp_le_of_map_le (hE.prodMap hE)
        (map_gagliardoProductMeasure_le hE hD) (hmeas.pow_const _)) zero_le

/-- The quadratic seminorm estimate is the exponent-two specialization. -/
theorem gagliardoSq_comp_le
    (hs : 0 ≤ (n : ℝ) / 2 + s) (hE : Measurable (fun x ↦ E x))
    (hL : LipschitzOnWith L E E.source)
    (hD : Measure.map E (volume.restrict E.source) ≤
      (D : ℝ≥0∞) • volume.restrict E.target)
    {u : ℝ^n → F} (hu : AEStronglyMeasurable u (volume.restrict E.target)) :
    gagliardoSq n s E.source (u ∘ E) ≤
      ENNReal.ofReal ((L : ℝ) ^ ((n : ℝ) / 2 + s)) ^ 2 *
        (D : ℝ≥0∞) ^ 2 * gagliardoSq n s E.target u := by
  simpa only [gagliardoSq, ENNReal.toReal_ofNat, ENNReal.rpow_two, enorm_eq_nnnorm]
    using lintegral_diffQuot_comp_le (p := 2) hs hE hL hD hu

omit [NormedSpace ℝ F] in
/-- Pullback preserves `Lᵖ` under a finite volume majorant, at every exponent. -/
theorem memLp_comp (hE : Measurable (fun x ↦ E x))
    (hD : Measure.map E (volume.restrict E.source) ≤
      (D : ℝ≥0∞) • volume.restrict E.target)
    {u : ℝ^n → F} (hu : MemLp u p (volume.restrict E.target)) :
    MemLp (u ∘ E) p (volume.restrict E.source) :=
  ((hu.smul_measure ENNReal.coe_ne_top).mono_measure hD).comp_of_map hE.aemeasurable

/-- The physical kernel and measure bounds preserve fractional membership.
This also holds at infinity, where the weighted difference expresses an essential
Hölder bound; no Banach-space assumption is used. -/
theorem memGagliardo_comp
    (hs : 0 ≤ (n : ℝ) / p.toReal + s) (hE : Measurable (fun x ↦ E x))
    (hL : LipschitzOnWith L E E.source)
    (hD : Measure.map E (volume.restrict E.source) ≤
      (D : ℝ≥0∞) • volume.restrict E.target)
    {u : ℝ^n → F} (hu : MemGagliardo n s E.target u (p := p)) :
    MemGagliardo n s E.source (u ∘ E) (p := p) := by
  have hbase := memLp_comp hE hD hu.1
  refine ⟨hbase, ?_⟩
  have hdiff : MemLp (diffQuot n s u (p := p) ∘ Prod.map E E) p
      (gagliardoProductMeasure n E.source) :=
    ((hu.2.smul_measure (by finiteness)).mono_measure
      (map_gagliardoProductMeasure_le hE hD)).comp_of_map (hE.prodMap hE).aemeasurable
  apply (hdiff.const_smul ((L : ℝ) ^ ((n : ℝ) / p.toReal + s))).mono
    (aestronglyMeasurable_diffQuot hbase.aestronglyMeasurable)
  have hmem := ae_restrict_mem (μ := volume) E.open_source.measurableSet
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hmem,
    Measure.quasiMeasurePreserving_snd.ae hmem] with z hx hy
  simpa only [Pi.smul_apply, norm_smul,
    Real.norm_of_nonneg (Real.rpow_nonneg L.coe_nonneg _), Function.comp_apply,
    Prod.map_apply'] using norm_diffQuot_comp_le hs hL u hx hy

end SobolevSpace.Fractional.Pullback
