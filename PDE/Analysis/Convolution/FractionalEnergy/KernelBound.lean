/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Bounds for signed compact kernels

Hölder's inequality controls a compact-kernel average by the local power energy.
For Banach-valued locally integrable data, compactness also ensures that the signed convolution
exists at every positive scale, so zero mean permits subtraction of the base value.
-/

@[expose] public section

open MeasureTheory Set Module
open scoped ENNReal

namespace ENNReal

/-- Hölder's inequality for one function and the constant function one, raised to a power. -/
theorem rpow_lintegral_le_mul_lintegral_rpow
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {p : ℝ} (hp : 1 < p) {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    (∫⁻ x, f x ∂μ) ^ p ≤ (μ univ) ^ (p - 1) * ∫⁻ x, (f x) ^ p ∂μ := by
  have hpq := Real.HolderConjugate.conjExponent hp
  have h := lintegral_mul_le_Lp_mul_Lq μ hpq hf
    (aemeasurable_const : AEMeasurable (fun _ : α ↦ (1 : ℝ≥0∞)) μ)
  simp only [Pi.mul_apply, mul_one, one_rpow, lintegral_const, one_mul] at h
  have hpow := ENNReal.rpow_le_rpow h hpq.nonneg
  rw [ENNReal.mul_rpow_of_nonneg _ _ hpq.nonneg,
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    one_div_mul_cancel hpq.ne_zero, ENNReal.rpow_one,
    show 1 / Real.conjExponent p * p = p - 1 by
      simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using
        hpq.div_conj_eq_sub_one] at hpow
  simpa only [mul_comm] using hpow

end ENNReal

namespace MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The norm power of a Banach-valued integral is controlled by its power energy
and the measure of the domain. -/
theorem ofReal_norm_integral_rpow_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {p : ℝ} (hp : 1 < p) {f : α → F} (hf : AEStronglyMeasurable f μ) :
    ENNReal.ofReal (‖∫ z, f z ∂μ‖ ^ p) ≤
      (μ univ) ^ (p - 1) * ∫⁻ z, ENNReal.ofReal (‖f z‖ ^ p) ∂μ := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp.le
  calc
    _ = ‖∫ z, f z ∂μ‖ₑ ^ p := by
      rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0,
        ofReal_norm]
    _ ≤ (∫⁻ z, ‖f z‖ₑ ∂μ) ^ p :=
      ENNReal.rpow_le_rpow (enorm_integral_le_lintegral_enorm f) hp0
    _ ≤ (μ univ) ^ (p - 1) * ∫⁻ z, ‖f z‖ₑ ^ p ∂μ :=
      ENNReal.rpow_lintegral_le_mul_lintegral_rpow μ hp hf.enorm
    _ = _ := by
      simp_rw [← ofReal_norm,
        ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- A continuous compact kernel against locally integrable data is integrable. -/
theorem integrable_smul_comp_sub_smul (μ : Measure E) [μ.IsAddHaarMeasure]
    {ψ : E → ℝ} {g : E → F} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hg : LocallyIntegrable g μ) (x : E) {t : ℝ} (ht : t ≠ 0) :
    Integrable (fun z ↦ ψ z • g (x - t • z)) μ := by
  let : μ.IsNegInvariant := ⟨by
    simpa only [Measure.neg_def, neg_one_smul, abs_inv, abs_pow, abs_neg, abs_one,
      one_pow, inv_one, ENNReal.ofReal_one, one_smul] using
      (Measure.map_addHaar_smul μ (neg_ne_zero.mpr (one_ne_zero : (1 : ℝ) ≠ 0)))⟩
  let e : E ≃ₜ E := Homeomorph.smul (Units.mk0 t⁻¹ (inv_ne_zero ht))
  have hc : HasCompactSupport (fun h : E ↦ ψ (t⁻¹ • h)) :=
    hψc.comp_homeomorph e
  have hi := (hc.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (hψ.comp (continuous_const_smul t⁻¹)) hg x).comp_smul ht
  simpa only [smul_smul, inv_mul_cancel₀ ht, one_smul,
    ContinuousLinearMap.lsmul_apply] using hi

variable [CompleteSpace F]

/-- A zero-mean compact kernel permits subtracting the value at the evaluation point. -/
theorem integral_smul_comp_sub_smul_eq_sub (μ : Measure E) [μ.IsAddHaarMeasure]
    {ψ : E → ℝ} {g : E → F} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hψzero : ∫ z, ψ z ∂μ = 0) (hg : LocallyIntegrable g μ)
    (x : E) {t : ℝ} (ht : t ≠ 0) :
    (∫ z, ψ z • g (x - t • z) ∂μ) =
      ∫ z, ψ z • (g (x - t • z) - g x) ∂μ := by
  have hi := integrable_smul_comp_sub_smul μ hψ hψc hg x ht
  have hc := (hψ.integrable_of_hasCompactSupport hψc (μ := μ)).smul_const (g x)
  simp_rw [smul_sub]
  rw [integral_sub hi hc, integral_smul_const, hψzero, zero_smul, sub_zero]

/-- At a positive scale, a mean-zero bounded kernel is controlled by local increments. -/
theorem ofReal_norm_signedKernel_rpow_le (μ : Measure E) [μ.IsAddHaarMeasure]
    {p R M : ℝ} (hp : 1 < p)
    {ψ : E → ℝ} {g : E → F} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hψsupport : Function.support ψ ⊆ Metric.ball 0 R)
    (hψbound : ∀ z, |ψ z| ≤ M) (hψzero : ∫ z, ψ z ∂μ = 0)
    (hg : LocallyIntegrable g μ) (x : E) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (‖t⁻¹ • ∫ z, ψ z • g (x - t • z) ∂μ‖ ^ p) ≤
      (μ (Metric.ball (0 : E) R)) ^ (p - 1) * ENNReal.ofReal (M ^ p) *
        (ENNReal.ofReal (t ^ (-p)) *
          ∫⁻ z in Metric.ball (0 : E) R,
            ENNReal.ofReal (‖g (x - t • z) - g x‖ ^ p) ∂μ) := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp.le
  have hi := integrable_smul_comp_sub_smul μ hψ hψc hg x ht.ne'
  have hc := (hψ.integrable_of_hasCompactSupport hψc (μ := μ)).smul_const (g x)
  have hd : Integrable (fun z ↦ ψ z • (g (x - t • z) - g x)) μ := by
    convert hi.sub hc using 1
    funext z
    exact smul_sub _ _ _
  have hs :
      (∫ z, ψ z • (g (x - t • z) - g x) ∂μ) =
        ∫ z in Metric.ball 0 R, ψ z • (g (x - t • z) - g x) ∂μ := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hzero : ψ z = 0 := Function.notMem_support.mp (fun hh ↦ hz (hψsupport hh))
    rw [hzero, zero_smul]
  have hh := ofReal_norm_integral_rpow_le (μ.restrict (Metric.ball 0 R)) hp
    hd.aestronglyMeasurable.restrict
  simp only [Measure.restrict_apply_univ] at hh
  have hb :
      (∫⁻ z in Metric.ball 0 R,
        ENNReal.ofReal (‖ψ z • (g (x - t • z) - g x)‖ ^ p) ∂μ) ≤
      ENNReal.ofReal (M ^ p) * ∫⁻ z in Metric.ball 0 R,
        ENNReal.ofReal (‖g (x - t • z) - g x‖ ^ p) ∂μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro z
    dsimp only
    rw [norm_smul, Real.norm_eq_abs, Real.mul_rpow (abs_nonneg _) (norm_nonneg _),
      ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _)]
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow (abs_nonneg _) (hψbound z) hp0)) _
  rw [integral_smul_comp_sub_smul_eq_sub μ hψ hψc hψzero hg x ht.ne', hs,
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht),
    Real.mul_rpow (inv_nonneg.mpr ht.le) (norm_nonneg _),
    ENNReal.ofReal_mul (Real.rpow_nonneg (inv_nonneg.mpr ht.le) _),
    Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]
  calc
    _ ≤ ENNReal.ofReal (t ^ (-p)) *
        ((μ (Metric.ball (0 : E) R)) ^ (p - 1) *
          (ENNReal.ofReal (M ^ p) * ∫⁻ z in Metric.ball 0 R,
            ENNReal.ofReal (‖g (x - t • z) - g x‖ ^ p) ∂μ)) :=
      mul_le_mul_right (hh.trans (mul_le_mul_right hb _)) _
    _ = _ := by ring

end MeasureTheory
