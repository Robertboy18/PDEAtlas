/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Localization.EdgeKernel

/-!
# Mixed-domain tails for relative zero extension

The gap is required only where the original function is nonzero. Translation
invariance bounds each mixed-domain contribution by the original Lᵖ energy
times the finite radial mass. The two domains may be unbounded.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace.Fractional.Localization

variable {n : ℕ} {s δ : ℝ} {A C : Set (ℝ^n)} {p : ℝ≥0∞}
variable {F : Type*} [NormedAddCommGroup F] {u : ℝ^n → F}

/-- Integrating the shifted tail over any set costs at most its whole-space mass. -/
theorem lintegral_edgeKernel_sub_le (x : ℝ^n) (p : ℝ≥0∞ := 2) :
    (∫⁻ y in C, ENNReal.ofReal (edgeKernel n s (x - y) (p := p))) ≤
      edgeMass n s (p := p) := by
  calc
    _ = ∫⁻ y in C, ENNReal.ofReal (edgeKernel n s (y - x) (p := p)) := by
      apply lintegral_congr
      intro y
      rw [← neg_sub y x, edgeKernel_neg (p := p)]
    _ ≤ ∫⁻ y : ℝ^n, ENNReal.ofReal (edgeKernel n s (y - x) (p := p)) :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = _ := by
      simpa only [sub_eq_add_neg, edgeMass] using
        lintegral_add_right_eq_self
          (fun h : ℝ^n ↦ ENNReal.ofReal (edgeKernel n s h (p := p))) (-x)

/-- A fixed active point contributes only a finite tail across a support gap.
The numerator may take values in any real normed space. -/
theorem lintegral_enorm_rpow_div_le_of_gap
    (hs : 0 < s) (hδ : 0 < δ) (hC : MeasurableSet C) (x : ℝ^n) (a : F)
    (hgap : a ≠ 0 → ∀ y ∈ C, δ ≤ dist x y) (hp : 0 < p.toReal) :
    (∫⁻ y in C, ‖a‖ₑ ^ p.toReal /
      (ENNReal.ofReal ‖x - y‖) ^ ((n : ℝ) + p.toReal * s)) ≤
      ENNReal.ofReal ((1 + δ⁻¹) ^ ((n : ℝ) + p.toReal * s)) *
        (‖a‖ₑ ^ p.toReal * edgeMass n s (p := p)) := by
  by_cases ha : a = 0
  · simp [ha, ENNReal.zero_rpow_of_pos hp]
  calc
    _ ≤ ∫⁻ y in C,
        ENNReal.ofReal ((1 + δ⁻¹) ^ ((n : ℝ) + p.toReal * s)) *
          (‖a‖ₑ ^ p.toReal * ENNReal.ofReal (edgeKernel n s (x - y) (p := p))) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hC] with y hy
      exact div_rpow_le_edgeKernel (by positivity) hδ (hgap ha y hy) _
    _ = ENNReal.ofReal ((1 + δ⁻¹) ^ ((n : ℝ) + p.toReal * s)) *
        (‖a‖ₑ ^ p.toReal *
          ∫⁻ y in C, ENNReal.ofReal (edgeKernel n s (x - y) (p := p))) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ (by finiteness)]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (lintegral_edgeKernel_sub_le x p) zero_le) zero_le

/-- The scalar squared form of the fixed-point support-gap estimate. -/
theorem lintegral_norm_div_rpow_sq_le_of_gap
    (hs : 0 < s) (hδ : 0 < δ) (hC : MeasurableSet C) (x : ℝ^n) (a : ℝ)
    (hgap : a ≠ 0 → ∀ y ∈ C, δ ≤ dist x y) :
    (∫⁻ y in C, (‖a / ‖x - y‖ ^ ((n : ℝ) / 2 + s)‖₊ : ℝ≥0∞) ^ 2) ≤
      ENNReal.ofReal ((1 + δ⁻¹) ^ ((n : ℝ) + 2 * s)) *
        ((‖a‖₊ : ℝ≥0∞) ^ 2 * edgeMass n s) := by
  by_cases ha : a = 0
  · simp [ha]
  calc
    _ ≤ ∫⁻ y in C,
        ENNReal.ofReal ((1 + δ⁻¹) ^ ((n : ℝ) + 2 * s)) *
          ((‖a‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (edgeKernel n s (x - y))) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hC] with y hy
      have h := ENNReal.ofReal_le_ofReal
        (norm_div_rpow_sq_le_edgeKernel (by positivity) hδ (hgap ha y hy) a)
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _),
        ENNReal.ofReal_mul (sq_nonneg ‖a‖)] at h
      simpa only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
        enorm_eq_nnnorm] using h
    _ = ENNReal.ofReal ((1 + δ⁻¹) ^ ((n : ℝ) + 2 * s)) *
        ((‖a‖₊ : ℝ≥0∞) ^ 2 *
          ∫⁻ y in C, ENNReal.ofReal (edgeKernel n s (x - y))) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ (by finiteness)]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (lintegral_edgeKernel_sub_le x) zero_le) zero_le

variable [NormedSpace ℝ F]

/-- The norm of the intrinsic difference quotient is symmetric in its two points. -/
theorem nnnorm_diffQuot_swap (u : ℝ^n → F) (z : ℝ^n × ℝ^n) (p : ℝ≥0∞ := 2) :
    ‖diffQuot n s u z.swap (p := p)‖₊ = ‖diffQuot n s u z (p := p)‖₊ := by
  simp only [diffQuot, Prod.fst_swap, Prod.snd_swap]
  rw [norm_sub_rev z.2 z.1, ← neg_sub (u z.1) (u z.2), smul_neg, nnnorm_neg]

/-- Swapping the domains leaves the mixed p-energy unchanged. -/
theorem lintegral_diffQuot_rpow_prod_swap (u : ℝ^n → F) :
    (∫⁻ z, ‖diffQuot n s u z (p := p)‖ₑ ^ p.toReal
      ∂(volume.restrict C).prod (volume.restrict A)) =
    ∫⁻ z, ‖diffQuot n s u z (p := p)‖ₑ ^ p.toReal
      ∂(volume.restrict A).prod (volume.restrict C) := by
  simpa only [enorm_eq_nnnorm, nnnorm_diffQuot_swap] using
    (lintegral_prod_swap
      (μ := volume.restrict A) (ν := volume.restrict C)
      (fun z ↦ ‖diffQuot n s u z (p := p)‖ₑ ^ p.toReal))

/-- Swapping the domains leaves the mixed squared difference quotient unchanged. -/
theorem lintegral_diffQuot_sq_prod_swap (u : ℝ^n → F) :
    (∫⁻ z, (‖diffQuot n s u z‖₊ : ℝ≥0∞) ^ 2
      ∂(volume.restrict C).prod (volume.restrict A)) =
    ∫⁻ z, (‖diffQuot n s u z‖₊ : ℝ≥0∞) ^ 2
      ∂(volume.restrict A).prod (volume.restrict C) := by
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two, enorm_eq_nnnorm] using
    lintegral_diffQuot_rpow_prod_swap (s := s) (A := A) (C := C) (p := 2) u

/-- One mixed-domain contribution of zero extension is controlled by Lᵖ.
No regularity or finite-volume hypothesis is imposed on either domain. -/
theorem lintegral_diffQuot_indicator_mixed_le
    (hs : 0 < s) (hδ : 0 < δ) (hA : MeasurableSet A) (hC : MeasurableSet C)
    (hAC : Disjoint A C)
    (hgap : ∀ x ∈ A, u x ≠ 0 → ∀ y ∈ C, δ ≤ dist x y)
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    (∫⁻ z, ‖diffQuot n s (A.indicator u) z (p := p)‖ₑ ^ p.toReal
      ∂(volume.restrict A).prod (volume.restrict C)) ≤
      ENNReal.ofReal ((1 + δ⁻¹) ^ ((n : ℝ) + p.toReal * s)) *
        ((∫⁻ x in A, ‖u x‖ₑ ^ p.toReal) * edgeMass n s (p := p)) := by
  classical
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  calc
    _ ≤ ∫⁻ x in A, ∫⁻ y in C,
        ‖diffQuot n s (A.indicator u) (x, y) (p := p)‖ₑ ^ p.toReal :=
      lintegral_prod_le _
    _ ≤ ∫⁻ x in A, ENNReal.ofReal ((1 + δ⁻¹) ^ ((n : ℝ) + p.toReal * s)) *
        (‖u x‖ₑ ^ p.toReal * edgeMass n s (p := p)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hA] with x hx
      calc
        _ = ∫⁻ y in C, ‖u x‖ₑ ^ p.toReal /
            (ENNReal.ofReal ‖x - y‖) ^ ((n : ℝ) + p.toReal * s) := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem hC] with y hy
          have hyA : y ∉ A := fun h ↦ Set.disjoint_left.mp hAC h hy
          simp only [enorm_diffQuot_rpow _ _ hp0 hptop, indicator_of_mem hx,
            indicator_of_notMem hyA, sub_zero, mul_comm s]
        _ ≤ _ := lintegral_enorm_rpow_div_le_of_gap hs hδ hC x (u x) (hgap x hx) hp
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_mul_const' _ _ (edgeMass_lt_top hs p hp).ne]

end SobolevSpace.Fractional.Localization
