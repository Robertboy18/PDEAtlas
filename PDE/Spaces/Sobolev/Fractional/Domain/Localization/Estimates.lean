/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Localization.Pointwise

/-!
# Fractional cutoff estimates on arbitrary domains

Tonelli and translation invariance bound the cutoff contribution by a finite
radial integral times the original Lp power integral. In particular, every globally
bounded Lipschitz scalar function multiplies the intrinsic fractional space
into itself for `0 < s < 1`. No regularity of the domain is required.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace SobolevSpace.Fractional.Localization

variable {n : ℕ} {s : ℝ} {Ω : Set (ℝ^n)} {φ u : ℝ^n → ℝ} {L M : ℝ≥0}

/-- The exact radial integral used in the cutoff bound; no closed form is needed. -/
def cutoffMass (n : ℕ) (s : ℝ) (p : ℝ := 2) : ℝ≥0∞ :=
  ∫⁻ h : ℝ^n, ENNReal.ofReal (cutoffKernel n s h (p := p))

theorem cutoffMass_lt_top (hs0 : 0 < s) (hs1 : s < 1) (p : ℝ := 2)
    (hp : 0 < p := by norm_num) : cutoffMass n s (p := p) < ∞ :=
  (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall (fun h ↦ cutoffKernel_nonneg h p))).mp
      (integrable_cutoffKernel hs0 hs1 p hp).hasFiniteIntegral

/-- Integrating the radial majorant over any domain costs at most its whole-space mass. -/
theorem lintegral_cutoffKernel_sub_le (y : ℝ^n) (p : ℝ := 2) :
    (∫⁻ x in Ω, ENNReal.ofReal (cutoffKernel n s (x - y) (p := p))) ≤ cutoffMass n s (p := p) := by
  calc
    _ ≤ ∫⁻ x : ℝ^n, ENNReal.ofReal (cutoffKernel n s (x - y) (p := p)) :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = _ := by
      simpa only [sub_eq_add_neg, cutoffMass] using
        lintegral_add_right_eq_self
          (fun h : ℝ^n ↦ ENNReal.ofReal (cutoffKernel n s h (p := p))) (-y)

/-- Tonelli turns the mixed cutoff term into the L2 square times the kernel mass. -/
theorem lintegral_sq_mul_cutoffKernel_le
    (hu : AEStronglyMeasurable u (volume.restrict Ω)) :
    (∫⁻ p, (‖u p.2‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (cutoffKernel n s (p.1 - p.2))
      ∂gagliardoProductMeasure n Ω) ≤
      (∫⁻ y in Ω, (‖u y‖₊ : ℝ≥0∞) ^ 2) * cutoffMass n s := by
  have hmeas : AEMeasurable
      (fun p : ℝ^n × ℝ^n ↦
        (‖u p.2‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (cutoffKernel n s (p.1 - p.2)))
      (gagliardoProductMeasure n Ω) :=
    ((hu.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).nnnorm.aemeasurable
      |>.coe_nnreal_ennreal.pow_const 2).mul
        ((measurable_cutoffKernel.comp (by fun_prop)).ennreal_ofReal.aemeasurable)
  rw [gagliardoProductMeasure, lintegral_prod_symm _ hmeas]
  calc
    _ = ∫⁻ y in Ω, (‖u y‖₊ : ℝ≥0∞) ^ 2 *
        ∫⁻ x in Ω, ENNReal.ofReal (cutoffKernel n s (x - y)) := by
      apply lintegral_congr
      intro y
      exact lintegral_const_mul' ((‖u y‖₊ : ℝ≥0∞) ^ 2)
        (fun x ↦ ENNReal.ofReal (cutoffKernel n s (x - y))) (by finiteness)
    _ ≤ ∫⁻ y in Ω, (‖u y‖₊ : ℝ≥0∞) ^ 2 * cutoffMass n s := by
      apply lintegral_mono
      intro y
      exact mul_le_mul_of_nonneg_left (lintegral_cutoffKernel_sub_le y) zero_le
    _ = _ := lintegral_mul_const'' _ (hu.nnnorm.aemeasurable.coe_nnreal_ennreal.pow_const 2)

/-- A quantitative bound for the squared intrinsic seminorm of a cutoff product. -/
theorem gagliardoSq_mul_le
    (hs : 0 ≤ (n : ℝ) + 2 * s) (hL : LipschitzWith L φ)
    (hM : ∀ x, ‖φ x‖ ≤ M) (hu : AEStronglyMeasurable u (volume.restrict Ω)) :
    gagliardoSq n s Ω (fun x ↦ φ x * u x) ≤
      ENNReal.ofReal (2 * (M : ℝ) ^ 2) * gagliardoSq n s Ω u +
        ENNReal.ofReal (2 * ((L : ℝ) ^ 2 + 4 * (M : ℝ) ^ 2)) *
          ((∫⁻ y in Ω, (‖u y‖₊ : ℝ≥0∞) ^ 2) * cutoffMass n s) := by
  have hdq := (aestronglyMeasurable_diffQuot (s := s) (p := 2) hu).nnnorm.aemeasurable
    |>.coe_nnreal_ennreal.pow_const 2
  unfold gagliardoSq
  calc
    _ ≤ ∫⁻ p, ENNReal.ofReal (2 * (M : ℝ) ^ 2) *
        (‖diffQuot n s u p‖₊ : ℝ≥0∞) ^ 2 +
        ENNReal.ofReal (2 * ((L : ℝ) ^ 2 + 4 * (M : ℝ) ^ 2)) *
          ((‖u p.2‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (cutoffKernel n s (p.1 - p.2)))
          ∂gagliardoProductMeasure n Ω := by
      apply lintegral_mono
      intro p
      have h := ENNReal.ofReal_le_ofReal (norm_diffQuot_mul_sq_le hs hL hM u p.1 p.2)
      rw [ENNReal.ofReal_add (by positivity)
          (mul_nonneg (by positivity) (mul_nonneg (sq_nonneg _) (cutoffKernel_nonneg _))),
        ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * (M : ℝ) ^ 2),
        ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * ((L : ℝ) ^ 2 + 4 * (M : ℝ) ^ 2)),
        ENNReal.ofReal_mul (sq_nonneg ‖u p.2‖)] at h
      simpa only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm,
        Prod.mk.eta] using h
    _ ≤ _ := by
      rw [lintegral_add_left' (hdq.const_mul _),
        lintegral_const_mul' (ENNReal.ofReal (2 * (M : ℝ) ^ 2)) _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' (ENNReal.ofReal (2 * ((L : ℝ) ^ 2 + 4 * (M : ℝ) ^ 2))) _
          ENNReal.ofReal_ne_top]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (lintegral_sq_mul_cutoffKernel_le hu) zero_le)

/-- Tonelli bounds the mixed term by the base power integral and the kernel mass. -/
theorem lintegral_enorm_rpow_mul_cutoffKernel_le {F : Type*} [NormedAddCommGroup F]
    {u : ℝ^n → F} {p : ℝ} (hp : 0 ≤ p)
    (hu : AEStronglyMeasurable u (volume.restrict Ω)) :
    (∫⁻ z, ‖u z.2‖ₑ ^ p * ENNReal.ofReal (cutoffKernel n s (z.1 - z.2) (p := p))
      ∂gagliardoProductMeasure n Ω) ≤
      (∫⁻ y in Ω, ‖u y‖ₑ ^ p) * cutoffMass n s (p := p) := by
  have hmeas : AEMeasurable
      (fun z : ℝ^n × ℝ^n ↦
        ‖u z.2‖ₑ ^ p * ENNReal.ofReal (cutoffKernel n s (z.1 - z.2) (p := p)))
      (gagliardoProductMeasure n Ω) :=
    ((hu.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).enorm.pow_const p).mul
      (((measurable_cutoffKernel p).comp (by fun_prop)).ennreal_ofReal.aemeasurable)
  rw [gagliardoProductMeasure, lintegral_prod_symm _ hmeas]
  calc
    _ = ∫⁻ y in Ω, ‖u y‖ₑ ^ p *
        ∫⁻ x in Ω, ENNReal.ofReal (cutoffKernel n s (x - y) (p := p)) := by
      apply lintegral_congr
      intro y
      exact lintegral_const_mul' (‖u y‖ₑ ^ p)
        (fun x ↦ ENNReal.ofReal (cutoffKernel n s (x - y) (p := p))) (by finiteness)
    _ ≤ ∫⁻ y in Ω, ‖u y‖ₑ ^ p * cutoffMass n s (p := p) := by
      apply lintegral_mono
      intro y
      exact mul_le_mul_of_nonneg_left (lintegral_cutoffKernel_sub_le y p) zero_le
    _ = _ := lintegral_mul_const'' _ (hu.enorm.pow_const p)

/-- The fractional power integral of a scalar product has a uniform quantitative bound. -/
theorem lintegral_enorm_diffQuot_smul_rpow_le {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {u : ℝ^n → F} {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (hs : 0 ≤ (n : ℝ) + p.toReal * s)
    (hL : LipschitzWith L φ) (hM : ∀ x, ‖φ x‖ ≤ M)
    (hu : AEStronglyMeasurable u (volume.restrict Ω)) :
    (∫⁻ z, ‖diffQuot n s (fun x ↦ φ x • u x) z (p := p)‖ₑ ^ p.toReal
      ∂gagliardoProductMeasure n Ω) ≤
      (2 : ℝ≥0∞) ^ p.toReal *
        (ENNReal.ofReal ((M : ℝ) ^ p.toReal) *
            (∫⁻ z, ‖diffQuot n s u z (p := p)‖ₑ ^ p.toReal
              ∂gagliardoProductMeasure n Ω) +
          ENNReal.ofReal ((L : ℝ) ^ p.toReal + (2 * (M : ℝ)) ^ p.toReal) *
            ((∫⁻ y in Ω, ‖u y‖ₑ ^ p.toReal) * cutoffMass n s (p := p.toReal))) := by
  have hdq := (aestronglyMeasurable_diffQuot (s := s) (p := p) hu).enorm.pow_const p.toReal
  calc
    _ ≤ ∫⁻ z, (2 : ℝ≥0∞) ^ p.toReal *
        (ENNReal.ofReal ((M : ℝ) ^ p.toReal) *
            ‖diffQuot n s u z (p := p)‖ₑ ^ p.toReal +
          ENNReal.ofReal ((L : ℝ) ^ p.toReal + (2 * (M : ℝ)) ^ p.toReal) *
            (‖u z.2‖ₑ ^ p.toReal *
              ENNReal.ofReal (cutoffKernel n s (z.1 - z.2) (p := p.toReal))))
        ∂gagliardoProductMeasure n Ω :=
      lintegral_mono fun z ↦ enorm_diffQuot_smul_rpow_le hp0 hp hs hL hM u z.1 z.2
    _ ≤ _ := by
      rw [lintegral_const_mul' _ _ (by finiteness), lintegral_add_left' (hdq.const_mul _),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left
          (lintegral_enorm_rpow_mul_cutoffKernel_le ENNReal.toReal_nonneg hu) zero_le)) zero_le

/-- A uniformly bounded Lipschitz scalar preserves base Lp membership. -/
theorem memLp_smul_cutoff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : ℝ^n → F} {p : ℝ≥0∞} (hL : LipschitzWith L φ) (hM : ∀ x, ‖φ x‖ ≤ M)
    (hu : MemLp u p (volume.restrict Ω)) :
    MemLp (fun x ↦ φ x • u x) p (volume.restrict Ω) :=
  hu.of_le_mul
    (hL.continuous.measurable.aestronglyMeasurable.smul hu.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x ↦ by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _))

/-- Uniformly bounded Lipschitz multiplication preserves the scalar base Lp condition. -/
theorem memLp_mul_cutoff {p : ℝ≥0∞} (hL : LipschitzWith L φ) (hM : ∀ x, ‖φ x‖ ≤ M)
    (hu : MemLp u p (volume.restrict Ω)) :
    MemLp (fun x ↦ φ x * u x) p (volume.restrict Ω) := by
  simpa only [smul_eq_mul] using memLp_smul_cutoff hL hM hu

/-- Bounded Lipschitz scalars preserve fractional membership for finite positive exponents.
No completeness, finite-dimensional codomain, or regularity of the domain is required. -/
theorem memGagliardo_smul_cutoff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : ℝ^n → F} {p : ℝ≥0∞} (hs0 : 0 < s) (hs1 : s < 1)
    (hL : LipschitzWith L φ) (hM : ∀ x, ‖φ x‖ ≤ M)
    (hu : MemGagliardo n s Ω u (p := p)) (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    MemGagliardo n s Ω (fun x ↦ φ x • u x) (p := p) := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hb := memLp_smul_cutoff hL hM hu.1
  have hmeas := aestronglyMeasurable_diffQuot (s := s) (p := p) hb.aestronglyMeasurable
  refine ⟨hb, ?_⟩
  rw [memLp_iff]
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hp hmeas).2
  have hu0 := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hp
    hu.1.aestronglyMeasurable).1 hu.1.eLpNorm_lt_top
  have hu1 := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hp
    hu.2.aestronglyMeasurable).1 hu.2.eLpNorm_lt_top
  have hm := cutoffMass_lt_top (n := n) hs0 hs1 p.toReal hr
  apply (lintegral_enorm_diffQuot_smul_rpow_le hp0 hp (by positivity)
    hL hM hu.1.aestronglyMeasurable).trans_lt
  exact ENNReal.mul_lt_top (by finiteness) (ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu1,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top hu0 hm)⟩)

/-- Bounded Lipschitz multiplication preserves the intrinsic scalar condition.
The exponent is inferred from the input; omitted endpoint proofs cover the quadratic case. -/
theorem memGagliardo_mul_cutoff {p : ℝ≥0∞}
    (hs0 : 0 < s) (hs1 : s < 1) (hL : LipschitzWith L φ) (hM : ∀ x, ‖φ x‖ ≤ M)
    (hu : MemGagliardo n s Ω u (p := p))
    (hp0 : p ≠ 0 := by norm_num) (hp : p ≠ ∞ := by norm_num) :
    MemGagliardo n s Ω (fun x ↦ φ x * u x) (p := p) := by
  simpa only [smul_eq_mul] using memGagliardo_smul_cutoff hs0 hs1 hL hM hu hp0 hp

end SobolevSpace.Fractional.Localization
