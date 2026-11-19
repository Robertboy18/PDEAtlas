/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Localization.RelativeExtension

/-!
# Finite-exponent norm bounds for relative zero extension

The two mixed-domain tails cost a fixed multiple of the base Lᵖ energy. Taking the
p-th root gives a bound in the Gagliardo graph norm. Only positive order
and a positive support gap are needed; the domains need not be bounded or regular,
and the real normed codomain need not be complete.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace.Fractional.GagliardoSpace.ZeroExtension

variable {n : ℕ} {s δ : ℝ} {A B : Set (ℝ^n)} {p : ℝ≥0∞}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The p-th root of one plus the two radial-tail costs. -/
def normBound (n : ℕ) (s δ : ℝ) (p : ℝ≥0∞) : ℝ :=
  (1 + 2 * (1 + δ⁻¹) ^ ((n : ℝ) + p.toReal * s) *
    (Localization.edgeMass n s (p := p)).toReal) ^ (1 / p.toReal)

/-- A positive gap gives a nonnegative extension bound. -/
theorem normBound_nonneg (n : ℕ) (s : ℝ) (hδ : 0 < δ) (p : ℝ≥0∞) :
    0 ≤ normBound n s δ p := Real.rpow_nonneg (by positivity) _

variable [Fact (1 ≤ p)] {f : ℝ^n → F}

/-- Relative zero extension preserves the base Lᵖ energy exactly. -/
theorem norm_toLp_rpow_eq_of_indicator_ae (hp : p ≠ ∞)
    (hA : MeasurableSet A) (hAB : A ⊆ B)
    (u : GagliardoSpace n s A (p := p) (F := F))
    (v : GagliardoSpace n s B (p := p) (F := F))
    (hu : (toLp n s A u : ℝ^n → F) =ᵐ[volume.restrict A] f)
    (hv : (toLp n s B v : ℝ^n → F) =ᵐ[volume.restrict B] A.indicator f) :
    ‖toLp n s B v‖ ^ p.toReal = ‖toLp n s A u‖ ^ p.toReal := by
  have h := Localization.lintegral_enorm_rpow_indicator hA hAB f
    (p.toReal_pos_iff_ne_top.mpr hp)
  rw [Lp.lintegral_enorm_rpow_eq_of_ae hp _ hv,
    Lp.lintegral_enorm_rpow_eq_of_ae hp _ hu] at h
  simpa only [ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)] using
    congrArg ENNReal.toReal h

/-- The fractional energy added across the gap is bounded by the original base energy. -/
theorem norm_differenceQuotient_rpow_le_of_indicator_ae (hp : p ≠ ∞)
    (hs : 0 < s) (hδ : 0 < δ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : A ⊆ B)
    (hgap : ∀ x ∈ A, f x ≠ 0 → ∀ y ∈ B \ A, δ ≤ dist x y)
    (u : GagliardoSpace n s A (p := p) (F := F))
    (v : GagliardoSpace n s B (p := p) (F := F))
    (hu : (toLp n s A u : ℝ^n → F) =ᵐ[volume.restrict A] f)
    (hv : (toLp n s B v : ℝ^n → F) =ᵐ[volume.restrict B] A.indicator f) :
    ‖differenceQuotient n s B v‖ ^ p.toReal ≤
      ‖differenceQuotient n s A u‖ ^ p.toReal +
      2 * (1 + δ⁻¹) ^ ((n : ℝ) + p.toReal * s) *
        (‖toLp n s A u‖ ^ p.toReal * (Localization.edgeMass n s (p := p)).toReal) := by
  have h := Localization.lintegral_diffQuot_indicator_le_of_gap
    hs hδ hA hB hAB hgap (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) hp
  have hdu := (differenceQuotient_apply_ae u).trans (diffQuot_congr_ae hu)
  have hdv := (differenceQuotient_apply_ae v).trans (diffQuot_congr_ae hv)
  rw [Lp.lintegral_enorm_rpow_eq_of_ae hp _ hdv,
    Lp.lintegral_enorm_rpow_eq_of_ae hp _ hdu,
    Lp.lintegral_enorm_rpow_eq_of_ae hp _ hu] at h
  have hmass := (Localization.edgeMass_lt_top (n := n) hs p (p.toReal_pos_iff_ne_top.mpr hp)).ne
  have hC : 0 ≤ (1 + δ⁻¹) ^ ((n : ℝ) + p.toReal * s) := by positivity
  have hr := ENNReal.toReal_mono (by finiteness) h
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at hr
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _),
    ENNReal.toReal_ofReal hC, ENNReal.toReal_ofNat] using hr

/-- The graph p-energy is multiplied by at most one plus the two tail costs. -/
theorem norm_rpow_le_of_indicator_ae (hp : p ≠ ∞)
    (hs : 0 < s) (hδ : 0 < δ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : A ⊆ B)
    (hgap : ∀ x ∈ A, f x ≠ 0 → ∀ y ∈ B \ A, δ ≤ dist x y)
    (u : GagliardoSpace n s A (p := p) (F := F))
    (v : GagliardoSpace n s B (p := p) (F := F))
    (hu : (toLp n s A u : ℝ^n → F) =ᵐ[volume.restrict A] f)
    (hv : (toLp n s B v : ℝ^n → F) =ᵐ[volume.restrict B] A.indicator f) :
    ‖v‖ ^ p.toReal ≤
      (1 + 2 * (1 + δ⁻¹) ^ ((n : ℝ) + p.toReal * s) *
        (Localization.edgeMass n s (p := p)).toReal) * ‖u‖ ^ p.toReal := by
  have hb := norm_toLp_rpow_eq_of_indicator_ae hp hA hAB u v hu hv
  have hd := norm_differenceQuotient_rpow_le_of_indicator_ae
    hp hs hδ hA hB hAB hgap u v hu hv
  rw [norm_rpow_eq hp, norm_rpow_eq hp, hb]
  have hnonneg : 0 ≤ 2 * (1 + δ⁻¹) ^ ((n : ℝ) + p.toReal * s) *
      (Localization.edgeMass n s (p := p)).toReal *
        ‖differenceQuotient n s A u‖ ^ p.toReal := by positivity
  nlinarith only [hd, hnonneg]

/-- A support gap gives a quantitative bound in the conventional graph norm. -/
theorem norm_le_of_indicator_ae (hp : p ≠ ∞)
    (hs : 0 < s) (hδ : 0 < δ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : A ⊆ B)
    (hgap : ∀ x ∈ A, f x ≠ 0 → ∀ y ∈ B \ A, δ ≤ dist x y)
    (u : GagliardoSpace n s A (p := p) (F := F))
    (v : GagliardoSpace n s B (p := p) (F := F))
    (hu : (toLp n s A u : ℝ^n → F) =ᵐ[volume.restrict A] f)
    (hv : (toLp n s B v : ℝ^n → F) =ᵐ[volume.restrict B] A.indicator f) :
    ‖v‖ ≤ normBound n s δ p * ‖u‖ := by
  have hpR : 0 < p.toReal := p.toReal_pos_iff_ne_top.mpr hp
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) (mul_nonneg
    (normBound_nonneg n s hδ p) (norm_nonneg _)) hpR).mp
  rw [Real.mul_rpow (normBound_nonneg n s hδ p) (norm_nonneg _), normBound,
    ← Real.rpow_mul (by positivity), one_div_mul_cancel hpR.ne', Real.rpow_one]
  exact norm_rpow_le_of_indicator_ae hp hs hδ hA hB hAB hgap u v hu hv

end SobolevSpace.Fractional.GagliardoSpace.ZeroExtension
