/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Localization.RelativeExtension
import PDE.Analysis.MeasureTheory.LpNorm

/-!
# The graph-norm cost of relative zero extension

The norm bound separates the support-gap cost from cutoff multiplication.
It applies to any two elements of the intrinsic spaces whose physical
representatives are related by relative zero extension.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace.Fractional.GagliardoSpace

variable {n : ℕ} {s δ : ℝ} {A B : Set (ℝ^n)} {f : ℝ^n → ℝ}

/-- The L2 square of any physical representative is the square of the base norm. -/
theorem lintegral_nnnorm_sq_eq_norm_toLp_sq (u : GagliardoSpace n s A)
    (hf : (toLp n s A u : ℝ^n → ℝ) =ᵐ[volume.restrict A] f) :
    (∫⁻ x in A, (‖f x‖₊ : ℝ≥0∞) ^ 2) = ENNReal.ofReal (‖toLp n s A u‖ ^ 2) :=
  Lp.lintegral_nnnorm_sq_eq_norm_sq_of_ae_eq (toLp n s A u) hf

/-- Relative zero extension preserves the square of the physical L2 norm. -/
theorem norm_toLp_sq_eq_of_indicator_ae
    (hA : MeasurableSet A) (hAB : A ⊆ B)
    (u : GagliardoSpace n s A) (v : GagliardoSpace n s B)
    (hu : (toLp n s A u : ℝ^n → ℝ) =ᵐ[volume.restrict A] f)
    (hv : (toLp n s B v : ℝ^n → ℝ) =ᵐ[volume.restrict B] A.indicator f) :
    ‖toLp n s B v‖ ^ 2 = ‖toLp n s A u‖ ^ 2 := by
  have h := Localization.lintegral_nnnorm_indicator_sq hA hAB f
  rw [lintegral_nnnorm_sq_eq_norm_toLp_sq v hv,
    lintegral_nnnorm_sq_eq_norm_toLp_sq u hu] at h
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using congrArg ENNReal.toReal h

/-- The added fractional square is controlled by the original physical L2 square. -/
theorem norm_differenceQuotient_sq_le_of_indicator_ae
    (hs : 0 < s) (hδ : 0 < δ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : A ⊆ B)
    (hgap : ∀ x ∈ A, f x ≠ 0 → ∀ y ∈ B \ A, δ ≤ dist x y)
    (u : GagliardoSpace n s A) (v : GagliardoSpace n s B)
    (hu : (toLp n s A u : ℝ^n → ℝ) =ᵐ[volume.restrict A] f)
    (hv : (toLp n s B v : ℝ^n → ℝ) =ᵐ[volume.restrict B] A.indicator f) :
    ‖differenceQuotient n s B v‖ ^ 2 ≤ ‖differenceQuotient n s A u‖ ^ 2 +
      2 * (1 + δ⁻¹) ^ ((n : ℝ) + 2 * s) *
        (‖toLp n s A u‖ ^ 2 * (Localization.edgeMass n s).toReal) := by
  have h := Localization.gagliardoSq_indicator_le_of_gap hs hδ hA hB hAB hgap
  rw [gagliardoSq_eq_norm_sq_of_toLp_ae v hv, gagliardoSq_eq_norm_sq_of_toLp_ae u hu,
    lintegral_nnnorm_sq_eq_norm_toLp_sq u hu] at h
  have hmass := (Localization.edgeMass_lt_top (n := n) hs).ne
  have hC : 0 ≤ (1 + δ⁻¹) ^ ((n : ℝ) + 2 * s) := by positivity
  have hr := ENNReal.toReal_mono (by finiteness) h
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at hr
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _),
    ENNReal.toReal_ofReal hC, ENNReal.toReal_ofNat]
      using hr

/-- The support gap multiplies the intrinsic graph norm by at most the square
root of one plus the two radial tail costs. -/
theorem norm_le_of_indicator_ae
    (hs : 0 < s) (hδ : 0 < δ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : A ⊆ B)
    (hgap : ∀ x ∈ A, f x ≠ 0 → ∀ y ∈ B \ A, δ ≤ dist x y)
    (u : GagliardoSpace n s A) (v : GagliardoSpace n s B)
    (hu : (toLp n s A u : ℝ^n → ℝ) =ᵐ[volume.restrict A] f)
    (hv : (toLp n s B v : ℝ^n → ℝ) =ᵐ[volume.restrict B] A.indicator f) :
    ‖v‖ ≤ Real.sqrt (1 + 2 * (1 + δ⁻¹) ^ ((n : ℝ) + 2 * s) *
      (Localization.edgeMass n s).toReal) * ‖u‖ := by
  have hb := norm_toLp_sq_eq_of_indicator_ae hA hAB u v hu hv
  have hd := norm_differenceQuotient_sq_le_of_indicator_ae hs hδ hA hB hAB hgap u v hu hv
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity), norm_sq_eq, norm_sq_eq, hb]
  have hnonneg : 0 ≤ 2 * (1 + δ⁻¹) ^ ((n : ℝ) + 2 * s) *
      (Localization.edgeMass n s).toReal * ‖differenceQuotient n s A u‖ ^ 2 := by
    positivity
  nlinarith only [hd, hnonneg]

end SobolevSpace.Fractional.GagliardoSpace
