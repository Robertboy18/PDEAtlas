/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Localization.Multiplier.Operator
import PDE.Analysis.MeasureTheory.LpNorm

/-!
# Bounded cutoff multiplication on the intrinsic fractional space

The scalar quadratic operator specializes the normed-valued cutoff construction.
Its sharper graph-norm bound follows from the quadratic integral product estimate,
including the finite mass of the localization kernel.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal FractionalSobolev

namespace SobolevSpace.Fractional.GagliardoSpace

variable {n : ℕ} {s : ℝ} {Ω : Set (ℝ^n)} {φ : ℝ^n → ℝ} {L M : ℝ≥0}

variable (hs0 : 0 < s) (hs1 : s < 1)
  (hL : LipschitzWith L φ) (hM : ∀ x, ‖φ x‖ ≤ M)

/-- Multiplication of the physical representative by a bounded Lipschitz cutoff. -/
def mulCutoff (u : W^{s,2}(Ω)) : W^{s,2}(Ω) :=
  smulCutoff hs0 hs1 (by norm_num) hL hM u

theorem toLp_mulCutoff_apply_ae (u : W^{s,2}(Ω)) :
    (toLp n s Ω (mulCutoff hs0 hs1 hL hM u) : ℝ^n → ℝ) =ᵐ[volume.restrict Ω]
      fun x ↦ φ x * toLp n s Ω u x := by
  simpa only [mulCutoff, smul_eq_mul] using
    (toLp_smulCutoff_apply_ae hs0 hs1 (by norm_num) hL hM u)

/-- The physical L2 norm has the usual uniform multiplication bound. -/
theorem norm_toLp_mulCutoff_le (u : W^{s,2}(Ω)) :
    ‖toLp n s Ω (mulCutoff hs0 hs1 hL hM u)‖ ≤ (M : ℝ) * ‖toLp n s Ω u‖ :=
  norm_toLp_smulCutoff_le hs0 hs1 (by norm_num) hL hM u

/-- The squared seminorm bound has an L2 contribution from the cutoff increment. -/
theorem norm_differenceQuotient_mulCutoff_sq_le (u : W^{s,2}(Ω)) :
    ‖differenceQuotient n s Ω (mulCutoff hs0 hs1 hL hM u)‖ ^ 2 ≤
      2 * (M : ℝ) ^ 2 * ‖differenceQuotient n s Ω u‖ ^ 2 +
        2 * ((L : ℝ) ^ 2 + 4 * (M : ℝ) ^ 2) *
          (‖toLp n s Ω u‖ ^ 2 * (Localization.cutoffMass n s).toReal) := by
  have h := Localization.gagliardoSq_mul_le (by positivity) hL hM
    (Lp.aestronglyMeasurable (toLp n s Ω u))
  rw [gagliardoSq_eq_norm_sq_of_toLp_ae _
      (toLp_mulCutoff_apply_ae hs0 hs1 hL hM u),
    gagliardoSq_eq_norm_sq_of_toLp_ae u (ae_eq_refl _)] at h
  have hl2 : (∫⁻ y in Ω, (‖toLp n s Ω u y‖₊ : ℝ≥0∞) ^ 2) =
      ENNReal.ofReal (‖toLp n s Ω u‖ ^ 2) :=
    Lp.lintegral_nnnorm_sq_eq_norm_sq_of_ae_eq (toLp n s Ω u) (ae_eq_refl _)
  rw [hl2] at h
  have hmass := (Localization.cutoffMass_lt_top (n := n) hs0 hs1).ne
  have hr := ENNReal.toReal_mono (by finiteness) h
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at hr
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * (M : ℝ) ^ 2),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * ((L : ℝ) ^ 2 + 4 * (M : ℝ) ^ 2))]
      using hr

/-- A graph-norm bound for cutoff multiplication, with its explicit radial integral. -/
theorem norm_mulCutoff_le (u : W^{s,2}(Ω)) :
    ‖mulCutoff hs0 hs1 hL hM u‖ ≤
      Real.sqrt (3 * (M : ℝ) ^ 2 + 2 * ((L : ℝ) ^ 2 + 4 * (M : ℝ) ^ 2) *
        (Localization.cutoffMass n s).toReal) * ‖u‖ := by
  have hb := pow_le_pow_left₀ (norm_nonneg _)
    (norm_toLp_mulCutoff_le hs0 hs1 hL hM u) 2
  have hd := norm_differenceQuotient_mulCutoff_sq_le hs0 hs1 hL hM u
  have hout := norm_sq_eq (mulCutoff hs0 hs1 hL hM u)
  have hin := norm_sq_eq u
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity), hout, hin]
  simp only [mul_pow] at hb
  refine (add_le_add hb hd).trans ?_
  have hcross : 0 ≤ 2 * (M : ℝ) ^ 2 * ‖toLp n s Ω u‖ ^ 2 +
      ((M : ℝ) ^ 2 + 2 * ((L : ℝ) ^ 2 + 4 * (M : ℝ) ^ 2) *
        (Localization.cutoffMass n s).toReal) * ‖differenceQuotient n s Ω u‖ ^ 2 := by
    positivity
  nlinarith only [hcross]

/-- Cutoff multiplication preserves addition of intrinsic fractional functions. -/
theorem mulCutoff_add (u v : W^{s,2}(Ω; ℝ)) :
    mulCutoff hs0 hs1 hL hM (u + v) =
      mulCutoff hs0 hs1 hL hM u + mulCutoff hs0 hs1 hL hM v :=
  smulCutoff_add hs0 hs1 (by norm_num) hL hM u v

/-- Cutoff multiplication commutes with real scalar multiplication. -/
theorem mulCutoff_smul (c : ℝ) (u : W^{s,2}(Ω; ℝ)) :
    mulCutoff hs0 hs1 hL hM (c • u) = c • mulCutoff hs0 hs1 hL hM u :=
  smulCutoff_smul hs0 hs1 (by norm_num) hL hM c u

/-- Bounded cutoff multiplication on the intrinsic fractional Hilbert space. -/
def mulCutoffCLM : W^{s,2}(Ω) →L[ℝ] W^{s,2}(Ω) :=
  smulCutoffL hs0 hs1 (by norm_num) hL hM

/-- Cutoff multiplication has the ordinary physical representative on the domain. -/
theorem toLp_mulCutoffCLM_apply_ae (u : W^{s,2}(Ω)) :
    (toLp n s Ω (mulCutoffCLM hs0 hs1 hL hM u) : ℝ^n → ℝ) =ᵐ[volume.restrict Ω]
      fun x ↦ φ x * toLp n s Ω u x :=
  toLp_mulCutoff_apply_ae hs0 hs1 hL hM u

/-- Valid choices of the Lipschitz and uniform bounds give the same operator. -/
theorem mulCutoffCLM_eq {L' M' : ℝ≥0}
    (hL' : LipschitzWith L' φ) (hM' : ∀ x, ‖φ x‖ ≤ M') :
    mulCutoffCLM (Ω := Ω) hs0 hs1 hL hM = mulCutoffCLM hs0 hs1 hL' hM' :=
  smulCutoffL_eq hs0 hs1 (by norm_num) hL hM hL' hM'

/-- The bounded operator agrees with multiplication of any intrinsic function. -/
theorem mulCutoffCLM_ofFunction {f : ℝ^n → ℝ} (hf : MemGagliardo n s Ω f) :
    mulCutoffCLM hs0 hs1 hL hM (ofFunction f hf) =
      ofFunction (fun x ↦ φ x * f x) (Localization.memGagliardo_mul_cutoff hs0 hs1 hL hM hf) := by
  simpa only [mulCutoffCLM, smul_eq_mul] using
    (smulCutoffL_ofFunction hs0 hs1 (by norm_num) hL hM hf)

theorem norm_mulCutoffCLM_le :
    ‖mulCutoffCLM (Ω := Ω) hs0 hs1 hL hM‖ ≤
      Real.sqrt (3 * (M : ℝ) ^ 2 + 2 * ((L : ℝ) ^ 2 + 4 * (M : ℝ) ^ 2) *
        (Localization.cutoffMass n s).toReal) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    (norm_mulCutoff_le hs0 hs1 hL hM)

end SobolevSpace.Fractional.GagliardoSpace
