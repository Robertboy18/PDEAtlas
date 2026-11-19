/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.LpNorm.PowerIntegral
public import PDE.Spaces.Sobolev.Fractional.Domain.Localization.Multiplier.Basic

/-!
# Bounded scalar multipliers on the fractional graph

The power-integral estimate for cutoff multiplication bounds both coordinates of
the Gagliardo graph. Taking the positive p-th root gives a continuous
linear operator for every finite exponent at least one and every real normed
codomain. The scalar quadratic estimate has a sharper constant.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped NNReal ENNReal FractionalSobolev

namespace SobolevSpace.Fractional.Localization

/-- A graph-norm bound in terms of the uniform bound, Lipschitz constant, and
radial kernel mass. Its p-th power bounds the two coordinate contributions. -/
def cutoffBound (n : ℕ) (s : ℝ) (p : ℝ≥0∞) (L M : ℝ≥0) : ℝ :=
  ((M : ℝ) ^ p.toReal + (2 : ℝ) ^ p.toReal *
    ((M : ℝ) ^ p.toReal + ((L : ℝ) ^ p.toReal + (2 * (M : ℝ)) ^ p.toReal) *
      (cutoffMass n s (p := p.toReal)).toReal)) ^ p.toReal⁻¹

/-- The multiplier norm bound is nonnegative. -/
theorem cutoffBound_nonneg (n : ℕ) (s : ℝ) (p : ℝ≥0∞) (L M : ℝ≥0) :
    0 ≤ cutoffBound n s p L M := by
  unfold cutoffBound
  positivity

end SobolevSpace.Fractional.Localization

namespace SobolevSpace.Fractional.GagliardoSpace

variable {n : ℕ} {s : ℝ} {Ω : Set (ℝ^n)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {φ : ℝ^n → ℝ} {L M : ℝ≥0}

variable (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞)
  (hL : LipschitzWith L φ) (hM : ∀ x, ‖φ x‖ ≤ M)

/-- The underlying Lp norm has the usual uniform scalar multiplication bound. -/
theorem norm_toLp_smulCutoff_le (u : W^{s,p}(Ω; F)) :
    ‖toLp n s Ω (smulCutoff hs0 hs1 hp hL hM u)‖ ≤ (M : ℝ) * ‖toLp n s Ω u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [toLp_smulCutoff_apply_ae hs0 hs1 hp hL hM u] with x hx
  rw [hx, norm_smul]
  exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)

/-- The fractional seminorm power has a base Lp contribution from cutoff increments. -/
theorem norm_differenceQuotient_smulCutoff_rpow_le
    (u : W^{s,p}(Ω; F)) :
    ‖differenceQuotient n s Ω (smulCutoff hs0 hs1 hp hL hM u)‖ ^ p.toReal ≤
      (2 : ℝ) ^ p.toReal *
        ((M : ℝ) ^ p.toReal * ‖differenceQuotient n s Ω u‖ ^ p.toReal +
          ((L : ℝ) ^ p.toReal + (2 * (M : ℝ)) ^ p.toReal) *
            (‖toLp n s Ω u‖ ^ p.toReal *
              (Localization.cutoffMass n s (p := p.toReal)).toReal)) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have h := Localization.lintegral_enorm_diffQuot_smul_rpow_le hp0 hp
    (by positivity : 0 ≤ (n : ℝ) + p.toReal * s) hL hM
    (Lp.aestronglyMeasurable (toLp n s Ω u))
  have hout := (differenceQuotient_apply_ae (smulCutoff hs0 hs1 hp hL hM u)).trans
    (diffQuot_congr_ae (toLp_smulCutoff_apply_ae hs0 hs1 hp hL hM u))
  rw [Lp.lintegral_enorm_rpow_eq_of_ae hp _ hout,
    Lp.lintegral_enorm_rpow_eq_of_ae hp _ (differenceQuotient_apply_ae u),
    Lp.lintegral_enorm_rpow_eq_of_ae hp _ (ae_eq_refl (toLp n s Ω u))] at h
  have hmass := (Localization.cutoffMass_lt_top (n := n) hs0 hs1 p.toReal hr).ne
  have hreal := ENNReal.toReal_mono (by finiteness) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness)] at hreal
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofNat, ENNReal.toReal_ofReal (by positivity : 0 ≤ ‖
      differenceQuotient n s Ω (smulCutoff hs0 hs1 hp hL hM u)‖ ^ p.toReal),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (M : ℝ) ^ p.toReal),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ ‖differenceQuotient n s Ω u‖ ^ p.toReal),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (L : ℝ) ^ p.toReal +
      (2 * (M : ℝ)) ^ p.toReal),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ ‖toLp n s Ω u‖ ^ p.toReal)] using hreal

/-- The cutoff action is bounded in the full intrinsic graph norm. -/
theorem norm_smulCutoff_le (u : W^{s,p}(Ω; F)) :
    ‖smulCutoff hs0 hs1 hp hL hM u‖ ≤ Localization.cutoffBound n s p L M * ‖u‖ := by
  have hr : 0 < p.toReal := p.toReal_pos_iff_ne_top.mpr hp
  have hb := Real.rpow_le_rpow (norm_nonneg _)
    (norm_toLp_smulCutoff_le hs0 hs1 hp hL hM u) hr.le
  rw [Real.mul_rpow M.coe_nonneg (norm_nonneg _)] at hb
  have hd := norm_differenceQuotient_smulCutoff_rpow_le hs0 hs1 hp hL hM u
  have hu0 : ‖toLp n s Ω u‖ ^ p.toReal ≤ ‖u‖ ^ p.toReal := by
    rw [norm_rpow_eq hp]
    exact le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg _) _)
  have hu1 : ‖differenceQuotient n s Ω u‖ ^ p.toReal ≤ ‖u‖ ^ p.toReal := by
    rw [norm_rpow_eq hp]
    exact le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _)
  apply (Real.rpow_le_rpow_iff (norm_nonneg _)
    (mul_nonneg (Localization.cutoffBound_nonneg n s p L M) (norm_nonneg _)) hr).mp
  rw [Real.mul_rpow (Localization.cutoffBound_nonneg n s p L M) (norm_nonneg _),
    Localization.cutoffBound, Real.rpow_inv_rpow (by positivity) hr.ne', norm_rpow_eq hp]
  refine (add_le_add hb hd).trans ?_
  calc
    _ ≤ (M : ℝ) ^ p.toReal * ‖u‖ ^ p.toReal + (2 : ℝ) ^ p.toReal *
        ((M : ℝ) ^ p.toReal * ‖u‖ ^ p.toReal +
          ((L : ℝ) ^ p.toReal + (2 * (M : ℝ)) ^ p.toReal) *
            (‖u‖ ^ p.toReal * (Localization.cutoffMass n s (p := p.toReal)).toReal)) := by
      gcongr
    _ = _ := by ring

/-- Bounded Lipschitz scalar multiplication on the normed-valued fractional space.
Neither completeness of the codomain nor regularity of the domain is needed. -/
def smulCutoffL :
    W^{s,p}(Ω; F) →L[ℝ] W^{s,p}(Ω; F) :=
  LinearMap.mkContinuous
    { toFun := smulCutoff hs0 hs1 hp hL hM
      map_add' := smulCutoff_add hs0 hs1 hp hL hM
      map_smul' := smulCutoff_smul hs0 hs1 hp hL hM }
    (Localization.cutoffBound n s p L M) (norm_smulCutoff_le hs0 hs1 hp hL hM)

/-- Applying the bundled operator is the scalar cutoff action. -/
@[simp]
theorem smulCutoffL_apply (u : W^{s,p}(Ω; F)) :
    smulCutoffL hs0 hs1 hp hL hM u = smulCutoff hs0 hs1 hp hL hM u :=
  rfl

/-- The bounded operator acts by scalar multiplication of physical representatives. -/
theorem toLp_smulCutoffL_apply_ae (u : W^{s,p}(Ω; F)) :
    (toLp n s Ω (smulCutoffL hs0 hs1 hp hL hM u) : ℝ^n → F) =ᵐ[volume.restrict Ω]
      fun x ↦ φ x • toLp n s Ω u x :=
  toLp_smulCutoff_apply_ae hs0 hs1 hp hL hM u

/-- The bounded operator is independent of the chosen Lipschitz and uniform bounds. -/
theorem smulCutoffL_eq {L' M' : ℝ≥0}
    (hL' : LipschitzWith L' φ) (hM' : ∀ x, ‖φ x‖ ≤ M') :
    smulCutoffL (Ω := Ω) (F := F) hs0 hs1 hp hL hM =
      smulCutoffL hs0 hs1 hp hL' hM' := by
  apply ContinuousLinearMap.ext
  intro u
  exact smulCutoff_eq hs0 hs1 hp hL hM hL' hM' u

/-- The bundled operator agrees with pointwise multiplication before passing to classes. -/
theorem smulCutoffL_ofFunction {f : ℝ^n → F} (hf : MemGagliardo n s Ω f (p := p)) :
    smulCutoffL hs0 hs1 hp hL hM (ofFunction f hf) =
      ofFunction (fun x ↦ φ x • f x)
        (Localization.memGagliardo_smul_cutoff hs0 hs1 hL hM hf
          (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hp) :=
  smulCutoff_ofFunction hs0 hs1 hp hL hM hf

/-- The operator norm is bounded by the explicit radial-kernel constant. -/
theorem norm_smulCutoffL_le :
    ‖smulCutoffL (Ω := Ω) (F := F) hs0 hs1 hp hL hM‖ ≤
      Localization.cutoffBound n s p L M :=
  ContinuousLinearMap.opNorm_le_bound _ (Localization.cutoffBound_nonneg n s p L M)
    (norm_smulCutoff_le hs0 hs1 hp hL hM)

end SobolevSpace.Fractional.GagliardoSpace
