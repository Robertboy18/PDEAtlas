/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.FirstOrder.Lp
public import PDE.Spaces.Sobolev.Fractional.Domain.Extension.ReflectionEstimate
import PDE.Analysis.MeasureTheory.LpNorm.PowerIntegral

/-!
# Even reflection on intrinsic Gagliardo graphs

Even reflection maps the intrinsic half-space Gagliardo space to the whole-space one.
For finite `p ≥ 1` its graph norm is bounded by `4 ^ (1 / p.toReal)`: the base power
integral doubles and the difference power integral grows by at most four. The codomain can
be any real normed space. `Reflection` makes it a bounded right inverse of restriction.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal FractionalSobolev

namespace SobolevSpace.Fractional.Extension

open SobolevSpace.HalfSpace GagliardoSpace

variable {n : ℕ} [Fact (0 < n)] {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Even reflection of an intrinsic Gagliardo element into the whole-space graph. -/
def evenReflection (hs : 0 ≤ (n : ℝ) / p.toReal + s)
    (u : W^{s,p}(ℝ^n₊; F)) :
    W^{s,p}(ℝ^n; F) :=
  ofFunction ((toLp n s ℝ^n₊ u : ℝ^n → F) ∘ foldUpper n)
    (memGagliardo_comp_foldUpper hs ⟨Lp.memLp _, toLp_mem_domain u⟩)

/-- The base coordinate is represented almost everywhere by folding the input. -/
theorem toLp_evenReflection_apply_ae (hs : 0 ≤ (n : ℝ) / p.toReal + s)
    (u : W^{s,p}(ℝ^n₊; F)) :
    (toLp n s Set.univ (evenReflection hs u) : ℝ^n → F) =ᵐ[volume]
      (toLp n s ℝ^n₊ u : ℝ^n → F) ∘ foldUpper n := by
  simpa only [evenReflection, Measure.restrict_univ] using
    toLp_ofFunction_apply_ae _ (memGagliardo_comp_foldUpper hs
      (⟨Lp.memLp _, toLp_mem_domain u⟩ : MemGagliardo n s ℝ^n₊
        (toLp n s ℝ^n₊ u : ℝ^n → F) (p := p)))

/-- The base-coordinate p-th norm power doubles under even reflection. -/
theorem norm_toLp_evenReflection_rpow (hp : p ≠ ∞)
    (hs : 0 ≤ (n : ℝ) / p.toReal + s)
    (u : W^{s,p}(ℝ^n₊; F)) :
    ‖toLp n s Set.univ (evenReflection hs u)‖ ^ p.toReal =
      2 * ‖toLp n s ℝ^n₊ u‖ ^ p.toReal := by
  have he : (toLp n s Set.univ (evenReflection hs u) : ℝ^n → F)
      =ᵐ[volume.restrict Set.univ] (toLp n s ℝ^n₊ u : ℝ^n → F) ∘ foldUpper n := by
    simpa only [Measure.restrict_univ] using toLp_evenReflection_apply_ae hs u
  have h := lintegral_enorm_comp_foldUpper (toLp n s ℝ^n₊ u)
    (Lp.aestronglyMeasurable _) p.toReal
  have hleft := Lp.lintegral_enorm_rpow_eq_of_ae hp _ he
  simp only [Measure.restrict_univ] at hleft
  rw [hleft, Lp.lintegral_enorm_rpow_eq_of_ae hp _ (ae_eq_refl _)] at h
  have hr := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _),
    ENNReal.toReal_mul, ENNReal.toReal_ofNat] using hr

/-- The difference-coordinate p-th norm power grows by at most four. -/
theorem norm_differenceQuotient_evenReflection_rpow_le (hp : p ≠ ∞)
    (hs : 0 ≤ (n : ℝ) / p.toReal + s)
    (u : W^{s,p}(ℝ^n₊; F)) :
    ‖differenceQuotient n s Set.univ (evenReflection hs u)‖ ^ p.toReal ≤
      4 * ‖differenceQuotient n s ℝ^n₊ u‖ ^ p.toReal := by
  have he : (toLp n s Set.univ (evenReflection hs u) : ℝ^n → F)
      =ᵐ[volume.restrict Set.univ] (toLp n s ℝ^n₊ u : ℝ^n → F) ∘ foldUpper n := by
    simpa only [Measure.restrict_univ] using toLp_evenReflection_apply_ae hs u
  have hdiff := (differenceQuotient_apply_ae (evenReflection hs u)).trans
    (diffQuot_congr_ae he)
  have h := lintegral_enorm_diffQuot_comp_foldUpper_le hs
    (Lp.aestronglyMeasurable (toLp n s ℝ^n₊ u))
  rw [Lp.lintegral_enorm_rpow_eq_of_ae hp _ hdiff,
    Lp.lintegral_enorm_rpow_eq_of_ae hp _ (differenceQuotient_apply_ae u)] at h
  have hr := ENNReal.toReal_mono (by finiteness) h
  simpa only [ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _),
    ENNReal.toReal_mul, ENNReal.toReal_ofNat] using hr

/-- The full graph estimate retains the separate base and difference constants. -/
theorem norm_evenReflection_rpow_le (hp : p ≠ ∞)
    (hs : 0 ≤ (n : ℝ) / p.toReal + s)
    (u : W^{s,p}(ℝ^n₊; F)) :
    ‖evenReflection hs u‖ ^ p.toReal ≤
      2 * ‖toLp n s ℝ^n₊ u‖ ^ p.toReal +
        4 * ‖differenceQuotient n s ℝ^n₊ u‖ ^ p.toReal := by
  rw [norm_rpow_eq hp, norm_toLp_evenReflection_rpow hp]
  exact add_le_add le_rfl (norm_differenceQuotient_evenReflection_rpow_le hp hs u)

/-- At a finite exponent, even reflection has graph-norm bound `4 ^ (1 / p.toReal)`. -/
theorem norm_evenReflection_le_rpow (hp : p ≠ ∞)
    (hs : 0 ≤ (n : ℝ) / p.toReal + s)
    (u : W^{s,p}(ℝ^n₊; F)) :
    ‖evenReflection hs u‖ ≤ (4 : ℝ) ^ (1 / p.toReal) * ‖u‖ := by
  have hp0 : 0 < p.toReal := p.toReal_pos_iff_ne_top.mpr hp
  apply (Real.rpow_le_rpow_iff (norm_nonneg _)
    (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (norm_nonneg _)) hp0).mp
  rw [Real.mul_rpow (Real.rpow_nonneg (by norm_num) _) (norm_nonneg _),
    one_div, Real.rpow_inv_rpow (by norm_num) hp0.ne', norm_rpow_eq hp u]
  have hb := Real.rpow_nonneg (norm_nonneg (toLp n s ℝ^n₊ u)) p.toReal
  nlinarith [norm_evenReflection_rpow_le hp hs u]

end SobolevSpace.Fractional.Extension
