/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Extension.Folding
public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij

/-!
# Intrinsic Gagliardo estimates for even reflection

Folding contracts distances and has multiplicity two. Thus the base power integral
of even reflection doubles, while the difference-quotient power integral grows by
at most four. Both estimates apply to functions with values in a real normed space.

The kernel comparison needs `0 ≤ n / p.toReal + s`. In particular it applies to
finite positive exponents throughout `0 < s < 1`. The quadratic formulas are
specializations of these estimates; no first-order extension theorem is used.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace.Fractional.Extension

open SobolevSpace.HalfSpace

variable {n : ℕ} [Fact (0 < n)] {s : ℝ} {p : ℝ≥0∞}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Folding decreases the norm of the difference quotient after pullback.
If the folded points coincide, both numerators vanish. -/
theorem norm_diffQuot_comp_foldUpper_le (hs : 0 ≤ (n : ℝ) / p.toReal + s)
    (u : ℝ^n → F) (z : ℝ^n × ℝ^n) :
    ‖diffQuot n s (u ∘ foldUpper n) z (p := p)‖ ≤
      ‖diffQuot n s u (Prod.map (foldUpper n) (foldUpper n) z) (p := p)‖ := by
  by_cases h : foldUpper n z.1 = foldUpper n z.2
  · simp [diffQuot, h]
  have hpos : 0 < ‖foldUpper n z.1 - foldUpper n z.2‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr h)
  simp only [diffQuot, Function.comp_apply, Prod.map_fst, Prod.map_snd,
    norm_smul, norm_inv, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  rw [mul_comm, ← div_eq_mul_inv, mul_comm, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left (norm_nonneg _)
    (Real.rpow_pos_of_pos hpos _)
    (Real.rpow_le_rpow (norm_nonneg _) (norm_foldUpper_sub_le n z.1 z.2) hs)

/-- The difference-quotient power integral grows by at most four under folding. -/
theorem lintegral_enorm_diffQuot_comp_foldUpper_le
    (hs : 0 ≤ (n : ℝ) / p.toReal + s) {u : ℝ^n → F}
    (hu : AEStronglyMeasurable u (volume.restrict ℝ^n₊)) :
    (∫⁻ z, ‖diffQuot n s (u ∘ foldUpper n) z (p := p)‖ₑ ^ p.toReal
      ∂gagliardoProductMeasure n Set.univ) ≤
      4 * ∫⁻ z, ‖diffQuot n s u z (p := p)‖ₑ ^ p.toReal
        ∂gagliardoProductMeasure n ℝ^n₊ := by
  simp only [gagliardoProductMeasure, Measure.restrict_univ]
  calc
    _ ≤ ∫⁻ z, ‖diffQuot n s u (Prod.map (foldUpper n) (foldUpper n) z)
        (p := p)‖ₑ ^ p.toReal ∂((volume : Measure (ℝ^n)).prod volume) := by
      apply lintegral_mono
      intro z
      apply ENNReal.rpow_le_rpow _ ENNReal.toReal_nonneg
      exact enorm_le_iff_norm_le.mpr (norm_diffQuot_comp_foldUpper_le hs u z)
    _ = _ := lintegral_comp_foldUpper_prod n _
      ((aestronglyMeasurable_diffQuot (s := s) (p := p) hu).enorm.pow_const p.toReal)

omit [NormedSpace ℝ F] in
/-- The base power integral of even reflection is exactly twice the intrinsic one. -/
theorem lintegral_enorm_comp_foldUpper (u : ℝ^n → F)
    (hu : AEStronglyMeasurable u (volume.restrict ℝ^n₊)) (q : ℝ) :
    ∫⁻ x, ‖(u ∘ foldUpper n) x‖ₑ ^ q = 2 * ∫⁻ x in ℝ^n₊, ‖u x‖ₑ ^ q :=
  lintegral_comp_foldUpper n _ (hu.enorm.pow_const q)

omit [NormedSpace ℝ F] in
/-- Even reflection preserves `Lᵖ` membership. -/
theorem memLp_comp_foldUpper {u : ℝ^n → F}
    (hu : MemLp u p (volume.restrict ℝ^n₊)) :
    MemLp (u ∘ foldUpper n) p (volume : Measure (ℝ^n)) :=
  (hu.smul_measure (c := 2) (by norm_num)).comp_measurePreserving
    (measurePreserving_foldUpper n)

/-- Even reflection extends every intrinsic Gagliardo function, without a
completeness assumption on its codomain. -/
theorem memGagliardo_comp_foldUpper (hs : 0 ≤ (n : ℝ) / p.toReal + s)
    {u : ℝ^n → F} (hu : MemGagliardo n s ℝ^n₊ u (p := p)) :
    MemGagliardo n s Set.univ (u ∘ foldUpper n) (p := p) := by
  have hb : MemLp (u ∘ foldUpper n) p (volume.restrict Set.univ) := by
    simpa only [Measure.restrict_univ] using memLp_comp_foldUpper hu.1
  refine ⟨hb, ?_⟩
  have hd := (hu.2.smul_measure (c := 4) (by norm_num)).comp_measurePreserving
    (measurePreserving_foldUpper_prod n)
  have hmeas := aestronglyMeasurable_diffQuot (s := s) (p := p)
    hb.aestronglyMeasurable
  simp only [gagliardoProductMeasure, Measure.restrict_univ] at hmeas ⊢
  exact hd.mono hmeas
    (Filter.Eventually.of_forall (norm_diffQuot_comp_foldUpper_le hs u))

/-- The squared intrinsic Gagliardo seminorm grows by at most four. -/
theorem gagliardoSq_comp_foldUpper_le (hs : 0 ≤ (n : ℝ) / 2 + s)
    {u : ℝ^n → ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict ℝ^n₊)) :
    gagliardoSq n s Set.univ (u ∘ foldUpper n) ≤ 4 * gagliardoSq n s ℝ^n₊ u := by
  simpa only [gagliardoSq, ENNReal.toReal_ofNat, ENNReal.rpow_two, enorm_eq_nnnorm]
    using lintegral_enorm_diffQuot_comp_foldUpper_le (p := 2) hs hu

/-- The squared `L²` integral of even reflection is exactly twice the intrinsic one. -/
theorem lintegral_norm_sq_comp_foldUpper {u : ℝ^n → ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict ℝ^n₊)) :
    ∫⁻ x, (‖(u ∘ foldUpper n) x‖₊ : ℝ≥0∞) ^ 2 =
      2 * ∫⁻ x in ℝ^n₊, (‖u x‖₊ : ℝ≥0∞) ^ 2 := by
  simpa only [ENNReal.rpow_two, enorm_eq_nnnorm] using
    lintegral_enorm_comp_foldUpper u hu 2

end SobolevSpace.Fractional.Extension
