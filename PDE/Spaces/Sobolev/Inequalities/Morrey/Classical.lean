/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Morrey.FullEmbedding
import PDE.Spaces.Sobolev.Inequalities.Morrey.FiniteExponent.Multidimensional.Estimate

/-!
# Morrey's inequality for arbitrary C¹ functions

The extended uniform norm plus Mathlib's extended Hölder seminorm satisfies Morrey's
inequality without any integrability or support premise. This includes the case of
an infinite Sobolev norm. When that norm is finite, `exists_morreyBound_of_contDiff`
gives the corresponding element of the full bounded Hölder space.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace SobolevSpace

/-- The analytic finite-exponent Morrey estimate controls Mathlib's extended Hölder
seminorm even when the derivative is not integrable. -/
theorem eHolderNorm_le_finiteMorrey_of_contDiff
    {n : ℕ} {p q : ℝ} (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q) (f : ℝ^n → ℝ) (hf : ContDiff ℝ 1 f) :
    eHolderNorm (finiteMorreyHolderExponent n p hn hp : ℝ≥0) f ≤
      finiteMorreyHolderConstantE n p q f := by
  by_cases htop : finiteMorreyHolderConstantE n p q f = ∞
  · simp only [htop, le_top]
  · have hholder : HolderWith (finiteMorreyHolderConstant n p q f)
        (finiteMorreyHolderExponent n p hn hp : ℝ≥0) f := by
      intro x y
      have h := enorm_sub_le_eLpNorm_fderiv_mul_rpow f hf hn hp hpq x y
      change ‖f y - f x‖ₑ ≤ finiteMorreyHolderConstantE n p q f *
        ENNReal.ofReal ‖y - x‖ ^ morreyExponent n (ENNReal.ofReal p) at h
      simpa [finiteMorreyHolderConstant, edist_dist, Real.dist_eq,
        Real.enorm_eq_ofReal_abs, abs_sub_comm, dist_eq_norm, norm_sub_rev,
        ENNReal.coe_toNNReal htop,
        Real.coe_toNNReal _ (morreyExponent_ofReal_pos hn hp).le] using h
    simpa only [finiteMorreyHolderConstant, ENNReal.coe_toNNReal htop] using
      hholder.eHolderNorm_le

/-- The geometric coefficient in the finite Morrey estimate is finite. -/
theorem finiteMorreyCoefficientE_ne_top
    {n : ℕ} {p q : ℝ} (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q) :
    finiteMorreyCoefficientE n p q ≠ ∞ := by
  have hball : morreyBallAverageConstant n ≠ ∞ := by
    simp [morreyBallAverageConstant]
  have hkernel : morreyCenteredKernelConstant n q ≠ ∞ := by
    unfold morreyCenteredKernelConstant
    exact ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.mpr hpq.symm.pos.le)
      ENNReal.ofReal_ne_top
  have hpower : ENNReal.ofReal 2 ^ morreyExponent n (ENNReal.ofReal p) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (morreyExponent_ofReal_pos hn hp).le
      ENNReal.ofReal_ne_top
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hball) hkernel) hpower

/-- The full extended Hölder norm has a finite-exponent Morrey bound for every
C¹ function, with no assumption that either `Lᵖ` norm is finite. -/
theorem fullENorm_le_finiteMorrey_of_contDiff
    {n : ℕ} {p q : ℝ} (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q) (f : ℝ^n → ℝ) (hf : ContDiff ℝ 1 f) :
    (⨆ x, ‖f x‖ₑ) + eHolderNorm (finiteMorreyHolderExponent n p hn hp : ℝ≥0) f ≤
      (morreyUnitBallLpFactor n p + 2 * finiteMorreyCoefficientE n p q) *
        (eLpNorm f (ENNReal.ofReal p) volume +
          eLpNorm (fderiv ℝ f) (ENNReal.ofReal p) volume) := by
  have hsup := iSup_le (enorm_apply_le_eLpNorm_add_finiteMorrey f hf hn hp hpq)
  have hsemi := eHolderNorm_le_finiteMorrey_of_contDiff hn hp hpq f hf
  refine (add_le_add hsup hsemi).trans ?_
  rw [finiteMorreyHolderConstantE_eq]
  let A := morreyUnitBallLpFactor n p
  let B := finiteMorreyCoefficientE n p q
  let X := eLpNorm f (ENNReal.ofReal p) volume
  let Y := eLpNorm (fderiv ℝ f) (ENNReal.ofReal p) volume
  change (X * A + B * Y) + B * Y ≤ (A + 2 * B) * (X + Y)
  calc
    (X * A + B * Y) + B * Y = A * X + (2 * B) * Y := by ring
    _ ≤ A * (X + Y) + (2 * B) * (X + Y) :=
      add_le_add (mul_le_mul_right le_self_add _) (mul_le_mul_right le_add_self _)
    _ = (A + 2 * B) * (X + Y) := (add_mul _ _ _).symm

/-- At infinity, the extended full Lipschitz norm is bounded by the essential
bounds of the function and its classical derivative. -/
theorem fullENorm_le_eLpNorm_top_of_contDiff
    {n : ℕ} (f : ℝ^n → ℝ) (hf : ContDiff ℝ 1 f) :
    (⨆ x, ‖f x‖ₑ) + eHolderNorm 1 f ≤
      eLpNorm f ∞ volume + eLpNorm (fderiv ℝ f) ∞ volume := by
  apply add_le_add
  · apply iSup_le
    intro x
    by_cases htop : eLpNorm f ∞ volume = ∞
    · simp [htop]
    · have h := norm_apply_le_eLpNorm_top_of_continuous hf.continuous htop x
      simpa only [ofReal_norm, ENNReal.ofReal_toReal htop] using ENNReal.ofReal_le_ofReal h
  · by_cases htop : eLpNorm (fderiv ℝ f) ∞ volume = ∞
    · simp [htop]
    · have hLip : LipschitzWith (eLpNorm (fderiv ℝ f) ∞ volume).toNNReal f := by
        apply LipschitzWith.of_dist_le_mul
        intro x y
        simpa only [dist_eq_norm, Real.norm_eq_abs, ENNReal.coe_toNNReal_eq_toReal] using
          norm_sub_le_eLpNorm_fderiv_top_toReal_mul_norm f hf htop y x
      simpa only [ENNReal.coe_toNNReal htop] using hLip.holderWith.eHolderNorm_le

/-- Morrey's full extended-norm inequality for every C¹ function and every
`n < p ≤ ∞`. The constant depends only on `n` and `p`; neither compact support
nor finite Sobolev norm is a hypothesis. -/
theorem exists_fullENorm_morreyBound
    {n : ℕ} {p : ℝ≥0∞} (hn : 0 < n) (hp : (n : ℝ≥0∞) < p) :
    ∃ C : ℝ≥0, ∀ (f : ℝ^n → ℝ), ContDiff ℝ 1 f →
      (⨆ x, ‖f x‖ₑ) + eHolderNorm (morreyHolderExponent n p hn hp : ℝ≥0) f ≤
        (C : ℝ≥0∞) * (eLpNorm f p volume + eLpNorm (fderiv ℝ f) p volume) := by
  by_cases htop : p = ∞
  · subst p
    refine ⟨1, fun f hf ↦ ?_⟩
    simpa only [morreyHolderExponent_top, HolderSpace.Exponent.coe_one,
      ENNReal.coe_one, one_mul] using fullENorm_le_eLpNorm_top_of_contDiff f hf
  · obtain ⟨r, hr, rfl⟩ : ∃ r : ℝ, 0 ≤ r ∧ ENNReal.ofReal r = p :=
      ⟨p.toReal, ENNReal.toReal_nonneg, ENNReal.ofReal_toReal htop⟩
    have hpReal : (n : ℝ) < r := by
      simpa only [ENNReal.toReal_natCast, ENNReal.toReal_ofReal hr] using
        ENNReal.toReal_strict_mono ENNReal.ofReal_ne_top hp
    have hp1 : 1 < r :=
      (show (1 : ℝ) ≤ n by exact_mod_cast hn).trans_lt hpReal
    have hconj := Real.HolderConjugate.conjExponent hp1
    let C := morreyUnitBallLpFactor n r + 2 * finiteMorreyCoefficientE n r r.conjExponent
    have hC : C ≠ ∞ :=
      ENNReal.add_ne_top.mpr ⟨morreyUnitBallLpFactor_ne_top n r,
        ENNReal.mul_ne_top (by simp) (finiteMorreyCoefficientE_ne_top hn hpReal hconj)⟩
    refine ⟨C.toNNReal, fun f hf ↦ ?_⟩
    rw [morreyHolderExponent_ofReal n r hn hpReal, ENNReal.coe_toNNReal hC]
    exact fullENorm_le_finiteMorrey_of_contDiff hn hpReal hconj f hf

end SobolevSpace
