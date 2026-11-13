/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import CAS.ExactTactic

/-!
# The square-integrable dilation derivative on the real line

For a continuously differentiable real function, the dilation derivative
`z u'(z)` controls the unweighted square integral:
`∫ u² ≤ 4 ∫ (z u')²`.

Square integrability of `u` fixes the constant mode. It also removes the
need to assume a boundary flux: bounded rational multipliers justify
integration by parts, and dominated convergence removes the multiplier.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open Filter MeasureTheory
open scoped Topology

/-- The dilation derivative controls the unweighted square integral.
The two integrability premises are memberships, not quantitative estimates;
no boundary limit is assumed. -/
theorem integral_sq_le_four_integral_dilation_deriv_sq
    (u u' : ℝ → ℝ) (hu : ∀ z, HasDerivAt u (u' z) z)
    (hu' : Continuous u')
    (hu2 : Integrable (fun z ↦ u z ^ 2))
    (hzu2 : Integrable (fun z ↦ (z * u' z) ^ 2)) :
    (∫ z, u z ^ 2) ≤ 4 * ∫ z, (z * u' z) ^ 2 := by
  have huc : Continuous u := continuous_iff_continuousAt.mpr fun z ↦ (hu z).continuousAt
  have hcross : Integrable (fun z ↦ u z * (z * u' z)) :=
    ((memLp_two_iff_integrable_sq huc.aestronglyMeasurable).mpr hu2).integrable_mul
      ((memLp_two_iff_integrable_sq (continuous_id.mul hu').aestronglyMeasurable).mpr hzu2)
  let q : ℝ → ℝ → ℝ := fun a z ↦ 1 / (1 + (a * z) ^ 2)
  let b : ℝ → ℝ → ℝ := fun a z ↦ z / (1 + (a * z) ^ 2)
  let d : ℝ → ℝ → ℝ := fun a z ↦ (1 - (a * z) ^ 2) / (1 + (a * z) ^ 2) ^ 2
  have hden (a z : ℝ) : 0 < 1 + (a * z) ^ 2 := by positivity
  have hq (a z : ℝ) : 0 ≤ q a z ∧ q a z ≤ 1 := by
    dsimp only [q]
    exact ⟨by positivity, (div_le_one (hden a z)).mpr (le_add_of_nonneg_right (sq_nonneg _))⟩
  have hdc (a : ℝ) : Continuous (d a) :=
    (by fun_prop : Continuous fun z ↦ 1 - (a * z) ^ 2).div₀ (by fun_prop)
      fun z ↦ (pow_pos (hden a z) 2).ne'
  have hd (a z : ℝ) : |d a z| ≤ 1 := by
    dsimp only [d]
    rw [abs_div, abs_of_pos (sq_pos_of_pos (hden a z)), div_le_one (sq_pos_of_pos (hden a z)),
      abs_le]
    constructor <;> nlinarith [sq_nonneg (a * z), sq_nonneg ((a * z) ^ 2)]
  have hb (a : ℝ) (ha : 0 < a) (z : ℝ) : |b a z| ≤ 1 / a := by
    dsimp only [b]
    rw [abs_div, abs_of_pos (hden a z), div_le_div_iff₀ (hden a z) ha]
    have hs := sq_nonneg (a * |z| - 1)
    rw [sub_sq, mul_pow, sq_abs] at hs
    nlinarith only [hs, sq_nonneg (a * z)]
  have hbder (a z : ℝ) : HasDerivAt (b a) (d a z) z := by
    dsimp [b, d]
    cas
  have hbound (a : ℝ) (ha : 0 < a) :
      (∫ z, d a z * u z ^ 2) ≤ (1 / 2 : ℝ) * (∫ z, u z ^ 2) + 2 * ∫ z, (z * u' z) ^ 2 := by
    have hqu : Integrable (fun z ↦ q a z * (u z * (z * u' z))) :=
      hcross.bdd_mul
        (continuous_const.div₀ (by fun_prop) fun z ↦ (hden a z).ne').aestronglyMeasurable <|
        .of_forall fun z ↦ (Real.norm_of_nonneg (hq a z).1).trans_le (hq a z).2
    have hdu : Integrable (fun z ↦ d a z * u z ^ 2) :=
      hu2.bdd_mul (hdc a).aestronglyMeasurable (.of_forall (hd a))
    have hbu : Integrable (fun z ↦ b a z * u z ^ 2) :=
      hu2.bdd_mul (continuous_id.div₀ (by fun_prop) fun z ↦ (hden a z).ne').aestronglyMeasurable
        (.of_forall (hb a ha))
    have e₁ (z : ℝ) : u z * (d a z * u z + b a z * u' z) =
        d a z * u z ^ 2 + q a z * (u z * (z * u' z)) := by
      dsimp only [b, q]
      ring
    have e₂ (z : ℝ) : u' z * (b a z * u z) = q a z * (u z * (z * u' z)) := by
      dsimp only [b, q]
      ring
    -- integration by parts against the bounded multiplier `b a`
    have hibp : ∫ z, d a z * u z ^ 2 + q a z * (u z * (z * u' z)) =
        -∫ z, q a z * (u z * (z * u' z)) := by
      simpa only [e₁, e₂] using integral_mul_deriv_eq_deriv_mul_of_integrable
        (v := fun z ↦ b a z * u z) (fun z _ ↦ hu z) (fun z _ ↦ (hbder a z).mul (hu z))
        ((hdu.add hqu).congr (.of_forall fun z ↦ (e₁ z).symm))
        (hqu.congr (.of_forall fun z ↦ (e₂ z).symm))
        (hbu.congr (.of_forall fun z ↦ by simp only [Pi.mul_apply]; ring))
    rw [integral_add hdu hqu] at hibp
    have hyoung (z : ℝ) : -2 * (q a z * (u z * (z * u' z))) ≤
        (1 / 2 : ℝ) * u z ^ 2 + 2 * (z * u' z) ^ 2 := by
      nlinarith [sq_nonneg (u z + 2 * q a z * (z * u' z)), mul_le_mul_of_nonneg_right
        (pow_le_one₀ (n := 2) (hq a z).1 (hq a z).2) (sq_nonneg (z * u' z))]
    have hint : ∫ z, -2 * (q a z * (u z * (z * u' z))) ≤
        ∫ z, ((1 / 2 : ℝ) * u z ^ 2 + 2 * (z * u' z) ^ 2) :=
      integral_mono (hqu.const_mul _) ((hu2.const_mul _).add (hzu2.const_mul _)) hyoung
    rw [integral_add (hu2.const_mul _) (hzu2.const_mul _), integral_const_mul, integral_const_mul,
      integral_const_mul] at hint
    linarith
  -- remove the multiplier by dominated convergence along `a = 1 / (n + 1) → 0`
  have hat : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun n : ℕ ↦ ∫ z, d (1 / ((n : ℝ) + 1)) z * u z ^ 2) atTop
      (𝓝 (∫ z, u z ^ 2)) := by
    refine tendsto_integral_of_dominated_convergence (fun z ↦ u z ^ 2)
      (fun n ↦ ((hdc _).mul (huc.pow 2)).aestronglyMeasurable) hu2
      (fun n ↦ .of_forall fun z ↦ ?_) (.of_forall fun z ↦ ?_)
    · rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
      exact mul_le_of_le_one_left (sq_nonneg _) (hd _ z)
    · have hc : ContinuousAt (fun s ↦ d s z) 0 := by
        dsimp only [d]
        fun_prop (disch := positivity)
      simpa [d] using (hc.tendsto.comp hat).mul_const (u z ^ 2)
  linarith [le_of_tendsto hlim (.of_forall fun n ↦ hbound _ (Nat.one_div_pos_of_nat))]

end PDE.Analysis
