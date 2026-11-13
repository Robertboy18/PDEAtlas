/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Positive pairings in real `L²`

A strictly positive weight detects every nonzero nonnegative `L²` class.
The measure is arbitrary, and the weight need not have a uniform positive
lower bound. Hölder integrability justifies all pairings.
-/

@[expose] public section

namespace MeasureTheory.Lp

open scoped ENNReal InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Pairing with a nonnegative `L²` weight preserves almost-everywhere order. -/
theorem inner_mono_of_nonneg_ae (w f g : Lp ℝ 2 μ)
    (hw : ∀ᵐ x ∂μ, 0 ≤ w x) (hfg : ∀ᵐ x ∂μ, f x ≤ g x) :
    ⟪w, f⟫_ℝ ≤ ⟪w, g⟫_ℝ := by
  simp only [L2.inner_def, RCLike.inner_apply, conj_trivial]
  apply integral_mono_ae ((Lp.memLp f).integrable_mul (Lp.memLp w))
    ((Lp.memLp g).integrable_mul (Lp.memLp w))
  filter_upwards [hw, hfg] with x hx h
  exact mul_le_mul_of_nonneg_right h hx

/-- A nonnegative class with zero pairing against a strictly positive weight
vanishes, even when the weight approaches zero. -/
theorem eq_zero_of_nonneg_ae_of_inner_eq_zero (w f : Lp ℝ 2 μ)
    (hw : ∀ᵐ x ∂μ, 0 < w x) (hf : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hinner : ⟪w, f⟫_ℝ = 0) : f = 0 := by
  have hprod : ∀ᵐ x ∂μ, 0 ≤ f x * w x := by
    filter_upwards [hw, hf] with x hx hy
    exact mul_nonneg hy hx.le
  have heq : (fun x ↦ f x * w x) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hprod
      ((Lp.memLp f).integrable_mul (Lp.memLp w))).mp (by
        simpa only [L2.inner_def, RCLike.inner_apply, conj_trivial] using hinner)
  apply Lp.ext
  filter_upwards [hw, heq, coeFn_zero ℝ 2 μ] with x hx he hzero
  exact ((mul_eq_zero.mp he).resolve_right hx.ne').trans hzero.symm

/-- A strictly positive weight has positive pairing with every nonzero
nonnegative class. -/
theorem inner_pos_of_pos_ae_of_nonneg_ae (w f : Lp ℝ 2 μ)
    (hw : ∀ᵐ x ∂μ, 0 < w x) (hf : ∀ᵐ x ∂μ, 0 ≤ f x) (hne : f ≠ 0) :
    0 < ⟪w, f⟫_ℝ := by
  have hnonneg : 0 ≤ ⟪w, f⟫_ℝ := by
    simp only [L2.inner_def, RCLike.inner_apply, conj_trivial]
    apply integral_nonneg_of_ae
    filter_upwards [hw, hf] with x hx hy
    exact mul_nonneg hy hx.le
  exact lt_of_le_of_ne hnonneg (fun h ↦
    hne (eq_zero_of_nonneg_ae_of_inner_eq_zero w f hw hf h.symm))

end MeasureTheory.Lp
