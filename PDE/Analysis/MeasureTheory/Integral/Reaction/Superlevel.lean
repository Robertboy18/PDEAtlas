/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# A reaction bound forced by an initial superlevel set

A field close in L² to a large initial value must either retain a large reaction
or spend that L² distance. Integrating this alternative gives a lower bound on
the reaction without assuming continuity or an evolution equation.
-/

@[expose] public section

open MeasureTheory Filter

namespace MeasureTheory

/-- On an initial superlevel set, either the displacement changes by at least `d`
or the reaction remains at least `b` in absolute value. -/
theorem sq_mul_sq_le_sq_sub_add_reaction {a b d u g : ℝ} {f : ℝ → ℝ}
    (hb : 0 ≤ b) (hd : 0 ≤ d) (hg : a + d ≤ g)
    (hf : ∀ z : ℝ, a ≤ z → b ≤ |f z|) :
    b ^ 2 * d ^ 2 ≤ b ^ 2 * (u - g) ^ 2 + d ^ 2 * (f u) ^ 2 := by
  by_cases hu : a ≤ u
  · have h := hf u hu
    have hsq : b ^ 2 ≤ (f u) ^ 2 := by nlinarith [sq_abs (f u)]
    nlinarith [mul_nonneg (sq_nonneg b) (sq_nonneg (u - g)),
      mul_le_mul_of_nonneg_left hsq (sq_nonneg d)]
  · have hsq : d ^ 2 ≤ (u - g) ^ 2 := by
      have hud : u - g ≤ -d := by linarith
      nlinarith
    nlinarith [mul_nonneg (sq_nonneg d) (sq_nonneg (f u)),
      mul_le_mul_of_nonneg_left hsq (sq_nonneg b)]

/-- An L² displacement estimate and an L² reaction estimate control the measure
of every initial superlevel set. The measure can already be restricted to that
set, or to a spacetime cylinder. -/
theorem mul_measure_le_integral_sq_sub_add_reaction
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {u g : X → ℝ} {f : ℝ → ℝ} {a b d : ℝ}
    (hb : 0 ≤ b) (hd : 0 ≤ d) (hg : ∀ᵐ x ∂μ, a + d ≤ g x)
    (hf : ∀ z : ℝ, a ≤ z → b ≤ |f z|)
    (hu : Integrable (fun x ↦ (u x - g x) ^ 2) μ)
    (hr : Integrable (fun x ↦ (f (u x)) ^ 2) μ) :
    b ^ 2 * d ^ 2 * μ.real Set.univ ≤
      b ^ 2 * (∫ x, (u x - g x) ^ 2 ∂μ) + d ^ 2 * (∫ x, (f (u x)) ^ 2 ∂μ) := by
  have h := integral_mono_ae (integrable_const (b ^ 2 * d ^ 2))
    ((hu.const_mul (b ^ 2)).add (hr.const_mul (d ^ 2)))
    (hg.mono fun x hx ↦ sq_mul_sq_le_sq_sub_add_reaction hb hd hx hf)
  simpa only [Pi.add_apply,
    integral_add (hu.const_mul (b ^ 2)) (hr.const_mul (d ^ 2)),
    integral_const_mul, integral_const, smul_eq_mul, mul_comm (μ.real Set.univ),
    mul_assoc] using h

end MeasureTheory
