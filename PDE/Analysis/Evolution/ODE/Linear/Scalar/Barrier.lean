/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Linear.Scalar

/-!
# Lower barriers for a time-dependent dissipative rate

For `q' + r q ≥ r β`, the deviation from the level `β` stays above its initial
lower bound multiplied by `exp (-∫ r)`. The rate and the initial deviation may have
any sign. The derivative is taken within `[a, b]` at the points of `[a, b)`.

The explicit scalar solution satisfies the same comparison when its source is at
least `r β`. This uses the sign convention `q' = f - r q`.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace PDE.Analysis.Evolution

/-- A time-dependent rate gives the lower barrier `β + κ exp (-∫ₐᵗ r)` whenever
`q' + r q ≥ r β` on `[a, b)` and `β + κ ≤ q(a)`. Here `r` and `κ` may have any sign. -/
theorem dissipative_lower_barrier_variable_rate
    {q dq r : ℝ → ℝ} {a b β κ : ℝ} (hab : a ≤ b)
    (hq : ContinuousOn q (Icc a b)) (hr : ContinuousOn r (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt q (dq t) (Icc a b) t)
    (hinit : β + κ ≤ q a)
    (hbound : ∀ t ∈ Ico a b, r t * β ≤ dq t + r t * q t) :
    ∀ t ∈ Icc a b, β + κ * Real.exp (-(∫ s in a..t, r s)) ≤ q t := by
  have h := le_mul_exp_integral_of_hasDerivWithinAt_le
    (e := fun t ↦ β - q t) (de := fun t ↦ -dq t) (k := fun t ↦ -r t)
    hab (continuousOn_const.sub hq) hr.neg
    (fun t ht ↦ (hd t ht).const_sub β) (fun t ht ↦ by
      have hb := hbound t ht
      nlinarith)
  intro t ht
  have hstart : β - q a ≤ -κ := by linarith
  have hle := (h t ht).trans
    (mul_le_mul_of_nonneg_right hstart (Real.exp_nonneg _))
  rw [intervalIntegral.integral_neg] at hle
  nlinarith

/-- For continuous `r` and `f`, the solution of `q' = f - r q` with `q(a) = q₀` and
`β + κ ≤ q₀` satisfies `β + κ exp (-∫ₐᵗ r) ≤ q(t)` on `[a, b]` when `r β ≤ f` on
`[a, b)`. -/
theorem scalarLinearSolution_lower_barrier
    {r f : ℝ → ℝ} (hr : Continuous r) (hf : Continuous f)
    {a b q₀ β κ : ℝ} (hab : a ≤ b) (hinit : β + κ ≤ q₀)
    (hsource : ∀ t ∈ Ico a b, r t * β ≤ f t) :
    ∀ t ∈ Icc a b,
      β + κ * Real.exp (-(∫ s in a..t, r s)) ≤ scalarLinearSolution r f a q₀ t := by
  apply dissipative_lower_barrier_variable_rate hab
    (fun t _ ↦ (hasDerivAt_scalarLinearSolution hr hf a q₀ t).continuousAt.continuousWithinAt)
    hr.continuousOn
    (fun t _ ↦ (hasDerivAt_scalarLinearSolution hr hf a q₀ t).hasDerivWithinAt)
  · simpa only [scalarLinearSolution_initial] using hinit
  · intro t ht
    simpa only [sub_add_cancel] using hsource t ht

end PDE.Analysis.Evolution
