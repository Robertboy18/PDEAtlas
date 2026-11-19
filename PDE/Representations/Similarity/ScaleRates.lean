/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Logarithmic rates of compatible scales

If `c = a * b` near a time and the three scales satisfy logarithmic derivative laws there,
then the rate of `c` is the sum of the rates of `a` and `b`, provided `c` is nonzero at that
time. The product rule and uniqueness of derivatives give the identity without choosing
a logarithm or defining one rate in terms of the others.
-/

@[expose] public section

namespace PDE.Representations.Similarity

open scoped Topology

/-- The logarithmic rate of a nonzero product is the sum of the factor rates.
Compatibility is required near the time of differentiation, not just at that time. -/
theorem logarithmicRate_eq_add_of_eventuallyEq_mul
    {a b c : ℝ → ℝ} {aRate bRate cRate τ : ℝ}
    (ha : HasDerivAt a (aRate * a τ) τ)
    (hb : HasDerivAt b (bRate * b τ) τ)
    (hc : HasDerivAt c (cRate * c τ) τ)
    (hc_ne : c τ ≠ 0)
    (hcompat : c =ᶠ[𝓝 τ] fun t ↦ a t * b t) :
    cRate = aRate + bRate := by
  apply mul_right_cancel₀ hc_ne
  have hderiv := hc.unique ((ha.mul hb).congr_of_eventuallyEq hcompat)
  calc
    cRate * c τ = (aRate * a τ) * b τ + a τ * (bRate * b τ) := hderiv
    _ = (aRate + bRate) * (a τ * b τ) := by ring
    _ = (aRate + bRate) * c τ := by rw [hcompat.eq_of_nhds]

end PDE.Representations.Similarity
