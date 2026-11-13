/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Product rules with vanishing or cancelling factors

When the differentiable factor vanishes, the other factor only needs to be
continuous. The difference quotient then has the usual product-rule limit.
For differentiable products `A * f - B * g`, the mixed terms cancel whenever
`B′ = A` and `f′ = g`. No differential equation or profile is fixed here.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace PDE.Analysis

/-- A differentiable zero absorbs the derivative of a merely continuous factor. -/
theorem hasDerivAt_mul_of_zero_of_continuousAt
    {f g : ℝ → ℝ} {f' a : ℝ} (hf : HasDerivAt f f' a)
    (hg : ContinuousAt g a) (hzero : f a = 0) :
    HasDerivAt (fun x ↦ f x * g x) (f' * g a) a := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hlim := hf.tendsto_slope.mul (hg.tendsto.mono_left nhdsWithin_le_nhds)
  convert hlim using 1
  ext x
  simp only [slope_def_field, hzero, zero_mul, sub_zero]
  field_simp

/-- Matching derivatives cancel the two mixed terms in a difference of products. -/
theorem HasDerivAt.mul_sub_mul_cancel
    {A B f g : ℝ → ℝ} {A' g' x : ℝ}
    (hA : HasDerivAt A A' x) (hB : HasDerivAt B (A x) x)
    (hf : HasDerivAt f (g x) x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun y ↦ A y * f y - B y * g y) (A' * f x - B x * g') x := by
  convert (hA.mul hf).sub (hB.mul hg) using 1
  ring

end PDE.Analysis
