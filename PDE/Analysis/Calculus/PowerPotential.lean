/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SignedPower
public import PDE.Analysis.Calculus.ConvexIntegralPotential
import Mathlib.Analysis.InnerProductSpace.NormPow
import CAS.ExactTactic

/-!
# The integral potential of the odd power

For `r ≥ 1`, the convex function `|x|^(r+1)/(r+1)` has derivative
`|x|^(r-1) x`, including at zero. Whenever the odd power defines a continuous
map into `L²`, the integral potential is differentiable in the domain norm,
with its derivative represented by that `L²` source.

The integral theorem works over an arbitrary measure space. Sobolev embeddings
enter only when constructing the continuous source map for a particular PDE.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace

namespace Real

/-- The scalar potential for the odd power. Its derivative and convexity below
require `r ≥ 1`. -/
def signedPowerPotential (r x : ℝ) : ℝ := |x| ^ (r + 1) / (r + 1)

/-- The potential vanishes at zero. -/
@[simp] theorem signedPowerPotential_zero {r : ℝ} (hr : 1 ≤ r) :
    signedPowerPotential r 0 = 0 := by
  have hp : r + 1 ≠ 0 := ne_of_gt (by linarith)
  simp only [signedPowerPotential, abs_zero, zero_rpow hp, zero_div]

/-- The derivative of the power potential at every real argument, including zero. -/
theorem hasDerivAt_signedPowerPotential {r : ℝ} (hr : 1 ≤ r) (x : ℝ) :
    HasDerivAt (signedPowerPotential r) (signedPower r x) x := by
  have hp : 1 < r + 1 := by linarith
  have hd := (hasDerivAt_abs_rpow x hp).div_const (r + 1)
  change HasDerivAt (signedPowerPotential r)
    ((r + 1) * |x| ^ (r + 1 - 2) * x / (r + 1)) x at hd
  have hvalue : (r + 1) * |x| ^ (r + 1 - 2) * x / (r + 1) = signedPower r x := by
    rw [show r + 1 - 2 = r - 1 by cas, signedPower, mul_assoc,
      mul_div_cancel_left₀ _ (ne_of_gt (zero_lt_one.trans hp))]
  rwa [hvalue] at hd

/-- The power potential is convex, by convexity and monotonicity of the
nonnegative real power composed with the norm. -/
theorem convexOn_signedPowerPotential {r : ℝ} (hr : 1 ≤ r) :
    ConvexOn ℝ univ (signedPowerPotential r) := by
  have hp : 1 ≤ r + 1 := by linarith
  have hnorm : ConvexOn ℝ univ (fun x : ℝ ↦ ‖x‖ ^ (r + 1)) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    exact (rpow_le_rpow (norm_nonneg _)
      ((convexOn_univ_norm (E := ℝ)).2 hx hy ha hb hab) (by linarith)).trans
        ((convexOn_rpow hp).2 (norm_nonneg x) (norm_nonneg y) ha hb hab)
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hdiv := div_le_div_of_nonneg_right (hnorm.2 hx hy ha hb hab)
    (add_nonneg (zero_le_one.trans hr) zero_le_one)
  simpa only [signedPowerPotential, Real.norm_eq_abs, smul_eq_mul,
    add_div, mul_div_assoc] using hdiv

/-- The odd-power potential is nonnegative when its exponent is at least one. -/
theorem signedPowerPotential_nonneg {r : ℝ} (hr : 1 ≤ r) (x : ℝ) :
    0 ≤ signedPowerPotential r x := by
  exact div_nonneg (rpow_nonneg (abs_nonneg x) _) (by linarith)

end Real

namespace PDE.Analysis.Calculus

variable {α V : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The actual odd-power source is the pivot gradient of its integral potential.
Neither differentiability of the source nor finite measure is required. -/
theorem hasFDerivAt_integral_signedPowerPotential
    (J : V →L[ℝ] Lp ℝ 2 μ) {r : ℝ} (hr : 1 ≤ r)
    (N : V → Lp ℝ 2 μ)
    (hNae : ∀ v, N v =ᵐ[μ] fun x ↦ Real.signedPower r (J v x))
    (v : V) (hN : ContinuousAt N v) :
    HasFDerivAt (fun w ↦ ∫ x, Real.signedPowerPotential r (J w x) ∂μ)
      ((innerSL ℝ (N v)).comp J) v :=
  hasFDerivAt_integral_convex_potential J (Real.convexOn_signedPowerPotential hr)
    (Real.hasDerivAt_signedPowerPotential hr) (Real.signedPowerPotential_zero hr)
    (Real.signedPower_zero r) N hNae v hN

/-- An `L²` argument whose odd power is also in `L²` has an integrable power
potential. The measure need not be finite. -/
theorem integrable_signedPowerPotential_of_L2_source
    {β : Type*} [MeasurableSpace β] {ν : Measure β}
    {r : ℝ} (hr : 1 ≤ r) (u p : Lp ℝ 2 ν)
    (hp : p =ᵐ[ν] fun y ↦ Real.signedPower r (u y)) :
    Integrable (fun y ↦ Real.signedPowerPotential r (u y)) ν :=
  integrable_convex_potential_of_L2_gradient
    (Real.convexOn_signedPowerPotential hr) (Real.hasDerivAt_signedPowerPotential hr)
    (Real.signedPowerPotential_zero hr) (Real.signedPower_zero r) u p hp

/-- The unnormalized power density is integrable under the same two `L²`
conditions, including on an infinite measure space. -/
theorem integrable_abs_rpow_of_L2_signedPower
    {β : Type*} [MeasurableSpace β] {ν : Measure β}
    {r : ℝ} (hr : 1 ≤ r) (u p : Lp ℝ 2 ν)
    (hp : p =ᵐ[ν] fun y ↦ Real.signedPower r (u y)) :
    Integrable (fun y ↦ |u y| ^ (r + 1)) ν := by
  have hden : r + 1 ≠ 0 := ne_of_gt (by linarith)
  simpa only [Real.signedPowerPotential, div_mul_cancel₀ _ hden] using
    (integrable_signedPowerPotential_of_L2_source hr u p hp).mul_const (r + 1)

end PDE.Analysis.Calculus
